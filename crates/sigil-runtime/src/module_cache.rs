//! Bounded, byte-keyed cache of compiled wasm modules for the ephemeral runtime.
//!
//! LOAD-BEARING: the key is the ENTIRE input byte string, compared byte for byte -- never a
//! hash or a prefix -- because a hit skips the host-profile check that guards compilation, and
//! only inputs that passed it are ever stored. The cache is bounded at
//! [`MODULE_CACHE_CAPACITY`] entries so a long-lived host (sigil-serve, sigil-mcp) running many
//! distinct tools cannot grow it without bound.
//!
//! WHY MORE THAN ONE ENTRY. The previous cache held a single module and compiled it while
//! holding the global lock. Test suites that execute several distinct multi-MB modules from
//! parallel test threads therefore evicted each other on every switch and serialised every
//! Cranelift compile behind one mutex. Here the global lock covers only lookup and insertion;
//! each entry has its own lock, held across that entry's compile, so different modules compile
//! in parallel while concurrent callers for the SAME module wait for one compile instead of
//! duplicating it.
//!
//! FAIL CLOSED. A failed compile is never cached: its entry is removed and the error returned,
//! so the next caller retries from scratch, exactly as the single-entry cache behaved. A lock
//! poisoned by a panicking compile is recovered and its entry treated as empty, so a panic can
//! cost a recompile but can never surface a half-built value.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex, MutexGuard};

/// How many distinct compiled modules the ephemeral runtime keeps.
///
/// Sized from a measured working set, not guessed. `tests/pipeline_differential.rs`, the
/// largest consumer, executes 11 distinct modules (2026-10-04): the single-entry cache compiled
/// them 112 times, capacity 8 still evicted (13 compiles), and 16 holds the set with headroom
/// for the other differential suites sharing the process. Each entry pins one compiled module
/// (native code plus metadata), so this is also the memory bound a long-lived host accepts.
pub(crate) const MODULE_CACHE_CAPACITY: usize = 16;

/// One cache slot: the exact key bytes and the value compiled from them, once compiled.
type Slot<T> = Arc<Mutex<Option<T>>>;

/// A fixed-capacity, least-recently-used cache from byte strings to compiled values.
pub(crate) struct ModuleCache<T> {
    capacity: usize,
    /// Most recently used first.
    entries: Mutex<VecDeque<(Vec<u8>, Slot<T>)>>,
}

fn recover<G>(result: Result<G, std::sync::PoisonError<G>>) -> G {
    result.unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl<T: Clone> ModuleCache<T> {
    /// An empty cache holding at most `capacity` entries.
    pub(crate) const fn new(capacity: usize) -> Self {
        Self {
            capacity,
            entries: Mutex::new(VecDeque::new()),
        }
    }

    /// Return the value cached for exactly `key`, compiling it with `compile` on a miss.
    ///
    /// `compile` runs with no global lock held. A second caller for the same key blocks until
    /// the first finishes and then shares its result; callers for other keys are not blocked.
    pub(crate) fn get_or_compile<E>(
        &self,
        key: &[u8],
        compile: impl FnOnce() -> Result<T, E>,
    ) -> Result<T, E> {
        let slot = self.slot_for(key);
        let mut value: MutexGuard<'_, Option<T>> = recover(slot.lock());
        if let Some(hit) = value.as_ref() {
            return Ok(hit.clone());
        }
        match compile() {
            Ok(compiled) => {
                *value = Some(compiled.clone());
                Ok(compiled)
            }
            Err(error) => {
                drop(value);
                self.forget(&slot);
                Err(error)
            }
        }
    }

    /// Find or insert the slot for `key`, marking it most recently used and evicting the least
    /// recently used entry beyond capacity. Holds the global lock only for this bookkeeping.
    fn slot_for(&self, key: &[u8]) -> Slot<T> {
        let mut entries = recover(self.entries.lock());
        if let Some(index) = entries
            .iter()
            .position(|(bytes, _)| bytes.as_slice() == key)
        {
            let entry = entries
                .remove(index)
                .expect("the index was just found in this same locked deque");
            let slot = Arc::clone(&entry.1);
            entries.push_front(entry);
            return slot;
        }
        let slot: Slot<T> = Arc::new(Mutex::new(None));
        entries.push_front((key.to_vec(), Arc::clone(&slot)));
        // An evicted entry still being compiled stays alive through its caller's `Arc`; that
        // caller gets its value, which simply is not cached.
        entries.truncate(self.capacity);
        slot
    }

    /// Drop `slot`'s entry after a failed compile, if it is still present.
    fn forget(&self, slot: &Slot<T>) {
        let mut entries = recover(self.entries.lock());
        entries.retain(|(_, candidate)| !Arc::ptr_eq(candidate, slot));
    }

    /// The keys currently cached, most recently used first. Test-only introspection.
    #[cfg(test)]
    fn keys(&self) -> Vec<Vec<u8>> {
        recover(self.entries.lock())
            .iter()
            .map(|(bytes, _)| bytes.clone())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc;
    use std::time::Duration;

    fn ok(value: u32) -> impl FnOnce() -> Result<u32, String> {
        move || Ok(value)
    }

    /// The regression this cache exists to fix: alternating between two modules must compile
    /// each ONCE. The single-entry cache it replaced compiles on every switch, so this fails
    /// against capacity 1 -- the second half asserts exactly that, proving the counter can see
    /// thrash when it happens.
    #[test]
    fn alternating_keys_compile_once_each_and_capacity_one_thrashes() {
        let compiles = AtomicUsize::new(0);
        let counting = |value: u32| {
            let compiles = &compiles;
            move || {
                compiles.fetch_add(1, Ordering::SeqCst);
                Ok::<u32, String>(value)
            }
        };

        let cache = ModuleCache::new(MODULE_CACHE_CAPACITY);
        for _ in 0..10 {
            assert_eq!(cache.get_or_compile(b"module-a", counting(1)), Ok(1));
            assert_eq!(cache.get_or_compile(b"module-b", counting(2)), Ok(2));
        }
        assert_eq!(
            compiles.load(Ordering::SeqCst),
            2,
            "each module compiles exactly once"
        );

        compiles.store(0, Ordering::SeqCst);
        let single = ModuleCache::new(1);
        for _ in 0..10 {
            single
                .get_or_compile(b"module-a", counting(1))
                .expect("compiles");
            single
                .get_or_compile(b"module-b", counting(2))
                .expect("compiles");
        }
        assert_eq!(
            compiles.load(Ordering::SeqCst),
            20,
            "anti-stub: a single-entry cache recompiles on every switch, and the counter sees it"
        );
    }

    #[test]
    fn least_recently_used_entry_is_evicted_at_capacity() {
        let cache = ModuleCache::new(2);
        cache.get_or_compile(b"a", ok(1)).expect("compiles");
        cache.get_or_compile(b"b", ok(2)).expect("compiles");
        // Touch `a`, so `b` becomes least recently used.
        cache.get_or_compile(b"a", ok(99)).expect("hit");
        cache.get_or_compile(b"c", ok(3)).expect("compiles");
        assert_eq!(cache.keys(), vec![b"c".to_vec(), b"a".to_vec()]);
        // A hit returns the ORIGINAL value, never the closure's: `a` was not recompiled.
        assert_eq!(cache.get_or_compile(b"a", ok(99)), Ok(1));
    }

    /// The key is the whole byte string: a prefix, an extension, or a one-byte change misses.
    #[test]
    fn keys_compare_every_byte() {
        let cache = ModuleCache::new(MODULE_CACHE_CAPACITY);
        cache.get_or_compile(b"module", ok(1)).expect("compiles");
        assert_eq!(cache.get_or_compile(b"modul", ok(2)), Ok(2));
        assert_eq!(cache.get_or_compile(b"modules", ok(3)), Ok(3));
        assert_eq!(cache.get_or_compile(b"moduLe", ok(4)), Ok(4));
        assert_eq!(cache.get_or_compile(b"module", ok(5)), Ok(1));
    }

    #[test]
    fn a_failed_compile_is_not_cached() {
        let cache = ModuleCache::new(MODULE_CACHE_CAPACITY);
        assert_eq!(
            cache.get_or_compile(b"bad", || Err::<u32, _>("rejected".to_string())),
            Err("rejected".to_string())
        );
        assert!(cache.keys().is_empty(), "a failure must not occupy a slot");
        assert_eq!(
            cache.get_or_compile(b"bad", ok(7)),
            Ok(7),
            "the next caller retries"
        );
    }

    /// Different keys compile CONCURRENTLY. Each compile waits for the other to start, so a
    /// cache that serialises compiles behind one lock (the bug this replaces) cannot finish:
    /// the bounded wait turns that deadlock into a failure instead of a hang.
    #[test]
    fn distinct_keys_compile_in_parallel() {
        let cache = Arc::new(ModuleCache::new(MODULE_CACHE_CAPACITY));
        let (a_started, a_seen) = mpsc::channel::<()>();
        let (b_started, b_seen) = mpsc::channel::<()>();
        let rendezvous = |started: mpsc::Sender<()>, other: mpsc::Receiver<()>, value: u32| {
            move || {
                started.send(()).expect("the peer thread is alive");
                other
                    .recv_timeout(Duration::from_secs(10))
                    .map(|()| value)
                    .map_err(|_| "the other compile never started: compiles are serialised")
            }
        };
        let left = {
            let cache = Arc::clone(&cache);
            let compile = rendezvous(a_started, b_seen, 1);
            std::thread::spawn(move || cache.get_or_compile(b"a", compile))
        };
        let right = {
            let cache = Arc::clone(&cache);
            let compile = rendezvous(b_started, a_seen, 2);
            std::thread::spawn(move || cache.get_or_compile(b"b", compile))
        };
        assert_eq!(left.join().expect("thread a"), Ok(1));
        assert_eq!(right.join().expect("thread b"), Ok(2));
    }

    /// Concurrent callers for the SAME key share one compile rather than racing to duplicate it.
    #[test]
    fn concurrent_callers_for_one_key_compile_once() {
        let cache = Arc::new(ModuleCache::new(MODULE_CACHE_CAPACITY));
        let compiles = Arc::new(AtomicUsize::new(0));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let cache = Arc::clone(&cache);
                let compiles = Arc::clone(&compiles);
                std::thread::spawn(move || {
                    cache.get_or_compile(b"shared", || {
                        compiles.fetch_add(1, Ordering::SeqCst);
                        std::thread::sleep(Duration::from_millis(50));
                        Ok::<u32, String>(42)
                    })
                })
            })
            .collect();
        for thread in threads {
            assert_eq!(thread.join().expect("caller thread"), Ok(42));
        }
        assert_eq!(compiles.load(Ordering::SeqCst), 1);
    }

    /// A compile that panics leaves its entry empty, not half-built: the next caller recompiles.
    #[test]
    fn a_panicking_compile_poisons_nothing() {
        let cache = Arc::new(ModuleCache::new(MODULE_CACHE_CAPACITY));
        let panicking = {
            let cache = Arc::clone(&cache);
            std::thread::spawn(move || {
                cache.get_or_compile(b"p", || -> Result<u32, String> {
                    panic!("compile blew up")
                })
            })
        };
        assert!(panicking.join().is_err(), "the compile panicked");
        assert_eq!(cache.get_or_compile(b"p", ok(5)), Ok(5));
        assert_eq!(
            cache.get_or_compile(b"p", ok(6)),
            Ok(5),
            "and the recompile is cached"
        );
    }
}
