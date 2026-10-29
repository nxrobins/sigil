# Serialized publication through existing KV

Public-source sigil/storage public.1 is an outer-ring trusted adapter over the unchanged
sigil/kv package. All parameters/results are Internal; effects are KvIO, Alloc,
FFI and Unsafe. It requires the existing ephemeral host profile for host calls
conditioned on prior host results. No new host operation or permission exists.
Normal Public-only package execution must continue to refuse this profile.

load(ns,ns_len,key,key_len) reads an opaque value. Namespace length is 1..64,
key length 1..128, and returned value at most 32768 bytes. All arguments are
i64 pointers/lengths; they must fit the positive signed 32-bit span before
conversion to the existing KV ABI. A missing value returns -404.

publish(ns,ns_len,key,key_len,expected,expected_len,next,next_len) validates
spans, reads the current value and requires byte equality to expected. Empty
expected means the key must be absent, not that any existing value may be
overwritten. Next must contain 1..32768 bytes. Missing/unexpected state or
unequal bytes returns -409; other KV failures propagate. Only after all checks
does one existing kv::put publish the new value. Returns 0 on success.

Read and write grants are separately required. A read grant never grants
writes; a write grant alone cannot satisfy the prior-state check. Missing or
wrong namespace grants fail closed. The atomic KV write leaves the old value
in place when it fails; the checkpoint envelope can retain a predecessor
inside the single value. This adapter never deletes values.

The host MUST serialize cooperating writers across load/validate/publish.
This is not concurrent compare-and-swap: a different writer can race the
read/write interval. The existing KV adapter has no conditional-write primitive.
Do not use this API as a multi-writer transaction or a crash-durable database;
durability retains KV's OS-write-back semantics. A successfully published value
followed by a host-side timeout is an uncertain outcome: read it before retry.

State bytes are opaque. Callers must validate their application/checkpoint
schema before publication and after load. The adapter does not authenticate
records, relabel stored data Public or run the inner-ring numerical packages.
Secret inputs remain inadmissible without separate explicit declassification.
Invalid backing can trap; callers must supply live owned input spans.
