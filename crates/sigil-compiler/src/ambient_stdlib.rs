//! Token-driven ambient standard-library injection.
//!
//! The scanner recognizes language-level conveniences such as `Ok`, `Vec`, and
//! bounded collections. A declarative graph expands their dependencies before
//! sources are appended in deterministic path order.

use std::collections::BTreeSet;

use crate::lexer::{TokenKind, lex_with_id};
use crate::source::SourceFile;
use crate::span::SourceId;

/// On-disk path for stdlib Result. Used as the SourceFile name so
/// M001 (filename = first module name) and cert source_fingerprint
/// behave naturally (the stdlib file declares `module result;`).
pub const STDLIB_RESULT_PATH: &str = "stdlib/sigil/result.sigil";

/// On-disk path for stdlib Option. Same M001 / fingerprint rationale.
pub const STDLIB_OPTION_PATH: &str = "stdlib/sigil/option.sigil";

/// Embedded source for `stdlib/sigil/result.sigil` (compile-time
/// `include_str!`, NO runtime filesystem access — matches Wall 5's
/// N8-W5S1 "hermetic compiler" lint).
pub const STDLIB_RESULT_SOURCE: &str = include_str!("../../../stdlib/sigil/result.sigil");

/// Embedded source for `stdlib/sigil/option.sigil`.
pub const STDLIB_OPTION_SOURCE: &str = include_str!("../../../stdlib/sigil/option.sigil");

/// On-disk path for stdlib Vec (PR C3). Same M001 / fingerprint rationale —
/// the file declares `module vec;`.
pub const STDLIB_VEC_PATH: &str = "stdlib/sigil/vec.sigil";

/// Embedded source for `stdlib/sigil/vec.sigil`.
pub const STDLIB_VEC_SOURCE: &str = include_str!("../../../stdlib/sigil/vec.sigil");

/// On-disk path for stdlib map (PR 4). Same M001 / fingerprint rationale —
/// the file declares `module map;`.
pub const STDLIB_MAP_PATH: &str = "stdlib/sigil/map.sigil";

/// Embedded source for `stdlib/sigil/map.sigil`.
pub const STDLIB_MAP_SOURCE: &str = include_str!("../../../stdlib/sigil/map.sigil");

/// On-disk path for stdlib strings (PR S-search). Declares `module strings;`.
pub const STDLIB_STRINGS_PATH: &str = "stdlib/sigil/strings.sigil";

/// Embedded source for `stdlib/sigil/strings.sigil`.
pub const STDLIB_STRINGS_SOURCE: &str = include_str!("../../../stdlib/sigil/strings.sigil");

/// On-disk path for stdlib owned-string construction (PR S2). Declares
/// `module string;` — SINGULAR (the OWNED builders `str_concat`/…), distinct
/// from the plural `strings.sigil` (the borrowing views). Injected only on an
/// owned-builder trigger so borrow-only programs stay byte-identical (ET-5).
pub const STDLIB_STRING_PATH: &str = "stdlib/sigil/string.sigil";

/// Embedded source for `stdlib/sigil/string.sigil`.
pub const STDLIB_STRING_SOURCE: &str = include_str!("../../../stdlib/sigil/string.sigil");

/// On-disk path for stdlib traits (PR-3c). Declares `module traits;` — the
/// `Hash`/`Eq` trait contracts + the built-in primitive impl fns.
pub const STDLIB_TRAITS_PATH: &str = "stdlib/sigil/traits.sigil";

/// Embedded source for `stdlib/sigil/traits.sigil`.
pub const STDLIB_TRAITS_SOURCE: &str = include_str!("../../../stdlib/sigil/traits.sigil");

/// BoundedVec PR-1: `module bounded_vec_i64;` — the BOUNDED, stack-backed `i64`
/// vectors. Injected on a `BoundedVec_i64_8` type-name trigger (a concrete,
/// non-generic name, so it appears bare, not as `Name<…>`).
pub const STDLIB_BOUNDED_VEC_I64_PATH: &str = "stdlib/sigil/bounded_vec_i64.sigil";

/// Embedded source for `stdlib/sigil/bounded_vec_i64.sigil`.
pub const STDLIB_BOUNDED_VEC_I64_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_vec_i64.sigil");

/// BoundedVec Phase 2 (zip/enumerate): `module bounded_pair_vec_i64;` — BOUNDED
/// vectors of `(i64, i64)` pairs, the `zip`/`enumerate` result type. Injected on a
/// `BoundedPairVec_i64_i64_8` type name AND transitively whenever `bounded_vec_i64`
/// is (its `zip`/`enumerate` methods reference this family).
pub const STDLIB_BOUNDED_PAIR_VEC_I64_PATH: &str = "stdlib/sigil/bounded_pair_vec_i64.sigil";

/// Embedded source for `stdlib/sigil/bounded_pair_vec_i64.sigil`.
pub const STDLIB_BOUNDED_PAIR_VEC_I64_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_pair_vec_i64.sigil");

/// BoundedMap PR (Phase 4): the BOUNDED `i64`→`i64` map. Injected on a
/// `BoundedMap_i64_i64_*` type-name trigger (+ transitive Option/Result for `get`).
pub const STDLIB_BOUNDED_MAP_I64_I64_PATH: &str = "stdlib/sigil/bounded_map_i64_i64.sigil";
pub const STDLIB_BOUNDED_MAP_I64_I64_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_map_i64_i64.sigil");

/// BoundedSet PR (Phase 4): the BOUNDED `i64` set. Injected on a `BoundedSet_i64_*`
/// trigger. No transitive deps (insert/contains return bool, `==` keys).
pub const STDLIB_BOUNDED_SET_I64_PATH: &str = "stdlib/sigil/bounded_set_i64.sigil";
pub const STDLIB_BOUNDED_SET_I64_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_set_i64.sigil");

/// BoundedMap PR (Phase 4): the BOUNDED `str`-keyed maps (`str`→`str`, `str`→`i64`).
/// Injected on a `BoundedMap_str_*` trigger (+ transitive strings/vec for the
/// content-equality `str_bytes_eq` key scan, + Option/Result for `get`).
pub const STDLIB_BOUNDED_MAP_STR_PATH: &str = "stdlib/sigil/bounded_map_str.sigil";
pub const STDLIB_BOUNDED_MAP_STR_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_map_str.sigil");

/// SOL1: the BOUNDED `u256`→`u256` map — the Solidity frontend's `mapping(address
/// => uint256)` / `mapping(uint256 => uint256)` target. Injected on a
/// `BoundedMap_u256_u256_*` trigger (+ transitive Option/Result for `get`, +
/// `u256.sigil` for the `==` key compare which lowers to `u256_eq` and the u256
/// value ops).
pub const STDLIB_BOUNDED_MAP_U256_U256_PATH: &str = "stdlib/sigil/bounded_map_u256_u256.sigil";
pub const STDLIB_BOUNDED_MAP_U256_U256_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_map_u256_u256.sigil");

/// SOL-AIRDROP (Rung C): the BOUNDED `u256` VECTOR — the `recipients`/`amounts`
/// arrays passed to `BoundedMap_u256_u256_64::batch_transfer`. The map's
/// `batch_transfer` SIGNATURE references `BoundedVec_u256_64`, so this module is
/// co-injected WHENEVER the map is (a single post-pass below), never on its own
/// trigger; DCE removes it when no airdrop is present.
pub const STDLIB_BOUNDED_VEC_U256_PATH: &str = "stdlib/sigil/bounded_vec_u256.sigil";
pub const STDLIB_BOUNDED_VEC_U256_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_vec_u256.sigil");

/// SOL-ERC20: the BOUNDED TWO-KEY `(u256, u256)`→`u256` map — the Solidity
/// frontend's `mapping(address => mapping(address => uint256))` (ERC20 `allowance`)
/// target. Injected on a `BoundedMap2_u256_u256_u256_*` trigger (+ transitive
/// Option/Result for `get`, + `u256.sigil` for the `==` key compares, + the
/// single-level `bounded_map_u256_u256` whose `transfer` is the `transfer_from`
/// balance-move callee).
pub const STDLIB_BOUNDED_MAP2_U256_U256_U256_PATH: &str =
    "stdlib/sigil/bounded_map2_u256_u256_u256.sigil";
pub const STDLIB_BOUNDED_MAP2_U256_U256_U256_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_map2_u256_u256_u256.sigil");

/// BoundedSet PR (Phase 4): the BOUNDED `str` set. Injected on a `BoundedSet_str_*`
/// trigger (+ transitive strings/vec for `str_bytes_eq`). No Option (bool API).
pub const STDLIB_BOUNDED_SET_STR_PATH: &str = "stdlib/sigil/bounded_set_str.sigil";
pub const STDLIB_BOUNDED_SET_STR_SOURCE: &str =
    include_str!("../../../stdlib/sigil/bounded_set_str.sigil");

/// Parser PR-0 (Tier 3): `module arena;` — the typed index-addressed arena
/// (`Arena<T>`, the SIGIL parser's AST storage). Injected on `Arena::` /
/// `Arena<` (the scoped two-follower pattern, like Vec/Map).
pub const STDLIB_ARENA_PATH: &str = "stdlib/sigil/arena.sigil";

/// Embedded source for `stdlib/sigil/arena.sigil`.
pub const STDLIB_ARENA_SOURCE: &str = include_str!("../../../stdlib/sigil/arena.sigil");

/// u256 PR-U1: `module u256;` — the native 256-bit checked multi-limb arithmetic
/// (the `u256 +`/`-`/comparison operators lower to these `u256_*` fns). Injected
/// whenever a `u256`/`i256` type name appears (a conservative over-include; the
/// unused fns are dead-code-eliminated). No transitive stdlib deps. A user
/// `module u256;` suppresses it.
pub const STDLIB_U256_PATH: &str = "stdlib/sigil/u256.sigil";

/// Embedded source for `stdlib/sigil/u256.sigil`.
pub const STDLIB_U256_SOURCE: &str = include_str!("../../../stdlib/sigil/u256.sigil");

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(usize)]
enum AmbientModule {
    Arena,
    BoundedMap2U256U256U256,
    BoundedMapI64I64,
    BoundedMapStr,
    BoundedMapU256U256,
    BoundedPairVecI64,
    BoundedSetI64,
    BoundedSetStr,
    BoundedVecI64,
    BoundedVecU256,
    Map,
    Option,
    Result,
    String,
    Strings,
    Traits,
    U256,
    Vec,
}

const ALL_MODULES: [AmbientModule; 18] = [
    AmbientModule::Arena,
    AmbientModule::BoundedMap2U256U256U256,
    AmbientModule::BoundedMapI64I64,
    AmbientModule::BoundedMapStr,
    AmbientModule::BoundedMapU256U256,
    AmbientModule::BoundedPairVecI64,
    AmbientModule::BoundedSetI64,
    AmbientModule::BoundedSetStr,
    AmbientModule::BoundedVecI64,
    AmbientModule::BoundedVecU256,
    AmbientModule::Map,
    AmbientModule::Option,
    AmbientModule::Result,
    AmbientModule::String,
    AmbientModule::Strings,
    AmbientModule::Traits,
    AmbientModule::U256,
    AmbientModule::Vec,
];

struct AmbientDescriptor {
    path: &'static str,
    source: &'static str,
    dependencies: &'static [AmbientModule],
}

const MODULE_DESCRIPTORS: [AmbientDescriptor; 18] = [
    AmbientDescriptor {
        path: STDLIB_ARENA_PATH,
        source: STDLIB_ARENA_SOURCE,
        dependencies: &[AmbientModule::Vec],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_MAP2_U256_U256_U256_PATH,
        source: STDLIB_BOUNDED_MAP2_U256_U256_U256_SOURCE,
        dependencies: &[
            AmbientModule::BoundedMapU256U256,
            AmbientModule::Option,
            AmbientModule::U256,
        ],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_MAP_I64_I64_PATH,
        source: STDLIB_BOUNDED_MAP_I64_I64_SOURCE,
        dependencies: &[AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_MAP_STR_PATH,
        source: STDLIB_BOUNDED_MAP_STR_SOURCE,
        dependencies: &[AmbientModule::Strings, AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_MAP_U256_U256_PATH,
        source: STDLIB_BOUNDED_MAP_U256_U256_SOURCE,
        dependencies: &[
            AmbientModule::BoundedVecU256,
            AmbientModule::Option,
            AmbientModule::U256,
        ],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_PAIR_VEC_I64_PATH,
        source: STDLIB_BOUNDED_PAIR_VEC_I64_SOURCE,
        dependencies: &[AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_SET_I64_PATH,
        source: STDLIB_BOUNDED_SET_I64_SOURCE,
        dependencies: &[],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_SET_STR_PATH,
        source: STDLIB_BOUNDED_SET_STR_SOURCE,
        dependencies: &[AmbientModule::Strings],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_VEC_I64_PATH,
        source: STDLIB_BOUNDED_VEC_I64_SOURCE,
        dependencies: &[AmbientModule::BoundedPairVecI64, AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_BOUNDED_VEC_U256_PATH,
        source: STDLIB_BOUNDED_VEC_U256_SOURCE,
        dependencies: &[AmbientModule::Option, AmbientModule::U256],
    },
    AmbientDescriptor {
        path: STDLIB_MAP_PATH,
        source: STDLIB_MAP_SOURCE,
        dependencies: &[
            AmbientModule::Vec,
            AmbientModule::Option,
            AmbientModule::Traits,
        ],
    },
    AmbientDescriptor {
        path: STDLIB_OPTION_PATH,
        source: STDLIB_OPTION_SOURCE,
        dependencies: &[AmbientModule::Result],
    },
    AmbientDescriptor {
        path: STDLIB_RESULT_PATH,
        source: STDLIB_RESULT_SOURCE,
        dependencies: &[],
    },
    AmbientDescriptor {
        path: STDLIB_STRING_PATH,
        source: STDLIB_STRING_SOURCE,
        dependencies: &[AmbientModule::Vec, AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_STRINGS_PATH,
        source: STDLIB_STRINGS_SOURCE,
        dependencies: &[AmbientModule::Vec, AmbientModule::Option],
    },
    AmbientDescriptor {
        path: STDLIB_TRAITS_PATH,
        source: STDLIB_TRAITS_SOURCE,
        dependencies: &[],
    },
    AmbientDescriptor {
        path: STDLIB_U256_PATH,
        source: STDLIB_U256_SOURCE,
        dependencies: &[],
    },
    AmbientDescriptor {
        path: STDLIB_VEC_PATH,
        source: STDLIB_VEC_SOURCE,
        dependencies: &[AmbientModule::Option],
    },
];

/// Exact compiler-coupled ambient stdlib inputs for package identity and
/// collision checks. Returned in lexical path order so callers never inherit
/// enum/table layout as protocol meaning.
pub(crate) fn all_module_sources() -> Vec<(&'static str, &'static str)> {
    let mut sources: Vec<_> = MODULE_DESCRIPTORS
        .iter()
        .map(|descriptor| (descriptor.path, descriptor.source))
        .collect();
    sources.sort_by_key(|(path, _)| *path);
    sources
}

// Consumed only by `package` (lock verification and ambient-ownership maps), which is
// itself json-gated — under solver-without-json builds this would otherwise be dead code.
#[cfg(feature = "json")]
pub(crate) fn all_module_names() -> Vec<&'static str> {
    let mut names: Vec<_> = MODULE_DESCRIPTORS
        .iter()
        .map(|descriptor| {
            descriptor
                .path
                .rsplit('/')
                .next()
                .and_then(|name| name.strip_suffix(".sigil"))
                .expect("embedded stdlib paths are canonical .sigil files")
        })
        .collect();
    names.sort();
    names
}

impl AmbientModule {
    fn descriptor(self) -> &'static AmbientDescriptor {
        &MODULE_DESCRIPTORS[self as usize]
    }

    fn path(self) -> &'static str {
        self.descriptor().path
    }

    fn source(self) -> &'static str {
        self.descriptor().source
    }

    fn dependencies(self) -> &'static [AmbientModule] {
        self.descriptor().dependencies
    }
}

/// Direct ambient needs and user declarations discovered during token scanning.
#[derive(Debug, Default, Clone, Copy)]
pub struct AmbientNeeds {
    pub need_result: bool,
    pub need_option: bool,
    pub need_vec: bool,
    pub declares_module_result: bool,
    pub declares_module_option: bool,
    pub declares_module_vec: bool,
    /// CF-C3: the source declares its OWN `record Vec` — never inject the
    /// stdlib vector over it (a second unqualified record named `Vec` would
    /// silently collide in the global type universe).
    pub declares_record_vec: bool,
    /// `Map::` / `Map<` used → inject `map.sigil` (and its transitive deps Vec +
    /// Option + traits, since the generic `Map<K: Hash + Eq, V>` uses all three).
    pub need_map: bool,
    pub declares_module_map: bool,
    /// CF-C3 analogue: the source declares its OWN `record Map` — suppress
    /// injection so the stdlib map never collides with the user's record.
    pub declares_record_map: bool,
    /// PR S(strings): a `.find(` / `.contains(` / `.starts_with(` /
    /// `.ends_with(` method call → inject `strings.sigil` (+ transitive
    /// Option). strings.sigil declares no record; only `module strings;`
    /// suppresses it.
    pub need_strings: bool,
    pub declares_module_strings: bool,
    /// PR S2 (owned strings): a `.concat(` (later `.join(` / `itoa(`) call →
    /// inject `string.sigil` — the SINGULAR, OWNED-construction module, kept
    /// SEPARATE from the plural borrowing `strings.sigil` so a borrow-only
    /// program never gains the owned code (ET-5). Only `module string;`
    /// suppresses it. (Distinct field from `need_strings` — note the plural.)
    pub need_string: bool,
    pub declares_module_string: bool,
    /// PR-3c (trait Wall): a `.hash(` / `.eq(` method call OR a `: Hash` /
    /// `: Eq` trait bound → inject `traits.sigil` (the `Hash`/`Eq` contracts +
    /// the built-in primitive impls). Self-contained — no transitive deps. Only
    /// a user `module traits;` suppresses it.
    pub need_traits: bool,
    pub declares_module_traits: bool,
    /// BoundedVec PR-1: a `BoundedVec_i64_8` type name (annotation or `::new()`)
    /// → inject `bounded_vec_i64.sigil` (+ transitive Option/Result for
    /// `pop`/`get`). A user `module bounded_vec_i64;` / `record BoundedVec_i64_8`
    /// suppresses it (the dup-module / record-collision guard).
    pub need_bounded_vec_i64: bool,
    pub declares_module_bounded_vec_i64: bool,
    pub declares_record_bounded_vec_i64: bool,
    /// BoundedVec Phase 2 (zip/enumerate): a `BoundedPairVec_i64_i64_8` type name →
    /// inject `bounded_pair_vec_i64.sigil` (+ transitive Option). Also pulled
    /// transitively by `bounded_vec_i64` (its zip/enumerate reference this family).
    pub need_bounded_pair_vec_i64: bool,
    pub declares_module_bounded_pair_vec_i64: bool,
    pub declares_record_bounded_pair_vec_i64: bool,
    /// BoundedMap/Set PR (Phase 4): per-family inject + suppress flags, mirroring
    /// the BoundedVec triple. Triggered by a `BoundedMap_i64_i64_*` / `BoundedSet_
    /// i64_*` / `BoundedMap_str_*` / `BoundedSet_str_*` type name; suppressed by a
    /// user `module bounded_*;` or same-prefixed `record`.
    pub need_bounded_map_i64_i64: bool,
    pub declares_module_bounded_map_i64_i64: bool,
    pub declares_record_bounded_map_i64_i64: bool,
    pub need_bounded_set_i64: bool,
    pub declares_module_bounded_set_i64: bool,
    pub declares_record_bounded_set_i64: bool,
    pub need_bounded_map_str: bool,
    pub declares_module_bounded_map_str: bool,
    pub declares_record_bounded_map_str: bool,
    /// SOL1: BoundedMap u256→u256 (Solidity `mapping` target). Same triple.
    pub need_bounded_map_u256_u256: bool,
    pub declares_module_bounded_map_u256_u256: bool,
    pub declares_record_bounded_map_u256_u256: bool,
    /// SOL-ERC20: BoundedMap2 (u256,u256)→u256 (Solidity nested `mapping` /
    /// ERC20 `allowance` target). Same triple.
    pub need_bounded_map2_u256_u256_u256: bool,
    pub declares_module_bounded_map2_u256_u256_u256: bool,
    pub declares_record_bounded_map2_u256_u256_u256: bool,
    pub need_bounded_set_str: bool,
    pub declares_module_bounded_set_str: bool,
    pub declares_record_bounded_set_str: bool,
    /// Parser PR-0: `Arena::` / `Arena<` → inject `arena.sigil` (+ its
    /// transitive Vec — the record holds a `Vec<T>` — which pulls Option +
    /// Result). A user `module arena;` / `record Arena` suppresses it.
    pub need_arena: bool,
    pub declares_module_arena: bool,
    pub declares_record_arena: bool,
    /// u256 PR-U1: a `u256` / `i256` type name appears → inject `u256.sigil` (the
    /// native checked multi-limb arithmetic the operators lower to). No
    /// transitive deps. Always injected (a primitive's stdlib is not
    /// user-shadowable; a user `module u256;` collides → clean M002).
    pub need_u256: bool,
}

impl AmbientNeeds {
    fn merge(&mut self, other: Self) {
        macro_rules! merge_flags {
            ($($field:ident),+ $(,)?) => {
                $(self.$field |= other.$field;)+
            };
        }

        merge_flags!(
            need_result,
            need_option,
            need_vec,
            declares_module_result,
            declares_module_option,
            declares_module_vec,
            declares_record_vec,
            need_map,
            declares_module_map,
            declares_record_map,
            need_strings,
            declares_module_strings,
            need_string,
            declares_module_string,
            need_traits,
            declares_module_traits,
            need_bounded_vec_i64,
            declares_module_bounded_vec_i64,
            declares_record_bounded_vec_i64,
            need_bounded_pair_vec_i64,
            declares_module_bounded_pair_vec_i64,
            declares_record_bounded_pair_vec_i64,
            need_bounded_map_i64_i64,
            declares_module_bounded_map_i64_i64,
            declares_record_bounded_map_i64_i64,
            need_bounded_set_i64,
            declares_module_bounded_set_i64,
            declares_record_bounded_set_i64,
            need_bounded_map_str,
            declares_module_bounded_map_str,
            declares_record_bounded_map_str,
            need_bounded_set_str,
            declares_module_bounded_set_str,
            declares_record_bounded_set_str,
            need_bounded_map_u256_u256,
            declares_module_bounded_map_u256_u256,
            declares_record_bounded_map_u256_u256,
            need_bounded_map2_u256_u256_u256,
            declares_module_bounded_map2_u256_u256_u256,
            declares_record_bounded_map2_u256_u256_u256,
            need_arena,
            declares_module_arena,
            declares_record_arena,
            need_u256,
        );
    }
}

impl AmbientModule {
    fn is_requested(self, needs: &AmbientNeeds) -> bool {
        match self {
            Self::Arena => needs.need_arena,
            Self::BoundedMap2U256U256U256 => needs.need_bounded_map2_u256_u256_u256,
            Self::BoundedMapI64I64 => needs.need_bounded_map_i64_i64,
            Self::BoundedMapStr => needs.need_bounded_map_str,
            Self::BoundedMapU256U256 => needs.need_bounded_map_u256_u256,
            Self::BoundedPairVecI64 => needs.need_bounded_pair_vec_i64,
            Self::BoundedSetI64 => needs.need_bounded_set_i64,
            Self::BoundedSetStr => needs.need_bounded_set_str,
            Self::BoundedVecI64 => needs.need_bounded_vec_i64,
            Self::BoundedVecU256 => false,
            Self::Map => needs.need_map,
            Self::Option => needs.need_option,
            Self::Result => needs.need_result,
            Self::String => needs.need_string,
            Self::Strings => needs.need_strings,
            Self::Traits => needs.need_traits,
            Self::U256 => needs.need_u256,
            Self::Vec => needs.need_vec,
        }
    }

    fn is_suppressed(self, needs: &AmbientNeeds) -> bool {
        match self {
            Self::Arena => needs.declares_module_arena || needs.declares_record_arena,
            Self::BoundedMap2U256U256U256 => {
                needs.declares_module_bounded_map2_u256_u256_u256
                    || needs.declares_record_bounded_map2_u256_u256_u256
            }
            Self::BoundedMapI64I64 => {
                needs.declares_module_bounded_map_i64_i64
                    || needs.declares_record_bounded_map_i64_i64
            }
            Self::BoundedMapStr => {
                needs.declares_module_bounded_map_str || needs.declares_record_bounded_map_str
            }
            Self::BoundedMapU256U256 => {
                needs.declares_module_bounded_map_u256_u256
                    || needs.declares_record_bounded_map_u256_u256
            }
            Self::BoundedPairVecI64 => {
                needs.declares_module_bounded_pair_vec_i64
                    || needs.declares_record_bounded_pair_vec_i64
            }
            Self::BoundedSetI64 => {
                needs.declares_module_bounded_set_i64 || needs.declares_record_bounded_set_i64
            }
            Self::BoundedSetStr => {
                needs.declares_module_bounded_set_str || needs.declares_record_bounded_set_str
            }
            Self::BoundedVecI64 => {
                needs.declares_module_bounded_vec_i64 || needs.declares_record_bounded_vec_i64
            }
            Self::BoundedVecU256 | Self::U256 => false,
            Self::Map => needs.declares_module_map || needs.declares_record_map,
            Self::Option => needs.declares_module_option,
            Self::Result => needs.declares_module_result,
            Self::String => needs.declares_module_string,
            Self::Strings => needs.declares_module_strings,
            Self::Traits => needs.declares_module_traits,
            Self::Vec => needs.declares_module_vec || needs.declares_record_vec,
        }
    }
}

fn dependency_closure<I>(requested: I, needs: &AmbientNeeds) -> BTreeSet<AmbientModule>
where
    I: IntoIterator<Item = AmbientModule>,
{
    let mut pending: Vec<_> = requested.into_iter().collect();
    let mut resolved = BTreeSet::new();
    while let Some(module) = pending.pop() {
        if module.is_suppressed(needs) || !resolved.insert(module) {
            continue;
        }
        pending.extend(module.dependencies().iter().copied());
    }
    resolved
}

fn requested_modules(needs: &AmbientNeeds) -> BTreeSet<AmbientModule> {
    dependency_closure(
        ALL_MODULES
            .iter()
            .copied()
            .filter(|module| module.is_requested(needs)),
        needs,
    )
}

/// PR B / N1-PRB + N16-PRB: scan a single source file's token stream
/// for ambient-include triggers. Lexes the file via `lex_with_id`
/// (the lexer strips comments at the byte level — `TokenKind` has no
/// Comment variant — and isolates string-literal content into
/// `StrLit(String)`, so neither comments nor string contents can
/// false-trigger).
///
/// Returns the union of triggers found in this source. The caller
/// accumulates `AmbientNeeds` across all input sources before
/// deciding which stdlib files to inject.
///
/// Per N13-PRB the scan is conservative: it may over-include (false
/// positives accepted per AG-PRB-H + AG-PRB-M) but MUST NOT
/// under-include. Trigger patterns:
/// - `Ident("Ok") LParen` → need_result
/// - `Ident("Err") LParen` → need_result
/// - `Ident("Some") LParen` → need_option
/// - `Ident("None")` (any followup, including standalone) → need_option
/// - `Question` in postfix-expression position (preceded by RParen,
///   Ident, or a literal-class token) → need_result
pub fn scan_source(source: &SourceFile) -> AmbientNeeds {
    let mut needs = AmbientNeeds::default();
    let (tokens, _diagnostics) = lex_with_id(source, SourceId::SYNTHETIC);

    for i in 0..tokens.len() {
        let kind = &tokens[i].kind;
        let next = tokens.get(i + 1).map(|t| &t.kind);

        // Detect `module result;` / `module option;` declarations:
        // any source that itself defines these modules MUST NOT have
        // the corresponding stdlib auto-included (M002 would fire).
        if let TokenKind::Module = kind
            && let Some(TokenKind::Ident(name)) = next
        {
            if name == "result" {
                needs.declares_module_result = true;
            } else if name == "option" {
                needs.declares_module_option = true;
            } else if name == "vec" {
                needs.declares_module_vec = true;
            } else if name == "map" {
                needs.declares_module_map = true;
            } else if name == "strings" {
                needs.declares_module_strings = true;
            } else if name == "string" {
                needs.declares_module_string = true;
            } else if name == "traits" {
                needs.declares_module_traits = true;
            } else if name == "bounded_vec_i64" {
                needs.declares_module_bounded_vec_i64 = true;
            } else if name == "bounded_pair_vec_i64" {
                needs.declares_module_bounded_pair_vec_i64 = true;
            } else if name == "bounded_map_i64_i64" {
                needs.declares_module_bounded_map_i64_i64 = true;
            } else if name == "bounded_set_i64" {
                needs.declares_module_bounded_set_i64 = true;
            } else if name == "bounded_map_str" {
                needs.declares_module_bounded_map_str = true;
            } else if name == "bounded_set_str" {
                needs.declares_module_bounded_set_str = true;
            } else if name == "bounded_map_u256_u256" {
                needs.declares_module_bounded_map_u256_u256 = true;
            } else if name == "bounded_map2_u256_u256_u256" {
                needs.declares_module_bounded_map2_u256_u256_u256 = true;
            } else if name == "arena" {
                needs.declares_module_arena = true;
            }
        }

        // CF-C3: a user-declared `record Vec` (with or without its own
        // `module vec;`) — suppress injection so the stdlib vector never
        // collides with the user's same-named record.
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name == "Vec"
        {
            needs.declares_record_vec = true;
        }

        // A user-declared `record Map` suppresses map injection (same collision
        // rationale as `record Vec`).
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name == "Map"
        {
            needs.declares_record_map = true;
        }

        // BoundedVec: a user-declared `record BoundedVec_i64_*` suppresses
        // bounded-vec injection (same collision rationale as `record Vec`). The
        // prefix covers every monomorphized size (`_8` / `_64` / `_256`).
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedVec_i64_")
        {
            needs.declares_record_bounded_vec_i64 = true;
        }

        // BoundedPairVec (Phase 2 zip/enumerate): a user `record
        // BoundedPairVec_i64_i64_*` suppresses the pair-family injection.
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedPairVec_i64_i64_")
        {
            needs.declares_record_bounded_pair_vec_i64 = true;
        }

        // BoundedMap/Set (Phase 4): a user `record BoundedMap_*`/`BoundedSet_*`
        // suppresses the matching family's injection (same collision rationale).
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedMap_i64_i64_")
        {
            needs.declares_record_bounded_map_i64_i64 = true;
        }
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedSet_i64_")
        {
            needs.declares_record_bounded_set_i64 = true;
        }
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedMap_str_")
        {
            needs.declares_record_bounded_map_str = true;
        }
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedSet_str_")
        {
            needs.declares_record_bounded_set_str = true;
        }
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedMap_u256_u256_")
        {
            needs.declares_record_bounded_map_u256_u256 = true;
        }

        // SOL-ERC20: a user `record BoundedMap2_u256_u256_u256_*` suppresses the
        // injected two-key map (record-collision guard). Disjoint from the
        // single-level prefix above (the `2` precludes a `BoundedMap_` match).
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name.starts_with("BoundedMap2_u256_u256_u256_")
        {
            needs.declares_record_bounded_map2_u256_u256_u256 = true;
        }

        // A user-declared `record Arena` suppresses arena injection (same
        // collision rationale as `record Vec` / `record Map`).
        if let TokenKind::Record = kind
            && let Some(TokenKind::Ident(name)) = next
            && name == "Arena"
        {
            needs.declares_record_arena = true;
        }

        match kind {
            // Result triggers: Ok/Err followed by LParen (constructor
            // call or match pattern).
            TokenKind::Ident(ident)
                if (ident == "Ok" || ident == "Err") && matches!(next, Some(TokenKind::LParen)) =>
            {
                needs.need_result = true;
            }

            // Option triggers: Some followed by LParen, or None
            // standalone (no LParen required since None is a unit
            // variant).
            TokenKind::Ident(ident)
                if ident == "Some" && matches!(next, Some(TokenKind::LParen)) =>
            {
                needs.need_option = true;
            }
            TokenKind::Ident(ident) if ident == "None" => {
                needs.need_option = true;
            }

            // Vec trigger (PR C3): `Vec::` (associated fn) or `Vec<` (type
            // position). Scoped to exactly these two followers so a bare `Vec`
            // word — a variant, field, or unrelated identifier — does NOT
            // over-inject (CF-C3 / AG-C6). A generic type always appears as
            // `Vec<…>` at a type position or `Vec::` at a call position, so
            // this is a sound over-approximation of "needs the stdlib Vec".
            TokenKind::Ident(ident)
                if ident == "Vec"
                    && matches!(next, Some(TokenKind::ColonColon) | Some(TokenKind::Lt)) =>
            {
                needs.need_vec = true;
            }

            // Map trigger: `Map::` (associated fn) or `Map<` (type position) —
            // the scoped two-follower pattern (like Vec) so a bare `Map` word
            // never over-injects.
            TokenKind::Ident(ident)
                if ident == "Map"
                    && matches!(next, Some(TokenKind::ColonColon) | Some(TokenKind::Lt)) =>
            {
                needs.need_map = true;
            }

            // Arena trigger (parser PR-0): `Arena::` (associated fn) or `Arena<`
            // (type position) — the same scoped two-follower pattern as Vec/Map,
            // so a bare `Arena` word never over-injects.
            TokenKind::Ident(ident)
                if ident == "Arena"
                    && matches!(next, Some(TokenKind::ColonColon) | Some(TokenKind::Lt)) =>
            {
                needs.need_arena = true;
            }

            // strings method triggers (PR S-search): `.find(` / `.contains(` /
            // `.starts_with(` / `.ends_with(` — a method call whose receiver may
            // be a `str`. The str-method dispatch rewrites these to the
            // `strings` module's `str_*` free fns; a same-named method on
            // another type pulls strings.sigil harmlessly (N13-PRB conservative
            // over-include). Matches the `Dot Ident LParen` shape (the leading
            // `.` distinguishes a method call from a bare identifier).
            TokenKind::Ident(ident)
                if matches!(
                    ident.as_str(),
                    "find"
                        | "contains"
                        | "starts_with"
                        | "ends_with"
                        | "split_on"
                        | "trim"
                        | "parse_i64"
                        | "is_char_boundary"
                        | "bytes_eq"
                        // Phase-3 completion: narrow/unsigned parsers + ASCII
                        // case-insensitive eq + head/rest split (strings.sigil).
                        | "parse_u64"
                        | "parse_i32"
                        | "parse_u32"
                        | "eq_ignore_case"
                        | "split_first"
                ) && matches!(next, Some(TokenKind::LParen))
                    && i > 0
                    && matches!(&tokens[i - 1].kind, TokenKind::Dot) =>
            {
                needs.need_strings = true;
            }

            // owned-string builder triggers (PR S2): `.concat(` / `.join(` /
            // `.itoa(` — method calls rewritten by the str/i64-method dispatch to
            // the `string` (owned) module's `str_concat` / `str_join` / `str_itoa`.
            // SEPARATE arm from the borrowing `strings` trigger above (different
            // target module) so a `.find`-only program injects `strings.sigil` but
            // NOT `string.sigil` (ET-5). Same `Dot Ident LParen` shape;
            // over-include on a same-named user method is harmless (an unused
            // stdlib module).
            TokenKind::Ident(ident)
                if matches!(
                    ident.as_str(),
                    "concat" | "join" | "itoa" | "from_bytes" | "valid_up_to"
                    // Phase-3 completion: `.to_string()` on any int receiver
                    // routes to string::str_itoa / str_utoa_u64.
                    | "to_string"
                ) && matches!(next, Some(TokenKind::LParen))
                    && i > 0
                    && matches!(&tokens[i - 1].kind, TokenKind::Dot) =>
            {
                needs.need_string = true;
            }

            // PR-E3: an interpolated string `f"…{e}…"` (the `FStrBegin` token) lowers
            // to a `str_concat` chain (+ `str_itoa` / a bool stringify in E3b) — all in
            // the owned `string.sigil` module — so it needs the same injection as
            // `.concat(`. The lowered calls are added at type-check, not present as
            // source `.concat(` tokens, so without this arm an f-string program would
            // miss the injection and fail to lower.
            TokenKind::FStrBegin => {
                needs.need_string = true;
            }

            // BoundedVec: a concrete `BoundedVec_i64_*` type name (in a
            // `: BoundedVec_i64_8` annotation or `BoundedVec_i64_64::new()`) →
            // inject the bounded module, which defines ALL sizes (`_8` / `_64` /
            // `_256`) in one unit. The prefix is the distinctive fully-qualified
            // mono family name, so a bare-word collision is negligible, and
            // over-include is harmless — an unused size is dead-code-eliminated.
            TokenKind::Ident(ident) if ident.starts_with("BoundedVec_i64_") => {
                needs.need_bounded_vec_i64 = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedPairVec_i64_i64_") => {
                needs.need_bounded_pair_vec_i64 = true;
            }
            // BoundedMap/Set (Phase 4): a concrete family type name → inject that
            // family's module (all monomorphs in one unit; unused ones are DCE'd).
            // The `str` prefixes are checked before the broader nothing-else so each
            // family is distinct (`BoundedMap_str_` vs `BoundedMap_i64_i64_`).
            TokenKind::Ident(ident) if ident.starts_with("BoundedMap_i64_i64_") => {
                needs.need_bounded_map_i64_i64 = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedSet_i64_") => {
                needs.need_bounded_set_i64 = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedMap_str_") => {
                needs.need_bounded_map_str = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedMap_u256_u256_") => {
                needs.need_bounded_map_u256_u256 = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedMap2_u256_u256_u256_") => {
                needs.need_bounded_map2_u256_u256_u256 = true;
            }
            TokenKind::Ident(ident) if ident.starts_with("BoundedSet_str_") => {
                needs.need_bounded_set_str = true;
            }

            // u256 PR-U1: a `u256` / `i256` type name (in an annotation, return
            // type, or field) → inject the native-arithmetic module the operators
            // lower to. Exact match (the constructor `u256_from_i64` is a distinct
            // ident). Conservative over-include; unused fns are DCE'd.
            TokenKind::Ident(ident) if ident == "u256" || ident == "i256" => {
                needs.need_u256 = true;
            }

            // trait method triggers (PR-3c): `.hash(` / `.eq(` — a primitive
            // built-in-impl method call, rewritten to a `traits::{prim}_{method}`
            // free fn. Same `Dot Ident LParen` shape as the strings triggers.
            TokenKind::Ident(ident)
                if matches!(ident.as_str(), "hash" | "eq")
                    && matches!(next, Some(TokenKind::LParen))
                    && i > 0
                    && matches!(&tokens[i - 1].kind, TokenKind::Dot) =>
            {
                needs.need_traits = true;
            }

            // trait bound triggers (PR-3c): `: Hash` / `: Eq` — the trait
            // declaration must be in scope to resolve the bound. Shape
            // `Colon Ident(Hash|Eq)`, e.g. `<T: Hash>`. Over-include is harmless
            // (an unused stdlib module).
            TokenKind::Ident(ident)
                if matches!(ident.as_str(), "Hash" | "Eq")
                    && i > 0
                    && matches!(&tokens[i - 1].kind, TokenKind::Colon) =>
            {
                needs.need_traits = true;
            }

            // explicit-impl trigger (PR-5): `impl Hash for …` / `impl Eq for …`.
            // Shape `Impl Ident(Hash|Eq)` — the trait declaration must be in
            // scope for the orphan/coherence check to resolve it.
            TokenKind::Ident(ident)
                if matches!(ident.as_str(), "Hash" | "Eq")
                    && i > 0
                    && matches!(&tokens[i - 1].kind, TokenKind::Impl) =>
            {
                needs.need_traits = true;
            }

            // ? operator in postfix position. The preceding token
            // must be RParen, Ident, or a literal — i.e., something
            // that produces an expression value. Bare `?` in other
            // contexts (none exist in SIGIL today) wouldn't trigger.
            TokenKind::Question
                if i > 0
                    && matches!(
                        &tokens[i - 1].kind,
                        TokenKind::RParen
                            | TokenKind::Ident(_)
                            | TokenKind::IntLit(_)
                            | TokenKind::FloatLit(_)
                            | TokenKind::StrLit(_)
                            | TokenKind::BoolLit(_)
                    ) =>
            {
                needs.need_result = true;
            }
            _ => {}
        }
    }

    needs
}

/// Result of applying ambient stdlib auto-include. `ambient_added`
/// holds the count of stdlib files newly injected (0 if no triggers
/// fired). Callers use this to know whether the project was
/// "transparently grown" so M001-M006 checks can be adjusted
/// appropriately — the user's input shouldn't see new multi-file
/// diagnostics just because Ok(...) appeared in their code.
pub struct AmbientResult {
    pub sources: Vec<SourceFile>,
    pub ambient_added: usize,
}

pub fn apply_ambient_includes_with_count(sources: Vec<SourceFile>) -> AmbientResult {
    let initial_len = sources.len();
    let merged = apply_ambient_includes(sources);
    let ambient_added = merged.len().saturating_sub(initial_len);
    AmbientResult {
        sources: merged,
        ambient_added,
    }
}

pub fn apply_ambient_includes(mut sources: Vec<SourceFile>) -> Vec<SourceFile> {
    let mut combined = AmbientNeeds::default();
    for source in &sources {
        combined.merge(scan_source(source));
    }

    let to_add = requested_modules(&combined);
    if to_add.is_empty() {
        return sources;
    }

    let existing: BTreeSet<String> = sources
        .iter()
        .map(|source| source.name().to_owned())
        .collect();
    for module in to_add {
        if !existing.contains(module.path()) {
            sources.push(SourceFile::new(module.path(), module.source()));
        }
    }
    sources
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn dependency_closure_is_idempotent_and_order_independent(mask in any::<u32>()) {
            let requested: Vec<_> = ALL_MODULES
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(index, module)| ((mask & (1 << index)) != 0).then_some(module))
                .collect();
            let mut reversed = requested.clone();
            reversed.reverse();

            let forward = dependency_closure(requested, &AmbientNeeds::default());
            let backward = dependency_closure(reversed, &AmbientNeeds::default());
            let repeated = dependency_closure(forward.iter().copied(), &AmbientNeeds::default());

            prop_assert_eq!(&forward, &backward);
            prop_assert_eq!(&forward, &repeated);
            let paths: Vec<_> = forward.iter().map(|module| module.path()).collect();
            prop_assert!(paths.windows(2).all(|pair| pair[0] <= pair[1]));
        }

        #[test]
        fn applying_ambient_includes_twice_is_idempotent(mask in any::<u16>()) {
            let triggers = [
                "Ok(1)",
                "Some(1)",
                "Vec::new()",
                "Map::new()",
                "value.find(needle)",
                "value.concat(other)",
                "value.hash()",
                "BoundedVec_i64_8::new()",
                "BoundedPairVec_i64_i64_8::new()",
                "BoundedMap_i64_i64_64::new()",
                "BoundedSet_i64_64::new()",
                "BoundedMap_str_i64_64::new()",
                "BoundedSet_str_16::new()",
                "BoundedMap_u256_u256_64::new()",
                "BoundedMap2_u256_u256_u256_64::new()",
                "Arena::new()",
            ];
            let body = triggers
                .iter()
                .enumerate()
                .filter_map(|(index, trigger)| ((mask & (1 << index)) != 0).then_some(*trigger))
                .collect::<Vec<_>>()
                .join(";\n");
            let first = apply_ambient_includes(vec![SourceFile::new(
                "generated.sigil",
                format!("module generated;\nfn main() {{ {body}; }}"),
            )]);
            let first_names: Vec<_> = first.iter().map(|source| source.name().to_owned()).collect();
            let second = apply_ambient_includes(first);
            let second_names: Vec<_> = second.iter().map(|source| source.name().to_owned()).collect();

            prop_assert_eq!(first_names, second_names);
        }
    }

    #[test]
    fn ambient_module_descriptors_have_unique_paths_and_sources() {
        let paths: BTreeSet<_> = ALL_MODULES.iter().map(|module| module.path()).collect();
        assert_eq!(paths.len(), ALL_MODULES.len());
        assert!(ALL_MODULES.iter().all(|module| !module.source().is_empty()));
    }

    #[test]
    fn bounded_set_str_closes_the_strings_dependency_graph() {
        let user = SourceFile::new(
            "set.sigil",
            "module set; fn main() { let s = BoundedSet_str_16::new(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        let names: BTreeSet<_> = merged.iter().map(|source| source.name()).collect();
        assert!(names.contains(STDLIB_BOUNDED_SET_STR_PATH));
        assert!(names.contains(STDLIB_STRINGS_PATH));
        assert!(names.contains(STDLIB_OPTION_PATH));
        assert!(names.contains(STDLIB_RESULT_PATH));
    }

    #[test]
    fn scan_detects_ok_constructor() {
        let src = SourceFile::new(
            "test.sigil",
            "module main;\nfn f() -> i64 { return 0; }\nlet x = Ok(42);",
        );
        let needs = scan_source(&src);
        assert!(needs.need_result, "Ok(42) must trigger need_result");
        assert!(!needs.need_option, "Ok(42) must NOT trigger need_option");
    }

    #[test]
    fn scan_detects_err_constructor() {
        let src = SourceFile::new("test.sigil", "module main; let x = Err(7);");
        let needs = scan_source(&src);
        assert!(needs.need_result, "Err(7) must trigger need_result");
    }

    #[test]
    fn scan_detects_some_constructor() {
        let src = SourceFile::new("test.sigil", "module main; let x = Some(42);");
        let needs = scan_source(&src);
        assert!(needs.need_option, "Some(42) must trigger need_option");
        assert!(!needs.need_result, "Some(42) must NOT trigger need_result");
    }

    #[test]
    fn scan_detects_none_standalone() {
        let src = SourceFile::new("test.sigil", "module main; let x = None;");
        let needs = scan_source(&src);
        assert!(needs.need_option, "None must trigger need_option");
    }

    #[test]
    fn scan_detects_question_postfix() {
        let src = SourceFile::new(
            "test.sigil",
            "module main; fn f() -> i64 { let x = call()?; return x; }",
        );
        let needs = scan_source(&src);
        assert!(needs.need_result, "call()? must trigger need_result");
    }

    #[test]
    fn scan_ignores_ok_in_string_literal() {
        // String contents live in TokenKind::StrLit(String), not as
        // Ident("Ok"). Lexer-level isolation prevents false-trigger.
        let src = SourceFile::new("test.sigil", "module main; let s: i64 = 0;");
        let needs = scan_source(&src);
        assert!(!needs.need_result, "absent triggers must not fire");
        assert!(!needs.need_option, "absent triggers must not fire");
    }

    #[test]
    fn apply_ambient_adds_result_for_ok_user_file() {
        let user = SourceFile::new("user.sigil", "module main; let x = Ok(1);");
        let merged = apply_ambient_includes(vec![user]);
        assert_eq!(merged.len(), 2);
        assert!(merged.iter().any(|s| s.name() == STDLIB_RESULT_PATH));
    }

    #[test]
    fn apply_ambient_adds_option_and_result_for_some_user_file() {
        // Transitive: Some triggers Option; Option's ok_or uses
        // Ok/Err → Result also added.
        let user = SourceFile::new("user.sigil", "module main; let x = Some(1);");
        let merged = apply_ambient_includes(vec![user]);
        assert_eq!(merged.len(), 3);
        assert!(merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH));
        assert!(merged.iter().any(|s| s.name() == STDLIB_RESULT_PATH));
    }

    #[test]
    fn apply_ambient_idempotent_under_multi_source() {
        let a = SourceFile::new("a.sigil", "module a; let x = Ok(1);");
        let b = SourceFile::new("b.sigil", "module b; let y = Err(2);");
        let c = SourceFile::new("c.sigil", "module c; let z = Ok(3);");
        let merged = apply_ambient_includes(vec![a, b, c]);
        // 3 user + 1 stdlib (result, deduped across 3 triggers)
        assert_eq!(merged.len(), 4);
        let result_count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_RESULT_PATH)
            .count();
        assert_eq!(
            result_count, 1,
            "stdlib result.sigil must dedup to one entry"
        );
    }

    #[test]
    fn apply_ambient_no_triggers_returns_unchanged() {
        let user = SourceFile::new("user.sigil", "module main; let x: i64 = 42;");
        let merged = apply_ambient_includes(vec![user]);
        assert_eq!(merged.len(), 1, "no triggers → no ambient include");
    }

    #[test]
    fn scan_detects_module_result_declaration() {
        let src = SourceFile::new(
            "result.sigil",
            "module result;\nenum Result<T,E> { Ok(T), Err(E) }",
        );
        let needs = scan_source(&src);
        assert!(
            needs.declares_module_result,
            "`module result;` must set declares_module_result"
        );
    }

    #[test]
    fn scan_detects_module_option_declaration() {
        let src = SourceFile::new(
            "option.sigil",
            "module option;\nenum Option<T> { Some(T), None }",
        );
        let needs = scan_source(&src);
        assert!(
            needs.declares_module_option,
            "`module option;` must set declares_module_option"
        );
    }

    #[test]
    fn apply_ambient_skips_when_user_declares_module_result() {
        // Smoke-test-style: user's source IS stdlib's result.sigil.
        // The source declares `module result;` and uses Ok/Err
        // patterns inside match arms — triggering need_result. But
        // because the user already declares the module, ambient
        // include must NOT add a second copy (M002 would fire).
        let user = SourceFile::new(
            "user.sigil",
            "module result;\nfn f() -> i64 { match x { Ok(v) => 1, Err(e) => 2 } }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert_eq!(
            merged.len(),
            1,
            "user-declared `module result;` must suppress ambient include"
        );
    }

    #[test]
    fn apply_ambient_skips_when_user_declares_module_option() {
        // User's source defines `module option;` AND uses Some(1).
        // The user takes responsibility for what's in their `option`
        // module — ambient include must NOT add a second stdlib
        // option file (M002 would fire). Transitively the Result
        // include is also not pulled (the user's option doesn't
        // itself contain Ok/Err triggers).
        let user = SourceFile::new(
            "user.sigil",
            "module option;\nfn f() -> i64 { let x = Some(1); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert_eq!(
            merged.len(),
            1,
            "user-declared `module option;` must suppress option include"
        );
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH),
            "stdlib option.sigil must NOT be auto-included when user declares module option"
        );
    }

    #[test]
    fn apply_ambient_skips_already_present_stdlib() {
        // N31-PRB: if user code already includes stdlib/sigil/result.sigil
        // (via some future plumbing), the ambient include must not
        // duplicate it.
        let user = SourceFile::new("user.sigil", "module main; let x = Ok(1);");
        let stdlib = SourceFile::new(STDLIB_RESULT_PATH, STDLIB_RESULT_SOURCE);
        let merged = apply_ambient_includes(vec![user, stdlib]);
        let result_count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_RESULT_PATH)
            .count();
        assert_eq!(
            result_count, 1,
            "already-present stdlib MUST NOT be re-added"
        );
    }

    // ── PR C3: ambient Vec ──

    #[test]
    fn scan_detects_vec_assoc_fn() {
        let src = SourceFile::new("test.sigil", "module tool; let v = Vec::new();");
        let needs = scan_source(&src);
        assert!(needs.need_vec, "`Vec::` must trigger need_vec");
    }

    #[test]
    fn scan_detects_vec_type_annotation() {
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f(v: Vec<i64>) -> i64 { return 0; }",
        );
        let needs = scan_source(&src);
        assert!(needs.need_vec, "`Vec<` must trigger need_vec");
    }

    #[test]
    fn scan_ignores_bare_vec_word() {
        // `Vec` NOT followed by `::` or `<` is not a stdlib-Vec reference.
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f() -> i64 { let Vec = 5; return Vec; }",
        );
        let needs = scan_source(&src);
        assert!(
            !needs.need_vec,
            "a bare `Vec` word must NOT trigger need_vec (AG-C6)"
        );
    }

    #[test]
    fn scan_detects_record_vec() {
        // CF-C3: a user-declared `record Vec` is flagged so injection is skipped.
        let src = SourceFile::new("test.sigil", "module tool; record Vec<T> { v: i64 }");
        let needs = scan_source(&src);
        assert!(
            needs.declares_record_vec,
            "`record Vec` must set declares_record_vec"
        );
    }

    #[test]
    fn apply_injects_vec_for_bare_use() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let v: Vec<i64> = Vec::new(); return v.len(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "bare `Vec` usage must auto-inject vec.sigil"
        );
        // Iterator protocol (PR-2) / ET-8: vec.sigil now uses `Option` (VecIter::next),
        // so the vec trigger must transitively inject option.sigil (+ result) — the
        // scanner never sees vec.sigil's own `Some`/`None`.
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH),
            "bare `Vec` usage must transitively inject option.sigil (vec.sigil uses Option)"
        );
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_RESULT_PATH),
            "option pulls result transitively, so a bare `Vec` use must inject result.sigil too"
        );
    }

    #[test]
    fn apply_skips_vec_when_user_declares_module_vec() {
        let user = SourceFile::new(
            "user.sigil",
            "module vec; record Vec<T> { v: i64 } fn f() -> i64 { let x: Vec<i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "a user `module vec;` must suppress vec.sigil injection"
        );
    }

    #[test]
    fn apply_skips_vec_when_user_declares_record_vec() {
        // CF-C3: a user record named `Vec` (without `module vec;`) still
        // suppresses injection — a second unqualified `Vec` would collide.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; record Vec<T> { v: i64 } fn f() -> i64 { let x: Vec<i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "CF-C3: a user `record Vec` must suppress vec.sigil injection"
        );
    }

    #[test]
    fn apply_skips_already_present_vec() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let v: Vec<i64> = Vec::new(); return 0; }",
        );
        let stdlib = SourceFile::new(STDLIB_VEC_PATH, STDLIB_VEC_SOURCE);
        let merged = apply_ambient_includes(vec![user, stdlib]);
        let count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_VEC_PATH)
            .count();
        assert_eq!(count, 1, "already-present vec.sigil must not be re-added");
    }

    // ---- PR 4 / PR 6: Map ambient injection (mirrors the Vec arms) ----

    #[test]
    fn scan_detects_map_assoc_fn() {
        let src = SourceFile::new("test.sigil", "module tool; let m = Map::new();");
        let needs = scan_source(&src);
        assert!(needs.need_map, "`Map::` must trigger need_map");
    }

    #[test]
    fn scan_detects_map_type_annotation() {
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f(m: Map<str, i64>) -> i64 { return 0; }",
        );
        let needs = scan_source(&src);
        assert!(needs.need_map, "`Map<` must trigger need_map");
    }

    #[test]
    fn scan_ignores_bare_map_word() {
        // `Map` NOT followed by `::` or `<` is not a stdlib-Map reference
        // (same scoped two-follower guard as Vec — AG-C6 parity).
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f() -> i64 { let Map = 5; return Map; }",
        );
        let needs = scan_source(&src);
        assert!(
            !needs.need_map,
            "a bare `Map` word must NOT trigger need_map"
        );
    }

    #[test]
    fn scan_detects_module_map() {
        let src = SourceFile::new(
            "test.sigil",
            "module map; fn h(k: str) -> i64 { return 0; }",
        );
        let needs = scan_source(&src);
        assert!(
            needs.declares_module_map,
            "`module map;` must set declares_module_map"
        );
    }

    #[test]
    fn scan_detects_record_map() {
        // A user-declared `record Map` is flagged so injection is skipped.
        let src = SourceFile::new("test.sigil", "module tool; record Map<K, V> { c: i64 }");
        let needs = scan_source(&src);
        assert!(
            needs.declares_record_map,
            "`record Map` must set declares_record_map"
        );
    }

    #[test]
    fn apply_injects_map_and_transitive_for_bare_use() {
        // The headline of PR 4/6: a BARE `Map` (no `Vec`/`Some`/`None`/`Ok` in
        // the user's own text) pulls map.sigil AND its transitive deps —
        // vec.sigil (slot + dense arrays) + option.sigil (the `get` return) +
        // result.sigil (option's `ok_or`) + traits.sigil (the `Hash`/`Eq`
        // contracts + built-in impls) — each exactly once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let m: Map<str, i64> = Map::new(); return m.len(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [
            STDLIB_MAP_PATH,
            STDLIB_VEC_PATH,
            STDLIB_OPTION_PATH,
            STDLIB_RESULT_PATH,
            STDLIB_TRAITS_PATH,
        ] {
            let count = merged.iter().filter(|s| s.name() == path).count();
            assert_eq!(
                count, 1,
                "bare `Map` must inject exactly one `{path}` (map + transitive vec/option/result/traits)"
            );
        }
    }

    #[test]
    fn apply_skips_map_when_user_declares_module_map() {
        let user = SourceFile::new(
            "user.sigil",
            "module map; record Map<K, V> { c: i64 } fn f() -> i64 { let x: Map<str, i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_MAP_PATH),
            "a user `module map;` must suppress map.sigil injection"
        );
    }

    #[test]
    fn apply_skips_map_when_user_declares_record_map() {
        // A user record named `Map` (without `module map;`) still suppresses
        // injection — a second unqualified `Map` would collide.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; record Map<K, V> { c: i64 } fn f() -> i64 { let x: Map<str, i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_MAP_PATH),
            "a user `record Map` must suppress map.sigil injection"
        );
    }

    #[test]
    fn apply_skips_already_present_map() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let m: Map<str, i64> = Map::new(); return 0; }",
        );
        let stdlib = SourceFile::new(STDLIB_MAP_PATH, STDLIB_MAP_SOURCE);
        let merged = apply_ambient_includes(vec![user, stdlib]);
        let count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_MAP_PATH)
            .count();
        assert_eq!(count, 1, "already-present map.sigil must not be re-added");
    }

    #[test]
    fn apply_map_respects_user_vec_shadow() {
        // The transitive edge is still shadow-suppressed: a bare `Map` use
        // alongside the user's OWN `module vec;` injects map.sigil but NOT the
        // stdlib vec (which would collide). map.sigil still needs option/result,
        // so those are injected.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let m: Map<str, i64> = Map::new(); return 0; }",
        );
        let user_vec = SourceFile::new("myvec.sigil", "module vec; record Vec<T> { v: i64 }");
        let merged = apply_ambient_includes(vec![user, user_vec]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_MAP_PATH),
            "map.sigil must still inject when only its vec dep is shadowed"
        );
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "a user `module vec;` must suppress the transitive stdlib vec injection"
        );
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH),
            "map.sigil's option dep is still injected (not shadowed)"
        );
    }

    // ---- PR S(strings): method-triggered search-layer injection ----

    #[test]
    fn scan_detects_find_method() {
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f() { let s: str = \"x\"; let o = s.find(\"y\"); }",
        );
        let needs = scan_source(&src);
        assert!(needs.need_strings, "`.find(` must trigger need_strings");
    }

    #[test]
    fn scan_detects_contains_starts_ends() {
        for method in ["contains", "starts_with", "ends_with", "bytes_eq"] {
            let src = SourceFile::new(
                "test.sigil",
                format!("module tool; fn f() {{ let s: str = \"x\"; let b = s.{method}(\"y\"); }}"),
            );
            assert!(
                scan_source(&src).need_strings,
                "`.{method}(` must trigger need_strings"
            );
        }
    }

    #[test]
    fn scan_ignores_find_without_dot() {
        // A free-fn-shaped `find(` with no preceding `.` is NOT a string method
        // call — it must NOT over-inject (the `Dot Ident LParen` guard).
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn find(x: i64) -> i64 { return x; } fn g() -> i64 { return find(5); }",
        );
        assert!(
            !scan_source(&src).need_strings,
            "a bare `find(` (no receiver dot) must NOT trigger need_strings"
        );
    }

    #[test]
    fn scan_detects_module_strings() {
        let src = SourceFile::new(
            "test.sigil",
            "module strings; fn str_find(h: str, n: str) -> i64 { return 0; }",
        );
        assert!(
            scan_source(&src).declares_module_strings,
            "`module strings;` must set declares_module_strings"
        );
    }

    // ---- PR-3c: trait-triggered injection ----

    #[test]
    fn scan_detects_hash_and_eq_methods() {
        for method in ["hash", "eq"] {
            let src = SourceFile::new(
                "test.sigil",
                format!("module tool; fn f() {{ let s: str = \"x\"; let r = s.{method}(s); }}"),
            );
            assert!(
                scan_source(&src).need_traits,
                "`.{method}(` must trigger need_traits"
            );
        }
    }

    #[test]
    fn scan_detects_hash_bound() {
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn keyed<T: Hash>(k: T) -> i64 { return 0; }",
        );
        assert!(
            scan_source(&src).need_traits,
            "a `: Hash` bound must trigger need_traits"
        );
    }

    #[test]
    fn scan_ignores_hash_without_dot() {
        // A bare `hash(` with no receiver dot is not a method call.
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn hash(x: i64) -> i64 { return x; } fn g() -> i64 { return hash(5); }",
        );
        assert!(
            !scan_source(&src).need_traits,
            "a bare `hash(` (no receiver dot) must NOT trigger need_traits"
        );
    }

    #[test]
    fn scan_detects_module_traits() {
        let src = SourceFile::new(
            "test.sigil",
            "module traits; fn str_hash(s: str) -> i64 { return 0; }",
        );
        assert!(
            scan_source(&src).declares_module_traits,
            "`module traits;` must set declares_module_traits"
        );
    }

    #[test]
    fn apply_injects_traits() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let s: str = \"x\"; return s.hash(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_TRAITS_PATH),
            "`.hash(` must inject traits.sigil"
        );
    }

    #[test]
    fn apply_skips_traits_when_user_declares_module_traits() {
        let user = SourceFile::new(
            "user.sigil",
            "module traits; fn str_hash(s: str) -> i64 { return s.hash(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_TRAITS_PATH),
            "a user `module traits;` must suppress the stdlib traits injection"
        );
    }

    #[test]
    fn apply_injects_strings_and_transitive() {
        // A bare `s.find(` pulls strings.sigil AND its transitive Option +
        // Result, each exactly once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let s: str = \"x\"; let o = s.find(\"y\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [STDLIB_STRINGS_PATH, STDLIB_OPTION_PATH, STDLIB_RESULT_PATH] {
            let count = merged.iter().filter(|s| s.name() == path).count();
            assert_eq!(
                count, 1,
                "a `.find(` must inject exactly one `{path}` (strings + transitive option/result)"
            );
        }
    }

    #[test]
    fn apply_skips_strings_when_user_declares_module_strings() {
        let user = SourceFile::new(
            "user.sigil",
            "module strings; pub fn str_find(h: str, n: str) -> i64 { let s: str = \"a\"; let o = s.find(\"b\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_STRINGS_PATH),
            "a user `module strings;` must suppress strings.sigil injection"
        );
    }

    #[test]
    fn apply_skips_already_present_strings() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let s: str = \"x\"; let o = s.find(\"y\"); return 0; }",
        );
        let stdlib = SourceFile::new(STDLIB_STRINGS_PATH, STDLIB_STRINGS_SOURCE);
        let merged = apply_ambient_includes(vec![user, stdlib]);
        let count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_STRINGS_PATH)
            .count();
        assert_eq!(
            count, 1,
            "already-present strings.sigil must not be re-added"
        );
    }

    #[test]
    fn apply_injects_string_on_concat() {
        // A `.concat(` pulls the OWNED string.sigil AND its transitive vec dep —
        // `str_join` (in the same module) consumes a `Vec<str>`, so the whole
        // module needs vec.sigil in scope to type-check.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let a: str = \"x\"; let r = a.concat(\"y\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_STRING_PATH),
            "`.concat(` must inject string.sigil"
        );
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "string.sigil's str_join needs the transitive vec.sigil"
        );
    }

    #[test]
    fn apply_does_not_inject_string_without_concat() {
        // ET-5 byte-identity: a borrow-only program (`.find(`) pulls the PLURAL
        // strings.sigil but NEVER the SINGULAR owned string.sigil — so adding
        // owned strings to the stdlib costs a non-concat program zero bytes.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let s: str = \"x\"; let o = s.find(\"y\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_STRINGS_PATH),
            "`.find(` still injects the borrowing strings.sigil"
        );
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_STRING_PATH),
            "ET-5: a `.find`-only program must NOT inject the owned string.sigil"
        );
    }

    #[test]
    fn apply_skips_string_when_user_declares_module_string() {
        // `module string;` + a `.concat(` use: the trigger fires but the
        // user-declared module suppresses injection (M002 dup-module guard).
        let user = SourceFile::new(
            "user.sigil",
            "module string; pub fn f(a: str) -> i64 { let r = a.concat(\"y\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_STRING_PATH),
            "a user `module string;` must suppress string.sigil injection"
        );
    }

    #[test]
    fn apply_injects_string_and_option_on_from_bytes() {
        // PR S3: `.from_bytes(` pulls the OWNED string.sigil AND its transitive
        // option dep — `str_from_bytes` returns `Option<str>`, so the whole module
        // needs option.sigil in scope to type-check (vec comes along for str_join).
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let p: i64 = 0; let o = p.from_bytes(3); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_STRING_PATH),
            "`.from_bytes(` must inject string.sigil"
        );
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH),
            "str_from_bytes returns Option<str> → option.sigil must be injected"
        );
    }

    #[test]
    fn scan_detects_bounded_vec_i64() {
        // BoundedVec PR-2: ANY `BoundedVec_i64_*` size triggers injection (the
        // prefix), since one module defines `_8` / `_64` / `_256` together. A
        // different element type (`BoundedVec_i32_*`) is a DIFFERENT module, so it
        // must NOT trigger the `i64` module here.
        for (snippet, want) in [
            ("let v: BoundedVec_i64_8 = BoundedVec_i64_8::new()", true),
            ("let v: BoundedVec_i64_64 = BoundedVec_i64_64::new()", true),
            (
                "let v: BoundedVec_i64_256 = BoundedVec_i64_256::new()",
                true,
            ),
            ("let n: i64 = consume(arg)", false), // control: no trigger
            ("let v: BoundedVec_i32_8 = other()", false), // different element type
        ] {
            let src = SourceFile::new("t.sigil", format!("module tool; fn g() {{ {snippet}; }}"));
            assert_eq!(
                scan_source(&src).need_bounded_vec_i64,
                want,
                "`{snippet}` need_bounded_vec_i64 should be {want}"
            );
        }
    }

    #[test]
    fn apply_injects_bounded_vec_and_option() {
        // A `BoundedVec_i64_8` use injects the module + its transitive option/result
        // (`pop`/`get` return `Option<i64>`).
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let v: BoundedVec_i64_8 = BoundedVec_i64_8::new(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            merged
                .iter()
                .any(|s| s.name() == STDLIB_BOUNDED_VEC_I64_PATH),
            "`BoundedVec_i64_8` must inject bounded_vec_i64.sigil"
        );
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_OPTION_PATH),
            "BoundedVec's pop/get return Option → option.sigil must be injected"
        );
    }

    #[test]
    fn apply_skips_bounded_vec_when_user_declares_module() {
        let user = SourceFile::new(
            "user.sigil",
            "module bounded_vec_i64; record BoundedVec_i64_8 { data: [i64; 8], count: i64 }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged
                .iter()
                .any(|s| s.name() == STDLIB_BOUNDED_VEC_I64_PATH),
            "a user `module bounded_vec_i64;` must suppress injection"
        );
    }

    #[test]
    fn apply_skips_bounded_vec_when_user_declares_record() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; record BoundedVec_i64_8 { x: i64 } fn f() -> i64 { let v: BoundedVec_i64_8 = BoundedVec_i64_8 { x: 0 }; return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged
                .iter()
                .any(|s| s.name() == STDLIB_BOUNDED_VEC_I64_PATH),
            "a user `record BoundedVec_i64_8` must suppress injection (collision)"
        );
    }

    #[test]
    fn scan_detects_owned_builders_distinct_from_strings() {
        // Each owned trigger (`.concat(` / `.join(` / `.itoa(` / `.from_bytes(` /
        // `.valid_up_to(`) sets need_string but NOT need_strings — the borrowing
        // module is never dragged in with the owned one (separate modules, ET-5).
        for snippet in [
            "a.concat(\"y\")",
            "sep.join(v)",
            "n.itoa()",
            "p.from_bytes(n)",
            "p.valid_up_to(n)",
        ] {
            let src = SourceFile::new(
                "test.sigil",
                format!("module tool; fn f() {{ let r = {snippet}; }}"),
            );
            let scanned = scan_source(&src);
            assert!(scanned.need_string, "`{snippet}` must trigger need_string");
            assert!(
                !scanned.need_strings,
                "`{snippet}` must NOT trigger need_strings (separate modules)"
            );
        }
    }

    #[test]
    fn scan_detects_split_trim_parse() {
        for method in ["split_on", "trim", "parse_i64"] {
            let src = SourceFile::new(
                "test.sigil",
                format!("module tool; fn f() {{ let s: str = \"x\"; let b = s.{method}(\"y\"); }}"),
            );
            assert!(
                scan_source(&src).need_strings,
                "`.{method}(` must trigger need_strings"
            );
        }
    }

    #[test]
    fn apply_split_injects_vec_transitively() {
        // `str_split_on` returns `Vec<str>`, so a `.split_on(` use pulls
        // vec.sigil too (alongside strings + option + result), each once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let s: str = \"a,b\"; let p = s.split_on(\",\"); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [
            STDLIB_STRINGS_PATH,
            STDLIB_VEC_PATH,
            STDLIB_OPTION_PATH,
            STDLIB_RESULT_PATH,
        ] {
            assert_eq!(
                merged.iter().filter(|s| s.name() == path).count(),
                1,
                "a `.split_on(` must inject exactly one `{path}`"
            );
        }
    }

    // ---- Parser PR-0: Arena ambient injection (mirrors the Vec/Map arms) ----

    #[test]
    fn scan_detects_arena_assoc_fn() {
        let src = SourceFile::new("test.sigil", "module tool; let a = Arena::new();");
        let needs = scan_source(&src);
        assert!(needs.need_arena, "`Arena::` must trigger need_arena");
    }

    #[test]
    fn scan_detects_arena_type_annotation() {
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f(a: Arena<i64>) -> i64 { return 0; }",
        );
        let needs = scan_source(&src);
        assert!(needs.need_arena, "`Arena<` must trigger need_arena");
    }

    #[test]
    fn scan_ignores_bare_arena_word() {
        // `Arena` NOT followed by `::` or `<` is not a stdlib-Arena reference
        // (the scoped two-follower guard — Vec/Map parity).
        let src = SourceFile::new(
            "test.sigil",
            "module tool; fn f() -> i64 { let Arena = 5; return Arena; }",
        );
        let needs = scan_source(&src);
        assert!(
            !needs.need_arena,
            "a bare `Arena` word must NOT trigger need_arena"
        );
    }

    #[test]
    fn scan_detects_module_arena() {
        let src = SourceFile::new(
            "test.sigil",
            "module arena; fn a(k: i64) -> i64 { return 0; }",
        );
        let needs = scan_source(&src);
        assert!(
            needs.declares_module_arena,
            "`module arena;` must set declares_module_arena"
        );
    }

    #[test]
    fn scan_detects_record_arena() {
        let src = SourceFile::new("test.sigil", "module tool; record Arena<T> { c: i64 }");
        let needs = scan_source(&src);
        assert!(
            needs.declares_record_arena,
            "`record Arena` must set declares_record_arena"
        );
    }

    #[test]
    fn apply_injects_arena_and_transitive_for_bare_use() {
        // A bare `Arena` pulls arena.sigil AND its transitive deps — vec.sigil
        // (the record's `store: Vec<T>`) + option.sigil + result.sigil (vec's
        // transitive pair) — each exactly once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let a: Arena<i64> = Arena::new(); return a.len(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [
            STDLIB_ARENA_PATH,
            STDLIB_VEC_PATH,
            STDLIB_OPTION_PATH,
            STDLIB_RESULT_PATH,
        ] {
            let count = merged.iter().filter(|s| s.name() == path).count();
            assert_eq!(
                count, 1,
                "bare `Arena` must inject exactly one `{path}` (arena + transitive vec/option/result)"
            );
        }
    }

    #[test]
    fn apply_skips_arena_when_user_declares_module_arena() {
        let user = SourceFile::new(
            "user.sigil",
            "module arena; record Arena<T> { c: i64 } fn f() -> i64 { let x: Arena<i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_ARENA_PATH),
            "a user `module arena;` must suppress arena.sigil injection"
        );
    }

    #[test]
    fn apply_skips_arena_when_user_declares_record_arena() {
        // A user record named `Arena` (without `module arena;`) still suppresses
        // injection — a second unqualified `Arena` would collide.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; record Arena<T> { c: i64 } fn f() -> i64 { let x: Arena<i64> = make(); return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_ARENA_PATH),
            "a user `record Arena` must suppress arena.sigil injection"
        );
    }

    #[test]
    fn apply_skips_already_present_arena() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let a: Arena<i64> = Arena::new(); return 0; }",
        );
        let stdlib = SourceFile::new(STDLIB_ARENA_PATH, STDLIB_ARENA_SOURCE);
        let merged = apply_ambient_includes(vec![user, stdlib]);
        let count = merged
            .iter()
            .filter(|s| s.name() == STDLIB_ARENA_PATH)
            .count();
        assert_eq!(count, 1, "already-present arena.sigil must not be re-added");
    }

    #[test]
    fn apply_arena_respects_user_vec_shadow() {
        // The transitive edge is shadow-suppressed: a bare `Arena` use alongside
        // the user's OWN `module vec;` injects arena.sigil but NOT the stdlib vec.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 ! { Alloc } { let a: Arena<i64> = Arena::new(); return 0; }",
        );
        let user_vec = SourceFile::new("myvec.sigil", "module vec; record Vec<T> { v: i64 }");
        let merged = apply_ambient_includes(vec![user, user_vec]);
        assert!(
            merged.iter().any(|s| s.name() == STDLIB_ARENA_PATH),
            "arena.sigil must still inject when only its vec dep is shadowed"
        );
        assert!(
            !merged.iter().any(|s| s.name() == STDLIB_VEC_PATH),
            "a user `module vec;` must suppress the transitive stdlib vec injection"
        );
    }

    // ---- SOL1: BoundedMap u256→u256 ambient injection ----

    #[test]
    fn scan_detects_bounded_map_u256_u256() {
        let src = SourceFile::new(
            "t.sigil",
            "module tool; fn g() { let m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new(); }",
        );
        assert!(
            scan_source(&src).need_bounded_map_u256_u256,
            "`BoundedMap_u256_u256_*` must trigger need_bounded_map_u256_u256"
        );
    }

    #[test]
    fn apply_injects_bounded_map_u256_and_transitive() {
        // A `BoundedMap_u256_u256_*` use injects the map module + u256.sigil (the
        // `==` key compare lowers to u256_eq) + transitive option/result (`get` →
        // Option<u256>) — each exactly once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new(); return m.len(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [
            STDLIB_BOUNDED_MAP_U256_U256_PATH,
            STDLIB_U256_PATH,
            STDLIB_OPTION_PATH,
            STDLIB_RESULT_PATH,
        ] {
            assert_eq!(
                merged.iter().filter(|s| s.name() == path).count(),
                1,
                "BoundedMap_u256_u256 must inject exactly one `{path}`"
            );
        }
    }

    #[test]
    fn apply_skips_bounded_map_u256_when_user_declares_record() {
        let user = SourceFile::new(
            "user.sigil",
            "module tool; record BoundedMap_u256_u256_64 { x: i64 } fn f() -> i64 { let m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64 { x: 0 }; return 0; }",
        );
        let merged = apply_ambient_includes(vec![user]);
        assert!(
            !merged
                .iter()
                .any(|s| s.name() == STDLIB_BOUNDED_MAP_U256_U256_PATH),
            "a user `record BoundedMap_u256_u256_64` must suppress injection"
        );
    }

    #[test]
    fn scan_detects_bounded_map2_u256_u256_u256() {
        let src = SourceFile::new(
            "t.sigil",
            "module tool; fn g() { let m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new(); }",
        );
        let needs = scan_source(&src);
        assert!(
            needs.need_bounded_map2_u256_u256_u256,
            "`BoundedMap2_u256_u256_u256_*` must trigger need_bounded_map2_u256_u256_u256"
        );
        // Disjoint prefixes: the two-key trigger must NOT also set the single-level need.
        assert!(
            !needs.need_bounded_map_u256_u256,
            "the two-key prefix must not false-trigger the single-level map"
        );
    }

    #[test]
    fn apply_injects_bounded_map2_with_single_level_and_transitive() {
        // A `BoundedMap2_*` use injects the two-key map + the single-level map (the
        // `transfer_from` balance-move callee) + u256.sigil + transitive option/result
        // (`get` → Option<u256>) — each exactly once.
        let user = SourceFile::new(
            "user.sigil",
            "module tool; fn f() -> i64 { let m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new(); return m.len(); }",
        );
        let merged = apply_ambient_includes(vec![user]);
        for path in [
            STDLIB_BOUNDED_MAP2_U256_U256_U256_PATH,
            STDLIB_BOUNDED_MAP_U256_U256_PATH,
            STDLIB_U256_PATH,
            STDLIB_OPTION_PATH,
        ] {
            assert_eq!(
                merged.iter().filter(|s| s.name() == path).count(),
                1,
                "BoundedMap2 must inject exactly one `{path}`"
            );
        }
    }
}
