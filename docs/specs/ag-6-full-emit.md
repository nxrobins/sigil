# Generic-enum full-emit contract

**Status:** Implemented. This is the current contract for the AG-6 generic-enum emission surface;
the incremental implementation journal is retired.

## Result

The self-hosted pipeline emits the certified compiler source with its real `tool_main`
byte-identically to the Rust oracle. The driver path includes `Option<str>::unwrap_or`, so the
capstone covers a generic-enum impl method, enum construction, and enum matching without a fixed
wrapper in the emitted image.

The claim is deliberately bounded. It establishes the generic-enum forms named below and the
certified with-driver image; it does not mean every SIGIL construct is accepted by the self-hosted
emitter.

## Emission invariants

### Concrete identity

- A concrete generic enum retains its type arguments wherever the emitter needs layout or method
  receiver information.
- Bare and qualified variant construction resolve to the same concrete enum identity under the
  same expected type.
- A monomorphized enum method is exported under the enum's defining module, not the module where
  the instance happened to be materialized.

### Cell layout

An enum cell is an `i32` declaration-order tag at offset 0 followed by packed payload bytes at
offset 4. A concrete generic-enum instance has one uniform size:

```text
4 + max(sum(substituted payload widths) for every variant)
```

Sizing from only the constructed variant is forbidden. In particular, constructing a unit or
narrow variant of an instance with an eight-byte type argument must still reserve the widest
substituted variant. The accepted scalar/pointer widths come from the same self-host type-token
mapping used by the differential corpus.

### Match and method surface

- Unit and single-payload variant matches emit through the ordinary tag-and-payload path.
- Multi-payload matches load binders from accumulating payload offsets.
- Generic-enum impl methods are monomorphized through the normal instance path; `unwrap_or` is the
  certified driver case.
- Forms that cannot recover a complete concrete enum identity must poison or be rejected. They may
  not emit using placeholder widths.

## Fail-closed boundary

The executable fence corpus governs unsupported or partially covered forms. Current non-claims
include recursive generic enums, `?`/`OptionTry`, uninstantiated library methods, closures or
iterators in enum-method bodies, and payload widths absent from the self-host width mapping.
Tuple-element, record-field, method-argument, and reassignment contexts remain fail-closed when a
complete enum instance cannot be recovered.

A zero poison census is necessary but insufficient: a mis-sized enum can produce valid-looking
Wasm without poison. Byte equality with the Rust oracle is the acceptance gate.

## Evidence

The current authorities are executable:

- `ag6_generic_enum_method_corpus` and `ag6_generic_enum_method_no_divergence` cover method
  monomorphization and the equality-or-poison rule.
- `ag6_multipayload_match_parity`, `ag6_multipayload_exec`, and
  `ag6_match_no_fail_open` cover match layout and execution.
- `generic_unit_variant_layout_is_context_independent` covers production bare/qualified identity.
- `ag6_6_narrow_variant_size_corpus` covers narrow/wide variants, four/eight-byte arguments,
  returns, calls, and multiple type parameters.
- `ag6_7_unresolved_generic_enum_contexts_fail_closed` pins unsupported contexts.
- `pin_fence_registry_never_diverges` requires every known emit hole to reject, poison, or equal the
  oracle, never silently diverge.
- `ag6_5_with_driver_byte_capstone` proves the complete with-driver image is byte-identical without
  an entry splice.

`docs/CLAIMS.md`, `docs/SOUNDNESS_MATRIX.md`, and the preservation manifests own the public claim,
residual-risk boundary, and required semantic case names.

## Change rule

Any newly emitted generic-enum form must land with a byte-differential fixture for that exact form.
Removing a poison fence without matching oracle bytes is a regression even when the result is valid
Wasm or executes successfully.
