# Bounded parameter trials

Private `sigil/optim` `0.1.0-public.1`, inner ring, Public-only, no host
imports or grants. It composes the unchanged numeric package. This is a staged
sign-update primitive, not a full optimizer or PyTorch API replacement.

`new_trial(rows,cols)->ParameterTrial !{Alloc}` allocates two numeric matrices:
original and proposed. Numeric's positive dimensions and 4096-element limit
apply. Check `error` before use. Phase 0 is idle; phase 1 has an open proposal.
All other APIs allocate no memory. Callers supply a separate live numeric
`Scalar` scratch cell, which may change during validation, including on error.

`begin_sign(trial @Mut,weights @ReadOnly,gradient @ReadOnly,step:f64,
low:f64,high:f64,cell @Mut)->i64` requires idle phase, equal shapes, finite
matrices and finite scalar arguments, step >= 0 and low <= high. Every weight
must already be within [low,high]. Stage
`clamp(weight-step*sign(gradient),low,high)`, treating zero gradient as zero.
Reject a nonfinite intermediate before clipping. The caller's weights stay
unchanged. Save the original values and publish the proposed matrix only after
all validation; phase becomes 1. All returned errors preserve both trial
matrices, phase and caller weights; scratch-cell contents are not preserved.

`commit_into(trial @Mut,weights @Mut,cell @Mut)->i64` requires open phase,
matching shapes and a destination whose current values equal the saved values.
Changed values return -409 without overwriting them or closing the trial.
On success, copy proposed values through numeric::scale_into and return to
idle. Equality is numerical, so signed zeros compare equal. This is not an
authenticated identity, concurrent-write lock or sealed transaction.

`rollback(trial @Mut)->i64` requires an open trial and returns it to idle.
It never writes caller weights: no tentative change was committed. Saved and
proposed matrices remain available for inspection until the next successful
begin. Double commit/rollback and begin while open refuse.

## Errors and ownership

Zero means success. -400 is invalid phase/metadata or forbidden aliasing;
-409 is a changed commit destination; -413 is numeric shape/span capacity;
-422 is shape incompatibility, invalid bounds/rate or nonfinite data/result.
Constructor failures propagate. Returned-error preservation does not cover
traps, exhausted fuel, concurrent memory mutation or forged backing.

Use live constructor-owned matrices and a separate Scalar cell. Trial matrices
must not overlap each other, inputs or commit destination. Read-only weights
and gradient may overlap each other. Records are unsealed: callers must not
edit trial internals or forge backing/scratch aliases. Numeric performs shape,
span and finite-input validation; ordinary operations use only fixed storage.
Fitness comparison and adaptive step-size policy belong to the application.
