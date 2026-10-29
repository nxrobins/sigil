# Bounded scalar reverse mode

Private `sigil/autodiff` `0.1.0-public.1`, experimental, unreviewed and not
admitted. Import `use sigil::autodiff;`. This is a scalar f64 computation tape,
not a tensor engine, GPU backend, general source transformation or straight
through estimator. The only effect is Alloc on constructors. All data is Public.

## Construction and handles

`new_tape(node_capacity:i64,sum_capacity:i64)->Tape !{Alloc}` allocates all
storage once. Node capacity is 1..4096; sum-edge capacity is 0..4096. Invalid
capacities produce a failed Tape with `.error` -400 or -413. Failed construction
still allocates metadata. `new_cell()->TapeCell !{Alloc}` allocates an output
cell with `.value = 0.0`. Other functions do not allocate.

Append functions return a positive i64 handle or a negative status. Handles
identify the tape's live allocator-owned marker, reset epoch and node index.
They are local to one execution, not portable serialized IR identifiers or
cryptographically unforgeable capabilities. Reset invalidates every old handle;
handles from another tape refuse. Each tape permits epochs 1..1048574, then
refuses reset rather than wrapping into stale identities.

| Function | Meaning |
| --- | --- |
| `variable(tape,value:f64)` | Differentiated leaf |
| `constant(tape,value:f64)` | Fixed leaf; not a gradient-query target |
| `add(tape,a,b)`, `sub(tape,a,b)`, `mul(tape,a,b)` | Arithmetic over two existing handles |
| `relu(tape,a)` | Maximum of input and zero; derivative zero at zero |
| `select(tape,condition:bool,yes,no)` | Fixed nondifferentiable condition; derivative flows only into the chosen branch; both handles must be valid |
| `sum(tape,nodes:Vec<i64>)` | Copy the supplied handles into reserved sum-edge storage, preserving order and repeated occurrences; empty sum is zero |

Append order is topological. Both ordinary operands and sum terms must already
exist on this tape. Sum input vectors are read-only, constructor-owned live
Public backing, at most 4096 slots; their handles are copied, so later edits to
the input list cannot change the graph. Successful graph mutation invalidates
previous gradient readiness. Failed append preserves graph and readiness.

## Backward and queries

`backward(tape,output:i64)->i64` seeds that scalar output with one and computes
all leaf gradients in one reverse traversal. Shared subexpressions and repeated
operands accumulate contributions. Disconnected variables receive zero.
Each call clears scratch adjoints first; repeated backward does not accumulate
an earlier call. No derivative flows through a select condition, and no surrogate
STEP rule is implied. Conditions must be supplied by the caller.

`value_into(tape,node,out:TapeCell)->i64` reads a node's forward value.
`gradient_into(tape,variable,out:TapeCell)->i64` reads a variable's gradient only
after successful backward on the current graph. `reset(tape)->i64` reuses the
same storage with a new epoch and an empty graph. Only queries take a read-only
Tape; all construction, reset and backward calls require a mutable Tape. Query
output cells are mutable and must be separate live constructor-owned cells.

`replay(tape,variables:Vec<i64>,values:Vec<f64>)->i64` updates distinct variable
handles and recomputes the existing graph transactionally through scratch.
The two read-only, caller-owned lists must have equal counts and at most 4096
slots. Successful replay invalidates gradient readiness, but retains handles
and topology. Failed replay preserves forward values and published gradients.
Select conditions remain the fixed decisions made when the graph was built;
rebuild/reset for a different branch decision. Duplicate variables refuse.
Duplicate detection is quadratic in the bounded update-list length; graph
replay is linear in nodes plus sum edges. The regression consumer updates two
variables rather than rebuilding its graph on every epoch.

Returned statuses are zero on success, -400 for invalid metadata/handles/query
state, -413 for capacity or epoch exhaustion, and -422 for nonfinite forward
values or derivative accumulation. Nonfinite arithmetic refuses rather than
publishing infinity or NaN. Backward uses scratch and publishes gradients only
after success; returned errors preserve the prior published gradient state.
Scratch may change on failure. Query errors preserve the caller's output cell.
Runtime traps or exhausted budgets can interrupt stores and are not atomic.

## Memory and numerical boundary

Tape records and vector headers are not sealed. Use constructor-owned live
storage; do not forge records, alter metadata/identity/epoch/operation arrays,
alias backing buffers or cells, change graph values behind the API, or mutate
them concurrently. Header, span and topological checks are not ownership or
backing-label proofs. Arbitrary forged addresses can still trap.

Finite binary64 values are supported. Reverse accumulation order can differ
from PyTorch, so tests use stated tolerances rather than cross-platform bitwise
equivalence. ReLU at zero follows the documented zero convention; finite
differences are checked away from branch boundaries. No higher derivatives,
broadcasting, optimizer, dynamic tape growth or new runtime grants are added.

Reference: [PyTorch autograd mechanics](https://docs.pytorch.org/docs/2.14/notes/autograd.html).
The library is original SIGIL code; actual CPU float64 PyTorch executions emit
the separate test answers.
