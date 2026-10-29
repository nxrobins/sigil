# Bounded CPU floating point matrices

Experimental public-source `sigil/numeric` `0.1.0-public.1`, unreviewed and not admitted.
Import `use sigil::numeric;`. Storage reuses the actual ambient stdlib `Vec<f64>`;
no new float-memory intrinsic, compiler cast, host service or native backend is
introduced. Ambient option/result/vector code is identified in certificates.

## Source API

`zeros(rows:i64,cols:i64)->Matrix !{Alloc}` creates a row-major matrix initialized
to zero. Dimensions must be positive and their product at most 4096 elements.
Invalid dimensions return a failed Matrix with `.error` -400 or -413 and no
element backing; metadata construction still allocates. `new_scalar()->Scalar
!{Alloc}` creates an initially zero `.value` result cell. These constructor-owned
records and their backing must remain live for calls using them.

The remaining functions have empty effect rows and return i64 status: zero on
success, negative on refusal. All parameters/results are Public. Scalars are
written through a caller-created Scalar; a negative floating-point value is
ordinary data, never an error sentinel.

| Operations | Inputs and destination |
| --- | --- |
| `set(a,row,col,value:f64)` | Set one in-range element of a valid Matrix |
| `get_into(a,row,col,out:Scalar)` | Read one element after validating the input |
| `add_into`, `sub_into`, `mul_into` | Two equal-shaped matrices and an equal-shaped Matrix output |
| `scale_into(a,factor:f64,out)` | Matrix and finite factor, equal-shaped output |
| `relu_into(a,out)` | Negative elements become zero; equal-shaped output |
| `sum_into`, `mean_into` | Matrix and Scalar output; reduction in row-major order |
| `dot_into(a,b,out:Scalar)` | Sum of pairwise products over equal-shaped flattened matrices, not a general torch.dot overload |
| `transpose_into(a,out)` | Output shape is `(a.cols,a.rows)` |
| `matmul_into(a,b,out)` | `(m,k)` times `(k,n)` into `(m,n)`; ordinary CPU loops |
| `mse_into(prediction,target,out:Scalar)` | Equal shapes; mean squared difference over all elements |
| `mse_grad_into(prediction,target,out)` | Equal-shaped output; derivative with respect to prediction, `2/N * (prediction-target)` |
| `sgd_step(weights,gradient,rate:f64)` | Equal shapes; updates weights in place by `weights-rate*gradient`; rate finite and nonnegative |

Matrix output parameters and the weights in sgd_step are mutable; other Matrix
parameters are read-only. Scalar outputs are mutable. General matrix outputs
must not overlap either input's declared backing region. Inputs may overlap
one another because they are read-only. SGD weights and gradient must be
disjoint. Scalar outputs must be separate constructor-owned cells.

## Refusals and memory boundary

Constructor failures propagate before use. Malformed shape/backing metadata,
out-of-range indices or forbidden aliasing return -400. Shape/element/span limits
return -413. Incompatible shapes, nonfinite inputs/results or invalid rates
return -422. Shape products are checked by division before multiplication;
validated spans stay below 2147483647 bytes/address units. Nonempty dimensions
avoid division by zero in mean/MSE. Metadata checks are not ownership proofs.

Every returned error preserves destination values, including SGD weights and
Scalar results. Arithmetic operations validate all results before their writing
pass, so a late overflow does not publish a successful prefix. Reductions commit
their Scalar only after the result is finite. `set` checks the selected index
and new value; other old elements are not inspected by that operation.

Do not forge records, edit vector metadata, alias Scalar cells with backing,
mutate source memory concurrently or use freed/incorrectly labeled backing.
Constructor ownership, lifetime and Public backing remain caller preconditions;
records are not sealed and no complete ownership/backing-label proof is claimed.
Traps and exhausted runtime fuel/memory can interrupt stores; returned-error
preservation is not transactionality under interruption. Normal operator calls
do not allocate. Constructors and user-created probes are measured separately.

## Numerical scope

This is binary64 CPU computation without SIMD, GPU, BLAS, broadcasting, strided
views, general automatic differentiation, momentum or Adam. IEEE NaN/infinity
are refused; signed zero and finite subnormal values are accepted. Reductions
use explicit left-to-right accumulation, not compensated summation. Finite
overflow is refused rather than wrapped or returned as infinity. Exact float
agreement with reordered/accelerated kernels is not promised.

Element counts convert exactly to f64 through bounded repeated addition because
this compiler has no general integer/float cast. That additional linear work is
included in measurements. Negative float literals are written `0.0 - value`;
no language extension or scientific-literal parsing change is included.

References: [PyTorch matmul](https://docs.pytorch.org/docs/2.14/generated/torch.matmul.html),
[MSELoss](https://docs.pytorch.org/docs/2.14/generated/torch.nn.MSELoss.html), and
[SGD](https://docs.pytorch.org/docs/2.14/generated/torch.optim.SGD.html). Valid-domain
CPU float64 observations are compared with actual PyTorch, plus analytic/finite
difference controls. This is a declared subset, not PyTorch API equivalence.
