# Proposal protocol v1

Native Public inner-ring application, Alloc only, no grants/imports. Candidate
validation and the ACPU wire/profile are identical to the CPU evaluator.
Request: canonical lowercase hex of APRP, version byte 1, mode byte 0 (seed) or
1 (restore), two zero reserved bytes, two little-endian u64 words, then one
complete ACPU request. Mode 0 words are seed/stream; mode 1 words are state/odd
increment for RNG snapshot version 1. Unknown modes/versions refuse.
Length is 100..144 bytes (200..288 hex characters).

One mutation kind is drawn uniformly in 0..5. Kinds 0/1/2 select an instruction
and replace opcode plus correctly ranged second operand / first register /
writable destination respectively. Kind 3 appends a random instruction unless
already at 12; kind 4 deletes one unless at 1. At those limits, the kind draw is
consumed but the candidate stays unchanged. Kind 5 selects a weight and adds
`unit()*0.5-0.25`, clipping to [-4096,4096]. It is not the original Q16 random
walk. All branch draw order is part of v1. The original policy remains in this
application, not the generic RNG package.

Response: five little-endian u64 words (version 1, new RNG state, odd increment,
kind, candidate-wire length), then the complete changed ACPU request, then
an exact echo of the input binary request. CPU step count is preserved.
Maximum response 304 bytes. Construction precedes a no-growth allocation fence;
mutation and snapshot use only preallocated records/buffers. Returned errors
publish no checkpoint: -413 bounds, -422 format/state/numerical input, -429
RNG retry limit, -500 allocation-fence violation. Runtime fuel/memory refusal
remains outside scalar status. The runtime limits are unchanged.

The JSON wrapper emits exactly format, algorithm, candidate, steps, state,
increment, mutation, request_sha256. Format is `sigil-autoresearch-proposal-v1`;
algorithm `pcg-xsh-rr-64-32-v1`. State/increment are canonical 16-digit lowercase
hex strings, avoiding JSON binary64 integer loss. It refuses duplicate/unknown
fields, invalid numbers, incompatible algorithms, echo mismatch and malformed
output. `request_sha256` identifies input bytes, not an authenticated receipt.
Resume validates the record but cannot authenticate who produced it.
The optional candidate output is create-new, including refusal of symlinks.
