# Canonical bounded evaluation exchange

Public-source sigil/exchange public.1 is inner-ring, Alloc-only and Flow-labeled.
It preserves input label joins; it does not declassify or promise constant-time
execution. Inputs are live, valid byte spans. Every returned record owns fresh
decoded storage; no operation changes request, response or prior result bytes.

## Requests

request(profile,profile_len,context,context_len,sequence,payload,payload_len)
returns packed pointer/length JSON or a negative status. Profiles contain 1..64
lowercase ASCII letters, digits, dash, dot, underscore or colon. Context is
1..128 arbitrary identity bytes. Sequence is an exact unsigned 64-bit word.
Payload is 0..512 opaque bytes. The canonical object is bounded at 1536 bytes
and contains, in this order: format=sigil-evaluation-request-v1, profile,
context_hex, sequence, payload_hex. Byte fields use lowercase hex; sequence
uses sixteen hexadecimal digits, not a JSON number.

open_request(ptr,len) returns EvaluationRequest with profile/profile_len,
context/context_len, sequence, payload/payload_len and error. It validates the
whole document, decodes fields and requires exact canonical reconstruction.
Unknown or duplicate fields, alternative spellings, whitespace, malformed hex
and noncanonical scalar encodings refuse. The library does not interpret the
profile or payload; applications must validate both before execution.

## Responses

respond(request_ptr,request_len,status,payload,payload_len) first validates the
request, then returns canonical JSON with format=sigil-evaluation-response-v1,
request_hex, status and payload_hex. It echoes the complete exact request,
not merely a sequence number or caller-provided hash. Payload is 0..1024 bytes;
the envelope is bounded at 6144 bytes. Status is an exact u64 in 0..4:
success=0, candidate-refused=1, worker-failed=2, cancelled=3, timed-out=4.
A failure is a typed result, not a poor fitness value; the application chooses
whether to stop or explicitly retry. A trapping worker may produce no response.

open_response(expected_ptr,expected_len,response_ptr,response_len) returns
EvaluationReply { status, payload, payload_len, error }. It validates both
records, requires byte equality with the entire expected request and checks
canonical response framing. It does not accept a response for another context,
sequence, profile or payload. It does not validate application-level result
structure or numerics, which must happen before updating application state.

## Trust and replay

An application derives the expected request from its current persisted state,
binds a unique job identity plus program/profile identity in context, and
advances its sequence on successful consumption. A repeated response then
fails against the new expected request. These pure functions themselves keep
no mutable replay ledger and cannot detect a caller deliberately rolling back
its own state or reusing an identity. Delivery is not guaranteed exactly once;
workers may need an idempotency policy for repeated requests.

Identity is not authentication. Neither echoed bytes nor an unsigned program
certificate proves that a worker executed the request or reported an honest
score. Authentication and trusted storage remain separate, explicit boundaries.

## Failure bounds

Invalid signed spans return -400, missing fields -404, incompatible format or
request mismatch -409, size excess -413, invalid schema/encoding/status -422;
existing JSON errors propagate. Exhausted execution budgets and invalid memory
may trap. The maximum-size combination must be measured under the caller's
existing budget, not used as permission to raise it.
