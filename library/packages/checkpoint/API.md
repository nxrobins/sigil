# Canonical bounded checkpoint envelopes

Public-source sigil/checkpoint public.1 is inner-ring, Alloc-only and Flow-labeled.
It imports records/json and owns framing, compatibility and revision checks,
not application-state semantics or storage. Live constructor-owned byte spans
are required; no signature or authenticated history is claimed.

initialize(domain,domain_len,compatibility,compatibility_len,current,current_len)
returns a canonical JSON checkpoint at revision zero. Identifiers contain
1..64 lowercase ASCII letters, digits, dash, underscore, dot or colon. Current
and previous payloads are opaque bytes, independently bounded at 4096 bytes.
Callers validate their own population, budget, RNG and other state invariants.

The exact ordered fields are format="sigil-checkpoint-v1", domain,
compatibility, revision, current_hex, previous_hex. Revision is sixteen lowercase
hex digits encoding an unsigned integer in 0..4294967295; payloads are lowercase
hex. Revision zero requires an empty previous payload. There is no extra
whitespace. An envelope is bounded at 32768 bytes.

open(ptr,len,domain,domain_len,compatibility,compatibility_len) validates the
whole document, checks expected identities, decodes the fields and requires
byte equality with canonical ordered chunks. Payloads are not repeatedly
re-encoded. Unknown/duplicate/missing fields,
alternate spellings, noncanonical whitespace and invalid scalar encodings refuse.
It returns Checkpoint { revision:u64, current, current_len, previous,
previous_len, error }, with fresh decoded spans. A missing field propagates -404;
malformed JSON is -400, incompatible identity -409, size/revision excess -413,
and schema/encoding/canonical mismatch -422.

advance(prior,prior_len,domain,domain_len,compatibility,compatibility_len,
expected_revision,next,next_len) first opens the prior record and requires
the expected revision. It returns a fresh envelope at revision+1 with the old
current payload as previous. Revision overflow refuses. Neither success nor
returned error modifies prior bytes. This retains one predecessor, not an
unbounded journal. An intentional rollback would be a new revision containing
the previous payload, not a silently rewound revision.

Every operation can allocate. Runtime interruption is not a returned status;
generic bounds are not a promise that every composition fits a caller's budget.
Flow preserves Public/Internal/Secret joins and does not declassify. The library
does not perform I/O. The separately granted state adapter publishes opaque
bytes; the host must keep pure validation and classified storage boundaries
explicit and serialize writers.
