# Packaged existing JSON codec

Private `sigil/json` `0.1.0-public.1` makes the existing
`stdlib/sigil/json.sigil` available through the local package loader, with
byte-identical source. It does not rewrite the parser or change its semantics.
The module's documented parse_field, parse_index, array_len, validate and
escape_string APIs remain label-preserving, inner-ring and host-free.

Extraction allocates and may return before validating a whole document. Call
validate first when whole-document strictness matters. Object duplicate keys
are not rejected; raw bytes above ASCII pass transparently, so callers retain
UTF-8 and application-schema obligations. The records dependency layer adds
bounded immutable construction and strict whole-document field extraction.

This is experimental, unreviewed and not admitted. Existing codec error,
nesting and entry limits remain. A byte-equality regression binds this source
to the original; upgrades must be explicit and preserve prior package pins.
