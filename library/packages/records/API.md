# Immutable bounded JSON records

Private `sigil/records` `0.1.0-public.1` packages the existing JSON codec
byte-for-byte and adds immutable object construction and exact binary scalars.
All records APIs preserve the join of input labels (Public, Internal, Secret);
they do not declassify or promise constant-time execution. Inner ring, Alloc
only, no host imports or grants. Previous bytes/numeric/autodiff packages stay
unchanged. The Public mutable bytes builder cannot consume classified KV data;
this layer instead copies inputs into fresh allocations.

## Construction

`new(limit)` returns an empty JsonRecord, with maximum output bytes 2..32768.
Each put accepts a read-only prior record and returns a new record; it never
changes the prior bytes or metadata. Check `error` before replacing your own
binding. An error record propagates through further puts and finish. Old records
remain available for rollback; there is no mutable shared builder state.

Keys are 1..64 ASCII bytes matching `[a-z_][a-z_0-9]*`. Duplicate keys refuse
with -409 rather than overwrite. At most 32 fields; order follows insertion.
`put_json(doc,key,key_len,value,value_len)` accepts up to 16384 ASCII bytes
containing one fully valid JSON value. Objects/arrays, booleans, null, numbers
and escaped Unicode are supported. Whitespace within supplied values is kept.
Nested object duplicates are not rejected by the existing JSON grammar.

`put_string` takes up to 2048 ASCII bytes, including controls, and uses existing
json::escape_string. It refuses non-ASCII input rather than claim UTF-8 validation
the underlying byte codec does not perform. Use escaped Unicode via put_json or
put_hex for arbitrary bytes. `finish(doc)` returns packed pointer/length or error.
Callers must keep constructor-owned records/backing live and not forge metadata.

Every put and scalar decode can allocate. Construction is bounded but not
allocation-free: prior complete records and temporary escaped values remain
until the ephemeral run ends. Runtime fuel/memory caps still apply; this is not
a proof that every maximum-size composition fits a particular tool's budget.

## Exact values

- `hex(ptr,len)` produces a quoted lowercase JSON hex string for 0..8191 bytes.
  `put_hex` adds that string as a field. `unhex(ptr,len,maximum)` consumes the
  decoded string body (no quotes), accepts lowercase even-length hex only and
  returns fresh bytes, never writes an existing destination. Maximum is 0..8191.
- `put_u64` stores exactly 16 big-endian textual hex digits, covering the entire
  unsigned range without a JSON floating-number conversion. `read_u64` consumes
  those 16 digits and returns WordValue { value:u64, error:i64 }.
- `put_f64le(doc,key,key_len,ptr,count)` stores 0..512 contiguous little-endian
  binary64 words as one hex string. `read_f64le(ptr,len,count)` decodes exactly
  that count to fresh bytes. Both reject infinities and every NaN payload;
  finite values, subnormals and signed zeros preserve their exact bits.
  Field/schema names must declare this representation: these are not JSON
  numeric literals and must not be interpreted as decimal numbers.

## Reading and errors

`field(ptr,len,key,key_len)` first validates the whole bounded document, then
uses json::parse_field. String results are decoded bodies, other results are
raw JSON values. It retains the existing -404 missing-field behavior. It does
not enforce an application schema, reject unknown/duplicate incoming fields,
or authenticate a record. Checkpoint restoration must enforce a version, exact
field set, identities and compatibility; deterministic reconstruction and byte
comparison can additionally enforce an application's canonical encoding.

Negative statuses: -400 invalid scalars/metadata/JSON, -404 absent field,
-409 duplicate added key, -413 capacity/work size, -422 key/encoding/nonfinite
value, plus existing JSON -429 entry and -430 nesting limits. Invalid backing
memory or exhausted runtime budgets may trap instead of returning an error.
No returned error modifies an input; no claim covers traps or forged aliasing.

The separate pinned json dependency retains its public API, including its less
strict direct extraction semantics. Prefer records::field for whole-document
validation. Source equality to stdlib/sigil/json.sigil is tested so a future
codec edit requires an explicit package update, not silent drift.
