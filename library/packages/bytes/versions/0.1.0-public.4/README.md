# bytes package

Read, write and manipulate bounded Public byte spans.

Public source revision `0.1.0-public.4` is experimental, unreviewed and not admitted.
The [API contract](API.md) defines the supported operations, caller preconditions,
error behavior and resource limits. These remain limits, not permission to widen
capabilities or bypass the compiler and certificate checks.

The implementation is preserved byte-for-byte from its preceding dogfood revision;
this revision gives it self-contained documentation and newly bound metadata.
`source-provenance.json` records the original version and module byte hashes.
Select the new version and content hash explicitly; an old lock or certificate
must not be reused for this graph. Keep the preceding root/cache for rollback.

Each package is MIT OR Apache-2.0 unless an accompanying provenance/license file
identifies an additional notice. Numerical packages run on CPU/Wasm, not a GPU.
