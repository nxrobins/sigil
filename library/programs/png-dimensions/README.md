# PNG dimension inspector

Inspect the size of a PNG without decoding its pixels. Give this SIGIL tool the
first 24 file bytes as hex; it returns dimensions such as `800x600`, without a
newline. This is a fresh application built from the bytes/fmt project starter,
not a migrated training tool. It uses the shared big-endian bytes reader and
unchanged fmt decimal formatter, with no application-local endian conversion.
The fixed-capacity `bytes_out` builder assembles the output without local copying,
formatted-pointer unpacking or output offsets; final failure is sticky.

Experimental source only: unreviewed, not admitted and not a PNG
validator. It checks the signature, IHDR length/type and dimension range, but
does not check CRCs, the remaining header fields, image chunks or pixels. See
the [API contract](API.md) for exact accepted input and refusal behavior.

## Run a fixed example

With the solver-enabled `sigil` from the [public workflow](../../WORKFLOW.md)
on PATH, run from the repository root:

```sh
sigil package-lock --root library/programs/png-dimensions --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.4 --dependency sigil/fmt=library/packages/fmt
sigil check --package library/programs/png-dimensions
sigil run --package library/programs/png-dimensions --input 89504e470d0a1a0a0000000d494844520000032000000258
```

The exact result is `800x600`. Create the lock only on a fresh checkout; the
working starter-derived project is already locked. Existing locks refuse
overwrite; ordinary repeated check/run uses that lock and its local cache.

## Inspect a real PNG

In Bash or zsh on a system with `xxd` and `tr`, choose a local image:

```sh
png_header_hex=$(xxd -p -l 24 path/to/image.png | tr -d '\n')
sigil run --package library/programs/png-dimensions --input "$png_header_hex"
```

The shell reads the file, not SIGIL. Exactly 48 hex characters are required;
uppercase hex is also accepted. Never pass the whole image as text. Short or
non-PNG prefixes, malformed hex, zero dimensions and dimensions above
2147483647 refuse execution. Normal fuel and memory limits remain in force.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
