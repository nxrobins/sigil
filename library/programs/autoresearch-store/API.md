# Autoresearch checkpoint storage transport

This experimental outer-ring tool imports storage and the unchanged KV adapter.
The root ABI takes two Public i64 input-span arguments and returns an Internal
packed byte span. Effects are Alloc, KvIO, FFI and Unsafe. Normal package-run
must refuse it. Execution requires a fresh solver-verified package graph and
the existing ephemeral host profile.

Input is binary, not JSON or hexadecimal inside SIGIL. An eight-byte header
contains AKVR for read or AKVP for publish, followed by version byte 1 and
three zero bytes. Read takes exactly that header. Publish appends a four-byte
little-endian previous length, the expected previous bytes and the next bytes.
Previous length is 0..8192; next length is 1..8192. Total input is at most 16396
bytes. Empty previous means the key must be absent. Read output is at most 8192
bytes. Publication returns an empty successful output, or a negative error.

Both operations address namespace autoresearch and key checkpoint. Separate
read and write grants remain mandatory for publication. The storage package
compares the previous value before one atomic write; this is single-writer
publication, not concurrent CAS or crash-durable storage. The host must serialize
cooperating writers and read after an uncertain publication outcome.

This tool treats bytes as opaque: native search must validate a checkpoint
before publication and after import. Malformed framing returns -400, -413 or
-422; storage errors propagate, including -403, -404, -409 and -500. Runtime
budgets remain 500000 cooperative fuel, 10000000 engine fuel and 16 MiB.

The separate host example requires --allow-public-checkpoint-import before
execution. This is an operator declaration that the selected job's stored
checkpoints may enter Public numerical computation, not proof that arbitrary
stored data is public. Stored results remain Internal inside SIGIL. The option
does not publish data, grant access, admit packages, bypass solver verification,
permit Secret inputs or change compiler and package-run rules.
