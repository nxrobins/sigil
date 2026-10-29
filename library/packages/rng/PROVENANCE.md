# PCG reference and SIGIL adaptation

The state transition, initialization and XSH-RR output adapt Melissa O'Neill's
[PCG minimal C implementation](https://github.com/imneme/pcg-c-basic/tree/bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3),
revision `bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3`, retrieved 2026-10-28.
Copyright 2014 Melissa O'Neill. This adaptation uses its Apache-2.0 license;
the complete license is included as LICENSE.txt. SIGIL modifications are
Copyright 2026 SIGIL contributors.

The [upstream usage guide](https://www.pcg-random.org/using-pcg-c-basic.html)
describes seeds, streams, bounded sampling and conversion to double. The
test fixture retains the C source/header and license at that revision.
Its reference generator compiles and executes those files, not this SIGIL
implementation, to produce comparison answers.

SIGIL changes: explicit u64 wrapping and 32-bit output masks; XOR expressed
as OR minus AND because SIGIL has no XOR token; Public-only ownership;
checked stream/snapshot metadata; preallocated signed/float result cells;
support for the full 2^32 bound; and a 32-attempt rejection limit with
transactional refusal. Snapshot serialization is versioned. These changes
do not introduce secure randomness or preserve the old autoresearch LCG.
