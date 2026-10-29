# Packaged existing KV adapter

Public-source sigil/kv public.1 contains stdlib/sigil/kv.sigil byte-for-byte. Its
get, put and delete operations retain Internal parameters/results, outer-ring
trusted declarations and the existing KvIO/FFI/Unsafe effects. Get also allocates.
Read and write namespaces are separately granted. Put is atomic per value;
durability is OS write-back, not multi-key transactions or compare-and-swap.

The source carries precise ABI, errors and size limits. This package changes
no runtime or permission and is experimental, unreviewed and not admitted.
