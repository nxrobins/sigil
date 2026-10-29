# Bracket matching tool contract

Experimental public-source consumer of `sigil/fmt`; not an admitted library release.

`tool::tool_main(input_ptr: i64 @Public, input_len: i64 @Public) -> i64 @Public ! { Alloc }`
reads the supplied byte buffer and returns exactly ASCII `true` or `false`.
The three bracket pairs `()`, `[]` and `{}` must close in nesting order. Empty
input is valid. Unmatched openers, unmatched closers and crossed pairs are
invalid. All other bytes, including NUL and UTF-8 bytes, are ignored. This is
not a parser: brackets inside quoted strings and comments still count. The
caller supplies a valid buffer of the stated length.

The result encodes `pointer * 4294967296 + length`. Its bytes belong to the
ephemeral runtime instance, which consumes them before discarding the store.
The validator requests an input-length stack allocation; `fmt::boolean` requests
one fresh four- or five-byte output allocation. Inputs and results are Public;
this entry point does not accept confidential data. There are no host imports,
filesystem/network grants or trusted surfaces.

For the documented CLI path, input is capped at 1 MiB, default SIGIL fuel is
100,000 (explicit 1..10,000,000), engine fuel is 10,000,000 and linear memory is
16 MiB. Long inputs may exhaust fuel. Resource limits are execution bounds, not
a guarantee that every input under the byte cap completes. The package
declaration describes intent, not independent admission.
