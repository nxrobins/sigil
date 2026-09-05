# Sigil tool-writing recipes

Short, load-bearing patterns the language reference doesn't cover in
depth. Use these as your scaffolding when starting a new tool.

## Pure tools (no FFI)

Default shape — runs in the inner ring, no host calls, no grants needed:

```sigil
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    // ... pure byte computation ...
}
```

* `i64` parameters — pointer arithmetic uses 64-bit math.
* `! { Alloc }` if and only if you call `alloc(...)`. If your tool just
  returns a packed pointer into the input buffer (e.g. `task001_echo`),
  drop the effect row entirely.
* No `#[ring(outer)]`, no `#[trusted]`. Pure tools live in the
  default inner ring.

## FFI tools (filesystem, network)

```sigil
#[ring(outer)] #[trusted] module tool;

extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64
    ! { FsIO, Alloc, FFI, Unsafe }
{
    let raw: i64 @Internal = fs_read(input_ptr, input_len);
    if raw < 0 { return raw; }
    let body_ptr: i64 @Internal = raw / 4294967296;
    let body_len: i64 @Internal = raw - body_ptr * 4294967296;
    // ... process @Internal-tainted bytes ...
}
```

Critical differences from pure tools:

1. **`i32` parameters, not `i64`.** The FFI ABI is fixed — pointer and
   length come in as `i32`. Mismatching causes a type error at
   `tool_main`.
2. **`#[ring(outer)] #[trusted]` on the module.** FFI requires the outer
   ring; without `#[trusted]` you cannot declare `extern "C"`.
3. **Effect row must include `FFI` and `Unsafe`** plus the resource
   effect (`FsIO` for filesystem, `NetIO` for network) and `Alloc` if
   you allocate output buffers.
4. **The extern signature also needs `! { FFI, Unsafe }`.**
5. **All values derived from the FFI return are `@Internal`-tainted.**
   The taint checker auto-marks FFI returns; you must propagate the
   annotation on every local that flows from them.

## Using the stdlib

If your task spec lists `stdlib_imports`, the harness composes those
modules into your compilation unit before `sigil_check` runs. Your
job: declare the import and call the function. You do NOT redeclare
the `extern "C"` shims — the stdlib module already does that.

**FFI-backed stdlib (`fs`, `crypto::sha*`, `time`, `random`, `http`,
`kv`)** — still needs the ring escalation:

```sigil
#[ring(outer)] #[trusted] module tool;

use sigil::fs;

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64
    ! { FsIO, Alloc, FFI, Unsafe }
{
    let raw: i64 @Internal = fs::read(input_ptr, input_len);
    if raw < 0 { return raw; }
    // ... etc ...
}
```

The `#[ring(outer)] #[trusted]` annotation, the effect row (including
`FFI` and `Unsafe`), and `@Internal` taint propagation rules from the
"FFI tools" recipe above ALL still apply. The only thing the stdlib
saves you is the `extern "C"` boilerplate and the packed-pointer
unpack helper.

**Pure-Sigil stdlib (`json`, `crypto::hex_*`)** — runs inner-ring,
no escalation needed:

```sigil
module tool;

use sigil::json;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let key_ptr: i64 = alloc(4);
    store8(key_ptr, 110);  // 'n'
    store8(key_ptr + 1, 97);  // 'a'
    store8(key_ptr + 2, 109);  // 'm'
    store8(key_ptr + 3, 101);  // 'e'
    return json::parse_field(input_ptr, input_len, key_ptr, 4);
}
```

`json::parse_field` returns the same packed-pointer ABI as your tool's
own return, so you can `return` its value directly.

### Ring escalation rule (R004)

Calling any FFI-backed stdlib module (`fs`, `crypto::sha*`, `time`,
`random`, `http`, `kv`) from a tool that DIDN'T declare `#[ring(outer)] #[trusted]`
emits R004 with the literal escalation text in the hint. Add the
annotation; don't try to work around it.

Pure-Sigil stdlib (`json`, `crypto::hex_*`) is callable from either
ring without escalation. If your task only needs pure-Sigil stdlib,
keep the tool inner-ring — fewer effect-row entries, smaller wasm,
no grant ceremony.

### Where to look up signatures

[`stdlib/STDLIB.md`](../../../../stdlib/STDLIB.md) is the canonical
per-module catalog: signatures, effect rows, grant requirements, and
per-fn determinism notes. Don't guess at signatures — the catalog is
load-bearing.

## Packed-pointer ABI

`tool_main` returns one `i64` that encodes both the output pointer and
the byte length:

```
return out_ptr * 4294967296 + out_len;
```

Equivalently `(out_ptr << 32) | out_len`, but multiply/add reads more
naturally and matches the rest of the bench corpus. A negative return
is propagated as an error code.

## Effect row cheat sheet

| Effect | When you need it |
|---|---|
| `Alloc` | Any call to `alloc(n)`. |
| `FFI`, `Unsafe` | Any `extern "C" fn` declaration AND any tool that calls one. |
| `FsIO` | Calling host filesystem FFI (`fs_read`, future `fs_write`). |
| `NetIO` | Calling host network FFI (`http_get`, `http_post`). |

Effect rows are **inferred at declaration sites** but **declared on the
function signature**. If your `tool_main` calls `alloc()` you must list
`Alloc`; if it calls `fs_read()` (which itself has `! { FFI, Unsafe }`),
you must list both `FFI` and `Unsafe` on `tool_main` — the rows merge,
they don't subsume.

## Taint at FFI boundaries

Every `extern "C"` return is `@Internal`-tainted automatically. This
flows through any local that receives it. The taint checker will reject
implicit-trust paths, e.g. you cannot return `@Internal` from a function
declared to return `@Public`. Where the bench harness asks you to render
output from an FFI body length, the rendered ASCII string remains
`@Internal` — and `tool_main`'s implicit return taint accommodates that.

In practice: when in doubt, annotate intermediate locals `@Internal`.
The checker only complains if a `@Public` declaration would be violated.

## Grants — what the host gives you

The harness will pass `grants` to `sigil_forge` based on the task spec.
Your tool source does **not** need to mention grants — they're a
host-side capability matrix, not source syntax.

* `fs: ["/abs/path"]` — host allows `fs_read` for any path under
  `/abs/path`. The harness canonicalizes paths so prefix-matching works.
* `net: ["example.com"]` — host allows `http_get` to that hostname.
  Pattern-matched against the URL host.

Without a matching grant the FFI returns a negative error code (403);
your tool must propagate that on `raw < 0`.

## Decimal-string rendering (common tail)

Many tasks return a number as ASCII decimal. Standard pattern:

```sigil
fn render_u64(n: i64) -> i64 ! { Alloc } {
    if n == 0 {
        let p = alloc(1);
        store8(p, 48); // '0'
        return p * 4294967296 + 1;
    }
    // count digits
    let mut tmp = n;
    let mut digits: i64 = 0;
    while tmp > 0 { tmp = tmp / 10; digits = digits + 1; }
    let p = alloc(digits);
    let mut i = digits - 1;
    let mut v = n;
    while i >= 0 {
        store8(p + i, 48 + (v - (v / 10) * 10));
        v = v / 10;
        i = i - 1;
    }
    return p * 4294967296 + digits;
}
```

If you need a signed renderer, prepend a `'-'` (45) for negatives and
delegate the magnitude to the unsigned form.

## Common diagnostics — quick fixes

| Code | Meaning | Fix |
|---|---|---|
| `T060` | Undefined local | Typo in identifier or missing `let` binding. |
| `T070` | Effect-row mismatch | Add the missing effect to your function signature. |
| `T080` | Type mismatch | Check `i32` vs `i64` — FFI uses `i32`. |
| `R001` | Wrong ring for FFI | Add `#[ring(outer)] #[trusted]` to the module. |
| `R002` | Missing `#[trusted]` | Required to declare `extern "C"`. |
| `O001` | Capability not granted | Host did not pass the grant; not a source problem. |
| `S002` | Missing `tool_main` | Add `pub fn tool_main(...)`. |
| `S003` | Wrong `tool_main` signature | Match the recipe shape exactly. |

When in doubt, call `sigil_lookup_error("CODE")` from outside this
prompt context — the harness exposes that tool. The catalog block
below carries the same data verbatim.
