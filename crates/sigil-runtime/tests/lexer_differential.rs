//! PR-1a — the differential-lexer harness foundation (see
//! `docs/specs/lexer-in-sigil.md`).
//!
//! Step 1 (this commit): prove the `as_output` TRANSFER — a pure-SIGIL,
//! inner-ring tool builds a `str` and ships its bytes to the host. Pure-SIGIL
//! byte output is otherwise blocked: raw `data_ptr` construction is quarantined,
//! and an FFI shim is unusable because the lexer needs inner-ring stdlib
//! (`Vec`/strings) while FFI is outer-ring. `s.as_output()` is the sanctioned
//! inner-ring intrinsic that packs a built `str`'s header into the forge ABI's
//! output return `(data_ptr << 32) | len`. The token-stream differential test
//! rests on this.

use sigil_compiler::compile_tool;
use sigil_compiler::diagnostics::{DiagnosticCode, codes};
use sigil_compiler::lexer::{Token, TokenKind, lex as oracle_lex};
use sigil_compiler::source::SourceFile;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The SIGIL lexer source, inlined into each tool (its `module lexer;` line is
/// stripped, like `vec_runtime.rs` inlines `vec.sigil`).
const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");

fn lexer_tool(body: &str) -> String {
    let defs = LEXER.replace("\nmodule lexer;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Decode a negative-sentinel scalar return (`return 0 - v;` → positive `v`).
fn decode_neg(source: &str, input: &[u8]) -> i64 {
    let compiled = compile_tool(source).expect("tool should compile");
    match execute_ephemeral(&compiled.wasm, input, FUEL, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("expected a negative sentinel, got: {message}"))
                + p.len();
            let e = message[s..].find(')').expect("malformed trap");
            message[s..s + e].parse::<i64>().expect("parse sentinel")
        }
        other => panic!("expected a negative sentinel, got {other:?}"),
    }
}

/// Generous fuel — the lexer scan + the O(tokens) encoder (records accumulate in a
/// `Vec<str>` joined once) are both linear, but the largest stdlib file (~3 K tokens,
/// ~13 KB) is still the dominant workload. A high ceiling keeps the differential about
/// CORRECTNESS, not performance; real usage is far under it.
const FUEL: u64 = 300_000_000;

fn forge(source: &str, input: &[u8]) -> Vec<u8> {
    let compiled = compile_tool(source).expect("tool should compile");
    execute_ephemeral(&compiled.wasm, input, FUEL, &IoGrants::none())
        .expect("tool should execute")
        .output
}

#[test]
fn as_output_round_trips_a_literal() {
    // `s.as_output()` packs the str header into the forge ABI's positive return,
    // so the host reads the string's bytes into ToolResult.output. Pure inner
    // ring — no FFI, no `#[ring(outer)]`.
    let src = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let s: str = "hello, lexer";
    return s.as_output();
}
"#;
    assert_eq!(forge(src, b""), b"hello, lexer");
}

#[test]
fn as_output_round_trips_a_constructed_string() {
    // The real use: emit a string the tool BUILT (`concat`, inner-ring) — this is
    // how the lexer ships its token-stream encoding. Both `concat` and the tool
    // are inner-ring, so no cross-ring (R004) wall.
    let src = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: str = "tok:";
    let b: str = a.concat("42");
    return b.as_output();
}
"#;
    assert_eq!(forge(src, b""), b"tok:42");
}

#[test]
fn as_output_round_trips_input_via_from_bytes() {
    // The lexer reads its source from the tool input via `from_bytes`, then emits.
    // This proves the full input→str→output path the differential harness uses.
    let src = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let opt: Option<str> = input_ptr.from_bytes(input_len);
    let s: str = opt.unwrap_or("<bad utf8>");
    return s.as_output();
}
"#;
    assert_eq!(forge(src, b"lex me"), b"lex me");
}

// ── the SIGIL lexer compiles + runs (smoke) ──────────────────────────────────

#[test]
fn lexer_compiles_and_counts_tokens() {
    // "foo 123 ( )" → Ident, IntLit, LParen, RParen, Eof = 5 tokens.
    let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
        \x20   let src: str = opt.unwrap_or(\"\");\n\
        \x20   let toks: Vec<Token> = lex(src);\n\
        \x20   return 0 - toks.len();";
    assert_eq!(decode_neg(&lexer_tool(body), b"foo 123 ( )"), 5);
}

#[test]
fn lexer_empty_source_is_just_eof() {
    let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
        \x20   let src: str = opt.unwrap_or(\"\");\n\
        \x20   let toks: Vec<Token> = lex(src);\n\
        \x20   return 0 - toks.len();";
    assert_eq!(decode_neg(&lexer_tool(body), b""), 1); // just Eof
}

// ── the differential test: SIGIL lex(src) == Rust lex_with_id (ET-2) ──────────

/// The StrLit tag — must match `selfhost/lexer.sigil`'s `T_STR`. The host uses it
/// to recognize string records when length-walking the decoded-value pool.
const T_STR: i64 = 5;

/// PR-E3: the f-string literal-chunk tag — must match `selfhost/lexer.sigil`'s
/// `T_FSTR_CHUNK` (and `tag_of(FStrChunk)`). A chunk carries decoded text in the pool
/// exactly like a StrLit, so the host length-walks the pool for it too.
const T_FSTR_CHUNK: i64 = 121;

/// The error-token tag — must match `selfhost/lexer.sigil`'s `T_ERR`. A token with
/// this tag is a lexer DIAGNOSTIC carried in the stream (its `value` is the L-code,
/// its span the error span); the host splits these out of the real-token stream and
/// compares them to `lex_with_id`'s diagnostics (PR-3b).
const T_ERR: i64 = 800;

/// The TOTAL `TokenKind -> tag` map (ET-9). NO `_` arm — a new Rust `TokenKind`
/// won't COMPILE until it is mapped here, so the contract can't silently drift
/// from the oracle. As of PR-2c every kind maps to a real named tag matching
/// `selfhost/lexer.sigil`'s consts — the SIGIL lexer lexes the whole token
/// vocabulary, so there is no longer an "unhandled" sentinel.
fn tag_of(kind: &TokenKind) -> i64 {
    use TokenKind::*;
    match kind {
        Eof => 0,
        Ident(_) => 1,
        IntLit(_) => 2,
        // u256 PR-U2: wide (>i64) literal. Tagged here only so this drift-locked
        // map compiles; the self-hosted lexer twin does not lex wide literals yet
        // (PR-U4, deferred), so no wide-literal fixture is in the differential
        // corpus and this arm is never exercised at runtime.
        IntLit256(_) => 900,
        BoolLit(_) => 3,
        FloatLit(_) => 4, // PR-2b: span only, value not compared (AG-L3)
        // single-char operators / punctuation / delimiters
        LParen => 10,
        RParen => 11,
        LBrace => 12,
        RBrace => 13,
        LBracket => 14,
        RBracket => 15,
        Semicolon => 16,
        Comma => 17,
        Dot => 18,
        Plus => 19,
        Minus => 20,
        Star => 21,
        Slash => 22,
        Percent => 23,
        Eq => 24,
        Lt => 25,
        Gt => 26,
        Ampersand => 27,
        Pipe => 28,
        Bang => 29,
        Question => 30,
        Colon => 31,
        Hash => 32,
        At => 33,
        // keywords
        Actor => 50,
        Ask => 51,
        Cap => 52,
        Const => 53,
        Declassify => 54,
        DeclassifyCt => 55,
        Distinct => 56,
        Else => 57,
        Effect => 58,
        Entry => 59,
        Enum => 60,
        Extern => 61,
        Handle => 62,
        Fn => 63,
        For => 64,
        If => 65,
        Impl => 66,
        In => 67,
        Init => 68,
        Let => 69,
        Match => 70,
        Module => 71,
        Mut => 72,
        On => 73,
        Break => 74,
        Continue => 75,
        Pub => 76,
        Grant => 77,
        Ring => 78,
        Record => 79,
        Region => 80,
        Return => 81,
        Send => 82,
        Spawn => 83,
        State => 84,
        Supervision => 85,
        Trait => 86,
        Type => 87,
        Use => 88,
        While => 89,
        With => 90,
        // multi-char operators (PR-2a, maximal munch) — must match the T_* consts
        // (100-119) in `selfhost/lexer.sigil`'s `scan_op`.
        PlusEq => 100,
        MinusEq => 101,
        StarEq => 102,
        SlashEq => 103,
        PercentEq => 104,
        EqEq => 105,
        FatArrow => 106,
        BangEq => 107,
        LtEq => 108,
        GtEq => 109,
        LtLt => 110,
        LtLtEq => 111,
        GtGt => 112,
        GtGtEq => 113,
        AmpersandEq => 114,
        PipeEq => 115,
        ColonColon => 116,
        Arrow => 117,
        DotDot => 118,
        DotDotEq => 119,
        // string literals (PR-2c) — value compared via the decoded-text channel.
        StrLit(_) => 5,
        // PR-E3: f-string token sequence. Tags must match `selfhost/lexer.sigil`'s
        // `T_FSTR_*` once the self-hosted lexer mirror lands; until then no f-string
        // fixture exercises these (the existing corpus has none), so they are inert.
        FStrBegin => 120,
        FStrChunk(_) => 121,
        FStrHoleStart => 122,
        FStrHoleEnd => 123,
        FStrEnd => 124,
        AndAnd => 125,
        OrOr => 126,
    }
}

/// The differential tool's wasm, compiled ONCE (the body is fixed; only the input
/// source varies). Avoids recompiling the lexer for every fixture.
fn lexer_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
            \x20   let src: str = opt.unwrap_or(\"\");\n\
            \x20   let toks: Vec<Token> = lex(src);\n\
            \x20   let enc: str = encode(toks);\n\
            \x20   return enc.as_output();";
        compile_tool(&lexer_tool(body))
            .expect("lexer tool should compile")
            .wasm
    })
}

/// The oracle's decoded SCALAR value for the kinds ET-3 compares via the record's
/// 4th field: IntLit (incl. hex) → the i64; BoolLit → 1/0. `None` for every other
/// kind — notably FloatLit (value span-only, AG-L3) and StrLit (compared via its
/// decoded-text channel, not a scalar). Unlike `tag_of`, a `_` arm is correct
/// here: this extracts values, it is not the totality contract.
fn value_of(kind: &TokenKind) -> Option<i64> {
    use TokenKind::*;
    match kind {
        IntLit(v) => Some(*v),
        BoolLit(b) => Some(i64::from(*b)),
        _ => None,
    }
}

/// A decoded SIGIL token: the four record fields, plus a StrLit's decoded string
/// value (sliced from the pool). `text` is `None` for every non-string kind.
#[derive(Debug, Clone, PartialEq)]
struct SToken {
    tag: i64,
    start: i64,
    end: i64,
    value: i64,
    text: Option<String>,
}

/// Run the SIGIL lexer on `source` and decode its `records|pool` stream. Records are
/// `tag,start,end,f4;…`; for a StrLit, f4 is the decoded byte-length and its bytes are
/// taken in order from the pool (length-walked, so arbitrary value bytes — `,`/`;`/`|`/
/// newline — are safe). The host splits on the FIRST `|`; records never contain one.
fn sigil_tokens(source: &str) -> Vec<SToken> {
    let out = execute_ephemeral(lexer_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("lexer tool should execute")
        .output;
    let enc = String::from_utf8(out).expect("encoding is utf8");
    let (records, pool) = enc
        .split_once('|')
        .expect("encoding carries a records|pool separator");
    let pool = pool.as_bytes();
    let mut cursor = 0usize;
    let mut toks = Vec::new();
    for rec in records.split(';').filter(|s| !s.is_empty()) {
        let mut it = rec.split(',').map(|x| x.parse::<i64>().expect("int field"));
        let tag = it.next().expect("tag");
        let start = it.next().expect("start");
        let end = it.next().expect("end");
        let value = it.next().expect("value");
        let text = if tag == T_STR || tag == T_FSTR_CHUNK {
            // PR-E3: both a StrLit and an f-string chunk carry f4 = decoded byte-length
            // with the bytes taken in order from the pool.
            let len = usize::try_from(value).expect("non-negative string length");
            let bytes = &pool[cursor..cursor + len];
            cursor += len;
            Some(String::from_utf8(bytes.to_vec()).expect("string value is utf8"))
        } else {
            None
        };
        toks.push(SToken {
            tag,
            start,
            end,
            value,
            text,
        });
    }
    toks
}

/// ET-2 + ET-3: compare the SIGIL token stream token-by-token against the Rust
/// oracle, localizing the first divergence — tag + start + end, AND the decoded
/// `value` for the value-bearing kinds (IntLit incl. hex, BoolLit true/false).
fn assert_lexes_like_oracle(source: &str) {
    check_lex(source, source);
}

/// The differential core for CLEAN sources. `label` (a filename for the stdlib
/// corpus, the source itself for the small hand corpus) is used in failure messages
/// instead of dumping the whole source — a 13 KB stdlib file would be unreadable.
fn check_lex(source: &str, label: &str) {
    let sigil = sigil_tokens(source);
    let sf = SourceFile::new("diff.sigil", source.to_string());
    let (oracle, diags) = oracle_lex(&sf);
    assert!(diags.is_empty(), "oracle lex errored on {label}: {diags:?}");
    compare_tokens(&sigil, &oracle, source, label);
}

/// Token-by-token comparison (tag + start + end + decoded value), shared by the clean
/// differential and the error differential. For the error corpus `sigil` is the
/// real-token stream with the error-tokens already removed (the oracle emits no token
/// for an error), so the two streams must still align position-for-position. Mismatches
/// print the oracle lexeme so a divergence is locatable.
fn compare_tokens(sigil: &[SToken], oracle: &[Token], source: &str, label: &str) {
    assert_eq!(
        sigil.len(),
        oracle.len(),
        "token COUNT differs on {label}: sigil={} oracle={}",
        sigil.len(),
        oracle.len()
    );
    for (idx, (s, r)) in sigil.iter().zip(oracle.iter()).enumerate() {
        let lexeme = source.get(r.span.start..r.span.end).unwrap_or("<span oob>");
        let rtag = tag_of(&r.kind);
        assert_eq!(
            s.tag, rtag,
            "token {idx} TAG differs on {label}: sigil={} oracle={:?}({rtag}) lexeme={lexeme:?}",
            s.tag, r.kind
        );
        assert_eq!(
            s.start as usize, r.span.start,
            "token {idx} START differs on {label}: oracle {:?} lexeme={lexeme:?}",
            r.kind
        );
        assert_eq!(
            s.end as usize, r.span.end,
            "token {idx} END differs on {label}: oracle {:?} lexeme={lexeme:?}",
            r.kind
        );
        // ET-3: the decoded value. StrLit and an f-string chunk compare their decoded
        // TEXT (escapes applied, byte-for-byte); the scalar kinds compare the i64 value.
        if let TokenKind::StrLit(expected) | TokenKind::FStrChunk(expected) = &r.kind {
            let got = s
                .text
                .as_deref()
                .unwrap_or_else(|| panic!("token {idx} string missing decoded text on {label}"));
            assert_eq!(
                got, expected,
                "token {idx} STRING VALUE differs on {label}: sigil={got:?} oracle={expected:?}"
            );
        } else if let Some(rval) = value_of(&r.kind) {
            assert_eq!(
                s.value, rval,
                "token {idx} VALUE differs on {label}: sigil={} oracle={:?}({rval}) lexeme={lexeme:?}",
                s.value, r.kind
            );
        }
    }
}

/// The PR-2c corpus — keyword-rich SIGIL-ish soup, every single-char + multi-char
/// operator (packed against idents/ints for the munch boundaries), bools, idents,
/// decimal + hex ints (decoded values, ET-3), floats (span only), line comments,
/// and string literals: plain, empty, every escape, unknown escapes, strings
/// carrying record-delimiter bytes (`,`/`;`), and non-ASCII content — each with its
/// decoded value compared byte-for-byte (ET-3). The whole token vocabulary now.
fn corpus() -> Vec<&'static str> {
    vec![
        "",
        "   leading and trailing spaces   ",
        "foo bar99 _x y2 z3 999 0 42",
        // every keyword + both bools (the coverage bedrock — ET-1)
        "actor ask cap const declassify declassify_ct distinct else effect entry \
         enum extern handle fn for if impl in init let match module mut on break \
         continue pub grant ring record region return send spawn state supervision \
         trait type use while with true false",
        // every single-char operator / delimiter
        "( ) { } [ ] ; , . + - * / % = < > & | ! ? : # @",
        // every multi-char operator, space-separated (coverage — ET-1)
        "+= -= *= /= %= == => != <= >= << <<= >> >>= &= |= :: -> .. ..=",
        // multi-char operators packed against identifiers/ints — the maximal-munch
        // boundary test: a 2/3-byte prefix must NOT mis-split into single tokens
        "a+=b c-=d e*=f g/=h i%=j k==l m!=n o<=p q>=r s::t u->v w..x y..=z",
        "a<<b c>>d e<<=f g>>=h i&=j k|=l m=>n",
        // line comments: skipped to EOL; tokens resume after
        "let x = 1 ; // trailing comment\nlet y = 2 ;",
        "// leading comment\nfn foo ( ) { }",
        "a // c1\nb // c2\nc",
        // near-real snippets
        "pub fn add ( a , b ) { let mut s = a + b ; return s ; }",
        "if x { return 1 ; } else { return 0 ; }",
        "match v { 1 , 2 , 3 } enum E record R while true",
        "fn f ( a : i64 ) -> i64 { return a ; } let p = Foo :: bar ;",
        "let r = lo .. hi ; flags |= mask ; n >>= 2 ; if a == b { } ",
        // numeric literals — decimal + hex (lower/upper digits, 0x/0X); the
        // decoded i64 value is compared per-token (ET-3), bools carry value 1/0
        "0 42 255 1000000 7 true false",
        "0x0 0xff 0xFF 0X1f 0xDEAD 0xCAFE 0x7FFFFFFF",
        // hex stops at the first non-hex byte — `0xFFz` is IntLit(255)·Ident(z)
        "let h = 0xFFz ; let k = 0xff + 1 ;",
        // floats are span-only (AG-L3); the int/dot boundaries must NOT float:
        // `1.foo` = Int·Dot·Ident, `2..3` = Int·DotDot·Int, spaced ranges too
        "3.14 0.5 100.0 2.0 0.0 42.999",
        "a = 1.foo ; b = 2..3 ; for i in 0 .. 9 { } let e = 1 ..= 5 ;",
        "x += 0x10 ; y = 3.5 ; z = 255 + 0xff ; w = true ; v = false ;",
        // string literals — plain + empty; the decoded value is compared (ET-3)
        "let s = \"hello\" ; let e = \"\" ;",
        // every escape: `\n` `\t` `\"` `\\` decode; the span covers the quotes
        "\"a\\nb\" \"t\\tu\" \"q\\\"x\" \"p\\\\q\"",
        // unknown escape keeps the char (the `\` dropped): `\x41`→`x41`, `\r`→`r`
        "\"\\x41\" \"hi\\rthere\"",
        // a string carrying record-delimiter bytes (`,` and `;`) — exercises the
        // pool channel: these MUST NOT corrupt the host's record parsing
        "fn g ( ) -> str { return \"ok\" ; } let m = \"a, b ; c\" ;",
        // non-ASCII content — appended a whole codepoint at a time, byte-for-byte
        "let u = \"héllo wörld\" ; let j = \"日本語\" ;",
        // PR-E3: f-strings `f"…{e}…"` — the lexer emits a TOKEN SEQUENCE (FStrBegin,
        // alternating FStrChunk + FStrHoleStart…hole-tokens…FStrHoleEnd, FStrEnd). Each
        // chunk's decoded TEXT is compared (escapes + `{{`/`}}` un-escaping), the holes'
        // inner tokens are byte-identical to top-level lexing (shared `lex_step`).
        "let r = f\"hello\" ;",                         // no holes
        "let e = f\"\" ;",                              // empty f-string (one empty chunk)
        "let r = f\"a{x}b\" ;",                         // leading + trailing chunks + hole
        "let r = f\"{x}\" ;",                           // hole only (empty chunks both sides)
        "let r = f\"{a}{b}\" ;",                        // adjacent holes (empty middle chunk)
        "let r = f\"id={n}!\" ;",                       // trailing text after the hole
        "let r = f\"{a + b}\" ; let q = f\"{g(x)}\" ;", // arith + call holes
        "let r = f\"{Foo::bar}\" ;",                    // path hole
        "let r = f\"{{lit}}\" ;",                       // escaped braces → literal `{lit}`
        "let r = f\"a\\nb{x}c\\td\" ;",                 // `\n`/`\t` escapes in chunks
        "let r = f\"q\\\"x{x}p\\\\q\" ;",               // `\"`/`\\` escapes in chunks
        // UTF-8 chunks around a hole — multi-byte codepoints pass whole (ET-E6)
        "let r = f\"héllo {s} 日本\" ;",
        // `f` NOT immediately before `\"` stays Ident + StrLit (no f-string)
        "let f = 1 ; let s = f ; let t = \"x\" ;",
    ]
}

#[test]
fn differential_core_tokens() {
    for src in corpus() {
        assert_lexes_like_oracle(src);
    }
}

/// The stdlib differential corpus — the design's "done" line. Every real
/// `stdlib/sigil/*.sigil` file MUST lex token-for-token AND value-for-value
/// identically to the oracle. Real files exercise the whole language at scale —
/// generics (`Vec<Vec<T>>` → `>>`), `#[...]` attributes, doc comments, strings
/// with escapes, hex/float numbers — far beyond the hand corpus. This is what
/// makes "the SIGIL lexer reproduces lex_with_id" a claim about real source.
#[test]
fn differential_stdlib_corpus() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/sigil");
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read stdlib dir {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "sigil"))
        .collect();
    files.sort();
    assert!(
        files.len() >= 10,
        "expected the full stdlib (>=10 files), found {} under {}",
        files.len(),
        dir.display()
    );
    for path in &files {
        let src = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let name = path.file_name().expect("file name").to_string_lossy();
        check_lex(&src, &name);
    }
}

/// Map a lexer `DiagnosticCode` to the i64 the SIGIL lexer carries in an error-token's
/// `value`. Only the lexer codes are expected here.
fn code_num(c: DiagnosticCode) -> i64 {
    if c == codes::L001 {
        1
    } else if c == codes::L002 {
        2
    } else if c == codes::L003 {
        3
    } else if c == codes::L004 {
        4
    } else {
        panic!("unexpected lexer diagnostic code {c:?}")
    }
}

/// PR-3b — the lexer-error differential (AG-L4: presence + position, not message text).
/// The SIGIL lexer emits an error-token (tag `T_ERR`, `value` = L-code, span = the error
/// span) exactly where the oracle emits a diagnostic + NO token. On a malformed corpus we
/// assert BOTH halves: (1) with the error-tokens removed, the real-token stream still
/// matches the oracle's tokens — i.e. error recovery resyncs to the same byte; and (2) the
/// error-tokens match the oracle's diagnostics by code + span. Covers the structural,
/// deterministic-span errors L001 (hex without digits), L003 (unterminated string), L004
/// (unexpected char). The value-overflow sub-cases — an int/hex literal exceeding i64, and
/// the (essentially unreachable) invalid-float L002 — are deferred: matching them would mean
/// reproducing Rust's exact `parse`/`from_str_radix` overflow boundary, and such literals
/// do not occur in real source.
#[test]
fn differential_lexer_errors() {
    let corpus: Vec<&str> = vec![
        // L004 unexpected char — one diagnostic per stray byte; scanning resyncs
        "let x = ~ ;",
        "a $ b ^ c",
        "fn f ( ) { return `x` ; }",
        // an error mid-stream, valid tokens on both sides (`\\` is not a token)
        "let a = 1 ; \\ let b = 2 ;",
        // L003 unterminated string — span runs to EOF (newlines are in-string)
        "let s = \"oops",
        "\"no close\nlet y = 1 ;",
        // L001 hex without digits — span covers the `0x`, then scanning resumes
        "let h = 0x ;",
        "let z = 0xZ + 1 ;",
        // several errors in one source, in order
        "0x ~ \"unterminated",
    ];
    for src in corpus {
        let sigil = sigil_tokens(src);
        let sigil_real: Vec<SToken> = sigil.iter().filter(|t| t.tag != T_ERR).cloned().collect();
        let sigil_errs: Vec<SToken> = sigil.iter().filter(|t| t.tag == T_ERR).cloned().collect();
        let sf = SourceFile::new("err.sigil", src.to_string());
        let (oracle, diags) = oracle_lex(&sf);
        assert!(
            !diags.is_empty(),
            "expected the oracle to report lexer diagnostics on {src:?}"
        );
        // (1) error recovery: the real-token stream matches the oracle's tokens.
        compare_tokens(&sigil_real, &oracle, src, src);
        // (2) AG-L4: error-tokens match the oracle's diagnostics by code + span.
        assert_eq!(
            sigil_errs.len(),
            diags.len(),
            "diagnostic COUNT differs on {src:?}: sigil={} oracle={}",
            sigil_errs.len(),
            diags.len()
        );
        for (idx, (e, d)) in sigil_errs.iter().zip(diags.iter()).enumerate() {
            let span = d.span().expect("a lexer diagnostic carries a span");
            assert_eq!(
                e.value,
                code_num(d.code()),
                "diag {idx} CODE differs on {src:?}: sigil={} oracle={:?}",
                e.value,
                d.code()
            );
            assert_eq!(
                e.start as usize, span.start,
                "diag {idx} START differs on {src:?}"
            );
            assert_eq!(
                e.end as usize, span.end,
                "diag {idx} END differs on {src:?}"
            );
        }
    }
}

#[test]
fn et1_corpus_covers_every_emitted_tag() {
    // ET-1: every tag the SIGIL lexer can emit must appear >=1x across the corpus
    // — otherwise "passes the corpus" is hollow (a tag could be wrong + untested).
    let mut seen = std::collections::HashSet::new();
    for src in corpus() {
        for t in sigil_tokens(src) {
            seen.insert(t.tag);
        }
    }
    let mut expected: Vec<i64> = vec![0, 1, 2, 3, 4, 5]; // EOF IDENT INT BOOL FLOAT STR
    expected.extend(10..=33); // single-char operators / delimiters
    expected.extend(50..=90); // keywords
    expected.extend(100..=119); // multi-char operators (PR-2a)
    let missing: Vec<i64> = expected
        .iter()
        .copied()
        .filter(|t| !seen.contains(t))
        .collect();
    assert!(
        missing.is_empty(),
        "corpus does not cover emitted tags: {missing:?}"
    );
}

#[test]
fn et4_spans_tile_the_source() {
    // ET-4 (oracle-INDEPENDENT): spans are monotonic + non-overlapping, every end
    // within the source, and Eof sits at exactly [len, len]. (Whitespace/comments
    // leave gaps BETWEEN tokens, so the law is `start >= prev_end`, not equality.)
    for src in corpus() {
        let toks = sigil_tokens(src);
        let n = src.len() as i64;
        let mut prev_end = 0i64;
        for (idx, t) in toks.iter().enumerate() {
            assert!(t.start <= t.end, "token {idx} start>end on {src:?}");
            assert!(t.end <= n, "token {idx} end past len on {src:?}");
            assert!(
                t.start >= prev_end,
                "token {idx} overlaps previous on {src:?}"
            );
            prev_end = t.end;
        }
        let last = toks.last().expect("at least Eof");
        assert_eq!(
            (last.start, last.end),
            (n, n),
            "Eof must be [len,len] on {src:?}"
        );
    }
}

#[test]
fn et8_lex_is_deterministic() {
    // ET-8: same source → identical token stream across runs.
    for src in corpus() {
        assert_eq!(
            sigil_tokens(src),
            sigil_tokens(src),
            "non-deterministic on {src:?}"
        );
    }
}

#[test]
fn et7_never_traps_on_adversarial_bytes() {
    // ET-7: the lexer must RETURN (a stream, now possibly with T_ERR=800 error-tokens)
    // and never trap. Inputs are valid UTF-8 oddballs (`from_bytes` rejects invalid
    // UTF-8 upstream): unknown punctuation, NUL, dense punctuation, whitespace,
    // adversarial numbers, and unterminated / oddly-escaped / non-ASCII strings.
    let inputs: Vec<&str> = vec![
        "~`^\\$", // bytes that start no token → L004 error-tokens
        "\0\0\0", // NUL run (valid UTF-8)
        "aaaaaaaaaaaaaaaaaaaa 9999999999",
        "{[(;,.+-*/%=<>&|!?:#@)]}", // dense punctuation (no whitespace)
        "\t\n\r   \n",              // whitespace only
        "0x",                       // hex prefix, no digits (EOF mid-literal)
        "0xG 0X 0x;",               // 0x followed by a non-hex byte / EOF / punct
        "1. 2.. 3...4 5.6.7",       // dot-adjacent numbers (float vs dot vs range)
        "999999999999999999999999", // 24 digits — i64 accumulation must not trap
        "\"oops",                   // unterminated string (EOF before closing quote)
        "\"trailing\\",             // backslash as the last byte (EOF mid-escape)
        "\"\\\"",                   // escaped quote then EOF (never actually closes)
        "\"héllo 日本\"",           // non-ASCII content — codepoint-aligned substr
        "\"\\é\"",                  // backslash before a multi-byte char (no trap)
    ];
    for src in inputs {
        let toks = sigil_tokens(src); // panics if the tool traps / mis-returns
        assert!(!toks.is_empty(), "must emit at least Eof on {src:?}");
    }
}
