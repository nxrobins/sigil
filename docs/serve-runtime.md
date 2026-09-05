# sigil-serve — the HTTP trigger and durable scheduler

**Status:** shipped (v1). The third tier of the platform story: with
`json` (codecs) and `kv` (durable storage) in the stdlib, this host
layer turns one-shot tools into long-lived services. The guest never
listens, never sleeps, never holds resident state — the HOST owns
every long-lived concern and maps each stimulus to one
`execute_ephemeral` run. This is the architecture the ephemeral
runtime was built for (see `memory-model.md`: leak-until-exit is only
correct because processes die in milliseconds — so processes must
keep dying).

```
            ┌───────────────────────── sigil-serve (host) ─────────────────────────┐
 HTTP req ──▶ route ──▶ execute_ephemeral(tool, body) ──▶ output = response body   │
            │                                                                      │
 interval ──▶ durable mark check ──▶ execute_ephemeral(tool, input) ──▶ log        │
            │        (state_dir/schedule_state.json, atomic tmp+rename)            │
            └──────────────────────────────────────────────────────────────────────┘
                     tools stay sandboxed: per-tool grants, per-run fuel
                     cross-run state lives behind kv grants
```

## Running

```
sigil-serve service.json            # start
sigil-serve service.json --check    # validate config + compile tools, exit
sigil-serve service.json --once T   # run schedule entry T now (marks untouched)
```

## Configuration

JSON, one file. Tool `source` paths and `state_dir` resolve relative
to the config file's directory.

```json
{
  "tools": {
    "counter": {
      "source": "counter.sigil",
      "fuel": 1000000,
      "grants": {
        "kv": ["demo=./kvdata"],
        "kv_write": ["demo=./kvdata"],
        "fs": [], "fs_write": [], "net": [],
        "time": ["wall"], "random": ["secure"]
      }
    }
  },
  "http": {
    "bind": "127.0.0.1:8787",
    "max_inflight": 16,
    "routes": [ { "path": "/counter", "tool": "counter", "content_type": "text/plain" } ]
  },
  "schedule": [ { "name": "tick", "tool": "counter", "every_ms": 2000, "input": "" } ],
  "state_dir": "state",
  "host_profile": "ephemeral"
}
```

Grant descriptors reuse the MCP envelope's conventions (`kv`:
`"NS=DIR"`, `time`: `"wall"`/`"frozen:<ms>"`, `random`:
`"secure"`/`"seeded:<u64>"`, `secret`: `"NAME=VALUE"`) with one
deliberate difference: a config file is operator intent, so malformed
descriptors and missing grant directories are BOOT ERRORS, never
silently dropped grants. Tools are compiled once at boot;
`execute_ephemeral` caches the compiled module, so per-request cost is
instantiate + run.

The `secret` grant is what makes `http::post_secret` reachable from a
served tool: the guest writes `{{secret:NAME}}` in its header blob and
the host substitutes the value on the way out, so the credential never
enters guest memory and cannot be copied into a response. Only the first
`=` separates name from value, so base64- and JWT-shaped credentials
need no escaping. An entry with no `=`, or an empty name, refuses to
boot rather than starting a server on which every placeholder would be
denied — a failure that would otherwise look like an upstream auth
error. Diagnostics never echo the entry, since a malformed one is still
a credential; note that the config file itself holds the value in the
clear, so keep it out of version control.

`host_profile` names the declared host profile every tool is compiled against.
`"ephemeral"` is the built-in host this service runs tools under: each of its host
operations (`fs_*`, `http_*`, `kv_*`, `crypto_*`, `random_bytes`, `time_now`) is declared
Internal-occurrence, so a tool may check one host result before making the next host call.
Omit the key for the legacy no-profile context, where every host operation is
Public-occurrence and such a tool is refused by the formal gate.

## The HTTP trigger contract (v1)

- Route patterns are `/`-separated segments: literals, `:name`
  parameters (bind one non-empty segment), and a final-position
  `*rest` wildcard (binds the remaining path, possibly empty; bare
  `*` matches without binding). Most-specific wins — literal beats
  parameter beats wildcard, compared left-to-right — and two routes
  with the same shape (`/t/:a` vs `/t/:b`) are a boot error, so
  shadowing cannot happen silently. Bound parameters are delivered in
  the request envelope's `params` field; raw-mode routes can use
  patterns for matching but do not see the bindings.
- Tool input, per-route `"input"` mode:
  - `"raw"` (default): the request body; for bodyless requests (GET
    et al.) the raw query string.
  - `"envelope"`: the framed request envelope — see below.
- Tool output, per-route `"output"` mode:
  - `"raw"` (default): output bytes = the 200 response body
    (`content_type` per route, default `application/octet-stream`).
  - `"envelope"`: the tool authors status + headers — see below.
- Tool negative codes map straight onto HTTP statuses — the stdlib's
  error conventions are HTTP-shaped on purpose, and any code in
  `[-599, -400]` passes through as that status (so a dispatching tool
  can answer `-405` → 405, `-401` → 401, …). Codes outside the range
  get no invented semantics: 500. Host-side failures (fuel
  exhaustion, genuine traps) are 500.
- Connections are persistent (HTTP/1.1 keep-alive): pipelined bytes
  are buffered correctly across requests, `Connection: close` and
  HTTP/1.0 are honored, idle connections close after the 5 s read
  timeout, and each connection rotates after 100 requests. Error
  responses always close. `Expect: 100-continue` is honored.

## The request envelope

`"input": "envelope"` routes hand the tool the full request shape:

```
input = <8-digit ASCII envelope length> <envelope JSON> <raw body bytes>
```

The envelope JSON (keys alphabetical, deterministic):

```json
{"headers":[["host","..."],["content-length","9"]],
 "method":"POST","params":[["id","42"]],
 "path":"/things/42","query":"a=1&b=2"}
```

- Header names are lowercased, values trimmed, arrival order kept;
  duplicates stay duplicated (array of pairs, not an object).
- `params` carries the route pattern's bound segments in pattern
  order (empty array for fully-literal routes).
- The BODY is the raw tail after the envelope — never re-encoded into
  the JSON, so binary bodies stay byte-exact. `body_len = input_len -
  8 - envelope_len`; an empty tail means a bodyless request (the
  query string is in the envelope).
- The 8-digit frame exists because JSON can't carry the body honestly
  (arbitrary bytes aren't a JSON string), and a self-describing
  `body_offset` field would need zero-padded numbers — which the
  strict `json` codec correctly rejects as leading zeros.

Guest-side recipe (the `json` codec is the intended consumer):

```sigil
// parse the frame
let mut env_len: i64 = 0;
let mut i: i64 = 0;
while i < 8 {
    env_len = env_len * 10 + load8(input_ptr + i) - 48;
    i += 1;
}
let env_ptr: i64 = input_ptr + 8;
// extract fields (strings come back escape-DECODED)
let m: i64 = json::parse_field(env_ptr, env_len, mkey_ptr, 6);
// headers: parse_field("headers") -> raw array slice,
// then json::parse_index for each ["name","value"] pair
```

`crates/sigil-serve/tests/serve_http.rs::dispatcher_tool_routes_on_method_via_json_codec`
is the worked example: method dispatch in-guest, `-405` for
disallowed methods, decoded query extraction on GET.

## The response envelope

`"output": "envelope"` routes let the TOOL author the response —
status and headers, not just the body. Same frame, reversed
direction; tool output becomes:

```
output = <8-digit ASCII envelope length> <envelope JSON> <raw body bytes>
```

The response envelope (both fields optional; `{}` = 200 with route
defaults):

```json
{"status": 201,
 "headers": [["content-type","application/json"],["location","/things/42"]]}
```

- `status` must be in 100..=599. Negative-return error paths are
  unchanged — the `[-599, -400]` passthrough still applies, so a tool
  only builds an envelope on its success paths.
- The tool's `content-type` header wins; the route's `content_type`
  fills in when absent.
- The HOST keeps ownership of the response framing:
  `Content-Length` is always computed from the actual body tail,
  `Connection` and `Transfer-Encoding` cannot be tool-set. A tool
  naming any host-owned header, using CR/LF or control bytes in a
  value (response-splitting), sending a malformed frame, a status
  outside range, an unknown envelope field, or a body on 204/304 gets
  a loud `500 malformed response envelope` — protocol bugs surface,
  they don't pass through.

Guest-side, the `json` encode primitive closes the loop:
`json::escape_string` renders header values, the envelope is byte
assembly, and the 8-digit frame is a ten-line render loop. Worked
examples:
`serve_http.rs::guest_builds_envelope_with_escape_string` (escaped
header values) and `both_envelopes_roundtrip_method_into_header`
(request envelope in, response envelope out — parse with
`parse_field`, answer with an authored header).

Bounds: 8 KB header cap (431), 5 MB body cap (413, checked against
`Content-Length` before transfer), 5 s per-connection read/write
timeouts, `max_inflight` concurrent connections (503 beyond — a
keep-alive connection occupies its slot for its whole life, bounded
by the idle timeout and the 100-request rotation).

## The durable scheduler contract (v1)

Entries carry exactly one cadence: `every_ms` (fixed interval; hard
floor 10 ms, use ≥ 1000 in production) or `cron` (five-field UTC
expression: `minute hour day-of-month month day-of-week`, supporting
`*`, `*/step`, ranges, and comma lists; numeric fields only, 0 =
Sunday; the classic vixie rule applies — when both day fields are
restricted, EITHER matches). Per-entry last-run marks persist to
`state_dir/schedule_state.json` via atomic tmp + rename after every
run. Semantics chosen for one-shot tools:

- **Never-ran intervals fire at boot** (infinitely overdue); a
  never-ran CRON entry instead waits for its next slot — cron means
  "at these times", not "this often".
- **Overdue fires ONCE** — a host that was down for 100 intervals
  catches up with one run, not a backfill storm.
- **A crash between run and persist re-runs at most once** — the
  failure mode is one early run, never a silent skip.
- `--once` is a manual poke: it runs the entry but does not touch the
  marks, so it cannot shift the cadence.

Marks are wall-clock epoch ms (restart durability requires the wall
clock); large NTP steps therefore shift cadence. v1 accepts this.

## Security posture

- The example configs bind `127.0.0.1`; put a real proxy in front
  before binding wider. For proxy fronting without any TCP loopback
  exposure, bind a unix socket instead: `"bind": "unix:/run/app.sock"`
  (stale socket files are replaced at boot, removed at shutdown).
- The host process is trusted (it holds the grants); each TOOL stays
  sandboxed exactly as under `sigil forge` — fail-closed grants,
  per-run fuel, 5 MB I/O caps. A route cannot reach anything its
  tool's grants don't name.
- Per-tool `"cert": "path.json"` pins a tool to its verification
  certificate: boot verifies schema, source and wasm fingerprints,
  fresh solver verification (the cert's own bit is forgeable and is
  ignored — build with the `solver` feature for a verifying host, or
  set `SIGIL_ALLOW_UNVERIFIED_CERT=1` to serve from a solver-less
  build), and the gated-effect ⇄ grant cross-check (`FsIO`, `NetIO`,
  and — beyond the CLI's list — `KvIO`): a cert-claimed effect without
  grants or a grant the cert never claims both refuse to boot.
- In-process TLS is a deliberate NON-goal — serve stays std-only.
  Terminate TLS in a fronting proxy (unix-socket bind recommended).

## Out of scope (v1)

- HTTP/2; chunked transfer encoding (Content-Length bodies only).
- Per-entry jitter; overlapping-run suppression across entries
  sharing a tool; cron day/month NAMES and non-UTC time zones.
- Keep-alive / HTTP/2, TLS, graceful drain on signal (abrupt exit is
  safe by the scheduler semantics above).

## Tests

`crates/sigil-serve/tests/` — `serve_http.rs` (echo + counter routes
over real TCP, status mapping, caps, concurrency, config rejection)
and `scheduler_durability.rs` (boot-run semantics, restart without
re-run, overdue-once, `--once` leaves marks alone). The counter tests
are the FaaS shape end-to-end: every increment is a fresh wasm
process; continuity lives in a kv grant.
