# CVE-2014-6271: Shellshock — bash environment variable command execution

**Affected:** GNU bash through 4.3
**CVE record:** https://nvd.nist.gov/vuln/detail/CVE-2014-6271
**Severity:** CVSS 9.8 (Critical, before CVSS v3); colloquially "10/10"
**Scope of claim:** BY-CONSTRUCTION

## What was the bug

GNU bash supports exporting shell functions through environment variables. A variable like `BASH_FUNC_x()=() { ... }` would be parsed at bash startup as a function definition. The bug: bash continued parsing characters AFTER the closing brace of the function body, treating them as additional shell commands to execute immediately.

An attacker who could control any environment variable inherited by a bash subprocess could append arbitrary commands. Since bash is invoked by CGI servers, mail filters, DHCP clients, and countless other privileged contexts that propagate env vars from external inputs, the attack surface was vast.

Disclosed September 24, 2014, Shellshock affected nearly every Unix-like system in the world. A patch on the same day was incomplete; the full fix required six CVE numbers across a week.

## How attackers exploited it

The canonical PoC against a CGI server:

```
HTTP request:
  User-Agent: () { :; }; /bin/cat /etc/passwd
```

The web server propagated the User-Agent into the `HTTP_USER_AGENT` environment variable when invoking the CGI script. Bash parsed the value as a function definition (the `() { :; };` part) and then executed the trailing `/bin/cat /etc/passwd` as a regular command — as the web server's user.

The bug was used against routers, NAS appliances, embedded Linux devices, and any web server running CGI scripts. Worms and exploit kits were deployed within hours.

## SIGIL's defense

The Shellshock bug existed because bash treated environment variable VALUES as code. SIGIL has no shell, no environment-variable evaluation step, and no equivalent of bash's "parse this string as a function definition" path.

Configuration values arrive in SIGIL as actor message payloads with declared types, or as capability spawn arguments. The wire format is the SIGIL type — there is no point at which bytes from the environment are interpreted as code. The Shellshock bug pattern is structurally inexpressible.

This is a BY-CONSTRUCTION defense: the language lacks the offending feature entirely. No vulnerable SIGIL fixture can be written.

## Vulnerable shape

Not expressible in SIGIL. See the SIGIL defense section above for why.

## Safe alternative

See [`06_cve_2014_6271_shellshock_safe.sigil`](06_cve_2014_6271_shellshock_safe.sigil). Configuration is a typed capability (`ConfigAuth`) passed at spawn time; never a string value being interpreted as code.

## Defense layer

| Original language | Defense gap | SIGIL primitive | Diagnostic |
|---|---|---|---|
| bash | Environment-variable parser executed trailing commands after function bodies | No shell, no string-as-code execution | (none — by construction) |

## Citations

- https://nvd.nist.gov/vuln/detail/CVE-2014-6271
- https://www.troyhunt.com/everything-you-need-to-know-about/
- https://www.invisiblethings.org/papers/SHELLSHOCK-tutorial.pdf
