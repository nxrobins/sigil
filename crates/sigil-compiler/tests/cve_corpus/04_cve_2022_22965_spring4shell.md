# CVE-2022-22965: Spring4Shell — Spring Framework ClassLoader access via reflection

**Affected:** Spring Framework before 5.2.20, 5.3.18 on JDK 9+
**CVE record:** https://nvd.nist.gov/vuln/detail/CVE-2022-22965
**Severity:** CVSS 9.8 (Critical)
**Scope of claim:** BY-CONSTRUCTION

## What was the bug

Spring Framework supports binding HTTP request parameters to Java POJO fields automatically. A request like `?user.name=Alice` maps to `bean.setUser().setName("Alice")` via Spring's property-path mechanism.

The bug: on JDK 9+, every Java object inherits `getClass()` which returns a `Class` object that has a `getClassLoader()` method. The Spring property-path mechanism would accept `class.classLoader.someProperty=...` and reach the ClassLoader instance via reflection, then walk further to mutable properties that ultimately controlled Tomcat's logging configuration. Attackers could write a JSP file containing a web shell.

This was the structural similarity to Spring2Shell (CVE-2010-1622): both bugs let unauthenticated requests reach reflection APIs that should have been gated.

## How attackers exploited it

A crafted POST request with parameters like:

```
class.module.classLoader.resources.context.parent.pipeline.first.pattern=...
class.module.classLoader.resources.context.parent.pipeline.first.suffix=.jsp
```

would reconfigure Tomcat's access-log valve to write a controllable filename with controllable content. Attackers wrote a web shell to a known path and then visited it to execute arbitrary commands.

Mass exploitation began within days of the March 31, 2022 disclosure.

## SIGIL's defense

The Spring4Shell bug fundamentally requires reflection: the attack reaches `ClassLoader` because Java's reflection API exposes it as a property of every object. SIGIL has no reflection whatsoever.

**Capabilities in SIGIL are TYPED values**, not properties reachable via name lookup. The only ways to obtain a capability of a given type are:

1. Receive it at spawn time as an init argument
2. Attenuate one you already hold via `.restrict` / `.split` / `.draw` / `.restrict_deadline`
3. Accept it as a message payload

There is no `find_cap_of_type::<ClassLoader>(target_object)` function — SIGIL has no syntax for "reach into another value and pull out a capability." The Spring4Shell attack pattern is structurally inexpressible.

This is a BY-CONSTRUCTION defense: the offending language feature simply doesn't exist. No vulnerable SIGIL fixture can be written.

## Vulnerable shape

Not expressible in SIGIL. See the SIGIL defense section above for why.

## Safe alternative

See [`04_cve_2022_22965_spring4shell_safe.sigil`](04_cve_2022_22965_spring4shell_safe.sigil). The ClassLoader capability is delegated explicitly via spawn argument; no reflection-style "discover and reach" pattern is possible.

## Defense layer

| Original language | Defense gap | SIGIL primitive | Diagnostic |
|---|---|---|---|
| Java/Spring | Reflection API exposed ClassLoader as property of every object | No reflection; capabilities only via typed parameter / message / attenuation | (none — by construction) |

## Citations

- https://nvd.nist.gov/vuln/detail/CVE-2022-22965
- https://spring.io/blog/2022/03/31/spring-framework-rce-early-announcement
- https://www.lunasec.io/docs/blog/spring-rce-vulnerabilities/
