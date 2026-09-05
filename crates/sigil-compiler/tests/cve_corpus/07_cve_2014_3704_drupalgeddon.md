# CVE-2014-3704: Drupalgeddon — Drupal SQL injection via array-placeholder expansion

**Affected:** Drupal 7.x before 7.32
**CVE record:** https://nvd.nist.gov/vuln/detail/CVE-2014-3704
**Severity:** CVSS 9.8 (Critical)
**Scope of claim:** BY-CONSTRUCTION

## What was the bug

Drupal 7 used a parameterized query API that accepted PHP arrays as placeholder values. The intent was that `$query->condition('name', $array, 'IN')` would expand into `name IN (?, ?, ?)` with each array element bound separately.

The bug was in the placeholder NAMING logic. Drupal generated placeholder names from the array's KEYS. For a regular indexed array `[0 => 'Alice', 1 => 'Bob']` this produced `:db_placeholder_0` and `:db_placeholder_1`. But for an associative array with attacker-controlled keys — say `["foo; DROP TABLE users; --" => "Alice"]` — Drupal interpolated the key string directly into the query template.

An unauthenticated attacker could submit such an array via the login form's `name` parameter and inject arbitrary SQL. This was 2014's "Drupalgeddon"; mass exploitation began within 7 hours of the public patch.

## How attackers exploited it

The canonical PoC, a single HTTP POST:

```
POST /?q=node&destination=node
Content-Type: application/x-www-form-urlencoded

name[0%20;UPDATE%20{users}%20SET%20pass%3D...]=Alice&pass=anything&form_id=user_login_block
```

The attacker controlled the URL-decoded key string `0 ;UPDATE {users} SET pass=...`, which Drupal pasted into the SQL query. The injection re-set the administrator password to a known value; attackers then logged in as admin.

## SIGIL's defense

The Drupalgeddon bug existed because PHP's array type carries arbitrary keyed structures, and Drupal's query builder mixed those keys directly into SQL templates. The fundamental shape — "untrusted input becomes a SQL fragment" — depends on a string-template substitution mechanism.

SIGIL has no string-to-SQL evaluator and no PHP-style array placeholder expansion. Database access in SIGIL would go through an actor with typed message handlers: each query is a SIGIL message with typed parameters, not a string template. The receiver of `Lookup(user_id: i64)` knows it has an `i64`, not a SQL fragment.

This is a BY-CONSTRUCTION defense: the offending mechanism doesn't exist. The SQL-injection class is structurally inexpressible in SIGIL.

## Vulnerable shape

Not expressible in SIGIL. See the SIGIL defense section above for why.

## Safe alternative

See [`07_cve_2014_3704_drupalgeddon_safe.sigil`](07_cve_2014_3704_drupalgeddon_safe.sigil). A typed actor message; the user_id flows as `i64`, never as a SQL fragment.

## Defense layer

| Original language | Defense gap | SIGIL primitive | Diagnostic |
|---|---|---|---|
| PHP/Drupal | String-template SQL builder accepting untrusted array keys | Typed actor messages; no string-to-SQL evaluator | (none — by construction) |

## Citations

- https://nvd.nist.gov/vuln/detail/CVE-2014-3704
- https://www.drupal.org/SA-CORE-2014-005
- https://www.sektioneins.de/en/advisories/advisory-012014-drupal-pre-auth-sql-injection-vulnerability.html
