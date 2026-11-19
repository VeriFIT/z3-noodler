---
title: Finding bugs
description: Real CVEs (Jinja2, CPython urllib and ipaddress) and classic bug patterns (path traversal, XSS, open redirect, SSRF, SQL injection) found or proved absent with the Z3-Noodler string solver.
---

# Finding bugs in string-handling code with an SMT solver

Sanitizers, URL checks and escaping functions are short, and they still have bugs. Each one rewrites a string and then checks it. We translate the code to string constraints and ask Z3-Noodler if an attacker's input exists. A **sat** answer comes with a concrete exploit. An **unsat** answer is a proof that no input works.
{: .lede}

{% include bug-stats.html %}

## How it works

1. **Model the code.** Every string operation has a counterpart in the SMT-LIB theory of strings: `replace` → `str.replace_all`, `startswith` → `str.prefixof`, a regex test → `str.in_re`. Z3-Noodler also accepts ECMAScript regexes as they are (`re.from_ecma2020`) and has `str.to_lower`.
2. **State the attack.** Add the attacker's goal: the cleaned path contains `../`, the browser sees `//host`, the SQL literal is not closed properly.
3. **Ask the solver.** *sat*: the model is an input that triggers the bug. *unsat*: no input does, for strings of any length.

The results below come from a native build of the solver. **Run in the playground** opens a query in the [playground](../playground/), which runs the solver locally via WebAssembly, so you can change the code and try your own fix.

**Real vulnerabilities**

- [Jinja2: HTML attribute injection through xmlattr](#jinja2-xmlattr) (CVE-2024-22195, CVE-2024-34064)
- [CPython: blocklist bypass in urllib.parse.urlsplit](#cpython-urlsplit) (CVE-2023-24329)
- [CPython: SSRF through octal octets in ipaddress](#cpython-ipaddress) (CVE-2021-29921)

**Classic bug patterns**

- [Path traversal through a one-pass filter](#path-traversal) (CWE-22)
- [Cross-site scripting through tag stripping](#xss) (CWE-79)
- [Open redirect after login](#open-redirect) (CWE-601)
- [Server-side request forgery through an unescaped dot](#url-allowlist) (CWE-918)
- [SQL injection through hand-made escaping](#sql) (CWE-89)

## Part 1: Real vulnerabilities {#real}

Three CVEs in widely used Python code, with the code taken from the released versions. In each, the vulnerable version misses a case. Z3-Noodler finds the missed input from a short query within seconds, and proves the final fix.

### Jinja2: HTML attribute injection through xmlattr {#jinja2-xmlattr}

CVE-2024-22195 · CVE-2024-34064
{: .tag}

Jinja2's `xmlattr` filter turns a dictionary into HTML attributes: `{% raw %}<div{{ {key: value}|xmlattr }}>{% endraw %}`. Values are HTML-escaped, but if an application passes a user-chosen *key*, the key itself can close the attribute name and start a new one, such as an event handler. This was reported as [CVE-2024-22195](https://github.com/pallets/jinja/security/advisories/GHSA-h5c8-rqwp-cp95). The fix in 3.1.3 turned out to be incomplete: [CVE-2024-34064](https://github.com/pallets/jinja/security/advisories/GHSA-h75v-3vvj-5mfj). The encoding below follows the real code: `markupsafe.escape` as five chained `replace_all`s and the validation regexes copied from each release.

#### 1. Jinja2 3.1.2: no check on keys

python · jinja2/filters.py
{: .code-label}

```python
rv = " ".join(
    f'{escape(key)}="{escape(value)}"'
    for key, value in d.items()
    if value is not None and not isinstance(value, Undefined)
)
```

{% include bug-result.html case="jinja-3.1.2" show="key" %}

A tab or a space in the key starts a new attribute: Jinja2 3.1.2 renders `<div`, a tab, and `onmouseover="…">`. We ran the key the solver found through the real Jinja2 3.1.2 release, and it produced the injected attribute.

#### 2. Jinja2 3.1.3: reject white space

python · jinja2/filters.py
{: .code-label}

```python
_space_re = re.compile(r"\s", flags=re.ASCII)
...
if _space_re.search(key) is not None:
    raise ValueError(f"Spaces are not allowed in attributes: '{key}'")
```

{% include bug-result.html case="jinja-3.1.3" show="key" %}

White space is not the only character that ends an attribute name in HTML. The solver goes around the check with `/onmouseover`, and Jinja2 3.1.3 really renders `<div /onmouseover="…">`, which a browser parses as an `onmouseover` attribute. This is the bypass that became CVE-2024-34064.

#### 3. Jinja2 3.1.4: reject every attribute-name terminator

python · jinja2/filters.py
{: .code-label}

```python
_attr_key_re = re.compile(r"[\s/>=]", flags=re.ASCII)
...
if _attr_key_re.search(key) is not None:
    raise ValueError(f"Invalid character in attribute name: {key!r}")
```

{% include bug-result.html case="jinja-3.1.4" %}

Unsat: the current check, together with the escaping, blocks every key that would inject an attribute. Before release, a query like this one would have found the gap in the first fix.

### CPython: blocklist bypass in urllib.parse.urlsplit {#cpython-urlsplit}

CVE-2023-24329
{: .tag}

Applications often reject dangerous links by checking `urlsplit(url).scheme`. Browsers follow the [WHATWG URL standard](https://url.spec.whatwg.org/), which first strips leading control characters and spaces, but `urlsplit` before Python 3.11.4 did not. So Python and the browser could read a different scheme from the same URL ([CVE-2023-24329](https://nvd.nist.gov/vuln/detail/CVE-2023-24329), [gh-102153](https://github.com/python/cpython/issues/102153)). The encoding models `urlsplit`'s scheme parsing from the CPython sources and the browser's parsing from the standard, and asks if they can disagree on `javascript:`.

#### 1. CPython 3.11.2

python · Lib/urllib/parse.py
{: .code-label}

```python
for b in _UNSAFE_URL_BYTES_TO_REMOVE:     # "\t", "\r", "\n"
    url = url.replace(b, "")
i = url.find(':')
if i > 0 and url[0].isascii() and url[0].isalpha():
    for c in url[:i]:
        if c not in scheme_chars:
            break
    else:
        scheme, url = url[:i].lower(), url[i+1:]
```

{% include bug-result.html case="cpython-3.11.2" show="url" %}

A single NUL byte in front of the URL is enough. `urlsplit` sees no scheme, so the blocklist passes the URL, and the browser strips the NUL and runs `javascript:`. Upper case is no obstacle either: the solver mixes it in because both sides compare case-insensitively.

#### 2. CPython 3.11.4: strip like the browser

python · Lib/urllib/parse.py
{: .code-label}

```python
# Only lstrip url as some applications rely on preserving trailing space.
url = url.lstrip(_WHATWG_C0_CONTROL_OR_SPACE)
scheme = scheme.strip(_WHATWG_C0_CONTROL_OR_SPACE)
for b in _UNSAFE_URL_BYTES_TO_REMOVE:
    ...
```

{% include bug-result.html case="cpython-3.11.4" %}

Unsat: after the fix, Python and the browser agree on the scheme for every string. The proof covers the interplay of `lstrip`, tab and newline removal, `find`, slicing and lower-casing.

### CPython: SSRF through octal octets in ipaddress {#cpython-ipaddress}

CVE-2021-29921
{: .tag}

An SSRF guard checks `ipaddress.ip_address(host).is_private` before the server connects to a host. Python reads every octet as decimal, but the C library that opens the connection (`inet_aton`, behind `getaddrinfo`) reads an octet with a leading `0` as *octal*, so `010` is 10 for Python and 8 for C ([CVE-2021-29921](https://nvd.nist.gov/vuln/detail/CVE-2021-29921), [bpo-36384](https://github.com/python/cpython/issues/80565)). Both readings are written with Z3-Noodler's `str.to_int`, with the octal value computed from the individual digits.

#### 1. CPython 3.9.4

python · Lib/ipaddress.py
{: .code-label}

```python
if not (octet_str.isascii() and octet_str.isdigit()):
    raise ValueError(msg % octet_str)
if len(octet_str) > 3:
    raise ValueError(msg % octet_str)
octet_int = int(octet_str, 10)
if octet_int > 255:
    raise ValueError("Octet %d (> 255) not permitted" % octet_int)
```

{% include bug-result.html case="ipaddress-3.9.4" show="host" %}

Python 3.9.4 sees the public address 12.0.70.100, but the C library connects to 10.0.56.100 in a private network. We checked the C side with `socket.inet_aton`, which returns exactly that. Python's three-character limit rules out the well-known `0177.0.0.1`, but the solver needs no such trick: it finds the private range that the limit still allows.

#### 2. CPython 3.9.5: reject leading zeros

python · Lib/ipaddress.py
{: .code-label}

```python
# Handle leading zeros as strict as glibc's inet_pton()
# See security bug bpo-36384
if octet_str != '0' and octet_str[0] == '0':
    raise ValueError("Leading zeros are not permitted in %r" % octet_str)
```

{% include bug-result.html case="ipaddress-3.9.5" %}

Unsat: Python and the C library now agree on every address that Python accepts. The proof combines regular constraints, string positions and string-to-integer conversion.

## Part 2: Classic bug patterns {#patterns}

Five bug patterns that keep coming back in security advisories, each shown with the typical code, a typical incomplete fix and a sound one.

### Path traversal through a one-pass filter {#path-traversal}

CWE-22
{: .tag}

A file-download endpoint deletes `../` from the requested name so that it cannot leave the upload directory. Filters like this appear in real path traversal advisories again and again. Deleting a pattern can create a new copy of it from the characters on both sides.

#### 1. The original filter

python
{: .code-label}

```python
def safe_open(name):
    name = name.replace("../", "")
    return open(os.path.join(UPLOAD_DIR, name))
```

{% include bug-result.html case="path-traversal" %}

The solver answers with `....//.`: removing the `../` in the middle glues the outer `..` and `/` into a new `../`.

#### 2. The quick fix: filter twice

python
{: .code-label}

```python
name = name.replace("../", "").replace("../", "")
```

{% include bug-result.html case="path-traversal-twice" %}

Nesting one level deeper defeats it: `......///.`. No fixed number of passes is enough, and the solver finds the counterexample for each one.

#### 3. A sound filter

python
{: .code-label}

```python
name = name.replace("..", "")
```

{% include bug-result.html case="path-traversal-fixed" %}

Deleting every `..` turns a run of *n* dots into *n* mod 2 dots, so no `..` survives. Z3-Noodler proves this for *all* inputs, not just the ones a test suite happens to try.

### Cross-site scripting through tag stripping {#xss}

CWE-79
{: .tag}

A comment form deletes `<script>` tags before it shows comments to other users. The browser reads tag names case-insensitively, so the encoding checks the *lower-cased* output with Z3-Noodler's `str.to_lower`.

#### 1. The original sanitizer

javascript
{: .code-label}

```javascript
function sanitize(comment) {
  return comment.replaceAll("<script>", "");
}
```

{% include bug-result.html case="xss-strip" %}

The attack combines two bugs: the filter is case-sensitive and does only one pass. Deleting both `<script>` tags leaves `<SCRIPT><`.

#### 2. The quick fix: lower-case first

javascript
{: .code-label}

```javascript
function sanitize(comment) {
  return comment.toLowerCase().replaceAll("<script>", "");
}
```

{% include bug-result.html case="xss-strip-nested" %}

This closes the case hole but not the nesting one. The solver now needs the lower-casing and the replacement together, and still finds an attack.

#### 3. The fix: escape, do not delete

javascript
{: .code-label}

```javascript
function sanitize(comment) {
  return comment.replaceAll("<", "&lt;");
}
```

{% include bug-result.html case="xss-escape" %}

With `<` escaped, the output cannot open any tag: unsat.

### Open redirect after login {#open-redirect}

CWE-601
{: .tag}

After login, the app redirects to `?next=<url>`. To keep users on the site, it accepts local paths but rejects protocol-relative URLs (`//evil.example`). The encoding models how a browser parses the URL under the [WHATWG URL standard](https://url.spec.whatwg.org/): it removes tabs and newlines and treats `\` like `/`.

#### 1. The original check

python
{: .code-label}

```python
def is_safe_redirect(url):
    return url.startswith("/") and not url.startswith("//")
```

{% include bug-result.html case="open-redirect" %}

`/\t/` (slash, tab, slash) passes the check. The browser deletes the tab and goes to another host.

#### 2. The quick fix: normalize backslashes

python
{: .code-label}

```python
def is_safe_redirect(url):
    u = url.replace("\\", "/")
    return u.startswith("/") and not u.startswith("//")
```

{% include bug-result.html case="open-redirect-backslash" %}

The patch fixes the backslash bypass from a bug report but not the tab bypass, and the solver finds it right away. A deny-list has to model the parser exactly, so it is easy to get wrong.

#### 3. The fix: an allow-list

python
{: .code-label}

```python
SAFE = re.compile(r"/(?:[A-Za-z0-9._~-][A-Za-z0-9._~/-]*)?(?:\?[A-Za-z0-9=&._~-]*)?")

def is_safe_redirect(url):
    return SAFE.fullmatch(url) is not None
```

{% include bug-result.html case="open-redirect-fixed" %}

The regular expression is pasted into the query as is, through Z3-Noodler's `re.from_ecma2020`. Unsat: none of the accepted URLs leaves the site, with any combination of the browser's rewrites.

### Server-side request forgery through an unescaped dot {#url-allowlist}

CWE-918
{: .tag}

A webhook may only call the company's own API servers, and a regular expression checks the URL before the server fetches it. The encoding states the attacker's goal: a URL that passes the check, whose host is *not* a subdomain of `example.com`, and that ends in `.com`, so anyone can register it.

#### 1. The original check

javascript
{: .code-label}

```javascript
const ALLOWED = /^https:\/\/(www|api).example.com\//;
if (!ALLOWED.test(url)) throw new Error("forbidden host");
await fetch(url);
```

{% include bug-result.html case="url-allowlist" %}

In a regular expression, `.` matches any character, so the attacker can register `api-example.com` and the check lets it through.

#### 2. The fix: escape the dots

javascript
{: .code-label}

```javascript
const ALLOWED = /^https:\/\/(www|api)\.example\.com\//;
```

{% include bug-result.html case="url-allowlist-fixed" %}

Unsat: every URL that passes the check goes to `example.com`.

### SQL injection through hand-made escaping {#sql}

CWE-89
{: .tag}

A query is built by escaping quotes in user input. The encoding asks if the escaped text can fail to be a well-formed body of a MySQL-style string literal, `([^'\\]|\\.)*`. If it does, a quote closes the literal early and the rest of the input runs as SQL.

#### 1. The original escaping

php
{: .code-label}

```php
$sql = "SELECT * FROM users WHERE name = '"
     . str_replace("'", "\\'", $name) . "'";
```

{% include bug-result.html case="sql-escape" %}

The classic: the input `\'` becomes `\\'`, an escaped backslash followed by a bare quote. We also required the payload to end with ` OR 1=1 -- `, and the solver built a complete exploit around it.

#### 2. The fix: escape the escape character first

php
{: .code-label}

```php
$esc = str_replace("'", "\\'", str_replace("\\", "\\\\", $name));
```

{% include bug-result.html case="sql-escape-fixed" %}

Unsat: two chained `replace_all`s, which Z3-Noodler handles as a composition of transducers, never produce a broken literal. (Prepared statements are still the better fix.)

#### 3. Then someone truncates the value

php
{: .code-label}

```php
$esc = str_replace("'", "\\'", str_replace("\\", "\\\\", $name));
$esc = substr($esc, 0, 16);   // fit the column
```

{% include bug-result.html case="sql-truncate" %}

Cutting the value after escaping can split an escape sequence in two. The solver finds an input of only letters and quotes whose escaped form is cut right after a backslash, and that backslash escapes the closing quote. This needs string lengths, positions and the transducers together.

## Why a string solver?

Fuzzers and test suites try inputs one at a time, but the inputs above are rare, such as `....//.` or a tab between two slashes. A solver reasons about all strings at once. Its exploits are short and easy to read, and its unsat answers are proofs for every input. Z3-Noodler represents the possible values of each string variable by an automaton. This is why `replace_all`, regex membership, case conversion and lengths can all appear in the same query. The same technique is used in symbolic execution, in analysis of cloud access policies and in test generation.

Want to try it on your own code? [Download a release](https://github.com/VeriFIT/z3-noodler/releases/latest), open the [playground](../playground/) or read the [documentation](../usage.md). All queries are in [web/bugs/cases](https://github.com/VeriFIT/z3-noodler/tree/devel/web/bugs/cases).

Results from Z3-Noodler {{ site.data.bugs.version }} (native build, `model=true`).
{: .note}
