#!/usr/bin/env python3
"""Builds the "Finding bugs" page of the web site from template.html, style.css, the stories below,
cases/*.smt2 and cases/results.json (the answers recorded by run-cases.sh).

Usage: python3 web/bugs/build.py [OUT_DIR]     (default: web/site/bugs)
"""
import base64
import html
import json
import pathlib
import re
import shutil
import sys
import zlib

ROOT = pathlib.Path(__file__).resolve().parent
# The page is served at <site>/bugs/, next to the playground.
PLAYGROUND = "../playground/"

# Each story is a bug class; each step is a version of the code checked by the solver.
STORIES = [
    {
        "id": "jinja2-xmlattr",
        "group": "real",
        "title": "Jinja2: HTML attribute injection through xmlattr",
        "tag": "CVE-2024-22195 · CVE-2024-34064",
        "intro": """Jinja2's <code>xmlattr</code> filter turns a dictionary into HTML attributes:
<code>&lt;div{{ {key: value}|xmlattr }}&gt;</code>. Values are HTML-escaped, but if an application
passes a user-chosen <em>key</em>, the key itself can close the attribute name and start a new one,
such as an event handler. This was reported as
<a href="https://github.com/pallets/jinja/security/advisories/GHSA-h5c8-rqwp-cp95">CVE-2024-22195</a>.
The fix in 3.1.3 turned out to be incomplete:
<a href="https://github.com/pallets/jinja/security/advisories/GHSA-h75v-3vvj-5mfj">CVE-2024-34064</a>.
The encoding below follows the real code: <code>markupsafe.escape</code> as five chained
<code>replace_all</code>s and the validation regexes copied from each release.""",
        "steps": [
            {
                "case": "jinja-3.1.2",
                "label": "Jinja2 3.1.2: no check on keys",
                "lang": "python · jinja2/filters.py",
                "code": 'rv = " ".join(\n    f\'{escape(key)}="{escape(value)}"\'\n    for key, value in d.items()\n    if value is not None and not isinstance(value, Undefined)\n)',
                "show": ["key"],
                "after": """A tab or a space in the key starts a new attribute: Jinja2 3.1.2 renders
<code>&lt;div</code>, a tab, and <code>onmouseover="…"&gt;</code>. We ran the key the solver found through the real Jinja2
3.1.2 release, and it produced the injected attribute.""",
            },
            {
                "case": "jinja-3.1.3",
                "label": "Jinja2 3.1.3: reject white space",
                "lang": "python · jinja2/filters.py",
                "code": '_space_re = re.compile(r"\\s", flags=re.ASCII)\n...\nif _space_re.search(key) is not None:\n    raise ValueError(f"Spaces are not allowed in attributes: \'{key}\'")',
                "show": ["key"],
                "after": """White space is not the only character that ends an attribute name in HTML.
The solver goes around the check with <code>/onmouseover</code>, and Jinja2 3.1.3 really renders
<code>&lt;div /onmouseover="…"&gt;</code>, which a browser parses as an <code>onmouseover</code>
attribute. This is the bypass that became CVE-2024-34064.""",
            },
            {
                "case": "jinja-3.1.4",
                "label": "Jinja2 3.1.4: reject every attribute-name terminator",
                "lang": "python · jinja2/filters.py",
                "code": '_attr_key_re = re.compile(r"[\\s/>=]", flags=re.ASCII)\n...\nif _attr_key_re.search(key) is not None:\n    raise ValueError(f"Invalid character in attribute name: {key!r}")',
                "after": """Unsat: the current check, together with the escaping, blocks every
key that would inject an attribute. Before release, a query like this one would have found the gap
in the first fix.""",
            },
        ],
    },
    {
        "id": "cpython-urlsplit",
        "group": "real",
        "title": "CPython: blocklist bypass in urllib.parse.urlsplit",
        "tag": "CVE-2023-24329",
        "intro": """Applications often reject dangerous links by checking
<code>urlsplit(url).scheme</code>. Browsers follow the
<a href="https://url.spec.whatwg.org/">WHATWG URL standard</a>, which first strips leading control
characters and spaces, but <code>urlsplit</code> before Python 3.11.4 did not. So Python and the
browser could read a different scheme from the same URL
(<a href="https://nvd.nist.gov/vuln/detail/CVE-2023-24329">CVE-2023-24329</a>,
<a href="https://github.com/python/cpython/issues/102153">gh-102153</a>). The encoding models
<code>urlsplit</code>'s scheme parsing from the CPython sources and the browser's parsing from the
standard, and asks if they can disagree on <code>javascript:</code>.""",
        "steps": [
            {
                "case": "cpython-3.11.2",
                "label": "CPython 3.11.2",
                "lang": "python · Lib/urllib/parse.py",
                "code": 'for b in _UNSAFE_URL_BYTES_TO_REMOVE:     # "\\t", "\\r", "\\n"\n    url = url.replace(b, "")\ni = url.find(\':\')\nif i > 0 and url[0].isascii() and url[0].isalpha():\n    for c in url[:i]:\n        if c not in scheme_chars:\n            break\n    else:\n        scheme, url = url[:i].lower(), url[i+1:]',
                "show": ["url"],
                "after": """A single NUL byte in front of the URL is enough. <code>urlsplit</code>
sees no scheme, so the blocklist passes the URL, and the browser strips the NUL and runs
<code>javascript:</code>. Upper case is no obstacle either: the solver mixes it in because both
sides compare case-insensitively.""",
            },
            {
                "case": "cpython-3.11.4",
                "label": "CPython 3.11.4: strip like the browser",
                "lang": "python · Lib/urllib/parse.py",
                "code": '# Only lstrip url as some applications rely on preserving trailing space.\nurl = url.lstrip(_WHATWG_C0_CONTROL_OR_SPACE)\nscheme = scheme.strip(_WHATWG_C0_CONTROL_OR_SPACE)\nfor b in _UNSAFE_URL_BYTES_TO_REMOVE:\n    ...',
                "after": """Unsat: after the fix, Python and the browser agree on the scheme for
every string. The proof covers the interplay of <code>lstrip</code>, tab and newline removal,
<code>find</code>, slicing and lower-casing.""",
            },
        ],
    },
    {
        "id": "cpython-ipaddress",
        "group": "real",
        "title": "CPython: SSRF through octal octets in ipaddress",
        "tag": "CVE-2021-29921",
        "intro": """An SSRF guard checks <code>ipaddress.ip_address(host).is_private</code> before the
server connects to a host. Python reads every octet as decimal, but the C library that opens the
connection (<code>inet_aton</code>, behind <code>getaddrinfo</code>) reads an octet with a leading
<code>0</code> as <em>octal</em>, so <code>010</code> is 10 for Python and 8 for C
(<a href="https://nvd.nist.gov/vuln/detail/CVE-2021-29921">CVE-2021-29921</a>,
<a href="https://github.com/python/cpython/issues/80565">bpo-36384</a>). Both readings are written
with Z3-Noodler's <code>str.to_int</code>, with the octal value computed from the individual digits.""",
        "steps": [
            {
                "case": "ipaddress-3.9.4",
                "label": "CPython 3.9.4",
                "lang": "python · Lib/ipaddress.py",
                "code": 'if not (octet_str.isascii() and octet_str.isdigit()):\n    raise ValueError(msg % octet_str)\nif len(octet_str) > 3:\n    raise ValueError(msg % octet_str)\noctet_int = int(octet_str, 10)\nif octet_int > 255:\n    raise ValueError("Octet %d (> 255) not permitted" % octet_int)',
                "show": ["host"],
                "after": """Python 3.9.4 sees the public address 12.0.70.100, but the C library connects to
10.0.56.100 in a private network. We checked the C side with <code>socket.inet_aton</code>, which
returns exactly that. Python's three-character limit rules out the well-known <code>0177.0.0.1</code>,
but the solver needs no such trick: it finds the private range that the limit still allows.""",
            },
            {
                "case": "ipaddress-3.9.5",
                "label": "CPython 3.9.5: reject leading zeros",
                "lang": "python · Lib/ipaddress.py",
                "code": "# Handle leading zeros as strict as glibc's inet_pton()\n# See security bug bpo-36384\nif octet_str != '0' and octet_str[0] == '0':\n    raise ValueError(\"Leading zeros are not permitted in %r\" % octet_str)",
                "after": """Unsat: Python and the C library now agree on every address that Python
accepts. The proof combines regular constraints, string positions and string-to-integer conversion.""",
            },
        ],
    },
    {
        "id": "path-traversal",
        "group": "pattern",
        "title": "Path traversal through a one-pass filter",
        "tag": "CWE-22",
        "intro": """A file-download endpoint deletes <code>../</code> from the requested name so that it
cannot leave the upload directory. Filters like this appear in real path traversal advisories again and
again. Deleting a pattern can create a new copy of it from the characters on both sides.""",
        "steps": [
            {
                "case": "path-traversal",
                "label": "The original filter",
                "lang": "python",
                "code": 'def safe_open(name):\n    name = name.replace("../", "")\n    return open(os.path.join(UPLOAD_DIR, name))',
                "after": """The solver answers with <code>....//.</code>: removing the <code>../</code> in the
middle glues the outer <code>..</code> and <code>/</code> into a new <code>../</code>.""",
            },
            {
                "case": "path-traversal-twice",
                "label": "The quick fix: filter twice",
                "lang": "python",
                "code": 'name = name.replace("../", "").replace("../", "")',
                "after": """Nesting one level deeper defeats it: <code>......///.</code>. No fixed number of
passes is enough, and the solver finds the counterexample for each one.""",
            },
            {
                "case": "path-traversal-fixed",
                "label": "A sound filter",
                "lang": "python",
                "code": 'name = name.replace("..", "")',
                "after": """Deleting every <code>..</code> turns a run of <i>n</i> dots into <i>n</i> mod 2
dots, so no <code>..</code> survives. Z3-Noodler proves this for <em>all</em> inputs, not just
the ones a test suite happens to try.""",
            },
        ],
    },
    {
        "id": "xss",
        "group": "pattern",
        "title": "Cross-site scripting through tag stripping",
        "tag": "CWE-79",
        "intro": """A comment form deletes <code>&lt;script&gt;</code> tags before it shows comments to
other users. The browser reads tag names case-insensitively, so the encoding checks the
<em>lower-cased</em> output with Z3-Noodler's <code>str.to_lower</code>.""",
        "steps": [
            {
                "case": "xss-strip",
                "label": "The original sanitizer",
                "lang": "javascript",
                "code": 'function sanitize(comment) {\n  return comment.replaceAll("<script>", "");\n}',
                "after": """The attack combines two bugs: the filter is case-sensitive and does only one pass.
Deleting both <code>&lt;script&gt;</code> tags leaves <code>&lt;SCRIPT&gt;&lt;</code>.""",
            },
            {
                "case": "xss-strip-nested",
                "label": "The quick fix: lower-case first",
                "lang": "javascript",
                "code": 'function sanitize(comment) {\n  return comment.toLowerCase().replaceAll("<script>", "");\n}',
                "after": """This closes the case hole but not the nesting one. The solver now needs the
lower-casing and the replacement together, and still finds an attack.""",
            },
            {
                "case": "xss-escape",
                "label": "The fix: escape, do not delete",
                "lang": "javascript",
                "code": 'function sanitize(comment) {\n  return comment.replaceAll("<", "&lt;");\n}',
                "after": """With <code>&lt;</code> escaped, the output cannot open any tag: unsat.""",
            },
        ],
    },
    {
        "id": "open-redirect",
        "group": "pattern",
        "title": "Open redirect after login",
        "tag": "CWE-601",
        "intro": """After login, the app redirects to <code>?next=&lt;url&gt;</code>. To keep users on the
site, it accepts local paths but rejects protocol-relative URLs (<code>//evil.example</code>). The encoding
models how a browser parses the URL under the <a href="https://url.spec.whatwg.org/">WHATWG URL
standard</a>: it removes tabs and newlines and treats <code>\\</code> like <code>/</code>.""",
        "steps": [
            {
                "case": "open-redirect",
                "label": "The original check",
                "lang": "python",
                "code": 'def is_safe_redirect(url):\n    return url.startswith("/") and not url.startswith("//")',
                "after": """<code>/\\t/</code> (slash, tab, slash) passes the check. The browser deletes
the tab and goes to another host.""",
            },
            {
                "case": "open-redirect-backslash",
                "label": "The quick fix: normalize backslashes",
                "lang": "python",
                "code": 'def is_safe_redirect(url):\n    u = url.replace("\\\\", "/")\n    return u.startswith("/") and not u.startswith("//")',
                "after": """The patch fixes the backslash bypass from a bug report but not the tab
bypass, and the solver finds it right away. A deny-list has to model the parser exactly, so it
is easy to get wrong.""",
            },
            {
                "case": "open-redirect-fixed",
                "label": "The fix: an allow-list",
                "lang": "python",
                "code": 'SAFE = re.compile(r"/(?:[A-Za-z0-9._~-][A-Za-z0-9._~/-]*)?(?:\\?[A-Za-z0-9=&._~-]*)?")\n\ndef is_safe_redirect(url):\n    return SAFE.fullmatch(url) is not None',
                "after": """The regular expression is pasted into the query as is, through Z3-Noodler's
<code>re.from_ecma2020</code>. Unsat: none of the accepted URLs leaves the site, with any
combination of the browser's rewrites.""",
            },
        ],
    },
    {
        "id": "url-allowlist",
        "group": "pattern",
        "title": "Server-side request forgery through an unescaped dot",
        "tag": "CWE-918",
        "intro": """A webhook may only call the company's own API servers, and a regular expression
checks the URL before the server fetches it. The encoding states the attacker's goal: a URL that
passes the check, whose host is <em>not</em> a subdomain of <code>example.com</code>, and that
ends in <code>.com</code>, so anyone can register it.""",
        "steps": [
            {
                "case": "url-allowlist",
                "label": "The original check",
                "lang": "javascript",
                "code": 'const ALLOWED = /^https:\\/\\/(www|api).example.com\\//;\nif (!ALLOWED.test(url)) throw new Error("forbidden host");\nawait fetch(url);',
                "after": """In a regular expression, <code>.</code> matches any character, so the attacker
can register <code>api-example.com</code> and the check lets it through.""",
            },
            {
                "case": "url-allowlist-fixed",
                "label": "The fix: escape the dots",
                "lang": "javascript",
                "code": 'const ALLOWED = /^https:\\/\\/(www|api)\\.example\\.com\\//;',
                "after": """Unsat: every URL that passes the check goes to <code>example.com</code>.""",
            },
        ],
    },
    {
        "id": "sql",
        "group": "pattern",
        "title": "SQL injection through hand-made escaping",
        "tag": "CWE-89",
        "intro": """A query is built by escaping quotes in user input. The encoding asks if the escaped
text can fail to be a well-formed body of a MySQL-style string literal,
<code>([^'\\\\]|\\\\.)*</code>. If it does, a quote closes the literal early and the rest of the
input runs as SQL.""",
        "steps": [
            {
                "case": "sql-escape",
                "label": "The original escaping",
                "lang": "php",
                "code": "$sql = \"SELECT * FROM users WHERE name = '\"\n     . str_replace(\"'\", \"\\\\'\", $name) . \"'\";",
                "after": """The classic: the input <code>\\'</code> becomes <code>\\\\'</code>, an escaped
backslash followed by a bare quote. We also required the payload to end with
<code> OR 1=1 -- </code>, and the solver built a complete exploit around it.""",
            },
            {
                "case": "sql-escape-fixed",
                "label": "The fix: escape the escape character first",
                "lang": "php",
                "code": "$esc = str_replace(\"'\", \"\\\\'\", str_replace(\"\\\\\", \"\\\\\\\\\", $name));",
                "after": """Unsat: two chained <code>replace_all</code>s, which Z3-Noodler handles
as a composition of transducers, never produce a broken literal. (Prepared statements are still
the better fix.)""",
            },
            {
                "case": "sql-truncate",
                "label": "Then someone truncates the value",
                "lang": "php",
                "code": "$esc = str_replace(\"'\", \"\\\\'\", str_replace(\"\\\\\", \"\\\\\\\\\", $name));\n$esc = substr($esc, 0, 16);   // fit the column",
                "after": """Cutting the value after escaping can split an escape sequence in two.
The solver finds an input of only letters and quotes whose escaped form is cut right after a
backslash, and that backslash escapes the closing quote. This needs string lengths, positions and
the transducers together.""",
            },
        ],
    },
]

SMT_KEYWORDS = {"set-logic", "declare-const", "declare-fun", "define-fun", "assert", "check-sat",
                "get-model", "set-option"}
SMT_TOKEN = re.compile(r"""(?P<comment>;[^\n]*)|(?P<string>"(?:[^"]|"")*")|(?P<squote>'[^'\n]*')|(?P<word>[A-Za-z_][\w.\-+*/<>=!?]*)""")


def highlight_smt(code):
    out, pos = [], 0
    for m in SMT_TOKEN.finditer(code):
        out.append(html.escape(code[pos:m.start()]))
        text = html.escape(m.group())
        kind = m.lastgroup
        if kind == "comment":
            out.append(f'<span class="c">{text}</span>')
        elif kind in ("string", "squote"):
            out.append(f'<span class="s">{text}</span>')
        elif m.group() in SMT_KEYWORDS:
            out.append(f'<span class="k">{text}</span>')
        elif m.group().startswith(("str.", "re.", "rat.")):
            out.append(f'<span class="f">{text}</span>')
        else:
            out.append(text)
        pos = m.end()
    out.append(html.escape(code[pos:]))
    return "".join(out)


SRC_TOKEN = re.compile(r"""(?P<comment>(?://|#)[^\n]*)|(?P<string>r?"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')""")


def highlight_source(code):
    out, pos = [], 0
    for m in SRC_TOKEN.finditer(code):
        out.append(html.escape(code[pos:m.start()]))
        cls = "c" if m.lastgroup == "comment" else "s"
        out.append(f'<span class="{cls}">{html.escape(m.group())}</span>')
        pos = m.end()
    out.append(html.escape(code[pos:]))
    return "".join(out)


def model_of(output):
    """Keeps only the values of declared constants (drops the define-funs of the encoding)."""
    lines = output.splitlines()
    answer, rest = lines[0], "\n".join(lines[1:])
    pairs = re.findall(r'\(define-fun (\S+) \(\) String\s+("(?:[^"]|"")*")\)', rest)
    return answer, pairs


def playground_link(code):
    state = {"v": 1, "code": code, "m": 1, "s": 0, "t": 10, "x": ""}
    data = json.dumps(state, separators=(",", ":")).encode()
    packer = zlib.compressobj(9, zlib.DEFLATED, -15)
    packed = packer.compress(data) + packer.flush()
    return PLAYGROUND + "#z=" + base64.urlsafe_b64encode(packed).decode().rstrip("=")


def render_step(number, step, results):
    smt = (ROOT / "cases" / f"{step['case']}.smt2").read_text()
    result = results[step["case"]]
    answer, model = model_of(result["output"])
    if "show" in step:
        model = [(n, v) for n, v in model if n in step["show"]]
    if answer == "sat":
        badge = '<span class="verdict bug">sat · bug found</span>'
    elif answer == "unsat":
        badge = '<span class="verdict safe">unsat · proved safe</span>'
    else:
        badge = f'<span class="verdict unk">{html.escape(answer)}</span>'
    model_html = ""
    if model:
        rows = "".join(f'<div><span class="var">{html.escape(n)}</span> = '
                       f'<span class="s">{html.escape(v)}</span></div>' for n, v in model)
        model_html = f'<div class="model">{rows}</div>'
    return f"""
    <div class="step">
      <div class="step-head"><span class="num">{number}</span><h3>{html.escape(step['label'])}</h3></div>
      <div class="grid">
        <div class="pane">
          <div class="pane-label">{step['lang']}</div>
          <pre class="src"><code>{highlight_source(step['code'])}</code></pre>
        </div>
        <div class="pane result">
          <div class="pane-label">Z3-Noodler · {result['seconds']:.2f} s</div>
          <div class="result-body">{badge}{model_html}</div>
        </div>
      </div>
      <p class="after">{step['after']}</p>
      <details>
        <summary>SMT-LIB encoding <span class="file">cases/{step['case']}.smt2</span></summary>
        <pre class="smt"><code>{highlight_smt(smt)}</code></pre>
      </details>
      <a class="run" href="{html.escape(playground_link(smt))}" target="_blank" rel="noopener">Run in the playground ↗</a>
    </div>"""


def main():
    results_file = json.loads((ROOT / "cases" / "results.json").read_text())
    results = results_file["cases"]
    toc, body = {"real": [], "pattern": []}, {"real": [], "pattern": []}
    for story in STORIES:
        group = story["group"]
        toc[group].append(f'<li><a href="#{story["id"]}">{html.escape(story["title"])}</a> <span class="cwe">{story["tag"]}</span></li>')
        steps = "".join(render_step(i + 1, s, results) for i, s in enumerate(story["steps"]))
        body[group].append(f"""
  <section class="story" id="{story['id']}">
    <div class="story-head">
      <span class="cwe">{story['tag']}</span>
      <h2><a href="#{story['id']}">{html.escape(story['title'])}</a></h2>
    </div>
    <p class="intro">{story['intro']}</p>
    {steps}
  </section>""")
    total = len(results)
    found = sum(1 for r in results.values() if r["answer"] == "sat")
    proved = sum(1 for r in results.values() if r["answer"] == "unsat")
    slowest = max(r["seconds"] for r in results.values())
    version = re.search(r"Z3 version (\S+)", results_file["solver"])
    page = (ROOT / "template.html").read_text()
    for key, value in {
        "TOC_REAL": "\n".join(toc["real"]),
        "TOC_PATTERN": "\n".join(toc["pattern"]),
        "REAL": "\n".join(body["real"]),
        "PATTERNS": "\n".join(body["pattern"]),
        "TOTAL": str(total),
        "FOUND": str(found),
        "PROVED": str(proved),
        "SLOWEST": f"{slowest:.2f}",
        "VERSION": version.group(1) if version else "unknown",
    }.items():
        page = page.replace("{{" + key + "}}", value)
    out_dir = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ROOT.parent / "site" / "bugs")
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "index.html").write_text(page)
    shutil.copy(ROOT / "style.css", out_dir / "style.css")
    print(f"{out_dir}: {len(STORIES)} stories, {total} queries")


if __name__ == "__main__":
    main()
