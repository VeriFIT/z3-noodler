#!/usr/bin/env bash
# Runs every web/bugs/cases/*.smt2 with a native Z3-Noodler build and records, for the "Finding bugs"
# page (web/site/bugs/index.md), the answer, the model, the time, the query and its playground link
# in web/site/_data/bugs.json. web/smoke-test.mjs checks that the WebAssembly solver gives the same
# answers.
#
# Usage: web/bugs/run-cases.sh [path/to/z3]   (default: build/z3)
#        web/bugs/run-cases.sh --from-results results.json   (re-renders recorded outputs, no solver)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

python3 - "$ROOT" "${1:-$ROOT/../../build/z3}" "${2:-}" <<'EOF'
import base64, json, pathlib, re, subprocess, sys, time, zlib

root, z3, recorded = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
out_file = root.parent / "site" / "_data" / "bugs.json"
TIMEOUT_MS = 10000


def model_of(output):
    """The values of the declared string constants (drops the define-funs of the encoding)."""
    return [list(p) for p in re.findall(r'\(define-fun (\S+) \(\) String\s+("(?:[^"]|"")*")\)', output)]


def playground_fragment(query):
    """The playground's share-link fragment: deflate-raw + base64url of its state (models on)."""
    state = {"v": 1, "code": query, "m": 1, "s": 0, "t": 10, "x": ""}
    packer = zlib.compressobj(9, zlib.DEFLATED, -15)
    packed = packer.compress(json.dumps(state, separators=(",", ":")).encode()) + packer.flush()
    return "#z=" + base64.urlsafe_b64encode(packed).decode().rstrip("=")


if z3 == "--from-results":
    old = json.loads(pathlib.Path(recorded).read_text())
    solver, runs = old["solver"], {k: (v["output"], v["seconds"]) for k, v in old["cases"].items()}
else:
    solver = subprocess.run([z3, "--version"], capture_output=True, text=True).stdout.strip()
    runs = {}
    for path in sorted((root / "cases").glob("*.smt2")):
        start = time.perf_counter()
        proc = subprocess.run([z3, "model=true", f"timeout={TIMEOUT_MS}", str(path)],
                              capture_output=True, text=True)
        runs[path.stem] = ((proc.stdout + proc.stderr).strip(), round(time.perf_counter() - start, 3))

cases = {}
for name, (output, seconds) in sorted(runs.items()):
    query = (root / "cases" / f"{name}.smt2").read_text()
    answer = output.splitlines()[0] if output else "error"
    cases[name] = {"answer": answer, "seconds": seconds, "model": model_of(output),
                   "query": query, "playground": playground_fragment(query)}
    print(f"{name + '.smt2':32} {answer:8} {seconds:.2f}s")

version = re.search(r"Z3 version (\S+)", solver)
data = {
    "solver": solver,
    "version": version.group(1) if version else "unknown",
    "total": len(cases),
    "found": sum(c["answer"] == "sat" for c in cases.values()),
    "proved": sum(c["answer"] == "unsat" for c in cases.values()),
    "slowest": f'{max(c["seconds"] for c in cases.values()):.2f}',
    "cases": cases,
}
out_file.parent.mkdir(parents=True, exist_ok=True)
out_file.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
EOF
