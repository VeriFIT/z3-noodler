#!/usr/bin/env bash
# Runs every web/bugs/cases/*.smt2 with a native Z3-Noodler build and records the answer, the model
# and the time in web/bugs/cases/results.json (read by build.py, checked by web/smoke-test.mjs).
#
# Usage: web/bugs/run-cases.sh [path/to/z3]   (default: build/z3)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
Z3="${1:-$ROOT/../../build/z3}"
TIMEOUT_MS=10000

python3 - "$ROOT" "$Z3" "$TIMEOUT_MS" <<'EOF'
import json, pathlib, subprocess, sys, time

root, z3, timeout_ms = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
version = subprocess.run([z3, "--version"], capture_output=True, text=True).stdout.strip()
results = {"solver": version, "cases": {}}
for path in sorted((root / "cases").glob("*.smt2")):
    start = time.perf_counter()
    proc = subprocess.run([z3, "model=true", f"timeout={timeout_ms}", str(path)],
                          capture_output=True, text=True)
    seconds = time.perf_counter() - start
    output = (proc.stdout + proc.stderr).strip()
    answer = output.splitlines()[0] if output else "error"
    results["cases"][path.stem] = {"answer": answer, "output": output, "seconds": round(seconds, 3)}
    print(f"{path.name:32} {answer:8} {seconds:.2f}s")
(root / "cases" / "results.json").write_text(json.dumps(results, indent=2) + "\n")
EOF
