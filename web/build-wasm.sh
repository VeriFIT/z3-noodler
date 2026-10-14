#!/usr/bin/env bash
# Builds the Z3-Noodler command-line binary as a single-threaded WebAssembly module and copies it
# (noodler.js + noodler.wasm + version.json) into the web page directory.
#
# Usage: web/build-wasm.sh [OUT_DIR] [extra cmake args...]
#   OUT_DIR    where to put the built files (default: web/site)
#   BUILD_DIR  environment variable, CMake build directory (default: build-web)
#   JOBS       environment variable, number of parallel build jobs (default: nproc)
#
# Requires an activated Emscripten SDK (emcmake/emcc on PATH). Mata is fetched and compiled to
# WebAssembly by the CMake build; pass -DFETCHCONTENT_SOURCE_DIR_MATA=<path> to reuse a local
# checkout of the right Mata version instead.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="$(realpath -m "${1:-$ROOT/web/site}")"
[[ $# -gt 0 ]] && shift
BUILD_DIR="$(realpath -m "${BUILD_DIR:-$ROOT/build-web}")"
JOBS="${JOBS:-$(nproc)}"

# Native wasm exceptions must be used consistently by Z3 and Mata (and match the link flags that
# Z3's CMakeLists adds for Emscripten).
COMMON_FLAGS="-fwasm-exceptions -sSUPPORT_LONGJMP=wasm"
# The page runs the solver in a Web Worker: a fresh instance per run (INVOKE_RUN=0 + callMain),
# input passed through the in-memory file system, no threads (no SharedArrayBuffer needed).
LINK_FLAGS="-sMODULARIZE=1 -sEXPORT_NAME=createNoodler -sINVOKE_RUN=0 -sEXIT_RUNTIME=1"
LINK_FLAGS+=" -sEXPORTED_RUNTIME_METHODS=callMain,FS -sENVIRONMENT=worker,node"
LINK_FLAGS+=" -sINITIAL_MEMORY=128MB -sMAXIMUM_MEMORY=4GB -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=64MB"

emcmake cmake -S "$ROOT" -B "$BUILD_DIR" \
  -DCMAKE_BUILD_TYPE=Release \
  -DZ3_SINGLE_THREADED=ON \
  -DZ3_POLLING_TIMER=ON \
  -DZ3_BUILD_LIBZ3_SHARED=OFF \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  -DMATA_BUILD_EXAMPLES=OFF \
  -DBUILD_TESTING=OFF \
  "-DCMAKE_C_FLAGS=$COMMON_FLAGS" \
  "-DCMAKE_CXX_FLAGS=$COMMON_FLAGS" \
  "-DCMAKE_EXE_LINKER_FLAGS=$COMMON_FLAGS" \
  "-DZ3_SHELL_LINK_FLAGS=$LINK_FLAGS" \
  "$@"

cmake --build "$BUILD_DIR" --target shell -j "$JOBS"

mkdir -p "$OUT_DIR"
cp "$BUILD_DIR/z3.js" "$OUT_DIR/noodler.js"
cp "$BUILD_DIR/z3.wasm" "$OUT_DIR/noodler.wasm"

# Version information shown on the page (and used by the nightly deployment to skip unchanged builds).
COMMIT="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
DESCRIBE="$(git -C "$ROOT" describe --tags --always 2>/dev/null || echo unknown)"
cat > "$OUT_DIR/version.json" <<EOF
{
  "commit": "$COMMIT",
  "describe": "$DESCRIBE",
  "built": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

echo "Built $(du -h "$OUT_DIR/noodler.wasm" | cut -f1) noodler.wasm into $OUT_DIR"
