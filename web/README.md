# Z3-Noodler in the browser

A static page that runs Z3-Noodler entirely in the browser via WebAssembly. It is deployed to
GitHub Pages at <https://verifit.github.io/z3-noodler/> by the nightly
[`noodler-web`](../.github/workflows/noodler-web.yml) workflow.

## How it works

- `build-wasm.sh` compiles the `z3` command-line binary (with Mata) to WebAssembly with Emscripten
  as a **single-threaded** module (`-DZ3_SINGLE_THREADED=ON`). The module does not use
  `SharedArrayBuffer`, so the page needs no cross-origin isolation headers, which GitHub Pages
  cannot set.
- The page (`site/`) runs the solver in a Web Worker. Each run gets a fresh module instance (the
  compiled module is reused), the input is written to the in-memory file system and passed to
  `callMain` together with the command-line options. Stop terminates the worker.
- Timeouts are passed as `timeout=<ms>`, which works thanks to the polling timer
  (`-DZ3_POLLING_TIMER=ON`). The `-T:` option of the native binary does not work in this build (it
  needs a thread). The page also terminates the worker shortly after the timeout as a backstop.
- `smoke-test.mjs` checks the built module in Node.js the same way the page uses it.

The generated files (`site/noodler.js`, `site/noodler.wasm`, `site/version.json`) are not
committed; the workflow builds them.

## Deployment

The workflow runs every night and redeploys only if `devel` has moved since the deployed build (it
compares the commit in the deployed `version.json`). It can also be run manually from the Actions
tab (`force` rebuilds even if nothing changed). Pull requests that touch `web/`, the workflow or
the CMake files the build depends on only build and smoke-test the page.

One-time setup: *Settings → Pages → Build and deployment → Source: GitHub Actions*.

## Building locally

Requires the [Emscripten SDK](https://emscripten.org/docs/getting_started/downloads.html) 3.1.73
(the version used in CI), activated in the shell.

```shell
web/build-wasm.sh                        # builds into build-web/, copies the result to web/site/
node web/smoke-test.mjs                  # tests the built module
python3 -m http.server -d web/site 8000  # open http://localhost:8000
```

A full build takes about 30 minutes on 4 cores. To reuse an existing Mata checkout of the right
version instead of fetching it, pass `-DFETCHCONTENT_SOURCE_DIR_MATA=<path>` to `build-wasm.sh`
(after the optional output directory).

## Limitations

- Single-threaded and slower than the native binary (about 1.5-2x on the bundled examples); use
  the native binary for benchmarking.
- Memory is limited to 4 GB, and very deeply nested formulas can exceed the browser's stack limit.
