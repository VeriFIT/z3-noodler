# Z3-Noodler web site

The web site of Z3-Noodler, deployed to GitHub Pages at <https://verifit.github.io/z3-noodler/> by
the nightly [`noodler-web`](../.github/workflows/noodler-web.yml) workflow. It is a Jekyll site
without a GitHub Pages theme: every page uses one layout (`site/_layouts/default.html`: header with
the navigation, footer) and one stylesheet (`site/assets/css/site.css`, light and dark), and the
navigation is defined once in `site/_config.yml`.

- **The documentation pages** (`site/*.md`) and **Finding bugs** (`site/bugs/index.md`) are Markdown.
- **The playground** (`site/playground/`) runs Z3-Noodler entirely in the browser via WebAssembly.
  Its `index.html` uses the same layout (with `wide: true`) and adds its own `style.css`; its
  scripts and the generated solver files are copied unchanged.

```
web/
├── bugs/                 the queries of the "Finding bugs" page and run-cases.sh (see below)
├── build-wasm.sh         builds the WebAssembly solver into site/playground/
├── smoke-test.mjs        tests the built solver in Node.js
├── Gemfile               for previewing the site locally (not used by the deployment)
└── site/                 Jekyll source of the site
    ├── _config.yml       title, description, navigation, default layout
    ├── _layouts/         default.html: the layout of every page
    ├── _includes/        bug-result.html, bug-stats.html (used by bugs/index.md)
    ├── _data/bugs.json   the recorded results of the "Finding bugs" queries (web/bugs/run-cases.sh)
    ├── assets/css/       site.css: the shared styles and colour tokens
    ├── index.md, installation.md, usage.md, publications.md
    ├── bugs/index.md     the "Finding bugs" page
    └── playground/       index.html, style.css, app.js, worker.js, examples.js
                          + noodler.js, noodler.wasm, version.json (generated, not committed)
```

Links between the pages point to the `.md` files (e.g. `[Usage](usage.md#options)`); the
`jekyll-relative-links` plugin, which GitHub Pages enables by default, turns them into links to the
generated pages under the site's base URL (`/z3-noodler/`). The layout builds the navigation links
with `relative_url`, so the site works under any base URL.

## How the playground works

- `build-wasm.sh` compiles the `z3` command-line binary (with Mata) to WebAssembly with Emscripten
  as a **single-threaded** module (`-DZ3_SINGLE_THREADED=ON`). The module does not use
  `SharedArrayBuffer`, so the page needs no cross-origin isolation headers, which GitHub Pages
  cannot set.
- The page runs the solver in a Web Worker. Each run gets a fresh module instance (the compiled
  module is reused), the input is written to the in-memory file system and passed to `callMain`
  together with the command-line options. Stop terminates the worker.
- Timeouts are passed as `timeout=<ms>`, which works thanks to the polling timer
  (`-DZ3_POLLING_TIMER=ON`). The `-T:` option of the native binary does not work in this build (it
  needs a thread). The page also terminates the worker shortly after the timeout as a backstop.
- `smoke-test.mjs` checks the built module in Node.js the same way the page uses it.

The generated files (`site/playground/noodler.js`, `noodler.wasm`, `version.json`) are not
committed; the workflow builds them.

## The "Finding bugs" page

`site/bugs/index.md` shows Z3-Noodler finding exploits in string-handling code and proving the
fixes: real CVEs (Jinja2, CPython) and classic bug patterns. The stories and the code snippets are
Markdown; each analysed version of the code is followed by

```liquid
{% include bug-result.html case="jinja-3.1.2" show="key" %}
```

which shows the solver's answer, the model (only the variables in `show`, if given), the time, the
SMT-LIB query and a link that opens the query in the playground. These come from
`site/_data/bugs.json`, which `web/bugs/run-cases.sh` writes by running every
`web/bugs/cases/*.smt2` with a native build. After changing or adding a query:

```shell
web/bugs/run-cases.sh build/z3     # a native release build; rewrites web/site/_data/bugs.json
```

`smoke-test.mjs` checks that the WebAssembly solver still gives every answer recorded in
`bugs.json`.

## Deployment

The workflow builds the WebAssembly solver into `web/site/playground`, smoke-tests it, builds the
site from `web/site` with [`actions/jekyll-build-pages`](https://github.com/actions/jekyll-build-pages)
(GitHub's own Pages builder: the `github-pages` gem with Jekyll 3.10 and the plugins GitHub allows)
and deploys the result. It runs every night and redeploys only if `devel` has moved since the
deployed build (it compares the commit in the deployed `playground/version.json`); changes of the
Markdown pages therefore appear the next night. It can also be run manually from the Actions tab
(`force` rebuilds even if nothing changed). Pull requests that touch `web/`, the workflow or the
CMake files the build depends on only build and test the site (WebAssembly smoke test and Jekyll
build).

One-time setup: *Settings → Pages → Build and deployment → Source: GitHub Actions*.

## Previewing the site locally

Requires Ruby and the [`github-pages`](https://github.com/github/pages-gem) gem, which pins the
Jekyll version and the plugins that GitHub Pages uses (`bundle install` in `web/`
installs it). From `web/`:

```shell
bundle exec jekyll serve --source site --baseurl /z3-noodler   # open http://localhost:4000/z3-noodler/
```

`bundle exec jekyll build --source site --baseurl /z3-noodler` only builds the site into `web/_site`.
The github-metadata plugin reads the repository's metadata from the GitHub API; without a token, it
warns "No GitHub API authentication could be found", which is harmless (set `JEKYLL_GITHUB_TOKEN`,
e.g. `JEKYLL_GITHUB_TOKEN=$(gh auth token)`, to avoid it).

The playground works in the preview only after `build-wasm.sh` has put the generated files into
`site/playground/`.

## Building the playground locally

Requires the [Emscripten SDK](https://emscripten.org/docs/getting_started/downloads.html) 3.1.73
(the version used in CI), activated in the shell.

```shell
web/build-wasm.sh              # builds into build-web/, copies the result to web/site/playground/
node web/smoke-test.mjs        # tests the built module
python3 -m http.server -d web/site/playground 8000  # open http://localhost:8000 (playground only)
```

A full build takes about 30 minutes on 4 cores. To reuse an existing Mata checkout of the right
version instead of fetching it, pass `-DFETCHCONTENT_SOURCE_DIR_MATA=<path>` to `build-wasm.sh`
(after the optional output directory).

## Limitations of the playground

- Single-threaded and slower than the native binary (about 1.5-2x on the bundled examples); use
  the native binary for benchmarking.
- Memory is limited to 4 GB, and very deeply nested formulas can exceed the browser's stack limit.
