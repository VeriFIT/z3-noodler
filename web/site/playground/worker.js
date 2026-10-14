/*
 * Z3-Noodler solver worker (classic Web Worker).
 *
 * Loads the Emscripten glue (noodler.js) and compiles noodler.wasm once, then runs every request in
 * a fresh module instance, so no solver state survives from one run to the next.
 *
 * Messages from the page:
 *   {type: 'init', version, module}   version: string appended to the asset URLs as ?v= (cache
 *                                     busting, may be ''); module: an already compiled
 *                                     WebAssembly.Module to reuse, or null to download and compile.
 *   {type: 'run', id, input, args}    input: SMT-LIB text; args: extra command-line arguments.
 *
 * Messages to the page:
 *   {type: 'loading', loaded, total}  download progress in bytes; total is 0 when unknown.
 *   {type: 'compiling'}               the download finished, compilation is being completed.
 *   {type: 'ready', module}           ready to run; module is the compiled WebAssembly.Module so the
 *                                     page can hand it to a replacement worker (omitted if it
 *                                     cannot be cloned).
 *   {type: 'error', message}          loading failed; the worker cannot run anything.
 *   {type: 'out' | 'err', id, text}   one line of the solver's stdout / stderr, sent immediately.
 *   {type: 'done', id, exitCode, ms, memory, error, crash}
 *                                     the run finished. exitCode is null if the solver crashed,
 *                                     ms is the time spent in main(), memory the final size of the
 *                                     wasm memory in bytes (or null), error a human-readable message
 *                                     if it crashed and crash its kind ('stack', 'memory',
 *                                     'exception', 'trap' or 'other'); after a crash the page
 *                                     replaces this worker.
 */
'use strict';

const INPUT_PATH = '/input.smt2';

let compiled = null;
let initStarted = false;

function post(message) {
  self.postMessage(message);
}

function versioned(path, version) {
  return version ? `${path}?v=${encodeURIComponent(version)}` : path;
}

function describe(error) {
  if (error == null) return 'unknown error';
  if (typeof error === 'string') return error;
  const message = error.message || String(error);
  return error.name && error.name !== 'Error' && !message.startsWith(error.name) ? `${error.name}: ${message}` : message;
}

self.onmessage = (event) => {
  const message = event.data || {};
  if (message.type === 'init') init(message);
  else if (message.type === 'run') run(message);
};

async function init({ version = '', module = null }) {
  if (initStarted) return;
  initStarted = true;
  try {
    if (typeof WebAssembly !== 'object') throw new Error('This browser does not support WebAssembly.');
    try {
      importScripts(versioned('noodler.js', version));
    } catch (error) {
      throw new Error(error && error.name === 'NetworkError'
        ? 'noodler.js could not be downloaded.'
        : `noodler.js failed to run (${describe(error)}).`);
    }
    if (typeof createNoodler !== 'function') throw new Error('noodler.js does not define createNoodler().');
    compiled = module instanceof WebAssembly.Module ? module : await loadModule(versioned('noodler.wasm', version));
  } catch (error) {
    post({ type: 'error', message: describe(error) });
    return;
  }
  try {
    post({ type: 'ready', module: compiled });
  } catch (_) {
    post({ type: 'ready' }); // the module cannot be cloned in this browser; the page copes without it
  }
}

/* ---------- Download and compilation ---------- */

function compileFailure(error) {
  return new Error(`This browser could not compile the solver (${describe(error)}). ` +
    'It needs WebAssembly with exception handling, available in current Firefox, Chrome, Edge and Safari.');
}

async function loadModule(url) {
  let response;
  try {
    response = await fetch(url);
  } catch (error) {
    throw new Error(`Could not download the solver (${describe(error)}).`);
  }
  if (!response.ok) throw new Error(`Could not download the solver: ${url} returned HTTP ${response.status}.`);

  trackProgress(response);

  try {
    if (typeof WebAssembly.compileStreaming !== 'function') throw new TypeError('no streaming compilation');
    return await WebAssembly.compileStreaming(response);
  } catch (error) {
    if (error instanceof WebAssembly.CompileError) throw compileFailure(error);
    // Most likely the server did not send Content-Type: application/wasm, which streaming
    // compilation insists on. Compile from the downloaded bytes instead.
  }
  let bytes;
  try {
    bytes = await (response.bodyUsed ? await fetch(url) : response).arrayBuffer();
  } catch (error) {
    throw new Error(`Could not download the solver (${describe(error)}).`);
  }
  try {
    return await WebAssembly.compile(bytes);
  } catch (error) {
    throw error instanceof WebAssembly.CompileError ? compileFailure(error) : error;
  }
}

// Reports download progress by reading a copy of the response body.
function trackProgress(response) {
  const encoding = (response.headers.get('Content-Encoding') || '').toLowerCase();
  const length = Number(response.headers.get('Content-Length')) || 0;
  // With HTTP compression (GitHub Pages gzips .wasm), Content-Length is the compressed size while
  // the body yields decompressed bytes, so the total is only trustworthy for unencoded responses.
  let total = !encoding || encoding === 'identity' ? length : 0;
  let loaded = 0;
  let lastReport = 0;
  const report = (force) => {
    const now = Date.now();
    if (!force && now - lastReport < 100) return;
    lastReport = now;
    post({ type: 'loading', loaded, total });
  };
  report(true);

  let reader;
  try {
    reader = response.clone().body.getReader();
  } catch (_) {
    return; // no streams: progress stays unknown
  }
  (async () => {
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      loaded += value.byteLength;
      if (total && loaded > total) total = 0;
      report(false);
    }
    report(true);
    post({ type: 'compiling' });
  })().catch(() => {});
}

/* ---------- Running ---------- */

function findMemory(instance, imports) {
  for (const value of Object.values(instance.exports)) {
    if (value instanceof WebAssembly.Memory) return value;
  }
  for (const module of Object.values(imports || {})) {
    for (const value of Object.values(module || {})) {
      if (value instanceof WebAssembly.Memory) return value;
    }
  }
  return null;
}

function isExit(error) {
  return error === 'unwind' || (error != null && error.name === 'ExitStatus');
}

const NATIVE_HINT = 'Try the native binary instead (see the README).';
const REPORT_HINT = 'If the input is valid, please report this on GitHub with a Share link.';

// Turns an exception thrown out of callMain() into {kind, message} for the page.
function explainCrash(error) {
  const text = describe(error);
  if (error instanceof RangeError && /call stack/i.test(text)) {
    return {
      kind: 'stack',
      message: "The solver exceeded the browser's stack limit, probably because the formula is too " +
        `deeply nested. A web page cannot raise this limit. ${NATIVE_HINT}`,
    };
  }
  if (/\bOOM\b|out of memory|Cannot enlarge memory|Maximum memory size|Array buffer allocation failed|could not allocate/i.test(text)) {
    return {
      kind: 'memory',
      message: `The solver ran out of memory: in the browser it can use at most 4 GB. ${NATIVE_HINT} (${text})`,
    };
  }
  if (typeof WebAssembly.Exception === 'function' && error instanceof WebAssembly.Exception) {
    return {
      kind: 'exception',
      message: 'The solver stopped with an unhandled C++ exception (the browser build cannot show ' +
        `its message). ${REPORT_HINT}`,
    };
  }
  if (error instanceof WebAssembly.RuntimeError) {
    const trap = error.message || 'unknown trap';
    return {
      kind: 'trap',
      message: `The solver ${/unreachable/i.test(trap) ? 'aborted' : 'crashed'} (WebAssembly trap: ${trap}). ${REPORT_HINT}`,
    };
  }
  return { kind: 'other', message: `The solver crashed: ${text.replace(/\.$/, '')}. ${REPORT_HINT}` };
}

async function run({ id, input, args }) {
  const out = (text) => post({ type: 'out', id, text: String(text) });
  const err = (text) => post({ type: 'err', id, text: String(text) });

  let exitCode = null;
  let failure = null;
  let memory = null;
  let solveStart = performance.now();

  try {
    if (!compiled) throw new Error('The solver is not loaded.');

    let instantiateFailed;
    const instantiateFailure = new Promise((_, reject) => { instantiateFailed = reject; });
    const instance = await Promise.race([
      createNoodler({
        noInitialRun: true,
        print: out,
        printErr: err,
        instantiateWasm(imports, success) {
          WebAssembly.instantiate(compiled, imports).then((wasmInstance) => {
            memory = findMemory(wasmInstance, imports);
            success(wasmInstance, compiled);
          }, instantiateFailed);
          return {}; // asynchronous instantiation
        },
        onExit(code) { exitCode = code; },
      }),
      instantiateFailure,
    ]);

    instance.FS.writeFile(INPUT_PATH, input);
    solveStart = performance.now();
    // callMain() returns the exit code (EXIT_RUNTIME=1 turns exit() into an ExitStatus exception
    // that the glue catches); anything else it throws is a crash.
    let returned;
    try {
      returned = instance.callMain([...args, INPUT_PATH]);
    } catch (error) {
      if (!isExit(error)) throw error;
      if (typeof error.status === 'number') exitCode = error.status;
    }
    if (typeof returned === 'number') exitCode = returned;
  } catch (error) {
    failure = explainCrash(error);
    exitCode = null;
  }

  let memoryBytes = null;
  try {
    if (memory) memoryBytes = memory.buffer.byteLength;
  } catch (_) { /* detached */ }

  post({
    type: 'done',
    id,
    exitCode,
    ms: performance.now() - solveStart,
    memory: memoryBytes,
    error: failure ? failure.message : null,
    crash: failure ? failure.kind : null,
  });
}
