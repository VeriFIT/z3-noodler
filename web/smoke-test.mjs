// Smoke test of the WebAssembly build used by the playground: runs a few SMT-LIB inputs through
// noodler.js in Node.js, the same way the playground's worker does (fresh instance per run, input
// in the in-memory file system, CLI arguments through callMain), and checks the answers.
//
// Usage: node web/smoke-test.mjs [DIR]   (default: web/site/playground)
import { createRequire } from 'node:module';
import path from 'node:path';
import fs from 'node:fs';

const siteDir = path.resolve(process.argv[2] ?? path.join(import.meta.dirname, 'site', 'playground'));
const require = createRequire(import.meta.url);
const createNoodler = require(path.join(siteDir, 'noodler.js'));
const wasmModule = await WebAssembly.compile(fs.readFileSync(path.join(siteDir, 'noodler.wasm')));

async function run(input, args = []) {
  const out = [];
  const module = await createNoodler({
    noInitialRun: true,
    instantiateWasm(imports, success) {
      WebAssembly.instantiate(wasmModule, imports).then(instance => success(instance));
      return {};
    },
    print: line => out.push(line),
    printErr: line => out.push(line),
  });
  module.FS.writeFile('/input.smt2', input);
  let exitCode = 0;
  try {
    exitCode = module.callMain([...args, '/input.smt2']) ?? 0;
  } catch (e) {
    if (e?.name !== 'ExitStatus') throw e;
    exitCode = e.status;
  }
  return { out: out.join('\n'), exitCode };
}

const tests = [
  {
    name: 'word equation with regular constraints (sat, model)',
    args: ['model=true'],
    input: `(declare-fun x () String) (declare-fun y () String)
            (assert (= (str.++ x "ab") (str.++ "ba" y)))
            (assert (str.in_re x (re.+ (str.to_re "b"))))
            (check-sat) (get-model)`,
    check: out => /^sat$/m.test(out) && /define-fun x/.test(out),
  },
  {
    name: 'equation with lengths (unsat)',
    input: `(declare-fun x () String) (declare-fun y () String)
            (assert (= (str.++ x "a") (str.++ "b" y)))
            (assert (= (str.len x) 0))
            (check-sat)`,
    check: out => /^unsat$/m.test(out),
  },
  {
    name: 'string-integer conversion (sat)',
    input: `(declare-fun s () String) (declare-fun n () Int)
            (assert (= n (str.to_int s))) (assert (> n 41)) (assert (< (str.len s) 3))
            (check-sat)`,
    check: out => /^sat$/m.test(out),
  },
  {
    name: 'ECMAScript regex with backreference (sat)',
    input: `(declare-fun x () String)
            (assert (str.in_re x (re.from_ecma2020 "(a|b)\\1c")))
            (assert (str.prefixof "b" x))
            (check-sat)`,
    check: out => /^sat$/m.test(out),
  },
  {
    name: 'options of a previous run (model=true) do not leak into the next run',
    input: `(declare-fun x () String) (assert (= x "a")) (check-sat)`,
    check: out => /^sat$/m.test(out) && !/x/.test(out.replace(/^sat$/m, '')),
  },
  {
    name: 'version flag',
    args: ['-version'],
    input: '',
    check: out => /Z3 version/.test(out),
  },
];

let failed = 0;
for (const t of tests) {
  const start = performance.now();
  let result;
  try {
    result = await run(t.input, t.args);
  } catch (e) {
    result = { out: `exception: ${e?.stack ?? e}`, exitCode: -1 };
  }
  const ok = t.check(result.out);
  failed += ok ? 0 : 1;
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${t.name} (${(performance.now() - start).toFixed(0)} ms)`);
  if (!ok) console.log(result.out.replace(/^/gm, '     | '));
}
console.log(failed ? `${failed} of ${tests.length} tests failed` : `all ${tests.length} tests passed`);
process.exit(failed ? 1 : 0);
