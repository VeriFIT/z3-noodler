// Z3-Noodler web page: editor, options, sharing, and the solver worker.

const REPO_URL = 'https://github.com/VeriFIT/z3-noodler';
const STORAGE_KEY = 'z3-noodler.page.v1';
const DEFAULT_TIMEOUT = 10;            // seconds; passed to the solver as timeout=<ms>
const MAX_TIMEOUT = 86400;             // seconds
// The solver polls its timeout, but some code paths do not poll, so the worker is killed as a
// backstop this many seconds after the timeout.
const KILL_GRACE_SECONDS = 3;
const MAX_LINES_PER_RUN = 20000;       // output lines shown per run; the rest is counted
const RECYCLE_AFTER_BYTES = 1024 ** 3; // replace the worker after a run that grew memory this far
// Highlighting: inputs up to FULL_HIGHLIGHT_CHARS are highlighted completely on every change; larger
// ones only around the visible lines (re-highlighting everything would make typing lag), and inputs
// over HIGHLIGHT_MAX_CHARS are edited without highlighting.
const FULL_HIGHLIGHT_CHARS = 20000;
const HIGHLIGHT_MAX_CHARS = 150000;
const HIGHLIGHT_MARGIN_LINES = 80;     // highlighted lines above and below the visible ones
const HIGHLIGHT_WINDOW_CHARS = 40000;  // at most this much text is highlighted at once
const GUTTER_DEFER_LINES = 3000;       // with more lines, the line numbers are updated after a pause
const MAX_SHARED_BYTES = 8 * 1024 * 1024; // unpacked size limit of a share link
const MAX_VERDICT_TAGS = 12;
// Extra options: parameters (name=value, e.g. smt.random_seed=3) and flags (-st, -v:10). Values are
// restricted to characters that option values need (no quotes, paths or shell syntax).
const OPTION_VALUE = '[A-Za-z0-9_.+:,-]+';
const PARAM_TOKEN = new RegExp(`^[A-Za-z_][A-Za-z0-9_.]*=${OPTION_VALUE}$`);
const FLAG_TOKEN = new RegExp(`^-[A-Za-z][A-Za-z0-9_]*(?::${OPTION_VALUE})?$`);
// The solver reads name=value as a file name if it ends with one of these extensions (main.cpp).
const FILE_EXTENSION = /\.(?:smt2|smt|dimacs|cnf|wcnf|opb|lp|log|drat|p)$/;
const VERDICTS = new Set(['sat', 'unsat', 'unknown', 'timeout']);

const FALLBACK_INPUT = `; Is there a string x that repeats "ab" at least three times
; and satisfies x ++ "ab" = "ab" ++ y?
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "ab" y)))
(assert (str.in_re x (re.+ (str.to_re "ab"))))
(assert (> (str.len x) 4))
(check-sat)
(get-model)
`;

const IS_MAC = /Mac|iPhone|iPad|iPod/.test(navigator.platform || navigator.userAgent);
// iOS Safari insets textarea text slightly, which breaks the overlay; edit as plain text there.
const IS_IOS = /iP(hone|ad|od)/.test(navigator.userAgent) ||
  (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);

const $ = (id) => document.getElementById(id);
const el = {
  notice: $('notice'),
  buildInfo: $('build-info'),
  exampleSelect: $('example-select'),
  examplePicker: $('example-picker'),
  shareBtn: $('share-btn'),
  sharePanel: $('share-panel'),
  shareUrl: $('share-url'),
  shareMsg: $('share-msg'),
  shareClose: $('share-close'),
  note: $('editor-note'),
  noteText: $('editor-note-text'),
  restoreBtn: $('restore-btn'),
  editor: $('editor'),
  textarea: $('editor-input'),
  hl: $('hl'),
  gutter: $('gutter'),
  models: $('opt-models'),
  stats: $('opt-stats'),
  timeout: $('opt-timeout'),
  extra: $('opt-extra'),
  extraError: $('extra-error'),
  runBtn: $('run-btn'),
  runKbd: $('run-kbd'),
  stopBtn: $('stop-btn'),
  loader: $('loader'),
  loadProgress: $('load-progress'),
  loadText: $('load-text'),
  outputPane: $('output-pane'),
  verdicts: $('verdicts'),
  clearBtn: $('clear-btn'),
  status: $('status'),
  elapsed: $('elapsed'),
  output: $('output'),
  outputEmpty: $('output-empty'),
};

/* ---------- Small helpers ---------- */

function formatSeconds(ms) {
  const s = ms / 1000;
  if (s < 10) return `${s.toFixed(2)} s`;
  if (s < 100) return `${s.toFixed(1)} s`;
  return `${Math.round(s)} s`;
}

function formatBytes(bytes) {
  if (bytes < 1024 * 1024) return `${Math.max(1, Math.round(bytes / 1024))} kB`;
  const mb = bytes / (1024 * 1024);
  return `${mb < 10 ? mb.toFixed(1) : Math.round(mb)} MB`;
}

function debounce(fn, ms) {
  let timer = 0;
  const debounced = () => {
    clearTimeout(timer);
    timer = setTimeout(fn, ms);
  };
  debounced.flush = () => {
    clearTimeout(timer);
    fn();
  };
  return debounced;
}

function escapeHtml(text) {
  return text.replace(/[&<>]/g, (c) => (c === '&' ? '&amp;' : c === '<' ? '&lt;' : '&gt;'));
}

function showNotice(message, { kind = 'error', retry = null, dismiss = false } = {}) {
  const box = document.createElement('div');
  const p = document.createElement('p');
  p.textContent = message;
  box.append(p);
  const addButton = (text, action) => {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'btn-link';
    button.textContent = text;
    button.addEventListener('click', () => {
      hideNotice();
      if (action) action();
    });
    p.append(' ', button);
  };
  if (retry) addButton('Try again', retry);
  if (dismiss) addButton('Dismiss', null);
  el.notice.dataset.kind = kind;
  el.notice.replaceChildren(box);
  el.notice.hidden = false;
}

function hideNotice() {
  el.notice.hidden = true;
  el.notice.replaceChildren();
}

/* ---------- SMT-LIB highlighting ---------- */

const COMMANDS = new Set([
  'assert', 'check-sat', 'check-sat-assuming', 'check-sat-using', 'declare-const', 'declare-datatype',
  'declare-datatypes', 'declare-fun', 'declare-sort', 'define-const', 'define-fun', 'define-fun-rec',
  'define-funs-rec', 'define-sort', 'echo', 'eval', 'exit', 'get-assertions', 'get-assignment',
  'get-info', 'get-model', 'get-option', 'get-proof', 'get-unsat-assumptions', 'get-unsat-core',
  'get-value', 'pop', 'push', 'reset', 'reset-assertions', 'set-info', 'set-logic', 'set-option',
  'simplify', 'minimize', 'maximize', 'get-objectives', 'display',
  'let', 'forall', 'exists', 'match', 'par', 'as', '!', '_',
]);
const SORTS = new Set(['String', 'Int', 'Bool', 'Real', 'RegLan', 'Array', 'Seq', 'Unicode', 'BitVec']);
const OPERATOR_PREFIX = /^(?:str|re|seq|int|char)\./;
const NUMBER = /^(?:\d+(?:\.\d+)?|#x[0-9A-Fa-f]+|#b[01]+)$/;
// comment | string literal ("" escapes a quote) | |quoted symbol| | parenthesis | other symbol
const TOKEN = /(;[^\n]*)|("(?:[^"]|"")*"?)|(\|[^|]*\|?)|([()])|([^\s()";|]+)/g;

function classifySymbol(symbol) {
  if (NUMBER.test(symbol) || symbol === 'true' || symbol === 'false') return 'number';
  if (symbol[0] === ':') return 'attr';
  if (COMMANDS.has(symbol)) return 'keyword';
  if (OPERATOR_PREFIX.test(symbol)) return 'op';
  if (SORTS.has(symbol)) return 'sort';
  return '';
}

// Where the string literal starting at `from` (just after its opening quote) ends: the index after
// the closing quote, or text.length if it is not closed.
function stringEnd(text, from) {
  for (let i = from; ;) {
    const quote = text.indexOf('"', i);
    if (quote === -1) return text.length;
    if (text[quote + 1] !== '"') return quote + 1;
    i = quote + 2; // "" is an escaped quote
  }
}

// The token that is still open at `pos`, the start of a line: '"' inside a string literal, '|'
// inside a quoted symbol, '' otherwise (comments end at the end of their line).
function openTokenAt(text, pos) {
  const special = /["|;]/g;
  for (let i = 0; i < pos;) {
    special.lastIndex = i;
    const m = special.exec(text);
    if (!m || m.index >= pos) return '';
    let end;
    if (m[0] === ';') {
      end = text.indexOf('\n', m.index);
      if (end === -1) return '';
      end += 1;
    } else if (m[0] === '|') {
      end = text.indexOf('|', m.index + 1);
      end = end === -1 ? text.length : end + 1;
    } else {
      end = stringEnd(text, m.index + 1);
    }
    if (end > pos) return m[0] === ';' ? '' : m[0];
    i = end;
  }
  return '';
}

// Highlights `text`; `open` is the token that is open at its start (see openTokenAt).
function highlight(text, open = '') {
  let html = '';
  let last = 0;
  if (open) {
    let end;
    if (open === '"') {
      end = stringEnd(text, 0);
    } else {
      end = text.indexOf('|');
      end = end === -1 ? text.length : end + 1;
    }
    const part = escapeHtml(text.slice(0, end));
    html += open === '"' ? `<span class="t-string">${part}</span>` : part;
    last = end;
  }
  TOKEN.lastIndex = last;
  for (let m = TOKEN.exec(text); m; m = TOKEN.exec(text)) {
    if (m.index > last) html += escapeHtml(text.slice(last, m.index));
    last = TOKEN.lastIndex;
    let cls = '';
    if (m[1] !== undefined) cls = 'comment';
    else if (m[2] !== undefined) cls = 'string';
    else if (m[4] !== undefined) cls = 'paren';
    else if (m[5] !== undefined) cls = classifySymbol(m[5]);
    html += cls ? `<span class="t-${cls}">${escapeHtml(m[0])}</span>` : escapeHtml(m[0]);
  }
  if (last < text.length) html += escapeHtml(text.slice(last));
  return html;
}

/* ---------- Editor: a transparent textarea over a highlighted <pre> ---------- */

function createEditor({ root, textarea, code, gutter, onChange }) {
  const pre = code.parentElement;
  let lineCount = -1;
  let gutterTimer = 0;
  let escapeArmed = false;
  // Large inputs: the highlighted lines [first, last) (last is Infinity up to the end), else null.
  let windowLines = null;
  let windowFrame = 0;

  function syncScroll() {
    const x = textarea.scrollLeft;
    const y = textarea.scrollTop;
    pre.style.transform = `translate(${-x}px, ${-y}px)`;
    gutter.style.transform = `translateY(${-y}px)`;
  }

  function renderGutter(lines) {
    clearTimeout(gutterTimer);
    gutterTimer = 0;
    if (lines === lineCount) return;
    lineCount = lines;
    let numbers = '';
    for (let i = 1; i <= lines; i++) numbers += `${i}\n`;
    gutter.textContent = numbers;
    root.style.setProperty('--digits', String(String(lines).length));
  }

  // The visible lines [first, last), estimated from the scroll position.
  function visibleLines() {
    const lineHeight = parseFloat(getComputedStyle(textarea).lineHeight) || 20;
    const first = Math.max(0, Math.floor(textarea.scrollTop / lineHeight) - 1);
    return { first, last: first + Math.ceil(textarea.clientHeight / lineHeight) + 2 };
  }

  // Highlights only the lines around the visible ones; the rest of the text is in the overlay as
  // plain text, so that it lines up with the textarea exactly.
  function renderWindow(text) {
    const visible = visibleLines();
    const firstWanted = Math.max(0, visible.first - HIGHLIGHT_MARGIN_LINES);
    const lastWanted = visible.last + HIGHLIGHT_MARGIN_LINES;
    let start = 0;
    let line = 0;
    while (line < firstWanted) {
      const nl = text.indexOf('\n', start);
      if (nl === -1) break;
      start = nl + 1;
      line++;
    }
    let end = start;
    let last = line;
    while (last < lastWanted && end < text.length) {
      const nl = text.indexOf('\n', end);
      end = nl === -1 ? text.length : nl + 1;
      last++;
    }
    if (end - start > HIGHLIGHT_WINDOW_CHARS) {
      end = start + HIGHLIGHT_WINDOW_CHARS;
      if (/[\uD800-\uDBFF]/.test(text[end - 1])) end--; // do not split a surrogate pair
      last = line;
      for (let i = text.indexOf('\n', start); i !== -1 && i < end; i = text.indexOf('\n', i + 1)) last++;
    }
    windowLines = { first: line, last: end >= text.length ? Infinity : last };
    const highlighted = document.createElement('span');
    highlighted.innerHTML = highlight(text.slice(start, end), openTokenAt(text, start));
    // The extra newline keeps the last (possibly empty) line as tall as in the textarea.
    code.replaceChildren(text.slice(0, start), highlighted, `${text.slice(end)}\n`);
  }

  function renderHighlight() {
    cancelAnimationFrame(windowFrame);
    windowFrame = 0;
    const text = textarea.value;
    const plain = IS_IOS || text.length > HIGHLIGHT_MAX_CHARS;
    root.classList.toggle('plain', plain);
    windowLines = null;
    if (plain) code.textContent = '';
    else if (text.length <= FULL_HIGHLIGHT_CHARS) code.innerHTML = `${highlight(text)}\n`;
    else renderWindow(text);
  }

  function render({ deferGutter = false } = {}) {
    const text = textarea.value;
    let lines = 1;
    for (let i = text.indexOf('\n'); i !== -1; i = text.indexOf('\n', i + 1)) lines++;
    if (deferGutter && lines > GUTTER_DEFER_LINES && lines !== lineCount) {
      // Rebuilding many line numbers on every keystroke makes typing lag.
      clearTimeout(gutterTimer);
      gutterTimer = setTimeout(() => renderGutter(lines), 150);
    } else {
      renderGutter(lines);
    }
    renderHighlight();
    syncScroll();
  }

  // After scrolling or resizing, a large input needs the newly visible lines highlighted.
  function onViewportChange() {
    syncScroll();
    if (!windowLines || windowFrame) return;
    const visible = visibleLines();
    if (visible.first >= windowLines.first && visible.last <= windowLines.last) return;
    windowFrame = requestAnimationFrame(() => {
      windowFrame = 0;
      renderHighlight();
    });
  }

  function insertText(text) {
    // execCommand keeps the browser's undo history; setRangeText is the fallback.
    let done = false;
    try {
      done = document.execCommand('insertText', false, text);
    } catch (_) { /* unsupported */ }
    if (!done) {
      textarea.setRangeText(text, textarea.selectionStart, textarea.selectionEnd, 'end');
      textarea.dispatchEvent(new Event('input', { bubbles: true }));
    }
  }

  function indent(outdent) {
    const value = textarea.value;
    const start = textarea.selectionStart;
    const end = textarea.selectionEnd;
    const multiline = value.slice(start, end).includes('\n');
    if (!outdent && !multiline) {
      insertText('  ');
      return;
    }
    const blockStart = value.lastIndexOf('\n', start - 1) + 1;
    let lastChar = end;
    if (end > start && value[end - 1] === '\n') lastChar = end - 1; // selection ends at a line start
    const nextBreak = value.indexOf('\n', lastChar);
    const blockEnd = nextBreak === -1 ? value.length : nextBreak;
    const lines = value.slice(blockStart, blockEnd).split('\n');
    const changed = lines.map((line) => (outdent ? line.replace(/^(?: {1,2}|\t)/, '') : line && `  ${line}`));
    const block = changed.join('\n');
    if (block === value.slice(blockStart, blockEnd)) return;
    textarea.setSelectionRange(blockStart, blockEnd);
    insertText(block);
    if (multiline) {
      textarea.setSelectionRange(blockStart, blockStart + block.length);
    } else {
      const removed = lines[0].length - changed[0].length;
      const caret = Math.max(blockStart, start - removed);
      textarea.setSelectionRange(caret, caret);
    }
  }

  textarea.addEventListener('input', () => {
    render({ deferGutter: true });
    onChange();
  });
  textarea.addEventListener('scroll', onViewportChange, { passive: true });
  textarea.addEventListener('keydown', (event) => {
    if (event.key === 'Escape') {
      escapeArmed = true;
      return;
    }
    if (event.key === 'Tab' && !event.ctrlKey && !event.metaKey && !event.altKey) {
      if (escapeArmed) {
        escapeArmed = false; // let Tab move the focus
        return;
      }
      event.preventDefault();
      indent(event.shiftKey);
      return;
    }
    escapeArmed = false;
    if (event.key === 'Enter' && !event.ctrlKey && !event.metaKey && !event.altKey && !event.shiftKey &&
        !event.isComposing && event.keyCode !== 229) {
      // Keep the indentation of the current line.
      const value = textarea.value;
      const caret = textarea.selectionStart;
      const lineStart = value.lastIndexOf('\n', caret - 1) + 1;
      const leading = /^[ \t]*/.exec(value.slice(lineStart, caret))[0];
      if (leading) {
        event.preventDefault();
        insertText(`\n${leading}`);
      }
    }
  });
  textarea.addEventListener('blur', () => { escapeArmed = false; });
  if (typeof ResizeObserver === 'function') new ResizeObserver(onViewportChange).observe(textarea);

  return {
    get value() { return textarea.value; },
    setValue(text) {
      textarea.value = text;
      textarea.scrollTop = 0;
      textarea.scrollLeft = 0;
      render();
    },
    focus() { textarea.focus(); },
  };
}

/* ---------- Options ---------- */

function readTimeout() {
  const raw = el.timeout.value.trim();
  const n = Math.floor(Number(raw));
  if (raw === '' || !Number.isFinite(n) || n < 0) return DEFAULT_TIMEOUT;
  return Math.min(n, MAX_TIMEOUT);
}

function readOptions() {
  return {
    models: el.models.checked,
    stats: el.stats.checked,
    timeout: readTimeout(),
    extra: el.extra.value.trim(),
  };
}

// Why an extra option token cannot be used, or '' if it is fine.
function rejectToken(token) {
  if (/^-T(?::|$)/.test(token)) {
    return `${token} does not work in the browser: the hard timeout needs threads, which this build does not have. ` +
      'Use the Timeout field instead, or timeout=<milliseconds>.';
  }
  if (/^-t(?::|$)/.test(token)) {
    return `Instead of ${token}, use the Timeout field or timeout=<milliseconds>, so that the page knows the time limit.`;
  }
  if (/^timeout=/.test(token) && !/^timeout=\d{1,9}$/.test(token)) {
    return `${token}: the timeout is a whole number of milliseconds, for example timeout=5000.`;
  }
  if (/^-(?:file|in)(?::|$)/.test(token)) {
    return `${token} cannot be used here: the input always comes from the editor.`;
  }
  if (PARAM_TOKEN.test(token)) {
    return FILE_EXTENSION.test(token)
      ? `${token}: the solver would read this as the name of an input file (it ends with a file extension).`
      : '';
  }
  if (FLAG_TOKEN.test(token)) return '';
  if (/^(?:[A-Za-z_][A-Za-z0-9_.]*=|-[A-Za-z])/.test(token)) {
    return `${token}: option values may contain only letters, digits and . _ - + : , characters.`;
  }
  return `“${token}” is not a solver option (the input always comes from the editor). ` +
    'Use name=value parameters such as smt.random_seed=3, or flags such as -v:10.';
}

// Returns the extra option tokens, or null (and shows why) if one of them cannot be used.
function validateExtra({ quiet = false } = {}) {
  const tokens = el.extra.value.split(/\s+/).filter(Boolean);
  let problem = '';
  for (const token of tokens) {
    problem = rejectToken(token);
    if (problem) break;
  }
  if (!problem) {
    el.extra.removeAttribute('aria-invalid');
    el.extraError.hidden = true;
    el.extraError.textContent = '';
    return tokens;
  }
  if (!quiet) {
    el.extra.setAttribute('aria-invalid', 'true');
    el.extraError.textContent = problem;
    el.extraError.hidden = false;
  }
  return null;
}

function buildArgs(options, extraTokens) {
  const args = [];
  if (options.models) args.push('model=true');
  if (options.stats) args.push('-st');
  if (options.timeout > 0) args.push(`timeout=${options.timeout * 1000}`);
  return args.concat(extraTokens);
}

// The time limit in milliseconds the solver gets from args (the last timeout= wins), 0 if none.
function effectiveTimeoutMs(args) {
  let ms = 0;
  for (const arg of args) {
    const m = /^timeout=(\d+)$/.exec(arg);
    if (m) ms = Number(m[1]);
  }
  return ms;
}

// Splits command-line arguments (e.g. an example's) into the page's option fields.
function optionsFromArgs(args, base = {}) {
  const options = { models: false, stats: false, timeout: base.timeout ?? DEFAULT_TIMEOUT, extra: '' };
  const rest = [];
  for (const arg of Array.isArray(args) ? args : []) {
    if (typeof arg !== 'string') continue;
    if (arg === 'model=true') options.models = true;
    else if (arg === '-st') options.stats = true;
    else if (/^timeout=\d+$/.test(arg) && Number(arg.slice(8)) % 1000 === 0) {
      options.timeout = Math.min(Number(arg.slice(8)) / 1000, MAX_TIMEOUT);
    } else if (/^-T:\d+$/.test(arg)) options.timeout = Math.min(Number(arg.slice(3)), MAX_TIMEOUT);
    else rest.push(arg);
  }
  options.extra = rest.join(' ');
  return options;
}

function applyOptions(options) {
  el.models.checked = !!options.models;
  el.stats.checked = !!options.stats;
  el.timeout.value = String(Number.isFinite(options.timeout) ? options.timeout : DEFAULT_TIMEOUT);
  el.extra.value = typeof options.extra === 'string' ? options.extra : '';
  validateExtra({ quiet: true });
  el.extra.removeAttribute('aria-invalid');
  el.extraError.hidden = true;
}

/* ---------- Saved state ---------- */

let editor = null;

function currentState() {
  return { code: editor.value, ...readOptions() };
}

function loadSavedState() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    const data = raw ? JSON.parse(raw) : null;
    return data && typeof data.code === 'string' ? data : null;
  } catch (_) {
    return null;
  }
}

const saveState = debounce(() => {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(currentState()));
  } catch (_) { /* storage unavailable or full */ }
}, 400);

function applyState(state) {
  editor.setValue(state.code);
  applyOptions(state);
  syncExampleUi();
}

/* ---------- Examples ---------- */

const examples = (Array.isArray(window.NOODLER_EXAMPLES) ? window.NOODLER_EXAMPLES : [])
  .filter((example) => example && typeof example.code === 'string');
let restoreText = null; // the user's own text replaced by an example

function populateExamples() {
  if (!examples.length) {
    el.examplePicker.hidden = true;
    return;
  }
  examples.forEach((example, index) => {
    const option = document.createElement('option');
    option.value = String(index);
    option.textContent = example.title || example.id || `Example ${index + 1}`;
    el.exampleSelect.append(option);
  });
}

function findExample(text) {
  return examples.findIndex((example) => example.code === text);
}

function syncExampleUi() {
  const index = findExample(editor.value);
  el.exampleSelect.value = index >= 0 ? String(index) : '';
  const description = index >= 0 && typeof examples[index].description === 'string' ? examples[index].description : '';
  el.noteText.textContent = description;
  el.noteText.hidden = !description;
  el.restoreBtn.hidden = restoreText === null;
  el.note.hidden = !description && restoreText === null;
}

// Remembers the user's own text before an example or a shared link replaces it.
function keepOwnText(text, replacement) {
  if (text.trim() !== '' && text !== replacement && findExample(text) < 0) restoreText = text;
}

function loadExample(index) {
  const example = examples[index];
  if (!example) return;
  keepOwnText(editor.value, example.code);
  editor.setValue(example.code);
  applyOptions(optionsFromArgs(example.args, { timeout: readTimeout() }));
  syncExampleUi();
  saveState();
}

/* ---------- Share links ---------- */

function toBase64Url(bytes) {
  let binary = '';
  for (let i = 0; i < bytes.length; i += 0x8000) {
    binary += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
  }
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function fromBase64Url(text) {
  let base64 = text.replace(/-/g, '+').replace(/_/g, '/');
  while (base64.length % 4) base64 += '=';
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
  return bytes;
}

async function transformBytes(bytes, transform) {
  const stream = new Blob([bytes]).stream().pipeThrough(transform);
  return new Uint8Array(await new Response(stream).arrayBuffer());
}

// Unpacks deflate-raw data, giving up (RangeError) once the result exceeds `limit` bytes, so that a
// crafted link cannot make the page unpack gigabytes. The input is fed in small pieces because one
// piece can unpack to a thousand times its size.
async function inflateLimited(bytes, limit) {
  const stream = new DecompressionStream('deflate-raw');
  const writer = stream.writable.getWriter();
  const reader = stream.readable.getReader();
  (async () => {
    for (let i = 0; i < bytes.length; i += 4096) await writer.write(bytes.subarray(i, i + 4096));
    await writer.close();
  })().catch(() => { /* reported by the reader */ });
  const chunks = [];
  let size = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    size += value.byteLength;
    if (size > limit) {
      reader.cancel().catch(() => {});
      throw new RangeError('too large');
    }
    chunks.push(value);
  }
  const result = new Uint8Array(size);
  let offset = 0;
  for (const chunk of chunks) {
    result.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return result;
}

// Fragment format: #z=<base64url(deflate-raw(JSON))> or #p=<base64url(JSON)>.
async function encodeShareFragment(state) {
  const json = JSON.stringify({
    v: 1, code: state.code, m: state.models ? 1 : 0, s: state.stats ? 1 : 0, t: state.timeout, x: state.extra,
  });
  const bytes = new TextEncoder().encode(json);
  const plain = `p=${toBase64Url(bytes)}`;
  if (typeof CompressionStream === 'function') {
    try {
      const packed = `z=${toBase64Url(await transformBytes(bytes, new CompressionStream('deflate-raw')))}`;
      if (packed.length < plain.length) return packed;
    } catch (_) { /* deflate-raw unsupported */ }
  }
  return plain;
}

async function decodeShareFragment(hash) {
  const match = /^#?([pz])=(.*)$/s.exec(hash);
  if (!match) return null;
  let bytes;
  try {
    if (!/^[A-Za-z0-9_-]*$/.test(match[2])) throw new Error('not base64url');
    bytes = fromBase64Url(match[2]);
  } catch (_) {
    throw new Error('The link is damaged (it is not valid base64url).');
  }
  if (match[1] === 'z') {
    if (typeof DecompressionStream !== 'function') {
      throw new Error('This browser cannot unpack compressed links; open it in a current Firefox, Chrome, Edge or Safari.');
    }
    try {
      bytes = await inflateLimited(bytes, MAX_SHARED_BYTES);
    } catch (error) {
      throw new Error(error instanceof RangeError
        ? `The link unpacks to more than ${formatBytes(MAX_SHARED_BYTES)}, which this page does not open.`
        : 'The link is damaged or incomplete.');
    }
  }
  let data;
  try {
    data = JSON.parse(new TextDecoder().decode(bytes));
  } catch (_) {
    throw new Error('The link is damaged or incomplete.');
  }
  if (!data || typeof data.code !== 'string') throw new Error('The link contains no input.');
  const timeout = Number(data.t);
  return {
    code: data.code,
    models: !!data.m,
    stats: !!data.s,
    timeout: Number.isFinite(timeout) && timeout >= 0 ? Math.min(Math.floor(timeout), MAX_TIMEOUT) : DEFAULT_TIMEOUT,
    extra: typeof data.x === 'string' ? data.x : '',
  };
}

async function buildShareUrl() {
  const url = new URL(location.href);
  url.hash = await encodeShareFragment(currentState());
  return url.href;
}

async function copyText(textPromise) {
  // Start the clipboard write inside the click handler, while the page still has user activation.
  if (navigator.clipboard && typeof navigator.clipboard.write === 'function' && typeof ClipboardItem === 'function') {
    try {
      const blob = textPromise.then((text) => new Blob([text], { type: 'text/plain' }));
      await navigator.clipboard.write([new ClipboardItem({ 'text/plain': blob })]);
      return true;
    } catch (_) { /* try the next method */ }
  }
  if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
    try {
      await navigator.clipboard.writeText(await textPromise);
      return true;
    } catch (_) { /* fall back to selecting the text */ }
  }
  return false;
}

async function share() {
  const urlPromise = buildShareUrl();
  const copied = await copyText(urlPromise);
  const url = await urlPromise;
  el.sharePanel.hidden = false;
  el.shareUrl.value = url;
  let message;
  if (copied) {
    message = 'Link copied to the clipboard.';
    el.shareMsg.dataset.kind = 'ok';
  } else {
    el.shareUrl.focus();
    el.shareUrl.select();
    message = `The link is selected; press ${IS_MAC ? '⌘C' : 'Ctrl+C'} to copy it.`;
    el.shareMsg.dataset.kind = '';
  }
  if (url.length > 8000) message += ' It is long, so some apps may cut it short.';
  el.shareMsg.textContent = message;
}

/* ---------- Output ---------- */

let currentRun = null;
let lastRun = null;
let runCounter = 0;

function makeLine(kind, text) {
  const line = document.createElement('div');
  let cls = 'line';
  if (kind === 'out') {
    const trimmed = text.trim();
    if (VERDICTS.has(trimmed)) cls += ` l-verdict l-${trimmed}`;
    else if (/^\(error\b/.test(trimmed)) cls += ' l-err';
  } else {
    cls += ` l-${kind}`;
  }
  line.className = cls;
  line.textContent = text;
  return line;
}

function isOutputAtBottom() {
  const o = el.output;
  return o.scrollHeight - o.scrollTop - o.clientHeight < 40;
}

function newRunBlock(args) {
  el.outputEmpty.hidden = true;
  const block = document.createElement('div');
  block.className = 'run';
  block.append(makeLine('cmd', ['z3', ...args, 'input.smt2'].join(' ')));
  el.output.append(block);
  el.output.scrollTop = Math.max(0, block.offsetTop - 8);
  return block;
}

function queueLine(run, kind, text) {
  if (kind === 'out') {
    const trimmed = text.trim();
    if (VERDICTS.has(trimmed)) {
      run.verdicts.push(trimmed);
      run.verdictsChanged = true;
    } else if (/^\(error\b/.test(trimmed)) {
      run.errors++;
      run.verdictsChanged = true;
    }
  }
  // Lines over the limit are only counted (also while a hidden tab does not render frames).
  if (run.lines >= MAX_LINES_PER_RUN) {
    run.dropped++;
    return;
  }
  run.lines++;
  run.pending.push(kind, text);
  if (!run.flushScheduled) {
    run.flushScheduled = true;
    requestAnimationFrame(() => flushLines(run));
  }
}

function flushLines(run) {
  run.flushScheduled = false;
  if (run.verdictsChanged) {
    run.verdictsChanged = false;
    renderVerdicts(run);
  }
  if (!run.pending.length) return;
  const pending = run.pending;
  run.pending = [];
  const stick = isOutputAtBottom();
  const fragment = document.createDocumentFragment();
  for (let i = 0; i < pending.length; i += 2) fragment.append(makeLine(pending[i], pending[i + 1]));
  run.block.append(fragment);
  if (stick) el.output.scrollTop = el.output.scrollHeight;
}

function appendNote(run, kind, text) {
  flushLines(run);
  const stick = isOutputAtBottom();
  run.block.append(makeLine(kind, text));
  if (stick) el.output.scrollTop = el.output.scrollHeight;
}

function renderVerdicts(run) {
  const tags = run ? [...run.verdicts] : [];
  if (run && run.errors) tags.push('error');
  if (run && run.final && run.final !== 'done') tags.push(run.final);
  const items = [];
  const shown = tags.length > MAX_VERDICT_TAGS ? tags.slice(0, MAX_VERDICT_TAGS - 1) : tags;
  for (const tag of shown) {
    const li = document.createElement('li');
    const span = document.createElement('span');
    span.className = `tag tag-${tag}`;
    span.textContent = tag;
    li.append(span);
    items.push(li);
  }
  if (shown.length < tags.length) {
    const li = document.createElement('li');
    li.className = 'tag tag-more';
    li.textContent = `and ${tags.length - shown.length} more`;
    items.push(li);
  }
  el.verdicts.replaceChildren(...items);
}

// `spoken` is read out by screen readers before the visible text (the status is a live region).
function setStatus(text, kind = '', spoken = '') {
  el.status.dataset.kind = kind;
  if (spoken) {
    const span = document.createElement('span');
    span.className = 'visually-hidden';
    span.textContent = `${spoken} `;
    el.status.replaceChildren(span, text);
  } else {
    el.status.textContent = text;
  }
}

// The answers of a run for screen readers, which do not get the tags announced.
function spokenResults(run) {
  const n = run.verdicts.length;
  if (!n) return '';
  const more = n > 5 ? ` and ${n - 5} more` : '';
  return `Result${n > 1 ? 's' : ''}: ${run.verdicts.slice(0, 5).join(', ')}${more}.`;
}

function clearOutput() {
  for (const child of [...el.output.children]) {
    if (child !== el.outputEmpty) child.remove();
  }
  if (currentRun) {
    currentRun.block = newRunBlock(currentRun.args);
  } else {
    el.outputEmpty.hidden = false;
    lastRun = null;
    renderVerdicts(null);
    if (workerReady) setStatus('Ready.');
  }
}

/* ---------- Worker ---------- */

let worker = null;
let workerReady = false;
let runQueued = false; // Ctrl+Enter was pressed while the worker restarted
let compiledModule = null; // kept so a replacement worker does not download and compile again
let assetVersion = '';
let unsupportedReason = null;

function updateControls() {
  const canRun = !unsupportedReason && workerReady && !currentRun;
  el.runBtn.disabled = !canRun;
  el.runBtn.title = workerReady || unsupportedReason ? '' : 'Available once the solver has loaded';
  el.stopBtn.disabled = !currentRun;
}

function setLoader(text, { loaded = null, total = 0, state = '' } = {}) {
  el.loader.hidden = false;
  el.loader.dataset.state = state;
  el.loadText.textContent = text;
  if (total > 0 && loaded !== null) {
    el.loadProgress.max = total;
    el.loadProgress.value = Math.min(loaded, total);
  } else {
    el.loadProgress.removeAttribute('value'); // indeterminate
  }
}

function startWorker() {
  workerReady = false;
  updateControls();
  let w;
  try {
    w = new Worker(assetVersion ? `worker.js?v=${encodeURIComponent(assetVersion)}` : 'worker.js');
  } catch (error) {
    failLoading(`The browser refused to start the solver worker (${error.message}).`);
    return;
  }
  worker = w;
  w.onmessage = (event) => {
    if (worker === w) handleWorkerMessage(event.data || {});
  };
  w.onerror = (event) => {
    if (worker !== w) return;
    event.preventDefault();
    handleWorkerFailure(event.message || 'the worker script failed');
  };
  const init = { type: 'init', version: assetVersion, module: compiledModule };
  try {
    w.postMessage(init);
  } catch (_) {
    compiledModule = null;
    w.postMessage({ ...init, module: null });
  }
  setLoader(init.module ? 'Restarting the solver…' : 'Loading the solver…');
  if (!lastRun && !currentRun) setStatus('Loading the solver…');
}

function stopWorker() {
  if (worker) worker.terminate();
  worker = null;
  workerReady = false;
}

function handleWorkerMessage(message) {
  switch (message.type) {
    case 'loading': {
      const { loaded = 0, total = 0 } = message;
      const text = total > 0
        ? `Downloading ${formatBytes(loaded)} of ${formatBytes(total)}`
        : `Downloading ${formatBytes(loaded)}`;
      setLoader(text, { loaded, total });
      break;
    }
    case 'compiling':
      setLoader('Preparing the solver…');
      break;
    case 'ready':
      if (message.module) compiledModule = message.module;
      workerReady = true;
      el.loader.hidden = true;
      if (!lastRun && !currentRun) setStatus('Ready.');
      updateControls();
      if (runQueued) {
        runQueued = false;
        startRun();
      }
      break;
    case 'error':
      failLoading(message.message || 'Unknown error.');
      break;
    case 'out':
    case 'err':
      if (currentRun && message.id === currentRun.id) queueLine(currentRun, message.type, message.text);
      break;
    case 'done':
      if (currentRun && message.id === currentRun.id) finishRun(currentRun, message);
      break;
    default:
      break;
  }
}

function failLoading(message) {
  runQueued = false;
  stopWorker();
  compiledModule = null;
  if (currentRun) endRun(currentRun, 'crashed');
  setLoader('The solver could not be loaded.', { state: 'error' });
  setStatus('The solver is not available.', 'error');
  showNotice(`The solver could not be loaded. ${message}`, { retry: startWorker });
  updateControls();
}

function handleWorkerFailure(message) {
  if (!workerReady && !currentRun) {
    failLoading(message);
    return;
  }
  stopWorker();
  if (currentRun) {
    const run = currentRun;
    appendNote(run, 'crash', `The solver worker failed: ${message}`);
    setStatus(`Crashed after ${formatSeconds(performance.now() - run.start)}.`, 'error');
    endRun(run, 'crashed');
  }
  startWorker();
}

/* ---------- Runs ---------- */

// Ctrl+Enter: while the worker restarts after Stop or a crash (a fraction of a second), the run
// starts as soon as it is ready instead of the key press being lost.
function requestRun() {
  if (!unsupportedReason && worker && !workerReady && compiledModule && !currentRun) {
    runQueued = true; // the loader says that the solver is restarting
    return;
  }
  startRun();
}

function startRun() {
  if (unsupportedReason || !workerReady || currentRun) return;
  const extraTokens = validateExtra();
  if (!extraTokens) {
    el.extra.focus();
    return;
  }
  const options = readOptions();
  el.timeout.value = String(options.timeout);
  const args = buildArgs(options, extraTokens);
  const timeoutMs = effectiveTimeoutMs(args);
  const run = {
    id: ++runCounter,
    args,
    timeoutMs,
    start: performance.now(),
    block: newRunBlock(args),
    verdicts: [],
    errors: 0,
    lines: 0,
    dropped: 0,
    pending: [],
    flushScheduled: false,
    verdictsChanged: false,
    final: null,
    killTimer: 0,
    ticker: 0,
  };
  currentRun = run;
  lastRun = run;
  worker.postMessage({ type: 'run', id: run.id, input: editor.value, args });
  if (timeoutMs > 0) {
    run.killTimer = setTimeout(() => killRun('timeout'), timeoutMs + KILL_GRACE_SECONDS * 1000);
  }
  const tick = () => { el.elapsed.textContent = formatSeconds(performance.now() - run.start); };
  tick();
  run.ticker = setInterval(tick, 100);
  el.outputPane.classList.add('running');
  setStatus('Running…');
  renderVerdicts(run);
  updateControls();
  saveState.flush();
}

function endRun(run, final) {
  run.final = final;
  clearTimeout(run.killTimer);
  clearInterval(run.ticker);
  flushLines(run);
  if (run.dropped) appendNote(run, 'note', `${run.dropped} more output lines are not shown.`);
  el.elapsed.textContent = '';
  el.outputPane.classList.remove('running');
  if (currentRun === run) currentRun = null;
  renderVerdicts(run);
  updateControls();
}

// What the solver's exit code means (Z3's error codes, src/util/error_codes.h).
const EXIT_CODES = {
  1: 'the input has errors',
  101: 'out of memory',
  102: 'timeout',
  103: 'parse error',
  105: 'incomplete',
  108: 'cannot open a file',
  109: 'invalid command-line option',
  110: 'error',
  111: 'type error',
  112: 'unknown result',
  113: 'allocation limit exceeded',
};

function formatTimeout(ms) {
  return ms % 1000 === 0 ? `${ms / 1000} s` : `${ms} ms`;
}

function finishRun(run, message) {
  flushLines(run);
  const time = formatSeconds(message.ms);
  if (message.error) {
    appendNote(run, 'crash', message.error);
    const what = message.crash === 'stack' ? 'Stack limit exceeded'
      : message.crash === 'memory' ? 'Out of memory' : 'Crashed';
    setStatus(`${what} after ${time}.`, 'error');
    endRun(run, 'crashed');
  } else {
    const code = message.exitCode;
    // The solver answers unknown when its timeout= expires; say so instead of leaving a puzzle.
    const timedOut = run.timeoutMs > 0 && message.ms >= run.timeoutMs - 50 && run.verdicts.includes('unknown');
    if (timedOut) appendNote(run, 'note', `The solver gave up when the ${formatTimeout(run.timeoutMs)} timeout expired.`);
    let text = `Finished in ${time}, exit code ${code ?? 'unknown'}`;
    if (code && EXIT_CODES[code]) text += ` (${EXIT_CODES[code]})`;
    if (message.memory) text += `, ${formatBytes(message.memory)} of memory`;
    if (timedOut) text += '; timeout reached';
    setStatus(`${text}.`, code ? 'error' : '', spokenResults(run));
    endRun(run, timedOut ? 'timeout' : 'done');
  }
  if (message.error || (message.memory && message.memory > RECYCLE_AFTER_BYTES)) {
    // Start over with a clean worker: after a crash its state is suspect, and a large memory is
    // released promptly.
    stopWorker();
    startWorker();
  }
}

function killRun(reason) {
  const run = currentRun;
  if (!run) return;
  stopWorker();
  const elapsed = formatSeconds(performance.now() - run.start);
  if (reason === 'timeout') {
    appendNote(run, 'killed', `Killed after ${elapsed}: the solver did not stop at its ${formatTimeout(run.timeoutMs)} timeout.`);
    setStatus(`Killed after ${elapsed} (timeout ${formatTimeout(run.timeoutMs)}).`, 'error', spokenResults(run));
    endRun(run, 'killed');
  } else {
    appendNote(run, 'killed', `Stopped after ${elapsed}.`);
    setStatus(`Stopped after ${elapsed}.`, '', spokenResults(run));
    endRun(run, 'stopped');
  }
  startWorker();
}

/* ---------- Build information ---------- */

async function fetchVersion() {
  const controller = typeof AbortController === 'function' ? new AbortController() : null;
  const timer = controller ? setTimeout(() => controller.abort(), 4000) : 0;
  try {
    const response = await fetch('version.json', { cache: 'no-cache', signal: controller && controller.signal });
    if (!response.ok) return null;
    const data = await response.json();
    return data && typeof data === 'object' ? data : null;
  } catch (_) {
    return null;
  } finally {
    clearTimeout(timer);
  }
}

function renderVersion(info) {
  const p = el.buildInfo;
  p.replaceChildren();
  const commit = info && typeof info.commit === 'string' && /^[0-9a-f]{7,40}$/i.test(info.commit) ? info.commit : '';
  const describe = info && typeof info.describe === 'string' && info.describe !== 'unknown' ? info.describe : '';
  if (!commit && !describe) {
    p.textContent = 'Build information is not available.';
    return;
  }
  p.append('Build ');
  const showDescribe = describe && !(commit && commit.startsWith(describe));
  if (showDescribe) {
    const code = document.createElement('code');
    code.textContent = describe;
    p.append(code);
  }
  if (commit) {
    const a = document.createElement('a');
    a.href = `${REPO_URL}/commit/${commit}`;
    a.textContent = commit.slice(0, 7);
    a.title = `Commit ${commit}`;
    if (showDescribe) p.append(' (commit ', a, ')');
    else p.append('from commit ', a);
  }
  const built = info && typeof info.built === 'string' ? new Date(info.built) : null;
  if (built && !Number.isNaN(built.getTime())) {
    const time = document.createElement('time');
    time.dateTime = info.built;
    time.textContent = built.toISOString().slice(0, 10);
    p.append(', ', time);
  }
}

/* ---------- Start-up ---------- */

function checkSupport() {
  if (typeof WebAssembly !== 'object' || typeof WebAssembly.instantiate !== 'function') {
    return 'This browser cannot run the solver because it does not support WebAssembly. Use a current version of Firefox, Chrome, Edge or Safari.';
  }
  if (typeof Worker !== 'function') {
    return 'This browser cannot run the solver because it does not support Web Workers. Use a current version of Firefox, Chrome, Edge or Safari.';
  }
  if (location.protocol === 'file:') {
    return 'Browsers do not run the solver from a file:// page. Serve this directory over HTTP instead, for example with python3 -m http.server.';
  }
  return null;
}

async function loadFromFragment() {
  if (location.hash.length <= 1) return null;
  let state = null;
  try {
    state = await decodeShareFragment(location.hash);
  } catch (error) {
    showNotice(`This shared link could not be opened. ${error.message}`, { dismiss: true });
    return null;
  }
  if (state) {
    // The link has done its job; from now on the saved state keeps the work across reloads.
    try {
      history.replaceState(null, '', location.pathname + location.search);
    } catch (_) { /* ignore */ }
  }
  return state;
}

function initialState() {
  const saved = loadSavedState();
  if (saved) return saved;
  if (examples.length) return { code: examples[0].code, ...optionsFromArgs(examples[0].args) };
  return { code: FALLBACK_INPUT, models: true, stats: false, timeout: DEFAULT_TIMEOUT, extra: '' };
}

function wireEvents() {
  el.runBtn.addEventListener('click', startRun);
  el.stopBtn.addEventListener('click', () => killRun('stopped'));
  el.clearBtn.addEventListener('click', clearOutput);
  el.shareBtn.addEventListener('click', share);
  el.shareClose.addEventListener('click', () => {
    el.sharePanel.hidden = true;
    el.shareBtn.focus();
  });
  el.shareUrl.addEventListener('focus', () => el.shareUrl.select());
  el.exampleSelect.addEventListener('change', () => {
    if (el.exampleSelect.value !== '') loadExample(Number(el.exampleSelect.value));
  });
  el.restoreBtn.addEventListener('click', () => {
    if (restoreText === null) return;
    editor.setValue(restoreText);
    restoreText = null;
    syncExampleUi();
    saveState();
    editor.focus();
  });
  for (const input of [el.models, el.stats, el.timeout]) input.addEventListener('change', saveState);
  el.timeout.addEventListener('input', saveState);
  el.timeout.addEventListener('blur', () => { el.timeout.value = String(readTimeout()); });
  el.extra.addEventListener('input', () => {
    // Only clear a shown error while typing; report new errors on Run.
    if (el.extra.getAttribute('aria-invalid') === 'true') validateExtra();
    saveState();
  });
  el.extra.addEventListener('blur', () => validateExtra());

  document.addEventListener('keydown', (event) => {
    if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') {
      event.preventDefault();
      if (!event.repeat) requestRun(); // holding the keys must not start run after run
    }
  });
  window.addEventListener('hashchange', async () => {
    const state = await loadFromFragment();
    if (state) {
      keepOwnText(editor.value, state.code);
      applyState(state);
      saveState.flush();
    }
  });
  window.addEventListener('pagehide', () => saveState.flush());
}

async function main() {
  const versionPromise = fetchVersion();
  el.runKbd.textContent = IS_MAC ? '⌘ Enter' : 'Ctrl Enter';
  editor = createEditor({
    root: el.editor,
    textarea: el.textarea,
    code: el.hl,
    gutter: el.gutter,
    onChange: () => {
      syncExampleUi();
      saveState();
    },
  });
  populateExamples();
  wireEvents();

  const linked = await loadFromFragment();
  if (linked) {
    const saved = loadSavedState();
    if (saved) keepOwnText(saved.code, linked.code);
    applyState(linked);
    saveState.flush();
  } else {
    applyState(initialState());
  }

  unsupportedReason = checkSupport();
  if (unsupportedReason) {
    showNotice(unsupportedReason);
    setLoader(unsupportedReason, { state: 'error' });
    setStatus('The solver is not available in this browser.', 'error');
    updateControls();
    renderVersion(await versionPromise);
    return;
  }

  const info = await versionPromise;
  renderVersion(info);
  if (info && typeof info.commit === 'string' && /^[0-9a-f]{7,40}$/i.test(info.commit)) assetVersion = info.commit;
  else if (info && typeof info.built === 'string') assetVersion = info.built;
  startWorker();
}

main();
