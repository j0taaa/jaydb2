import fs from 'node:fs';
import path from 'node:path';
import { AdmissionError, loadToolchain, sha256 } from './bootstrap.mjs';
import { preflight } from './preflight.mjs';
import { prepareKernel, auditLoopCalls, validateKernelEntry, validateForeignSnapshot, removeForeignSnapshot } from './kernel.mjs';
import { checkBook } from '../verifier/check.mjs';

export { AdmissionError, bootstrapInfo } from './bootstrap.mjs';
export { preflight } from './preflight.mjs';

const admittedBooks = new WeakMap();
const sourceCleanup = new FinalizationRegistry(removeForeignSnapshot);
const reject = (code, message) => { throw new AdmissionError(code, 'policy', message); };

function walk(term, visit) {
  const all = [term], seen = new Set();
  while (all.length) {
    const t = all.pop();
    if (!t || typeof t !== 'object' || seen.has(t)) continue;
    seen.add(t);
    visit(t);
    for (const [k, v] of Object.entries(t)) if (k !== 's' && v && typeof v === 'object') all.push(v);
  }
}

function references(term) {
  const refs = new Set();
  walk(term, t => {
    if (t.$ === 'Hol') reject('META', `Metavariable: ${t.k}`);
    // Match tags and literals matter too; merely scanning Ref misses them.
    if (['Ref', 'ADT', 'Ctr', 'Mat', 'Lit', 'PCtr'].includes(t.$)) refs.add(t.k);
  });
  return refs;
}

function terms(B, t) {
  const result = [B.term_lower(t.T)];
  if (t.$ === 'ADT') return result.concat(t.c.map(c => B.term_lower(c.T)));
  if (t.v) result.push(B.term_lower(t.v));
  if (t.e) result.push(t.e);
  return result;
}

function sameTerm(B, a, b) {
  return B.term_key(B.term_lower(a)) === B.term_key(B.term_lower(b));
}

function assertBindings(B, book, plan, mustBeOpen) {
  const app = (k, ...xs) => xs.reduce((f, x) => B.App(f, B.Ref(x)), B.Ref(k));
  const canonical = plan.canonicalRefs;
  const bind = plan.records.get(canonical.bindings).ns;
  const inst = plan.records.get(canonical.instance).ns;
  const client = plan.records.get(canonical.client).ns;
  const expected = {
    [bind + ':certificate']: app(canonical.contractPrefix + 'Requirements:Certifies', inst + ':config', bind + ':code', client + ':program', inst + ':context', inst + ':arguments'),
    [bind + ':terminates']: app(canonical.contractPrefix + 'Interface:ProgramTerminates', inst + ':config', client + ':program'),
  };
  if (plan.certificateMode === 'universal') {
    const apply = (k, ...xs) => xs.reduce((f, x) => B.App(f, x), B.Ref(k));
    expected[bind + ':certificate'] = B.All(B.Lone(), 'ctx', 0, B.Ref(canonical.contractPrefix + 'Data:Context'), ctx =>
      B.All(B.Lone(), 'args', 1, B.Ref(canonical.contractPrefix + 'Data:Value'), args =>
        apply(canonical.contractPrefix + 'Requirements:Certifies', B.Ref(inst + ':config'), B.Ref(bind + ':code'),
          B.Ref(client + ':program'), ctx, args)));
  }
  if (plan.readOnly) expected[bind + ':read_only'] = app('ReadOnly:Program', client + ':program');
  for (const [k, T] of Object.entries(expected)) {
    const t = book.tlds[k];
    if (!t || t.$ !== 'Def' || !t.l || !sameTerm(B, t.T, T) || (mustBeOpen && t.v !== null)) {
      reject('TARGET', `Incorrect host target: ${k}`);
    }
  }
  const code = book.tlds[bind + ':code'];
  const v = code?.v && B.term_lower(code.v);
  if (code?.$ !== 'Def' || code.n !== 0 || !sameTerm(B, code.T, B.Ref('String'))
      || v?.$ !== 'Lit' || v.k !== 'String' || v.v !== plan.records.get(canonical.client).text) {
    reject('SOURCE_BINDING', `${bind}.code must be the exact source literal for ${canonical.client}`);
  }
  if (plan.certificateMode === 'universal') {
    const proof = book.tlds[bind + ':proof_source'];
    const value = proof?.v && B.term_lower(proof.v);
    const proofFile = plan.openTargets[bind + ':certificate'];
    if (proof?.$ !== 'Def' || proof.n !== 0 || !sameTerm(B, proof.T, B.Ref('String'))
        || value?.$ !== 'Lit' || value.k !== 'String' || value.v !== plan.records.get(proofFile).text)
      reject('SOURCE_BINDING', `${bind}.proof_source must be the exact universal proof source literal`);
  }
  return expected;
}

function assertInitialization(B, book, plan) {
  if (plan.purpose !== 'initialize') return {};
  const { configuration, state, proof } = plan.initialization;
  const T = B.App(B.App(B.Ref(plan.canonicalRefs.contractPrefix + 'Requirements:Valid'), B.Ref(configuration)), B.Ref(state));
  const p = book.tlds[proof];
  if (p?.$ !== 'Def' || !p.l || p.v === null || !sameTerm(B, p.T, T)) {
    reject('INITIALIZATION', `Required proof: ${proof} : Requirements.Valid(${configuration}(), ${state}())`);
  }
  for (const k of [configuration, state]) {
    const t = book.tlds[k];
    if (t?.$ !== 'Def' || t.n !== 0 || t.v === null || t.i !== undefined || t.u) reject('INITIALIZATION', `Initial value is not a closed pure definition: ${k}`);
  }
  return { [proof]: T };
}

function parseSnapshots(B, plan, base) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', base, '', Object.create(null));
  const baseNames = new Set(Object.keys(book.tlds));
  const baseCtors = new Set(Object.keys(book.ctrs));
  for (const k of baseNames) book.tlds[k].b = true;
  const owners = new Map(), fillers = new Map();
  for (const rec of plan.ordered) {
    const before = new Map(Object.entries(book.tlds).map(([k, t]) => [k, { ...t }]));
    const beforeCtors = new Map(Object.entries(book.ctrs));
    B.parse_book(book, path.join(plan.root, path.posix.dirname(rec.path)) + '/', rec.body, rec.ns, rec.aliases);
    for (const [k, t] of Object.entries(book.tlds)) {
      const old = before.get(k);
      if (!old) {
        if (!k.startsWith(rec.ns ? rec.ns + ':' : '') || baseNames.has(k)) reject('SHADOW', `Declaration in another module: ${k}`);
        owners.set(k, rec);
        continue;
      }
      const changed = new Set([...Object.keys(old), ...Object.keys(t)].filter(f => old[f] !== t[f]));
      if (!changed.size) continue;
      if (plan.openTargets[k] !== rec.path || fillers.has(k) || old.$ !== 'Def' || old.v !== null
          || [...changed].some(f => !['n', 'v', 'u', 'i'].includes(f))) {
        reject('REDEFINITION', `Unauthorized target implementation: ${rec.path} -> ${k}`);
      }
      fillers.set(k, rec);
    }
    for (const [k, c] of Object.entries(book.ctrs)) {
      if (beforeCtors.has(k)) {
        if (beforeCtors.get(k) !== c) reject('REDEFINITION', `Constructor redefined: ${k}`);
      } else {
        if (baseCtors.has(k) || (rec.ns && !k.startsWith(rec.ns + ':'))) reject('SHADOW', `Constructor in another module: ${k}`);
        owners.set(k, rec);
      }
    }
    if (!plan.kernelOnly && rec.path === plan.canonicalRefs.bindings) assertBindings(B, book, plan, true);
  }
  for (const k of Object.keys(plan.openTargets)) if (!fillers.has(k)) reject('OPEN_LAW', `Unimplemented target: ${k}`);
  if (!plan.kernelOnly) assertBindings(B, book, plan, false);
  assertInitialization(B, book, plan);
  return { book, baseNames, baseCtors, owners, fillers, plan, primitives: new Set() };
}

function audit(B, state) {
  const { book, baseNames, owners, fillers } = state;
  if (book.hols !== 0) reject('META', 'Derivation contains metavariables');
  const graph = new Map(), baseForbidden = new Set(['IO', 'IO.OP', 'File', 'Socket', 'Listener', 'Window', 'Audio', 'Chan']);
  // Instantiation is done by the official checker. Its generated names inherit
  // the template's origin, never the privileges of their textual name.
  const instances = new Map();
  for (const [template, variants] of Object.entries(book.tmps)) {
    for (const k of variants.values()) instances.set(k, template);
  }
  const origin = k => {
    while (instances.has(k)) k = instances.get(k);
    return k;
  };
  for (const [k, t] of Object.entries(book.tlds)) {
    const original = origin(k), isBase = baseNames.has(original);
    if (t.b === true && !isBase && !state.primitives.has(k)) reject('KERNEL_ABI', `Definition outside the boundary is marked as Base: ${k}`);
    if (t.u || t.i !== undefined) {
      if (!isBase && (t.u || !state.primitives.has(k))) reject(t.u ? 'UNSAFE' : 'FOREIGN', `Impure definition: ${k}`);
      baseForbidden.add(k);
    }
    if (t.$ === 'Def' && t.v === null && !isBase && !state.primitives.has(k)) reject('OPEN_LAW', `Axiom or open law: ${k}`);
    const refs = new Set();
    for (const term of terms(B, t)) for (const r of references(term)) refs.add(r);
    // ~ binders are scoped constants in Def.e, not global capabilities. Their
    // domains were already traversed in T; only the exact binder names qualify.
    if (t.$ === 'Def' && t.x) {
      let tel = B.term_lower(t.T);
      for (let i = 0; i < t.x && tel.$ === 'All'; i++, tel = tel.B) refs.delete(k + '~' + tel.k);
    }
    graph.set(k, refs);
    if (t.$ === 'ADT') for (const c of t.c) graph.set(c.k, new Set([k, ...references(B.term_lower(c.T))]));
  }
  // Backward closure marks every Base wrapper of an effect/opaque handle. No
  // substring filtering: a client can name a pure function IO_print or unsafe.
  let grew;
  do {
    grew = false;
    for (const [k, refs] of graph) {
      if (baseNames.has(origin(k)) && !baseForbidden.has(k) && [...refs].some(r => baseForbidden.has(r))) {
        baseForbidden.add(k); grew = true;
      }
    }
  } while (grew);
  const kernelIO = new Set(['IO', 'IO.OP', 'Emit', 'Halt', 'Exit', 'IO.pure', 'IO.bind']);
  for (const [k, refs] of graph) {
    if (baseNames.has(origin(k)) || state.baseCtors.has(k)) continue;
    const rec = owners.get(origin(k));
    const trustedIO = state.plan.kernel && (rec?.role === 'kernel' || rec?.path === state.plan.entry);
    for (const r of refs) {
      if (baseForbidden.has(r) && !(trustedIO && (kernelIO.has(r) || state.primitives.has(r)))) reject('IO', `External capability: ${k} -> ${r}`);
      if (owners.get(origin(r))?.role === 'kernel' && !trustedIO) reject('KERNEL_CAPTURE', `Pure module reaches kernel: ${k} -> ${r}`);
    }
  }
  // Audit the entire client closure, including types, erased terms, constructors,
  // checked trees, specializations, and helpers never used by the program.
  const roots = new Set([...owners].filter(([, rec]) => rec.role === 'client').map(([k]) => k));
  for (const [k, rec] of fillers) if (rec.role === 'client') roots.add(k);
  const closure = new Set(roots);
  for (const k of closure) {
    const inst = state.plan.records.get(state.plan.canonicalRefs.instance)?.ns;
    if (state.plan.certificateMode === 'universal' && [inst + ':context', inst + ':arguments'].includes(origin(k)))
      reject('HOST_CAPTURE', `Reusable client reaches a concrete preparation value: ${k}`);
    const rec = owners.get(origin(k));
    if (rec?.role === 'kernel') reject('KERNEL_CAPTURE', `Client reaches kernel: ${k}`);
    if (rec?.role === 'host' && !rec.exports.has(origin(k)) && !fillers.has(origin(k))) {
      reject('HOST_CAPTURE', `Client reaches private host symbol: ${k}`);
    }
    if (baseForbidden.has(k)) reject('IO', `External capability: ${k}`);
    for (const r of graph.get(k) ?? []) closure.add(r);
  }
  return closure;
}

/** Returns an opaque checked handle and exact source snapshots. */
export async function admitSubmission(options) {
  return admit(options, false);
}

/** Trusted initialization/preprocessing, with no client or fabricated binding. */
export async function admitKernel(options) {
  return admit(options, true);
}

async function admit(options, kernelOnly) {
  // No frontend code runs until the *entire* explicit graph passes preflight.
  const plan = preflight(options, kernelOnly);
  const tc = await loadToolchain(options.toolchain);
  const { B, S } = tc;
  let state, foreignSnapshot;
  try {
    try {
      const base = fs.readFileSync(B.BASE_BEND);
      if (sha256(base) !== tc.info.files['bend2/base.bend']) throw new Error('Base changed during bootstrap');
      state = parseSnapshots(B, plan, base.toString('utf8'));
      foreignSnapshot = prepareKernel(B, state);
      validateKernelEntry(B, state);
      audit(B, state);
      auditLoopCalls(B, state);
    } catch (cause) {
      if (cause instanceof AdmissionError) throw cause;
      if (!frontendDiagnostic(cause)) {
        throw new AdmissionError('FRONTEND_INFRASTRUCTURE', 'parse', diagnostic(B, cause), { cause });
      }
      throw new AdmissionError('PARSE', 'parse', diagnostic(B, cause), { cause });
    }
    try {
      B.book_valid(state.book);
    } catch (cause) {
      if (!frontendDiagnostic(cause)) {
        const last = state.book.order.filter(k => state.book.tlds[k]?.e).at(-1);
        throw new AdmissionError('FRONTEND_INFRASTRUCTURE', 'primary',
          `Frontend failure after ${last ?? '(none)'}: ${diagnostic(B, cause)}`, { cause });
      }
      throw new AdmissionError('PRIMARY_CHECK', 'primary', diagnostic(B, cause), { cause });
    }
    // book_valid checked every primitive's signature too. Only these exact ABI
    // foreign declarations become Safe's opaque runtime boundary; no other
    // kernel definition/ADT/entry is excluded from its roots.
    for (const k of state.primitives) state.book.tlds[k].b = true;
    const closure = audit(B, state);
    auditLoopCalls(B, state);
    if (!kernelOnly) assertBindings(B, state.book, plan, false);
    assertInitialization(B, state.book, plan);
    const checkedDefinitions = Object.entries(state.book.tlds).map(([k, t]) => [k, t, t.T, t.v, t.e, t.n, t.x, t.b]);
    try {
      state.verifier = checkBook(S, state.book, tc.info.verifier);
      // The source Book has already passed the primary checker. A negative
      // result for its translated payload establishes pipeline disagreement,
      // not absence of a derivation for the original source certificate.
      if (state.verifier.why !== null) throw new AdmissionError('BENDTT_INFRASTRUCTURE', 'bendtt',
        'Primary checker accepted but the official kernel rejected the translated Book:\n' + state.verifier.why);
      // Official Safe may add symbolic template constants. Preserve those,
      // while the existing checked definitions remain the ones sent to C.
      if (checkedDefinitions.some(([k, t, T, v, e, n, x, b]) =>
        state.book.tlds[k] !== t || t.T !== T || t.v !== v || t.e !== e || t.n !== n || t.x !== x || t.b !== b)) {
        throw new Error('Official Safe changed a checked definition');
      }
    } catch (cause) {
      if (cause instanceof AdmissionError) throw cause;
      throw new AdmissionError('BENDTT_INFRASTRUCTURE', 'bendtt', cause.stack ?? cause.message, { cause });
    }
    const sourceRecords = [...plan.records.values(), ...(plan.kernel ? [{ ...plan.kernel.foreign, role: 'kernel-foreign' }] : [])];
    const sources = Object.freeze(sourceRecords.map(r => Object.freeze({ path: r.path, role: r.role, sha256: r.sha256, bytes: r.bytes, text: r.text })));
    const kernel = plan.kernel && Object.freeze({ module: plan.kernel.module,
      primitives: Object.freeze([...state.primitives]), foreign: Object.freeze({ path: plan.kernel.foreign.path, sha256: plan.kernel.foreign.sha256 }),
      loopStep: plan.kernel.loopStep,
      contract: plan.kernel.primitives.includes('loop') ? 'jaydb-native-io-v2' : 'jaydb-native-io-v1', boundary: 'trusted-runtime-effects' });
    const report = Object.freeze({ version: tc.info.version, primary: true, bendtt: true,
      purpose: plan.purpose, certificateMode: plan.certificateMode, readOnly: plan.readOnly, canonicalRefs: plan.canonicalRefs, kernel,
      initialization: plan.purpose === 'initialize' ? Object.freeze({ ...plan.initialization }) : null,
      toolchainSha256: sha256(JSON.stringify([tc.info.version, tc.info.files, tc.info.kernelSha256])),
      verifier: Object.freeze({ ...tc.info.verifier, inputSha256: state.verifier.inputSha256 }),
      sourceSetSha256: sha256(JSON.stringify(sources.map(({ path, sha256 }) => [path, sha256]).sort())),
      sources: Object.freeze(sources.map(({ text, ...r }) => Object.freeze(r))),
      targets: Object.freeze(Object.keys(plan.openTargets)), clientClosureSize: closure.size });
    const result = Object.freeze({ sources, report });
    admittedBooks.set(result, { tc, book: state.book, foreignSnapshot });
    if (foreignSnapshot) sourceCleanup.register(result, foreignSnapshot, result);
    return result;
  } catch (e) { removeForeignSnapshot(foreignSnapshot); throw e; }
}

// Only the pinned frontend's diagnostic record establishes a source rejection.
// IO errors, internal exceptions and incomplete lookalike markers establish no
// mathematical verdict. Client source is parsed as data, never executed here.
function frontendDiagnostic(cause) {
  return cause !== null && typeof cause === 'object' && cause.$ === 'Err'
    && ['bok', 'ctx', 'exp', 'obs', 'spn', 'def', 'nte'].every(key => Object.hasOwn(cause, key))
    && cause.bok !== null && typeof cause.bok === 'object'
    && Array.isArray(cause.bok.order) && cause.bok.tlds !== null && typeof cause.bok.tlds === 'object'
    && (cause.ctx?.$ === 'Emp' || cause.ctx?.$ === 'Bin')
    && (typeof cause.exp === 'string' || (cause.exp !== null && typeof cause.exp === 'object'));
}

function diagnostic(B, cause) {
  if (frontendDiagnostic(cause)) {
    try { return B.err_show(cause); }
    catch { return 'The checker rejected the derivation; diagnostic expansion exceeded frontend resources.'; }
  }
  return cause?.stack ?? cause?.message ?? String(cause);
}

/** Emits from the very same checked object; never reloads request files. */
function checkedState(admitted) {
  const state = admittedBooks.get(admitted);
  if (!state) throw new AdmissionError('BOOK_CHANGED', 'compile', 'Invalid admission handle');
  return state;
}

/** Read only the three logical limits; never expose the checked AST. */
export function configurationLimits(admitted) {
  const { tc: { B }, book } = checkedState(admitted);
  const nat = value => {
    let count = 0n;
    for (;;) {
      value = B.term_strip(value);
      if (value.$ === 'Lit' && value.k === 'Nat') {
        if (!Number.isSafeInteger(value.v) || value.v < 0) throw new Error('Inexact Nat metadata');
        return count + BigInt(value.v);
      }
      let head = value, args = [];
      while (head.$ === 'App') { args.unshift(head.x); head = B.term_strip(head.f); }
      if (head.$ === 'Ref' && args.length === 2 && ['Nat.add', 'Nat.mul', 'Nat.sub', 'Nat.min', 'Nat.max'].includes(head.k)) {
        const a = nat(args[0]), b = nat(args[1]);
        return count + ({ 'Nat.add': () => a + b, 'Nat.mul': () => a * b,
          'Nat.sub': () => a > b ? a - b : 0n, 'Nat.min': () => a < b ? a : b,
          'Nat.max': () => a > b ? a : b }[head.k])();
      }
      if (value.$ === 'Ctr' && value.k === 'Zero') return count;
      if (value.$ === 'Ctr' && value.k === 'Succ') { count++; value = value.x[0]; continue; }
      const reduced = B.term_wnf(book, value);
      if (reduced === value) throw new Error('Expected closed Nat in configuration');
      value = reduced;
    }
  };
  const limits = B.term_wnf(book, B.App(B.Ref('Semantics:limits'), B.Ref('Configuration:config')));
  if (limits.$ !== 'Ctr' || limits.k !== 'Semantics:Limits' || limits.x.length !== 3) throw new Error('Invalid configuration limits');
  return Object.freeze(Object.fromEntries(['message', 'state', 'response'].map((name, i) => [name, String(nat(limits.x[i]))])));
}

export function emitC(admitted) {
  const s = checkedState(admitted);
  try {
    if (s.c !== undefined) return s.c;
    validateForeignSnapshot(s.foreignSnapshot);
    s.c = s.tc.C.compile_book(s.book);
    removeForeignSnapshot(s.foreignSnapshot);
    sourceCleanup.unregister(admitted);
    return s.c;
  } catch (cause) {
    throw new AdmissionError('COMPILE', 'compile', cause.message ?? String(cause), { cause });
  }
}
