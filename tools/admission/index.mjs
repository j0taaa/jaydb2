import fs from 'node:fs';
import path from 'node:path';
import { loadPinnedGenericCompiler } from './generic.mjs';
import { AdmissionError, loadToolchain, sha256 } from './bootstrap.mjs';
import { preflight } from './preflight.mjs';
import { prepareKernel, auditLoopCalls, validateKernelEntry, validateForeignSnapshot, removeForeignSnapshot } from './kernel.mjs';
import { checkBook } from '../verifier/check.mjs';
import { bookFingerprint as seal } from './book-graph.mjs';

export { AdmissionError, bootstrapInfo } from './bootstrap.mjs';
export { preflight } from './preflight.mjs';

const admittedBooks = new WeakMap();
const sourceCleanup = new FinalizationRegistry(removeForeignSnapshot);
const reject = (code, message) => { throw new AdmissionError(code, 'policy', message); };

function walk(term, visit) {
  const todo = [term], seen = new Set();
  while (todo.length) {
    const t = todo.pop();
    if (!t || typeof t !== 'object' || seen.has(t)) continue;
    seen.add(t);
    visit(t);
    for (const [k, v] of Object.entries(t)) if (k !== 's' && v && typeof v === 'object') todo.push(v);
  }
}

function references(term) {
  const refs = new Set();
  walk(term, t => {
    if (t.$ === 'Hol') reject('META', `Metavariável: ${t.k}`);
    // Match tags and literals matter too; merely scanning Ref misses them.
    if (['Ref', 'ADT', 'Ctr', 'Mat', 'Lit', 'PCtr'].includes(t.$)) refs.add(t.k);
  });
  return refs;
}

function terms(B, t) {
  return [B.term_lower(t.T), ...(t.$ === 'ADT' ? t.c.map(c => B.term_lower(c.T))
    : [...(t.v ? [B.term_lower(t.v)] : []), ...(t.e ? [t.e] : [])])];
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
    [bind + ':certificado']: app(canonical.contractPrefix + 'Requisitos:Certifica', inst + ':config', bind + ':codigo', client + ':programa', inst + ':contexto', inst + ':argumentos'),
    [bind + ':termina']: app(canonical.contractPrefix + 'Interface:ProgramaTermina', inst + ':config', client + ':programa'),
  };
  for (const [k, T] of Object.entries(expected)) {
    const t = book.tlds[k];
    if (!t || t.$ !== 'Def' || !t.l || !sameTerm(B, t.T, T) || (mustBeOpen && t.v !== null)) {
      reject('TARGET', `Alvo do host incorreto: ${k}`);
    }
  }
  const code = book.tlds[bind + ':codigo'];
  const v = code?.v && B.term_lower(code.v);
  if (code?.$ !== 'Def' || code.n !== 0 || !sameTerm(B, code.T, B.Ref('String'))
      || v?.$ !== 'Lit' || v.k !== 'String' || v.v !== plan.records.get(canonical.client).text) {
    reject('SOURCE_BINDING', `${bind}.codigo deve ser o literal exato da fonte ${canonical.client}`);
  }
  return expected;
}

function assertInitialization(B, book, plan) {
  if (plan.purpose !== 'initialize') return {};
  const { configuration, state, proof } = plan.initialization;
  const T = B.App(B.App(B.Ref(plan.canonicalRefs.contractPrefix + 'Requisitos:Valido'), B.Ref(configuration)), B.Ref(state));
  const p = book.tlds[proof];
  if (p?.$ !== 'Def' || !p.l || p.v === null || !sameTerm(B, p.T, T)) {
    reject('INITIALIZATION', `Prova exigida: ${proof} : Requisitos.Valido(${configuration}(), ${state}())`);
  }
  for (const k of [configuration, state]) {
    const t = book.tlds[k];
    if (t?.$ !== 'Def' || t.n !== 0 || t.v === null || t.i !== undefined || t.u) reject('INITIALIZATION', `Valor inicial não é uma definição pura fechada: ${k}`);
  }
  return { [proof]: T };
}

function parseSnapshots(B, plan, base) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', base, '', Object.create(null));
  const baseNames = new Set(Object.keys(book.tlds));
  const baseCtors = new Set(Object.keys(book.ctrs));
  for (const k of baseNames) book.tlds[k].b = true;
  const owners = new Map(), fillers = new Map(), rawTrees = new Map();
  for (const rec of plan.ordered) {
    const before = new Map(Object.entries(book.tlds).map(([k, t]) => [k, { ...t }]));
    const beforeCtors = new Map(Object.entries(book.ctrs));
    B.admission_observe((owner, term) => {
      if (owner !== null) {
        if (!rawTrees.has(owner)) rawTrees.set(owner, new Set());
        rawTrees.get(owner).add(term);
      }
    });
    try {
      B.parse_book(book, path.join(plan.root, path.posix.dirname(rec.path)) + '/', rec.body, rec.ns, rec.aliases);
    } finally { B.admission_observe(null); }
    for (const [k, t] of Object.entries(book.tlds)) {
      const old = before.get(k);
      if (!old) {
        if (!k.startsWith(rec.ns ? rec.ns + ':' : '') || baseNames.has(k)) reject('SHADOW', `Declaração em módulo alheio: ${k}`);
        owners.set(k, rec);
        continue;
      }
      const changed = new Set([...Object.keys(old), ...Object.keys(t)].filter(f => old[f] !== t[f]));
      if (!changed.size) continue;
      if (plan.openTargets[k] !== rec.path || fillers.has(k) || old.$ !== 'Def' || old.v !== null
          || [...changed].some(f => !['n', 'v', 'u', 'i'].includes(f))) {
        reject('REDEFINITION', `Preenchimento não autorizado: ${rec.path} -> ${k}`);
      }
      fillers.set(k, rec);
    }
    for (const [k, c] of Object.entries(book.ctrs)) {
      if (beforeCtors.has(k)) {
        if (beforeCtors.get(k) !== c) reject('REDEFINITION', `Construtor redefinido: ${k}`);
      } else {
        if (baseCtors.has(k) || (rec.ns && !k.startsWith(rec.ns + ':'))) reject('SHADOW', `Construtor em módulo alheio: ${k}`);
        owners.set(k, rec);
      }
    }
    if (!plan.kernelOnly && rec.path === plan.canonicalRefs.bindings) assertBindings(B, book, plan, true);
  }
  for (const k of Object.keys(plan.openTargets)) if (!fillers.has(k)) reject('OPEN_LAW', `Alvo não preenchido: ${k}`);
  if (!plan.kernelOnly) assertBindings(B, book, plan, false);
  assertInitialization(B, book, plan);
  const rawRefs = new Map([...rawTrees].map(([k, trees]) => [k, references([...trees])]));
  return { book, baseNames, baseCtors, owners, fillers, rawRefs, plan, primitives: new Set() };
}

function audit(B, state) {
  const { book, baseNames, owners, fillers } = state;
  if (book.hols !== 0) reject('META', 'Derivação contém metas');
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
    if (t.b === true && !isBase && !state.primitives.has(k)) reject('KERNEL_ABI', `Definição fora da fronteira marcada como Base: ${k}`);
    if (t.u || t.i !== undefined) {
      if (!isBase && (t.u || !state.primitives.has(k))) reject(t.u ? 'UNSAFE' : 'FOREIGN', `Definição impura: ${k}`);
      baseForbidden.add(k);
    }
    if (t.$ === 'Def' && t.v === null && !isBase && !state.primitives.has(k)) reject('OPEN_LAW', `Axioma ou lei aberta: ${k}`);
    const refs = new Set(state.rawRefs.get(k) ?? []);
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
      if (baseForbidden.has(r) && !(trustedIO && (kernelIO.has(r) || state.primitives.has(r)))) reject('IO', `Capacidade externa: ${k} -> ${r}`);
      if (owners.get(origin(r))?.role === 'kernel' && !trustedIO) reject('KERNEL_CAPTURE', `Módulo puro alcança kernel: ${k} -> ${r}`);
    }
  }
  // Audit the entire client closure, including types, erased terms, constructors,
  // checked trees, specializations, and helpers never used by the program.
  const roots = new Set([...owners].filter(([, rec]) => rec.role === 'client').map(([k]) => k));
  for (const [k, rec] of fillers) if (rec.role === 'client') roots.add(k);
  const closure = new Set(roots);
  for (const k of closure) {
    const rec = owners.get(origin(k));
    if (rec?.role === 'kernel') reject('KERNEL_CAPTURE', `Cliente alcança kernel: ${k}`);
    if (rec?.role === 'host' && !rec.exports.has(origin(k)) && !fillers.has(origin(k))) {
      reject('HOST_CAPTURE', `Cliente alcança símbolo privado do host: ${k}`);
    }
    if (baseForbidden.has(k)) reject('IO', `Capacidade externa: ${k}`);
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
      if (sha256(base) !== tc.info.files['bend2/base.bend']) throw new Error('Base mudou durante bootstrap');
      state = parseSnapshots(B, plan, base.toString('utf8'));
      foreignSnapshot = prepareKernel(B, state);
      validateKernelEntry(B, state);
      audit(B, state);
      auditLoopCalls(B, state);
    } catch (cause) {
      if (cause instanceof AdmissionError) throw cause;
      if (cause instanceof RangeError) {
        throw new AdmissionError('FRONTEND_INFRASTRUCTURE', 'parse', diagnostic(B, cause), { cause });
      }
      throw new AdmissionError('PARSE', 'parse', diagnostic(B, cause), { cause });
    }
    try {
      B.book_valid(state.book);
      // First preserve the original source checks. Then close erased calls and
      // replay the original checker on the final graph before capability audit.
      // No checker/emitter is allowed to add a declaration after this loop.
      const created = new Set();
      let rewrites = 0;
      for (;;) {
        const closed = S.admission_prepare_book(state.book);
        for (const k of closed.created) created.add(k);
        rewrites += closed.rewrites;
        const preparedState = seal(B, state.book);
        B.book_valid(state.book);
        const ordered = new Set(state.book.order);
        for (const [k, t] of Object.entries(state.book.tlds)) {
          if (t.$ === 'Def' && t.b !== true && t.e !== undefined && !ordered.has(k)) t.e = B.def_check(state.book, k, t);
        }
        const final = S.admission_prepare_book(state.book);
        for (const k of final.created) created.add(k);
        rewrites += final.rewrites;
        // The original checker can rebuild an annotation which closure then
        // rewrites back to the SAME prepared graph. Events are diagnostics;
        // equality of the complete prepared state is the fixed-point test.
        if (seal(B, state.book) === preparedState) {
          state.instanceClosure = { created: [...created], rewrites, sourceLinks: final.sourceLinks };
          break;
        }
      }
    } catch (cause) {
    if (cause instanceof RangeError) {
      const last = state.book.order.filter(k => state.book.tlds[k]?.e).at(-1);
      throw new AdmissionError('FRONTEND_INFRASTRUCTURE', 'primary',
        `Frontend stack/resource failure after ${last ?? '(none)'}: ${diagnostic(B, cause)}`, { cause });
    }
      throw new AdmissionError('PRIMARY_CHECK', 'primary', diagnostic(B, cause), { cause });
    }
    // book_valid checked every primitive's signature too. Only these exact ABI
    // foreign declarations become Safe's opaque runtime boundary; no other
    // kernel definition/ADT/entry is excluded from its roots.
    for (const k of state.primitives) state.book.tlds[k].b = true;
    const closure = audit(B, state);
    auditLoopCalls(B, state);
    const actualTargets = kernelOnly ? {} : assertBindings(B, state.book, plan, false);
    Object.assign(actualTargets, assertInitialization(B, state.book, plan));
    const primaryClosure = Object.entries(state.book.tlds).map(([k, t]) => [k, t, t.T, t.v, t.e, t.n, t.x, t.b]);
    try {
      if (sha256(fs.readFileSync(tc.info.kernelPath)) !== tc.info.kernelSha256) throw new Error('BendTT mudou durante admissão');
      state.verifier = checkBook(S, state.book, tc.info.verifier, { ...options.verification, actualTargets });
      const why = state.verifier.why;
      if (why !== null) throw new AdmissionError('BENDTT_CHECK', 'bendtt', why);
      if (Object.keys(state.book.tlds).length !== primaryClosure.length || primaryClosure.some(([k, t, T, v, e, n, x, b]) =>
        state.book.tlds[k] !== t || t.T !== T || t.v !== v || t.e !== e || t.n !== n || t.x !== x || t.b !== b)) {
        throw new Error('Safe changed the primary checked closure');
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
      contract: plan.kernel.primitives.some(k => ['loop', 'enter'].includes(k)) ? 'jaydb-native-io-v2' : 'jaydb-native-io-v1', boundary: 'trusted-runtime-effects' });
    const report = Object.freeze({ version: tc.info.version, primary: true, bendtt: true,
      purpose: plan.purpose, canonicalRefs: plan.canonicalRefs, kernel,
      initialization: plan.purpose === 'initialize' ? Object.freeze({ ...plan.initialization }) : null,
    toolchainSha256: sha256(JSON.stringify([tc.info.files, tc.info.kernelSha256, tc.info.frontendObserverSha256, tc.info.safeNumeralsSha256, tc.info.safeStringsSha256, tc.info.safeTemplatesSha256, tc.info.conversionSha256, tc.info.frontendResourcesSha256, tc.info.verifierRunnerSha256, tc.info.verifier, tc.info.frontend])),
      safeNumeralsSha256: tc.info.safeNumeralsSha256,
      safeStringsSha256: tc.info.safeStringsSha256,
      safeTemplatesSha256: tc.info.safeTemplatesSha256,
      frontendResourcesSha256: tc.info.frontendResourcesSha256,
      verifierRunnerSha256: tc.info.verifierRunnerSha256,
      verifier: Object.freeze({ ...tc.info.verifier, fuel: state.verifier.fuel, attempts: state.verifier.attempts,
        modelFuel: state.verifier.modelFuel, modelAttempts: state.verifier.modelAttempts,
        ...(state.verifier.correspondence?{correspondence:Object.freeze(state.verifier.correspondence)}:{}),
        schemas: Object.freeze(state.verifier.schemas), instances: Object.freeze(state.verifier.instances), inputSha256: state.verifier.inputSha256 }),
      instanceClosure: Object.freeze({ ...state.instanceClosure,
        created: Object.freeze(state.instanceClosure.created), sourceLinks: Object.freeze(state.instanceClosure.sourceLinks) }),
      sourceSetSha256: sha256(JSON.stringify(sources.map(({ path, sha256 }) => [path, sha256]).sort())),
      sources: Object.freeze(sources.map(({ text, ...r }) => Object.freeze(r))),
      targets: Object.freeze(Object.keys(plan.openTargets)), clientClosureSize: closure.size });
    const result = Object.freeze({ sources, report });
    admittedBooks.set(result, { tc, book: state.book, foreignSnapshot });
    if (foreignSnapshot) sourceCleanup.register(result, foreignSnapshot, result);
    return result;
  } catch (e) { removeForeignSnapshot(foreignSnapshot); throw e; }
}

function diagnostic(B, cause) {
  if (cause?.$ === 'Err') {
    try { return B.err_show(cause); }
    catch { return 'O checker recusou a derivação; a expansão do diagnóstico excedeu os recursos do frontend.'; }
  }
  return cause?.stack ?? cause?.message ?? String(cause);
}

/** Emits from the very same checked object; never reloads request files. */
function checkedState(admitted) {
  const state = admittedBooks.get(admitted);
  if (!state) throw new AdmissionError('BOOK_CHANGED', 'compile', 'Handle de admissão inválido');
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
  const limits = B.term_wnf(book, B.App(B.Ref('Semantica:limites'), B.Ref('Configuration:config')));
  if (limits.$ !== 'Ctr' || limits.k !== 'Semantica:Limites' || limits.x.length !== 3) throw new Error('Invalid configuration limits');
  return Object.freeze(Object.fromEntries(['mensagem', 'estado', 'resposta'].map((name, i) => [name, String(nat(limits.x[i]))])));
}

export function emitC(admitted) {
  const s = checkedState(admitted);
  if (s.emitter && s.emitter !== 'official') throw new AdmissionError('BACKEND_CHANGED', 'compile', 'Um Book admite apenas um backend de emissão');
  try {
    if (s.c !== undefined) return s.c;
    s.emitter = 'official';
    validateForeignSnapshot(s.foreignSnapshot);
    s.c = s.tc.C.compile_book(s.book);
    removeForeignSnapshot(s.foreignSnapshot);
    sourceCleanup.unregister(admitted);
    return s.c;
  } catch (cause) {
    throw new AdmissionError('COMPILE', 'compile', cause.message ?? String(cause), { cause });
  }
}

/** Generic Nat/Array representation; accepts a pinned backend hash, no callback. */
export async function emitGenericC(admitted, options = {}) {
  const s = checkedState(admitted);
  if (!options || Object.keys(options).some(k => k !== 'backendSha256') || !/^[a-f0-9]{64}$/.test(options.backendSha256)) {
    throw new AdmissionError('BACKEND', 'compile', 'backendSha256 do emissor genérico deve ser fixado pelo host');
  }
  const emitter = 'generic:' + options.backendSha256;
  if (s.emitter && s.emitter !== emitter) throw new AdmissionError('BACKEND_CHANGED', 'compile', 'Um Book admite apenas um backend de emissão');
  if (s.emission) return s.emission;
  s.emitter = emitter;
  s.emission = (async () => {
    try {
      const compiler = await loadPinnedGenericCompiler(s.tc.info.sourceDir, options.backendSha256);
      validateForeignSnapshot(s.foreignSnapshot);
      const c = compiler.compile_book(s.book);
      return Object.freeze({ c, backendSha256: options.backendSha256, compilerSha256: compiler.sourceSha256,
        cSha256: sha256(c), sourceSetSha256: admitted.report.sourceSetSha256,
        toolchainSha256: admitted.report.toolchainSha256, sameCheckedBook: true });
    } catch (cause) {
      if (cause instanceof AdmissionError) throw cause;
      throw new AdmissionError('COMPILE', 'compile', cause.message ?? String(cause), { cause });
    } finally { removeForeignSnapshot(s.foreignSnapshot); sourceCleanup.unregister(admitted); }
  })();
  return s.emission;
}

export async function buildKernel(options, emissionOptions) {
  const admitted = await admitKernel(options);
  return Object.freeze({ admitted, emission: await emitGenericC(admitted, emissionOptions) });
}
