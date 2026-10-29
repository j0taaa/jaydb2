// Close template applications with the original elaborator, before final checks.
// No body already present in the Book is regenerated or replaced here.
import { bookFingerprint } from './book-graph.mjs';
export const instanceClosureFingerprint = bookFingerprint;
const claims = new WeakMap();
export const instanceSourceClaims = book => claims.get(book) ?? new Map();

// A source body is re-elaborated, never copied from the physical body. If two
// physical aliases already exist, preserve the physical reference occurring at
// this source position after checking their original template AND arguments
// with the original definitional equality. This is resolution of the expected
// source call, not replacement of the actual body or merger of declarations.
function alignSourceResolution(B, book, expected, actual) {
  const origins = new Map();
  for (const [template, variants] of Object.entries(book.tmps)) for (const [key, name] of variants)
    if (!origins.has(name) && book.tlds[name] !== undefined)
      origins.set(name, [template, key.split('\n').map(x => B.term_higher(JSON.parse(x)))]);
  const align = (source, physical) => {
    if (source === null || typeof source !== 'object') return source;
    if (source.$ === 'Ref' && physical?.$ === 'Ref' && source.k !== physical.k) {
      const a = origins.get(source.k), b = origins.get(physical.k);
      if (a && b && a[0] === b[0] && a[1].length === b[1].length
          && a[1].every((x, i) => B.term_compare('EQ', book, x, b[1][i])))
        return { ...source, k: physical.k };
    }
    if (Array.isArray(source)) return source.map((x, i) => align(x, physical?.[i]));
    return Object.fromEntries(Object.entries(source).map(([key, value]) =>
      [key, key === 's' ? value : align(value, physical?.[key])]));
  };
  return align(expected, actual);
}
export function resolvePhysicalInstance(B, book, k, args) {
    const def = book.tlds[k];
    const prior = B.admission_instance(book, k, args);
    if (prior !== undefined && book.tlds[prior] !== undefined) return prior;
    // A ghost from a generic local scope has no physical declaration. Keep
    // its reserved name/counter, but check the body anew in the real Book using
    // exactly the tele_check/def_check construction of official def_inst.
    if (prior !== undefined) {
      const lhs = { t: B.Ref(k), n: 0, def: '', qs: [] };
      const T = B.tele_check(book, lhs, def.T, args, B.None(), B.ctx_nil(), 0).tel;
      const inst = { $: 'Def', n: def.n - def.x, x: 0, T,
        v: args.reduce((v, a) => B.term_apply(v, a), def.v), u: def.u };
      book.tlds[prior] = { ...inst, v: null };
      inst.e = B.def_check(book, prior, inst);
      book.tlds[prior] = inst;
      return prior;
    }
    return B.def_inst(book, { t: B.Ref(k), n: 0, def: '', qs: [] }, B.Ref(k), def, args, B.ctx_nil(), 0);
  }
export function prepareClosedInstances(B, book, options = {}) {
  const deadline = options.deadlineNs === undefined ? null : BigInt(options.deadlineNs);
  const checkTime = () => {
    if (deadline !== null && process.hrtime.bigint() >= deadline) {
      const error = new Error('Host verification deadline expired during instance closure');
      error.code = 'HOST_VERIFICATION_DEADLINE'; throw error;
    }
  };
  const isClosed = root => {
    const visit = (node, bound) => {
      if (!node || typeof node !== 'object') return true;
      if (node.$ === 'Var') return node.i < 0 ? node.v !== undefined && visit(node.v, bound) : bound.has(node.i);
      if (node.$ === 'Ref' && book.tlds[node.k] === undefined) return false;
      if (node.$ === 'Lam' || node.$ === 'All') {
        const inner = new Set(bound); inner.add(node.i);
        return (node.$ !== 'All' || visit(node.A, bound)) && visit(node.$ === 'Lam' ? node.f : node.B, inner);
      }
      if (node.$ === 'Let') {
        const inner = new Set([...bound, ...node.i]);
        return node.v.every(x => visit(x, bound)) && visit(node.f, inner);
      }
      return Object.entries(node).every(([k, v]) => k === 's' || visit(v, bound));
    };
    return visit(root, new Set());
  };
  let rewrites = 0;
  const transform = node => {
    checkTime();
    if (!node || typeof node !== 'object') return node;
    // Preserve the original official key before rewriting nested arguments.
    if (node.$ === 'App') {
      const xs = []; let head = node;
      while (head.$ === 'App') { xs.unshift(head.x); head = head.f; }
      while (head.$ === 'Ann') head = head.x;
      const def = head.$ === 'Ref' ? book.tlds[head.k] : undefined;
      if (def?.$ === 'Def' && def.x > 0 && xs.length >= def.x && xs.slice(0, def.x).every(isClosed)) {
        const name = resolvePhysicalInstance(B, book, head.k, xs.slice(0, def.x).map(x => B.term_higher(x)));
        rewrites++;
        return xs.slice(def.x).reduce((f, x) => B.App(f, transform(x)), B.Ref(name, head.s, head.b));
      }
    }
    if (Array.isArray(node)) return node.map(transform);
    return Object.fromEntries(Object.entries(node).map(([k, v]) => [k, k === 's' ? v : transform(v)]));
  };
  const before = new Set(Object.keys(book.tlds));
  const done = new Set();
  const links = new Map();
  // Newly minted instances can reveal further applications in T/e. No bound
  // on passes, instances, key length or depth is introduced.
  for (;;) {
    const next = Object.keys(book.tlds).find(k => !done.has(k));
    if (next === undefined) {
      let more = false;
      for (const [template, variants] of Object.entries(book.tmps)) for (const [encoded, name] of variants) {
        if (links.has(name) || book.tlds[name] === undefined) continue;
        const original = book.tlds[template], concrete = book.tlds[name];
        const xs = encoded.split('\n').map(a => B.term_higher(JSON.parse(a)));
        const expected = { ...concrete, v: xs.reduce((v, x) => B.term_apply(v, x), original.v) };
        // A check result is kept separately. Never overwrite the physical .e.
        const checked = B.def_check(book, name, expected);
        const expectedTree = transform(B.term_lower(B.term_higher(checked)));
        const physicalTree = B.term_lower(B.term_higher(concrete.e));
        links.set(name, alignSourceResolution(B, book, expectedTree, physicalTree));
        more = true;
      }
      if (more || Object.keys(book.tlds).some(k => !done.has(k))) continue;
      break;
    }
    done.add(next); checkTime();
    const def = book.tlds[next];
    if (def.b === true) continue;
    const higher = (object, field) => {
      if (object[field] == null) return;
      const old = B.term_lower(object[field]); const count = rewrites;
      const value = transform(old);
      if (rewrites !== count) object[field] = B.term_higher(value);
    };
    higher(def, 'T');
    if (def.$ === 'ADT') for (const c of def.c) higher(c, 'T');
    else {
      higher(def, 'v');
      if (def.e !== undefined) { const count = rewrites; const value = transform(B.term_lower(B.term_higher(def.e))); if (rewrites !== count) def.e = value; }
    }
  }
  checkTime();
  claims.set(book, links);
  return { rewrites, created: Object.keys(book.tlds).filter(k => !before.has(k)), sourceLinks: [...links.keys()] };
}
