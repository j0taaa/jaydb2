// The semantic Book graph includes constructor identities/order and all metadata.
// Only source spans are diagnostic; reduction cells remain represented by value.
import { createHash } from 'node:crypto';

// Prototype identity and descriptors matter even when Object.keys sees no
// change: the compiler uses ordinary JS lookup for optional metadata. Keep
// process-local identities only for functions/symbols/prototypes, never for
// generated lowered nodes. Do not invoke getters or inherited toJSON hooks.
const identities = new WeakMap(), symbols = new Map();
let nextIdentity = 0;
const identity = value => {
  const ids = typeof value === 'symbol' ? symbols : identities;
  if (!ids.has(value)) ids.set(value, ++nextIdentity);
  return ids.get(value);
};
const descriptor = Object.getOwnPropertyDescriptor;
const prototype = Object.getPrototypeOf;
const ownKeys = Reflect.ownKeys;
const mapEntries = Function.call.bind(Map.prototype.entries);
const setValues = Function.call.bind(Set.prototype.values);
const stringify = JSON.stringify;
function hashGraph(hash, B, root, canonicalMemos = false) {
  const seen = new Map();
  const primitives = new Map();
  let chunks = [], size = 0;
  const emit = text => {
    chunks.push(text); size += text.length;
    if (size >= 65536) { hash.update(chunks.join('')); chunks = []; size = 0; }
  };
  const write = value => {
    if (value === null) { emit('null;'); return; }
    const kind = typeof value;
    if (kind === 'function' || kind === 'symbol') { emit(kind + identity(value) + ';'); return; }
    if (kind !== 'object') {
      let text = primitives.get(value);
      if (text === undefined) { text = kind + ':' + stringify(String(value)) + ';'; primitives.set(value, text); }
      emit(text); return;
    }
    if (seen.has(value)) { emit('ref:' + seen.get(value) + ';'); return; }
    seen.set(value, seen.size);
    const proto = prototype(value);
    emit('object:proto:' + (proto === null ? 'null' : identity(proto)) + '{');
    if (!seen.has(proto)) write(proto);
    if (value instanceof Map) { emit('map['); for (const pair of mapEntries(value)) { write(pair[0]); write(pair[1]); } emit(']'); }
    if (value instanceof Set) { emit('set['); for (const entry of setValues(value)) write(entry); emit(']'); }
    // A reduction cell is represented by its forced semantic value. Its
    // internal i/v sharing/path compression may legitimately change in WNF.
    const memo = canonicalMemos && descriptor(value, '$')?.value === 'Var' && descriptor(value, 'i')?.value < 0 && descriptor(value, 'v')?.value !== undefined;
    for (const key of ownKeys(value)) {
      if (key === 's' || memo && (key === 'i' || key === 'v')) continue;
      write(key);
      const d = descriptor(value, key);
      emit(d.enumerable ? 'enumerable:' : 'hidden:');
      if ('value' in d) write(d.value);
      else { emit('accessor:'); write(d.get); write(d.set); }
    }
    if (memo) { emit('forced:'); write(B.term_lower(value)); }
    emit('}');
  };
  write(root);
  if (chunks.length) hash.update(chunks.join(''));
}
const term = (B, t) => t == null ? t : B.term_lower(t);
const ctor = (B, c) => ({ ...c, T: term(B, c.T) });
export function bookFingerprint(B, book) {
  const graph = { ...book,
    tlds: Object.entries(book.tlds).map(([k, t]) => [k, { ...t, T: term(B, t.T),
      ...(t.$ === 'ADT' ? { c: t.c.map(c => ctor(B, c)) }
        : { v: term(B, t.v), e: t.e === undefined ? undefined : term(B, B.term_higher(t.e)) }) }]),
    ctrs: Object.entries(book.ctrs).map(([k, c]) => [k, ctor(B, c)]),
    tmps: Object.entries(book.tmps).map(([k, variants]) => [k, [...variants]]),
  };
  const hash = createHash('sha256');
  hashGraph(hash, B, graph);
  // The first view retains canonical HOAS/memo semantics. This second view
  // also seals original prototypes, hidden fields and physical term metadata
  // which rebuilding a lowered node (or spreading a declaration) would lose.
  hashGraph(hash, B, book, true);
  return hash.digest('hex');
}

function freezeData(roots) {
  const seen = new Set(), todo = [...roots];
  while (todo.length) {
    const value = todo.pop();
    if (value === null || !['object', 'function'].includes(typeof value) || seen.has(value)) continue;
    seen.add(value);
    if (value instanceof Map || value instanceof Set) {
      for (const entry of value instanceof Map ? [...value].flat() : value) todo.push(entry);
      if (!Object.isFrozen(value)) {
        const denied = () => { throw new Error('Mutation after verification is forbidden'); };
        for (const method of value instanceof Map ? ['set', 'delete', 'clear'] : ['add', 'delete', 'clear'])
          Object.defineProperty(value, method, { value: denied });
      }
    }
    for (const key of ownKeys(value)) if (key !== 's') {
      const d = Object.getOwnPropertyDescriptor(value, key);
      if ('value' in d) todo.push(d.value);
      else todo.push(d.get, d.set);
    }
    if (value.$ === 'Var' && value.i < 0 && value.v !== undefined) {
      // These are the only two fields written by the pinned WNF/conversion
      // runtime. Their value is NOT omitted from bookFingerprint.
      for (const key of ownKeys(value)) if (key !== 'i' && key !== 'v') {
        const d = Object.getOwnPropertyDescriptor(value, key);
        Object.defineProperty(value, key, { ...d, ...('value' in d ? { writable: false } : {}), configurable: false });
      }
      Object.seal(value);
    } else Object.freeze(value);
  }
}

const closedBooks = new WeakSet();
export function closeEmissionBook(B, book) {
  const roots = [];
  for (const t of Object.values(book.tlds)) {
    roots.push(t, term(B, t.T));
    if (t.$ === 'ADT') for (const c of t.c) roots.push(term(B, c.T));
    else {
      if (t.v) roots.push(term(B, t.v));
      if (t.e) roots.push(term(B, B.term_higher(t.e)));
    }
  }
  for (const c of Object.values(book.ctrs)) roots.push(c, term(B, c.T));
  roots.push(book.order, ...Object.values(book.tmps));
  freezeData(roots);
  if (closedBooks.has(book)) return;
  // The compiler's IO analysis shadows entries in a scratch child table.
  // Keep that possible without allowing writes to the actual checked table.
  const table = value => {
    Object.seal(value);
    const denied = () => { throw new Error('Declaration after verification is forbidden'); };
    let closed;
    closed = new Proxy(value, { set(target, key, next, receiver) {
      if (receiver === closed) return denied();
      return Reflect.set(target, key, next, receiver);
    }, defineProperty: denied, deleteProperty: denied, setPrototypeOf: denied });
    return closed;
  };
  book.tlds = table(book.tlds); book.ctrs = table(book.ctrs); book.tmps = table(book.tmps);
  Object.freeze(book);
  closedBooks.add(book);
}
