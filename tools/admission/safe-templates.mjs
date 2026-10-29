// Reviewed adapter over the hash-pinned Safe source. Templates are compile-time
// schemas, not closed values for which a theorem prover must invent inhabitants.
const once = (source, anchor, replacement) => {
  if (source.split(anchor).length !== 2) throw new Error('Safe stage anchor changed: ' + anchor.slice(0, 90));
  return source.replace(anchor, replacement);
};

export function adaptSafeTemplates(source) {
  source = once(source, 'type Probe = { left: number; depth: number; cut: boolean };',
    'type Probe = { left: bigint; depth: number; cut: boolean };');
  source = once(source, 'const MODEL_FUEL = 1 << 22;', `let MODEL_FUEL = 1n << 22n;
let ADMISSION_DEADLINE: bigint | null = null;
let ADMISSION_SCHEMAS: string[] = [];
let ADMISSION_INSTANCES: string[] = [];
let ADMISSION_SOURCE_CLAIMS = new Map<string, B.LTerm>();
export class SafeResourceExhausted extends Error {
  code = "SAFE_MODEL_EXHAUSTED";
}
export class SafeDeadlineExceeded extends Error {
  code = "HOST_VERIFICATION_DEADLINE";
}
class AdmissionInstanceRequest extends Error {
  constructor(public name: string, public parameters: HTerm[]) { super("Closed template instance needed: " + name); }
}
function admission_deadline(): void {
  if (ADMISSION_DEADLINE !== null && process.hrtime.bigint() >= ADMISSION_DEADLINE)
    throw new SafeDeadlineExceeded("Host verification deadline expired during Safe elaboration");
}`);
  source = once(source, 'for (; probe.cut && probe.left > 0; probe.depth *= 2)',
    'for (; probe.cut && probe.left > 0n; probe.depth *= 2)');
  source = once(source, '  return m;\n}\n\n// a datatype\'s key',
    '  if (probe.cut && probe.left <= 0n) throw new SafeResourceExhausted("Safe model budget exhausted");\n  return m;\n}\n\n// a datatype\'s key');
  source = once(source, '  if (path.length + d > probe.depth || probe.left <= 0) {',
    '  admission_deadline();\n  if (path.length + d > probe.depth || probe.left <= 0n) {');
  source = once(source, '  probe.left -= 1;', '  probe.left -= 1n;');
  source = once(source, '      probe.left -= key.length;', '      probe.left -= BigInt(key.length);');
  source = once(source, '  const tld = e.book.tlds[k];\n  const ns: string[] = [];',
    '  admission_deadline();\n  const tld = e.book.tlds[k];\n  if (tld.$ === "Def" && tld.x > 0) return admission_schema(e, k);\n  const ns: string[] = [];');
  source = once(source, 'function term(e: Safe, s0: Scope, t: HTerm, live: boolean): O {\n  const [x, T] = open(t);',
    'function term(e: Safe, s0: Scope, t: HTerm, live: boolean): O {\n  if ((e as any).admissionStage && !live) { const annotation = open(t)[1]; t = typed(B.term_snf(e.book, t), annotation); }\n  const [x, T] = open(t);');
  source = once(source, '  const [f, T] = open(h);\n  if (f.$ !== "Ref") {', `  const [f, T] = open(h);
  const stage = (e as any).admissionStage;
  if (stage && f.$ === "Ref") {
    const bound = stage.refs.get(f.k);
    if (bound !== undefined) return args(e, s, bound.o, bound.T, xs, live);
    const inst = e.inst.get(f.k);
    const name = inst?.[0] ?? f.k;
    const header = stage.refs.get(name) ?? stage.header(name);
    if (header !== undefined) return args(e, s, header.o, header.T, [...(inst?.[1] ?? []), ...xs], live);
  }
  // A physical instance is the exact checked tree consumed by compile_book.
  // Keep calls linked to that declaration, not to a fresh specialization of
  // the generic template body. The latter could hide an instance mutation.
  if (f.$ === "Ref" && e.inst.has(f.k)) {
    const concrete = e.book.tlds[f.k];
    if (concrete?.$ === "Def" && concrete.x === 0) return args(e, s, f.k, concrete.T, xs, live);
  }
  if (f.$ !== "Ref") {`);
  source = once(source, '    if (q === 1 && uses(e, f, l) > 1) {',
    '    if (!(e as any).admissionStage && q === 1 && uses(e, f, l) > 1) {');
  source = once(source, 'const r2: Q = uses(e, body, lt) > 1 || uses(e, body, la) > 1 ? 2 : q;',
    'const r2: Q = !(e as any).admissionStage && (uses(e, body, lt) > 1 || uses(e, body, la) > 1) ? 2 : q;');
  source = once(source, 'q: q === 1 && uses(e, b, l) > 1 ? 2 : q, l, v, f: b',
    'q: !(e as any).admissionStage && q === 1 && uses(e, b, l) > 1 ? 2 : q, l, v, f: b');
  const roots = 'for (const k of [...new Set([...book.order].reverse())].reverse().filter((k) => book.tlds[k].b !== true)) {';
  source = once(source, roots, `for (const k of admission_roots(e)) {`);
  source = once(source, '  for (let it = e.todo.pop(); it !== undefined; it = e.todo.pop()) {',
    '  admission_source_links(e);\n  for (let it = e.todo.pop(); it !== undefined; it = e.todo.pop()) {');
  source = once(source, '  const nx = tld?.$ === "Def" ? tld.x : 0;\n  const ps: Arg[] = [];', `  const nx = tld?.$ === "Def" ? tld.x : 0;
  if (nx > 0 && xs.length >= nx) {
    // Preserve the official argument key, rather than normalizing a different
    // logical specialization. Only variables actually specialized in Scope
    // are substituted. Open generic parameters continue through schema binders.
    const prefix = xs.slice(0, nx).map(x => {
      const value = subst(x, s.d, o => o.$ === "Var" && (o.i as number) >= 0 && (o.i as number) < s.d
        ? s.c[o.i as number]?.v ?? B.Var(o.k as Name, o.i as number) : undefined);
      return admission_open_argument(e, s, value) ? null : value;
    });
    if (prefix.every(x => x !== null)) {
      const name = B.admission_instance(e.book, k as Name, prefix as HTerm[]);
      const concrete = name === undefined ? undefined : e.book.tlds[name];
      if (concrete?.$ === "Def" && concrete.x === 0)
        return args(e, s, name as Name, concrete.T, xs.slice(nx), live);
      // Only the prospective pass catches this request. The final translation
      // cannot manufacture an independent .qv definition from a generic body.
      throw new AdmissionInstanceRequest(k as Name, prefix as HTerm[]);
    }
    if (!live) {
      // Open template calls in a TYPE can also occur in an ordinary def.
      // If conversion really closes them, retain physical resolution below;
      // otherwise use the checked erased body, never model an inhabitant.
      const normal = xs.slice(0, nx).map(x => closed_val(e, s, x));
      if (normal.some(x => x === null || admission_open_argument(e, s, x)))
        return args(e, s, admission_projection(admission_body(e, k as Name)), tld!.T, xs, false);
    }
  }
  const ps: Arg[] = [];`);
  source = once(source, '  // a call that closed a live cycle goes again, through its group', `  if (nx > 0 && ps.length >= nx) {
    // A syntactically open argument may normalize to a closed value (for
    // example ignore(runtimeVariable)). It must use a physical instance too.
    const prefix = ps.slice(0, nx).map(p => p[3] as HTerm);
    const name = B.admission_instance(e.book, k as Name, prefix);
    const concrete = name === undefined ? undefined : e.book.tlds[name];
    if (concrete?.$ === "Def" && concrete.x === 0)
      return args(e, s, name as Name, concrete.T, xs.slice(nx), live);
    throw new AdmissionInstanceRequest(k as Name, prefix);
  }
  // a call that closed a live cycle goes again, through its group`);
  return source + helpers;
}

const helpers = `
import { prepareClosedInstances, resolvePhysicalInstance, instanceSourceClaims, instanceClosureFingerprint } from "jaydb:admission-closure";
// A scoped symbolic Ref has no level index, but is still not globally closed.
// Never send one to the physical resolver or select an arbitrary inhabitant.
function admission_open_argument(e: Safe, s: Scope, value: HTerm): boolean {
  const locals = (e as any).admissionStage?.locals as Set<string> | undefined;
  const visit = (node: any): boolean => {
    if (node === null || typeof node !== "object") return false;
    if (node.$ === "Var" && node.i >= 0 && node.i < s.d) return true;
    if (node.$ === "Ref" && locals?.has(node.k)) return true;
    return Object.entries(node).some(([key, child]) => key !== "s" && visit(child));
  };
  return visit(B.term_lower(value, s.d));
}
export function admission_prepare_book(book: Book, options: {deadlineNs?: string} = {}) {
  try {
    const initial = new Set(Object.keys(book.tlds));
    let rewrites = 0;
    let fuel = 1n << 22n;
    for (;;) {
      const prepared = prepareClosedInstances(B, book, options);
      rewrites += prepared.rewrites;
      const previous = [MODEL_FUEL, ADMISSION_DEADLINE, ADMISSION_SCHEMAS, ADMISSION_INSTANCES, ADMISSION_SOURCE_CLAIMS] as const;
      MODEL_FUEL = fuel;
      ADMISSION_DEADLINE = options.deadlineNs === undefined ? null : BigInt(options.deadlineNs);
      ADMISSION_SCHEMAS = []; ADMISSION_INSTANCES = [];
      ADMISSION_SOURCE_CLAIMS = instanceSourceClaims(book);
      try {
        admission_deadline();
        // Run the real translator prospectively too: beta substitutions in
        // codomains can reveal closed calls absent from the original syntax.
        const before = instanceClosureFingerprint(B, book);
        safe_book(admission_snapshot(book));
        admission_deadline();
        // Trusted WNF may change sharing cells during the prospective pass.
        // Repeat until their represented graph is stable too, so no fresh
        // argument key can first appear after the final primary/audit phase.
        if (instanceClosureFingerprint(B, book) !== before) continue;
        return { ...prepared, rewrites, created: Object.keys(book.tlds).filter(k => !initial.has(k)) };
      } catch (error) {
        if (error instanceof AdmissionInstanceRequest) {
          resolvePhysicalInstance(B, book, error.name, error.parameters);
          continue;
        }
        if (error instanceof SafeResourceExhausted) { fuel *= 2n; continue; }
        throw error;
      } finally {
        [MODEL_FUEL, ADMISSION_DEADLINE, ADMISSION_SCHEMAS, ADMISSION_INSTANCES, ADMISSION_SOURCE_CLAIMS] = previous;
      }
    }
  }
  catch (error) {
    if ((error as any)?.code === "HOST_VERIFICATION_DEADLINE") throw new SafeDeadlineExceeded((error as Error).message);
    throw error;
  }
}

function admission_snapshot(book: Book): Book {
  return { ...book, tlds: { ...book.tlds }, tmps: Object.fromEntries(Object.entries(book.tmps).map(([k, v]) => [k, new Map(v)])) };
}

// A source-link is a kernel conversion check, not an alternative definition.
// Both the certificate and compiler still name the exact physical declaration.
function admission_source_links(e: Safe): void {
  for (const [k, expected] of ADMISSION_SOURCE_CLAIMS) {
    admission_deadline();
    const T = e.book.tlds[k].T;
    const s = scope_nil();
    const equality: O = { $: "Eql", T: term(e, s, T, false),
      // Compare the actual physical body itself. The kernel intentionally
      // keeps recursive references opaque in conversion, so eta(explicit Ref)
      // need not convert to its own lambda-match even for an unchanged body.
      a: arg_term(e, s, B.term_higher((e.book.tlds[k] as Def).e as B.LTerm), T, false),
      b: arg_term(e, s, B.term_higher(expected), T, false) };
    const payload: O = { $: "Ann", x: { $: "Rfl" }, T: equality };
    e.out.push([fresh(e, name_tt(k) + ".source_link"), UT, { $: "Let", q: 0, l: 0, v: payload, f: UV }, false]);
  }
}

// All physical closed instances minted by the primary are claims too, even
// though upstream book_valid intentionally leaves them outside book.order.
function admission_roots(e: Safe): Name[] {
  const roots = [...new Set([...e.book.order].reverse())].reverse().filter(k => e.book.tlds[k].b !== true);
  for (const [name, def] of Object.entries(e.book.tlds)) {
    if (def.b !== true && !roots.includes(name)) {
      roots.push(name);
      ADMISSION_INSTANCES.push(name);
    }
  }
  return roots;
}

// A symbolic template's actual checked body lives in an ERASED Sigma field.
// It is never a function/proposition constant usable by live certificates. Its
// projection is used only while checking erased schemas, preserving the source
// equations (including case reduction and recursive calls), not arbitrary
// hypotheses about functions with the same header.
type AdmissionBody = { name: string, T?: O, body?: O };
function admission_bundle_type(T: O): O {
  return { $: "Sig", q: 0, l: 0, A: T, B: UT };
}
function admission_projection(body: AdmissionBody): O {
  const T = body.T ?? oos("a cyclic template type without a checked header");
  const projection: O = { $: "Ann", x: { $: "Prj", h:
    { $: "Lam", q: 0, l: 0, f: { $: "Lam", q: 1, l: 1, f: { $: "Var", l: 0 } } } },
    T: { $: "All", q: 1, l: 0, A: admission_bundle_type(T), B: T } };
  return { $: "App", q: 1, f: projection, x: { $: "Ref", k: body.name } };
}
function admission_body(e: Safe, k: Name): AdmissionBody {
  const bodies: Map<Name, AdmissionBody> = (e as any).admissionBodies ??= new Map();
  const prior = bodies.get(k);
  if (prior !== undefined) return prior;
  admission_deadline();
  const tld = e.book.tlds[k] as Def;
  if (tld.e === undefined) oos("a template without its primary checked tree");
  const item: AdmissionBody = { name: fresh(e, name_tt(k) + ".template_body") };
  // Use the translator's own mutation trail, so a failed root cannot leave a
  // cached reference to an item which undo removed from the output.
  put(e, bodies as any, k, item as any);
  const book = { ...e.book, tlds: Object.assign(Object.create(null), e.book.tlds) };
  const se: Safe = { ...e, book, mb: { ...book, tlds: Object.create(book.tlds) } };
  const stage = { refs: new Map<string, {o: O, T: HTerm}>(), locals: new Set<string>(),
    header: (name: Name): {o: O, T: HTerm} | undefined => {
      const def = e.book.tlds[name];
      return def?.$ === "Def" && def.x > 0
        ? { o: admission_projection(admission_body(e, name)), T: def.T } : undefined;
    } };
  (se as any).admissionStage = stage;
  // The full original type is closed; symbolic calls in it use actual bodies
  // too. No outer binder is added while translating an inner Scope.
  item.T = term(se, scope_nil(), tld.T, false);
  let s = scope_nil(), T = tld.T;
  const binders: Binder[] = [];
  for (let j = 0; j < tld.x; j++) {
    admission_deadline();
    const F = B.term_wnf(book, T);
    if (F.$ !== "All") oos("template prefix exceeds its telescope");
    const name = k + "~" + F.k;
    const domain = B.term_snf(book, F.A);
    const A = term(se, s, domain, false);
    const o: O = { $: "Var", l: s.D };
    binders.push([quant(F.q), s.D, A]);
    stage.refs.set(name, { o, T: domain });
    stage.locals.add(name);
    book.tlds[name] = { $: "Def", n: 0, x: 0, T: F.A, v: null, b: true };
    s = scope_hide(s); T = F.B(B.Ref(name));
  }
  item.body = lams(se, binders, tree(se, s, B.term_higher(tld.e as B.LTerm), []));
  e.out.push([item.name, admission_bundle_type(item.T), { $: "Tup", q: 0, a: item.body, b: UV }, false]);
  return item;
}
function admission_schema(e: Safe, k: Name): [string[], string | null] {
  const item = admission_body(e, k);
  const n = fresh(e, name_tt(k) + ".compile_schema");
  const payload: O = { $: "Ann", x: item.body as O, T: item.T as O };
  e.out.push([n, UT, { $: "Let", q: 0, l: 0, v: payload, f: UV }, false]);
  ADMISSION_SCHEMAS.push(k);
  return [[n], null];
}

export function admission_safe_emit(book: Book, out: string, options: { modelFuel?: string, deadlineNs?: string } = {}): {oos: string[], schemas: string[], instances: string[], modelFuel: string, modelAttempts: string} {
  admission_prepare_book(book, options);
  const previous = [MODEL_FUEL, ADMISSION_DEADLINE, ADMISSION_SCHEMAS, ADMISSION_INSTANCES, ADMISSION_SOURCE_CLAIMS] as const;
  MODEL_FUEL = BigInt(options.modelFuel ?? "4194304");
  ADMISSION_DEADLINE = options.deadlineNs === undefined ? null : BigInt(options.deadlineNs);
  ADMISSION_SCHEMAS = [];
  ADMISSION_INSTANCES = [];
  ADMISSION_SOURCE_CLAIMS = instanceSourceClaims(book);
  try {
    // Closure is already final. Fuel retries rerun only the translator, on a
    // fresh table snapshot of the SAME Book; they cannot mint declarations or
    // restart either the closure or the host deadline.
    let attempts = 0n;
    for (;;) {
      admission_deadline();
      attempts++;
      ADMISSION_SCHEMAS = []; ADMISSION_INSTANCES = [];
      try {
        const oos = safe_emit(admission_snapshot(book), out);
        admission_deadline();
        return { oos, schemas: [...new Set(ADMISSION_SCHEMAS)], instances: [...new Set(ADMISSION_INSTANCES)],
          modelFuel: MODEL_FUEL.toString(), modelAttempts: attempts.toString() };
      } catch (error) {
        if (!(error instanceof SafeResourceExhausted)) throw error;
        MODEL_FUEL *= 2n;
      }
    }
  } finally {
    [MODEL_FUEL, ADMISSION_DEADLINE, ADMISSION_SCHEMAS, ADMISSION_INSTANCES, ADMISSION_SOURCE_CLAIMS] = previous;
  }
}
`;
