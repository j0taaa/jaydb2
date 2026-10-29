/** Experimental C backend adapter. Does not check/admit a Book or execute it. */
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';

export const COMP_SHA256 = 'efcd6a0c476849fce03faefd718e3058633b2a28ea34d45ca14fa383c726d0ef';
const hash = s => crypto.createHash('sha256').update(s).digest('hex');

/** Load alongside the SAME bend.ts instance used by the gate. No Book reload. */
export async function loadGenericCompiler(bend2Directory) {
  const directory = fs.realpathSync(bend2Directory);
  let source = fs.readFileSync(path.join(directory, 'comp.ts'), 'utf8');
  if (hash(source) !== COMP_SHA256) throw new Error('NATIVE_TOOLCHAIN: comp.ts is not pinned Bend 2.0.39');
  function replace(before, after) {
    if (source.split(before).length !== 2) throw new Error(`NATIVE_PATCH: expected one occurrence: ${before}`);
    source = source.replace(before, after);
  }
  replace('from "./bend.ts"', `from ${JSON.stringify(pathToFileURL(path.join(directory, 'bend.ts')).href)}`);
  // Runtime metadata uses a full machine-word ID, separate from tag/location.
  // A table indexed by that word cannot have more entries than the process can
  // address. Do not impose a smaller source-level constructor/function quota.
  replace('    ms.length > 65536 ? die("an id over 65535")\n      : ms.map((m, i) => `#define ${m} ${i}`));',
    '    ms.map((m, i) => `#define ${m} ${i}`));');
  // WIDE remains a flattening heuristic, not a limit on runtime arity.
  // Native tables and the collector store actual machine-word field counts.
  replace('    while (lay.ks.length > WIDE && lay.ks.length & (lay.ks.length - 1)) {\n      lay.ks.push("w32");\n    }\n', '');
  replace('cids.set(k, [n > WIDE ? 240 + Math.log2(n) : n, Number(FL.hot.has(k)), d]);',
    'cids.set(k, [n, Number(FL.hot.has(k)), d]);');
  replace('  if (entries.some((s) => s.params.length > WIDE)\n    || [...cids.values()].some(([n]) => n > 255)) {\n    die("an arity over " + WIDE);\n  }\n', '');
  replace('{ U32: W32, F32: W32, Nat: W64 }', '{ U32: W32, F32: W32 }');
  // The Book, type identities, constructors, and proofs remain unchanged.
  // These checks choose machine representations, not language meanings.
  replace('const ret = all.B(DUMMY);\n  if (adt.k === "Nat") {',
    'const ret = all.B(DUMMY);\n  if (false && adt.k === "Nat") {');
  // All Nat values remain BOX to retain polymorphic/captured/state layouts.
  // Ownership is explicit: compact predecessor and arithmetic consume their
  // arguments. Disable borrow inference rather than treating a loan as owned.
  replace(`function brw_of(k: Name): boolean[] {
  return memo(FL.brws, k, () => {
    const { live, lays } = fun_of(k);
    return lays.map((l, i) => done_live(FL.book.tlds[k])
      && l.ks.includes("box") && ty_adt(live[i][2])?.k !== "Array"
      && !FL.own.has(k + "~" + i));
  });
}`, 'function brw_of(k: Name): boolean[] {\n  return fun_of(k).lays.map(() => false);\n}');
  source = source.replaceAll('"Array"', '"JayDB~disabled-array-representation"');
  replace('const OPTIMIZED: Record<Name, Native> =', `
Object.assign(OPERATIONS, {
  nat_add: { C: "jaydb_nat_add(e, $0, $1)" },
  nat_double: { C: "jaydb_nat_double(e, $0)" },
  nat_sub: { C: "jaydb_nat_sub(e, $0, $1)" },
  nat_mul: { C: "jaydb_nat_mul(e, $0, $1)" },
  nat_cmp: { C: "jaydb_nat_cmp(e, $0, $1)" },
  nat_is_lt: { C: "jaydb_nat_lt(e, $0, $1)" },
  nat_min: { C: "jaydb_nat_minmax(e, $0, $1, false)" },
  nat_max: { C: "jaydb_nat_minmax(e, $0, $1, true)" },
  nat_divmod: { C: "JAYDB_NAT_DIVMOD" },
  nat_div: { C: "jaydb_nat_div(e, $0, $1, false)" },
  nat_mod: { C: "jaydb_nat_div(e, $0, $1, true)" },
  nat_pow: { C: "jaydb_nat_pow(e, $0, $1)" },
  u32_to_nat: { C: "JAYDB_NAT_SMALL((u32)$0)" },
  u32_from_nat: { C: "jaydb_nat_to_u32(e, $0)" },
  u32_pow: { C: "jaydb_nat_u32_pow(e, $0, $1)" },
  u32_shln: { C: "jaydb_nat_u32_shift(e, $0, $1, false)" },
  u32_shrn: { C: "jaydb_nat_u32_shift(e, $0, $1, true)" },
  u32_log2: { C: "JAYDB_NAT_SMALL(31 - CLZ((u32)$0 | 1))" },
});
const OPTIMIZED: Record<Name, Native> =`);
  replace('function intr_of(k: Name, js = false): Intr | undefined {',
    `function intr_of(k: Name, js = false): Intr | undefined {
  if (/^(array_|map_bit$|map_msb_u$)/.test(op_name(k))) return undefined;`);
  replace('function ctr_build(sc: Scope, k: Name, exprs: string[], stat = false): string {',
    `function ctr_build(sc: Scope, k: Name, exprs: string[], stat = false): string {
  if (k === "Zero") return "JAYDB_NAT_ZERO";
  if (k === "Succ") return emit_alias(sc, "jaydb_nat_succ(e, " + exprs[0] + ")", "nat", "box");`);
  replace('  const flds = ctr_flds(x.k, x.x);\n  const ctr = FL.book.ctrs[x.k];',
    `  const flds = ctr_flds(x.k, x.x);
  const ctr = FL.book.ctrs[x.k];
  if (adt.k === "Nat") {
    if (x.k === "Zero") return val_new(["JAYDB_NAT_ZERO"], BOX, true);
    const vs = emit_each(sc, flds, [], ctr_doms(ctr, adt.x));
    return val_new([emit_alias(sc, "jaydb_nat_succ(e, " + val_own(sc, vs[0])[0] + ")", "nat", "box")], BOX);
  }`);
  replace('function node_fields(sc: Scope, t: string, k: Name, tail = false): Val[] {',
    `function node_fields(sc: Scope, t: string, k: Name, tail = false): Val[] {
  if (k === "Zero") return [];
  if (k === "Succ") return [val_new(["jaydb_nat_pred(e, " + t + ")"], BOX)];`);
  replace('  const is = (c: Name) => `term_aux(${sw}) == ${cid_mac(c)}`;',
    '  const is = (c: Name) => adt.k === "Nat"\n'
    + '    ? (c === "Zero" ? "" : "!") + "jaydb_nat_is_zero(" + sw + ")"\n'
    + '    : `term_aux(${sw}) == ${cid_mac(c)}`;');
  replace('  const lay = lay_of(ty);\n  const all = Array.isArray(C)',
    `  const lay = lay_of(ty);
  if (op === "nat_divmod") {
    const out = emit_dst(sc, lay, "nq");
    file_push(sc, "jaydb_nat_divmod(e, " + ws.join(", ") + ", &" + out.ws[0] + ", &" + out.ws[1] + ");");
    return out;
  }
  const all = Array.isArray(C)`);
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-generic-'));
  const file = path.join(temp, 'comp.ts');
  fs.writeFileSync(file, source);
  try {
    const compiler = await import(pathToFileURL(file).href);
    return Object.freeze({
      sourceSha256: hash(source),
      compile_book(book) {
        if (compiler.io_type(book) === null) throw new Error('NATIVE_MAIN: expected trusted IO main');
        return `// JAYDB_NATIVE_GENERIC_V1 ${hash(source)}\n// JAYDB_NATIVE_COMPACT_NAT_V1\n// JAYDB_NATIVE_WIDE_IDS_V1\n// JAYDB_NATIVE_WORD_ARITY_V1\n// JAYDB_NATIVE_ADDRESS_WORD_V1\n` + compiler.compile_book(book);
      },
    });
  } finally {
    fs.rmSync(temp, { recursive: true, force: true });
  }
}
