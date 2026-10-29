/** Experimental inspection of constructor provenance BEFORE layout flattening.
 * No declaration rewriting, no runtime events or generic.mjs/cache-pin change.
 * A frozen Book is required. This inspector has not audited its full before/
 * after Book fingerprint (including writable reduction memo cells).
 * Each emission is compared byte for byte with the unmodified derived emitter.
 * This helper currently uses Node's TS loader; it is not the jitless service
 * frontend. A future runtime integration needs an explicitly pinned offline
 * transformation, not a silent fallback in the installed frontend.
 */
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { registerHooks } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { loadGenericCompiler } from './generic.mjs';

const hash = value => crypto.createHash('sha256').update(value).digest('hex');

export async function loadConstructionMetadataCompiler(directory) {
  let captured;
  const hook = registerHooks({
    load(url, context, nextLoad) {
      if (url.startsWith('file:') && url.endsWith('/comp.ts')
          && fileURLToPath(url).includes('/jaydb-generic-')) {
        if (captured !== undefined) throw new Error('Multiple generated compiler texts during capture');
        captured = fs.readFileSync(fileURLToPath(url), 'utf8');
        return { format: 'module', source: 'export function io_type(){}; export function compile_book(){}', shortCircuit: true };
      }
      return nextLoad(url, context);
    },
  });
  let adapter;
  try { adapter = await loadGenericCompiler(directory); }
  finally { hook.deregister(); }
  if (captured === undefined || hash(captured) !== adapter.sourceSha256)
    throw new Error('Captured compiler differs from pinned generic adapter text');
  let source = captured;
  function replace(before, after) {
    if (source.split(before).length !== 2) throw new Error('Constructor inspection anchor changed: ' + before);
    source = source.replace(before, after);
  }
  // Production emission deletes its private foreign file after closing and
  // emitting the Book. The inspection receives the exact prior bytes as data;
  // it neither recreates that path nor rewrites a foreign reference in Book.
  replace('  const path = fs.realpathSync(tld.i.find((x) => x.endsWith(ext))\n    ?? die(miss + Bend.name_key(k)));',
    '  const requested = tld.i.find((x) => x.endsWith(ext)) ?? die(miss + Bend.name_key(k));\n'
    + '  const saved = jaydb_foreign_sources.get(requested);\n'
    + '  const path = saved?.path ?? fs.realpathSync(requested);');
  replace('    const raw = fs.readFileSync(path, "utf8");',
    '    const raw = saved?.source ?? fs.readFileSync(path, "utf8");');
  source += '\nlet jaydb_foreign_sources = new Map<string, {path: string, source: string}>();\n'
    + 'export function jaydb_inspection_foreign(entries: any[]): void { jaydb_foreign_sources = new Map(entries); }\n';
  const readerSource = source;
  replace('function ctr_build(sc: Scope, k: Name, exprs: string[], stat = false): string {',
    'function jaydb_original_ctr_build(sc: Scope, k: Name, exprs: string[], stat = false): string {');
  replace('FL.hot.has(k))})`;', 'FL.hot.has(k), k)})`;');
  replace('function node_fill(sc: Scope, k: string, alloc: string,\n  exprs: string[], shr = false): string {',
    'function node_fill(sc: Scope, k: string, alloc: string,\n  exprs: string[], shr = false, constructor: Name | null = null): string {\n  const jaydb_start_line = sc.seg.lines.length;');
  replace('  return nd;\n}\n\nfunction node_fields', `  jaydb_constructor_sites.push({
    kind: constructor === null ? "raw-storage" : "constructor-storage",
    origin: sc.def, segment: sc.seg.fid, constructor, variable: nd,
    allocation: alloc, words: exprs.length, values: [...exprs], shared: shr,
    startLine: jaydb_start_line, endLine: sc.seg.lines.length,
  });
  return nd;
}

function node_fields`);
  replace('function emit_ctr(sc: Scope, x: Of<"Ctr">, ty: HTerm | null,\n  at: Lay | null): Val {',
    'function jaydb_original_emit_ctr(sc: Scope, x: Of<"Ctr">, ty: HTerm | null,\n  at: Lay | null): Val {');
  // Capture actual guard ENTRY arguments before lambdas consume their affine
  // bindings. Records identify the original wire n (high/low), not the later
  // decremented remaining count or an arena allocation size. This is metadata:
  // presence of a guard invocation does NOT prove that its Cabe arm executed.
  replace('function emit_body(sc: Scope, tm: HTerm, ty0: HTerm | null,\n  ers: HTerm[], args: Val[], dst: Val | null): void {',
    `function emit_body(sc: Scope, tm: HTerm, ty0: HTerm | null,
  ers: HTerm[], args: Val[], dst: Val | null): void {
  if (ty0 === FL.book.tlds[sc.def]?.T && args.length === fun_of(sc.def).lays.length) {
    const name = sc.def.split(":").at(-1);
    if (["concluir_palavra", "abrir_conferido", "abrir_variavel", "ler_tag", "percorrer"].includes(name!)) {
      const f = fun_of(sc.def);
      jaydb_constructor_sites.push({ kind: "decoder-guard-entry", origin: sc.def,
        segment: sc.seg.fid, startLine: sc.seg.lines.length, endLine: sc.seg.lines.length,
        arguments: args.map((v, i) => ({ name: f.live[i]?.[1],
          words: [...v.ws], layout: [...v.lay.ks],
          arms: v.lay.arms === null ? null : Object.keys(v.lay.arms) })),
        successfulArmNotInferred: true });
    }
  }`);
  // Earlier optimizer fixed-point passes are not concrete emitted sites.
  replace('    FL.segs = [];', '    jaydb_constructor_sites = [];\n    FL.segs = [];');
  source += `
// Inspection records only. A value-expression record is NOT AlocouCampo.
let jaydb_constructor_sites: any[] = [];
export function jaydb_reset_constructor_sites(): void { jaydb_constructor_sites = []; }
export function jaydb_take_constructor_sites(): any[] { return jaydb_constructor_sites; }
function ctr_build(sc: Scope, k: Name, exprs: string[], stat = false): string {
  const start = sc.seg.lines.length;
  const result = jaydb_original_ctr_build(sc, k, exprs, stat);
  jaydb_constructor_sites.push({ kind: "boxed-expression", constructor: k,
    origin: sc.def, segment: sc.seg.fid, values: [...exprs], expression: result,
    constant: stat, startLine: start, endLine: sc.seg.lines.length });
  return result;
}
function emit_ctr(sc: Scope, x: Of<"Ctr">, ty: HTerm | null, at: Lay | null): Val {
  const start = sc.seg.lines.length;
  const result = jaydb_original_emit_ctr(sc, x, ty, at);
  jaydb_constructor_sites.push({ kind: "value-expression", constructor: x.k,
    origin: sc.def, segment: sc.seg.fid, words: [...result.ws],
    layout: [...result.lay.ks], constant: result.stat,
    fieldLayouts: result.lay.arms?.[x.k]?.map((field: Lay) => [...field.ks]) ?? null,
    liveBindings: [...sc.uses].map(([variable, bind]) => ({ name: variable.k,
      variable: variable.i, words: [...bind.val.ws], layout: [...bind.val.lay.ks] })),
    startLine: start, endLine: sc.seg.lines.length });
  return result;
}
`;
  const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-constructor-compiler-'));
  try {
    const originalPath = path.join(temporary, 'original.ts');
    const annotatedPath = path.join(temporary, 'annotated.ts');
    fs.writeFileSync(originalPath, readerSource);
    fs.writeFileSync(annotatedPath, source);
    const original = await import(pathToFileURL(originalPath).href);
    const annotated = await import(pathToFileURL(annotatedPath).href);
    return Object.freeze({
      sourceSha256: hash(source), coreSourceSha256: adapter.sourceSha256,
      compile_book(book, foreignSnapshots = []) {
        if (!Object.isFrozen(book)) throw new Error('Use the production emission Book guard before inspection');
        original.jaydb_inspection_foreign(foreignSnapshots);
        annotated.jaydb_inspection_foreign(foreignSnapshots);
        if (original.io_type(book) === null) throw new Error('Expected trusted IO main');
        const plain = original.compile_book(book);
        annotated.jaydb_reset_constructor_sites();
        const inspected = annotated.compile_book(book);
        if (plain !== inspected) throw new Error('Constructor inspection changed emitted C');
        const sites = JSON.parse(JSON.stringify(annotated.jaydb_take_constructor_sites()));
        return { c: plain, sites, emittedCSha256: hash(plain), emittedCUnchanged: true,
          sameBookObject: true, noRuntimeEventsClaimed: true,
          coreSourceSha256: adapter.sourceSha256, inspectionSourceSha256: hash(source) };
      },
    });
  } finally { fs.rmSync(temporary, { recursive: true, force: true }); }
}
