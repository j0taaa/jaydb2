/** Staged accounted lowering. generic.mjs remains frozen until root's swap.
 * The generated adapter is self-contained so the ordinary offline cache pins
 * its ENTIRE transformed compiler text; no runtime sidecar/JSON grants coverage.
 */
import fs from 'node:fs';
import crypto from 'node:crypto';
const hash=x=>crypto.createHash('sha256').update(x).digest('hex');
export const normalizeCodecSource=s=>s.replace(/^import[^\n]*$/gm,'').replace(/^[ \t\r]+$/gm,'');
// The C machine is specific to these sources. Staging must not silently
// authorize an edited Codec by recomputing its fingerprint.
export const ACCOUNTED_SOURCE_PINS=Object.freeze({
  codec:'e77f2c6c6f3afceb8f63fb845ef4fe9f7d94937319db2b0ddafd22cb3a4d9963',
  data:'c48fd2da20ecbadb9e9a000532bf578b9e3f6fe55ed6306b414cafc535d4bbbf',
  bytes:'04efd3ca9bf6d3c023a8a9f0d7fb3c00ad893b18c451fd2f99b963e0cf208bee',
});

export function transformAccountedCompiler(source,pins) {
  const replace=(before,after)=>{
    if(source.split(before).length!==2)throw new Error('ACCOUNTED_PATCH: '+before);
    source=source.replace(before,after);
  };
  replace('import * as fs from "node:fs";', 'import * as fs from "node:fs";\nimport { createHash as jaydb_hash } from "node:crypto";');
  replace('export function compile_book(book: Bend.Book', 'function jaydb_original_compile_book(book: Bend.Book');
  replace('function emit_unfold(m: Spine): HTerm | null {',
    'function emit_unfold(m: Spine): HTerm | null {\n  if (m.k && jaydb_decoders.has(m.k)) return null;');
  replace('function flat_of(k: Name): boolean {',
    'function flat_of(k: Name): boolean {\n  if (jaydb_decoders.has(k)) return false;');
  replace('const once = FL.sites.get(ck.k) === 1',
    'const once = !jaydb_decoders.has(ck.k) && FL.sites.get(ck.k) === 1');
  replace('  const facts = () => FL.own.size + FL.hot.size + FL.stat.size;',
    '  jaydb_check_codec_entries();\n  const facts = () => FL.own.size + FL.hot.size + FL.stat.size;');
  replace('  // keep nothing memoized: clang may run next, while this process waits',
    '  jaydb_live_entries = [...jaydb_decoders.keys()].filter(k=>FL.segs.some(s=>s.fid===seg_fid(k))).map(k=>[k,seg_fid(k)]);\n'
      +'  // keep nothing memoized: clang may run next, while this process waits');
  replace('function emit_body(sc: Scope, tm: HTerm, ty0: HTerm | null,\n  ers: HTerm[], args: Val[], dst: Val | null): void {',
    'function jaydb_original_emit_body(sc: Scope, tm: HTerm, ty0: HTerm | null,\n  ers: HTerm[], args: Val[], dst: Val | null): void {');
  source+=`
// Private native lowering. Only a complete pinned trusted module is eligible;
// local client Dados.Valor constructors are never rewritten by this path.
let jaydb_decoders = new Map<string,{data:string,bytes:string}>();
let jaydb_codec_modules = new Set<string>();
let jaydb_external_entries = new Set<string>();
let jaydb_unknown_decoders = new Set<string>();
let jaydb_live_entries: [string,string][] = [];
function jaydb_file(t: any): any { return t?.s?.file; }
function jaydb_source(t: any): any {
  return jaydb_file(t?.T) ?? jaydb_file(t?.e) ?? jaydb_file(t?.v);
}
function jaydb_normalize(s: string): string {
  return s.replace(/^import[^\\n]*$/gm, '').replace(/^[ \\t\\r]+$/gm, '');
}
function jaydb_digest(s: string): string { return jaydb_hash('sha256').update(jaydb_normalize(s)).digest('hex'); }
export function compile_book(book: Bend.Book, ...rest: any[]): string {
  jaydb_decoders = new Map();
  jaydb_codec_modules = new Set();
  jaydb_external_entries = new Set();
  jaydb_unknown_decoders = new Set();
  jaydb_live_entries = [];
  const sources = new Map<string,string>();
  for (const [name,t] of Object.entries(book.tlds)) {
    const file=jaydb_source(t); if(file?.str) sources.set(file.ns,jaydb_digest(file.str));
  }
  for(const [name,t] of Object.entries(book.tlds)) {
    if(!name.endsWith(':decodificar') || sources.get(jaydb_source(t)?.ns)!==${JSON.stringify(pins.codec)})continue;
    const aliases=jaydb_source(t).al;
    const data=aliases.D,bytes=aliases.B;
    if(sources.get(data)!==${JSON.stringify(pins.data)} || sources.get(bytes)!==${JSON.stringify(pins.bytes)})throw new Error('ACCOUNTED_BINDING: pinned Codec dependencies missing');
    const need=['VAusente','VBool','VInt','VTexto','VListaVazia','VLista','VRegistroVazio','VRegistro','Campo'];
    if(need.some(k=>!book.ctrs[data+':'+k]))throw new Error('ACCOUNTED_BINDING: constructor set changed');
    jaydb_decoders.set(name,{data,bytes});
    jaydb_codec_modules.add(jaydb_source(t).ns);
  }
  for(const name of Object.keys(book.tlds))
    if(name.endsWith(':decodificar') && !jaydb_decoders.has(name))jaydb_unknown_decoders.add(name);
  const text=jaydb_original_compile_book(book,...rest);
  return '// JAYDB_NATIVE_ACCOUNTED_CODEC_V1 '+jaydb_live_entries.map(([k])=>k).join(',')+'\\n'
    +jaydb_live_entries.map(([,fid])=>'// JAYDB_NATIVE_ACCOUNTED_ENTRY_V1 '+fid+'\\n').join('')
    +[...jaydb_external_entries].map(k=>'// JAYDB_NATIVE_ACCOUNTED_UNCOVERED_V1 '+k+'\\n').join('')
    +(!jaydb_live_entries.length && !jaydb_external_entries.size?'// JAYDB_NATIVE_ACCOUNTED_EMPTY_V1\\n':'')+text;
}
function jaydb_check_codec_entries(): void {
  for(const name of jaydb_unknown_decoders)if(FL.srcs.has(name))jaydb_external_entries.add(name);
  if(!jaydb_decoders.size)return;
  for(const [k,t] of done_defs()) {
    if(jaydb_codec_modules.has(jaydb_source(t)?.ns))continue;
    term_any(fun_of(k).h!,s=>{
      if(s.$==='Ref' && jaydb_codec_modules.has(jaydb_source(FL.book.tlds[s.k])?.ns)
          && !jaydb_decoders.has(s.k)) {
        // Preserve the source language and every legacy entry. This artifact
        // cannot authorize counted execution until this additional entry has
        // a real wire context; report the missing cut for native refusal.
        jaydb_external_entries.add(s.k);
      }
      return false;
    });
  }
}
function emit_body(sc: Scope,tm: HTerm,ty0: HTerm|null,ers: HTerm[],args: Val[],dst: Val|null): void {
  if(!jaydb_decoders.has(sc.def) || ty0!==FL.book.tlds[sc.def].T
      || args.length!==fun_of(sc.def).lays.length) {
    return jaydb_original_emit_body(sc,tm,ty0,ers,args,dst);
  }
  const f=fun_of(sc.def);
  if(args.length!==2 || args[0].ws.length!==1 || args[1].ws.length!==2
      || f.ret.ks.join(',')!=='w32,box')throw new Error('ACCOUNTED_LAYOUT: trusted Codec ABI changed');
  const name=name_local(sc,'jaydb_decoded');
  file_push(sc,'if (jaydb_accounted_enabled()) {');
  file_push(sc,'Term '+name+'[2];');
  const binding=jaydb_decoders.get(sc.def)!;
  const ctors=['VAusente','VBool','VInt','VTexto','VListaVazia','VLista','VRegistroVazio','VRegistro','Campo'];
  file_push(sc,'static const struct jaydb_decoder_ids '+name+'_ids = {'
    + ctors.map(k=>cid_mac(binding.data+':'+k)).join(', ')+'};');
  file_push(sc,'jaydb_codec_accounted(e, '+args[0].ws[0]+', '+args[1].ws.join(', ')+', '+name+', &'+name+'_ids);');
  emit_put({...sc,spares:[...sc.spares]},dst,val_new(['(u32)'+name+'[0]',name+'[1]'],f.ret));
  file_push(sc,'} else {');
  jaydb_original_emit_body(sc,tm,ty0,ers,args,dst);
  file_push(sc,'}');
}
`;
  return source;
}

export function stageAccountedAdapter(baseGenericPath,outputPath,root) {
  const original=fs.readFileSync(baseGenericPath,'utf8');
  const pins={codec:hash(normalizeCodecSource(fs.readFileSync(root+'/src/Codec.bend','utf8'))),
    data:hash(normalizeCodecSource(fs.readFileSync(root+'/contrato/Dados.bend','utf8'))),
    bytes:hash(normalizeCodecSource(fs.readFileSync(root+'/contrato/Bytes.bend','utf8')))};
  for(const key of Object.keys(pins))if(pins[key]!==ACCOUNTED_SOURCE_PINS[key])
    throw new Error('ACCOUNTED_SOURCE_CHANGED: '+key+' requires a new reviewed lowering');
  const anchor="  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-generic-'));";
  if(original.split(anchor).length!==2)throw new Error('ACCOUNTED_ADAPTER: frozen generic anchor changed');
  const staged=original.replace(anchor,`  source = transformAccountedCompiler(source, ${JSON.stringify(pins)});\n`+anchor)
    +'\n'+transformAccountedCompiler.toString()+'\n';
  fs.writeFileSync(outputPath,staged);
  return {genericSha256:hash(original),stagedSha256:hash(staged),pins};
}
