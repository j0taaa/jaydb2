// Structural only: one logical spelling in erased type positions. Physical
// source-link BODY comparisons retain their exact dependencies.
export function canonicalTypes(source) {
 source='import {templateAffected} from "jaydb:admission-affected";\n'+source;
 source=source.replace('function item_emit(e: Safe, k: Name, cols: Cols, n: string): void {',
   'function item_emit(e: Safe, k: Name, cols: Cols, n: string): void {\n  e={...e,physicalBody:false,canonicalType:false,admissionStage:undefined} as any;');
 source=source.replace('return def?.$ === "Def" && def.x > 0','return def?.$ === "Def" && def.e !== undefined && admission_affected(e,name)');
 source=source.replace('function term(e: Safe, s0: Scope, t: HTerm, live: boolean): O {',
  'function term(e: Safe, s0: Scope, t: HTerm, live: boolean): O {\n  if (!live && !(e as any).physicalBody) e={...e,canonicalType:true} as any;');
 const anchor='  if (f.$ === "Ref" && e.inst.has(f.k)) {';
 source=source.replace(anchor,`  if (f.$ === "Ref" && (e as any).canonicalType && !(e as any).physicalBody) {
    const origin=e.inst.get(f.k);
    if(origin) return args(e,s,admission_projection(admission_body(e,origin[0])),e.book.tlds[origin[0]].T,[...origin[1],...xs],false);
    const d=e.book.tlds[f.k];
    if(d?.$ === "Def" && d.e !== undefined && d.x === 0 && admission_type_affected(e,f.k))
      return args(e,s,admission_projection(admission_body(e,f.k)),d.T,xs,false);
  }
${anchor}`);
 source=source.replace('  const nx = tld?.$ === "Def" ? tld.x : 0;',`  if(typeof k === "string" && (e as any).canonicalType && !(e as any).physicalBody && tld?.$ === "Def" && tld.x > 0)
    return args(e,s,admission_projection(admission_body(e,k)),tld.T,xs,false);
  const nx = tld?.$ === "Def" ? tld.x : 0;`);
 source=source.replace('arg_term(e, s, B.term_higher((e.book.tlds[k] as Def).e as B.LTerm), T, false),','arg_term({...e,physicalBody:true,canonicalType:false} as any, s, B.term_higher((e.book.tlds[k] as Def).e as B.LTerm), T, false),');
 source=source.replace('b: arg_term(e, s, B.term_higher(expected), T, false)', 'b: arg_term({...e,physicalBody:true,canonicalType:false} as any, s, B.term_higher(expected), T, false)');
 return source+'\nfunction admission_affected(e:Safe,k:string):boolean { return ((e as any).admissionAffected ??= templateAffected(B,e.book)).has(k); }\nfunction admission_type_affected(e:Safe,k:string):boolean { return ((e as any).admissionTypeAffected ??= templateAffected(B,e.book,true)).has(k); }\n';
}
