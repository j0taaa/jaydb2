// Authenticated access to the derived emitter's own typed output. This does
// not change an original checker rule or expose a second source Book.
export function adaptSafeState(source,{canonical=false}={}){
 const replace=(anchor,value)=>{
  if(source.split(anchor).length!==2)throw Error('Safe output adapter anchor changed');
  source=source.replace(anchor,value);
 };
 replace('    e.out.push([fresh(e, name_tt(k) + ".source_link"), UT,',
  '    const guard=fresh(e,name_tt(k)+".source_link"); ((e as any).admissionGuards ??= new Map()).set(k,guard);\n    e.out.push([guard, UT,');
 replace('return { text: book_show(e), oos };','ADMISSION_OUTPUT_STATE = e; ADMISSION_OUTPUT_CONTEXT = [MODEL_FUEL, ADMISSION_SCHEMAS, ADMISSION_INSTANCES, ADMISSION_SOURCE_CLAIMS]; return { text: book_show(e), oos };');
 return source+`\nlet ADMISSION_OUTPUT_STATE: Safe;
let ADMISSION_OUTPUT_CONTEXT: [bigint,string[],string[],Map<string,B.LTerm>];
export function admission_safe_state() {
 const e=ADMISSION_OUTPUT_STATE;
 let context=ADMISSION_OUTPUT_CONTEXT;
 const inside=<T>(f:()=>T):T=>{
  const previous=[MODEL_FUEL,ADMISSION_SCHEMAS,ADMISSION_INSTANCES,ADMISSION_SOURCE_CLAIMS] as const;
  [MODEL_FUEL,ADMISSION_SCHEMAS,ADMISSION_INSTANCES,ADMISSION_SOURCE_CLAIMS]=context;
  try{return f();}finally{
   context=[MODEL_FUEL,ADMISSION_SCHEMAS,ADMISSION_INSTANCES,ADMISSION_SOURCE_CLAIMS];
   [MODEL_FUEL,ADMISSION_SCHEMAS,ADMISSION_INSTANCES,ADMISSION_SOURCE_CLAIMS]=previous;
  }
 };
 return {state:e,
  logical:(k:string)=>inside(()=>${canonical?'admission_type_affected(e,k)?admission_projection(admission_body(e,k)):({$:"Ref",k:item_ref(e,k,[],true)} as O)':'admission_projection(admission_body(e,k))'}),
  term:(t:HTerm)=>inside(()=>term(e,scope_nil(),t,false)),text:()=>inside(()=>book_show(e))};
}\n`;
}
