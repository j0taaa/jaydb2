// A derived declaration's live calls must name an earlier declaration (or
// its own structurally smaller call). Types and erased arguments impose no
// live order. The original kernel remains the authority for quantities and
// descent; this pass only orders generated definitions, never source Book.
export function liveDependencies(term,top=true,result=new Set()){
 switch(term.$){
  case 'App': {
   if(top){let h=term;while(h.$==='App')h=h.f;if(h.$==='Ref')result.add(h.k);}
   liveDependencies(term.f,false,result);
   if(term.q!==0)liveDependencies(term.x,true,result);break;
  }
  case 'Ref':if(top)result.add(term.k);break;
  case 'Ann':liveDependencies(term.x,true,result);break;
  case 'Lam':liveDependencies(term.f,true,result);break;
  case 'Let':if(term.q!==0)liveDependencies(term.v,true,result);liveDependencies(term.f,true,result);break;
  case 'Tup':if(term.q!==0)liveDependencies(term.a,true,result);liveDependencies(term.b,true,result);break;
  case 'Prj':liveDependencies(term.h,true,result);break;
  case 'Mat':liveDependencies(term.h,true,result);liveDependencies(term.m,true,result);break;
  case 'Rwt':liveDependencies(term.e,true,result);liveDependencies(term.f,true,result);break;
  case 'Min':liveDependencies(term.a,true,result);liveDependencies(term.b,true,result);break;
 }
 return result;
}
export function orderDeclarations(declarations){
 const byName=new Map(declarations.map(d=>[d[0],d])),done=new Set(),active=new Set(),out=[];
 if(byName.size!==declarations.length)throw Error('A generated declaration name was reused');
 const visit=k=>{
  if(done.has(k))return;
  if(active.has(k))throw Error('Representation unsupported: generated mutual live dependency '+[...active,k].join(' -> '));
  active.add(k);const d=byName.get(k);
  for(const dep of liveDependencies(d[2]))if(dep!==k&&byName.has(dep))visit(dep);
  active.delete(k);done.add(k);out.push(d);
 };
 for(const [k]of declarations)visit(k);
 return out;
}
