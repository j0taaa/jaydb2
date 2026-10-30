// A finite dependency closure on the FINAL source Book. No ordinary argument
// is specialized and no witness/model is chosen by this analysis.
export function templateAffected(B,book,typesOnly=false){
 const graph=new Map(),affected=new Set(),indices=new Set();
 const references=(term,inType=false)=>{
   const refs=new Set(),todo=[term],seen=new Set();
   while(todo.length){const x=todo.pop();if(!x||typeof x!=='object'||seen.has(x))continue;seen.add(x);
     if(['Ref','ADT','Ctr','Mat','Lit'].includes(x.$))refs.add(x.k);
     if(inType&&x.$==='Eql')for(const v of [x.a,x.b])for(const k of references(v))indices.add(k);
     for(const[k,v]of Object.entries(x))if(k!=='s')todo.push(v);
   }
   return refs;
 };
 for(const[k,d]of Object.entries(book.tlds)){
   const refs=references(B.term_lower(d.T),typesOnly);graph.set(k,refs);
   if(d.$==='Def'){
     if(d.x>0)affected.add(k);
     let T=typesOnly?B.term_wnf(book,d.T):null,i=0;
     while(typesOnly&&T.$==='All')T=B.term_wnf(book,T.B(B.Var(T.k,6000000+i++)));
     const typeBody=typesOnly&&['Typ','Qnt'].includes(T.$);
     if(!typesOnly||typeBody)for(const t of [d.v===null?null:B.term_lower(d.v),d.e])for(const r of references(t,typeBody))refs.add(r);
   }else for(const c of d.c){const rs=references(B.term_lower(c.T),typesOnly);graph.set(c.k,new Set([k,...rs]));for(const r of rs)refs.add(r);}
 }
 // Values occurring in an equality are part of the type's meaning even
 // when their own result type is unchanged. Preserve their equations too.
 if(typesOnly){const full=templateAffected(B,book);for(const k of indices)if(full.has(k))affected.add(k);}
 for(const[k,variants]of Object.entries(book.tmps))for(const name of variants.values())graph.get(name)?.add(k);
 let grew=true;while(grew){grew=false;for(const[k,rs]of graph)if(!affected.has(k)&&[...rs].some(r=>affected.has(r))){affected.add(k);grew=true;}}
 return affected;
}
