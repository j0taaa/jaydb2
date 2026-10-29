// A finite dependency closure on the FINAL source Book. No ordinary argument
// is specialized and no witness/model is chosen by this analysis.
export function templateAffected(B,book){
 const graph=new Map(),affected=new Set();
 const references=term=>{
   const refs=new Set(),todo=[term],seen=new Set();
   while(todo.length){const x=todo.pop();if(!x||typeof x!=='object'||seen.has(x))continue;seen.add(x);
     if(['Ref','ADT','Ctr','Mat','Lit'].includes(x.$))refs.add(x.k);
     for(const[k,v]of Object.entries(x))if(k!=='s')todo.push(v);
   }
   return refs;
 };
 for(const[k,d]of Object.entries(book.tlds)){
   const refs=references(B.term_lower(d.T));graph.set(k,refs);
   if(d.$==='Def'){
     if(d.x>0)affected.add(k);
     for(const t of [d.v===null?null:B.term_lower(d.v),d.e])for(const r of references(t))refs.add(r);
   }else for(const c of d.c){const rs=references(B.term_lower(c.T));graph.set(c.k,new Set([k,...rs]));for(const r of rs)refs.add(r);}
 }
 for(const[k,variants]of Object.entries(book.tmps))for(const name of variants.values())graph.get(name)?.add(k);
 let grew=true;while(grew){grew=false;for(const[k,rs]of graph)if(!affected.has(k)&&[...rs].some(r=>affected.has(r))){affected.add(k);grew=true;}}
 return affected;
}
