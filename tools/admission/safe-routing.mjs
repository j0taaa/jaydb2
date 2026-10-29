import {instanceSourceClaims} from './closed-instances.mjs';
import {templateAffected} from './template-affected.mjs';
import {constrainProofViews} from './structural-views.mjs';
import {structuralEmitter} from './structural-emitter.mjs';

export function routeSafe(B,legacy,extended){
 const collect=(book,safe)=>{
  const affected=templateAffected(B,book),proofNames=[],relevant=new Set();
  const refs=x=>{
   if(!x||typeof x!=='object')return false;
   if(['Ref','ADT','Ctr','Mat','Lit'].includes(x.$)&&affected.has(x.k))return true;
   return Object.entries(x).some(([k,v])=>k!=='s'&&refs(v));
  };
  for(const[k,d]of Object.entries(book.tlds))if(d.$==='Def'&&d.x===0&&d.e!==undefined){
   const name=safe.state.names.get(k);if(name===undefined||!safe.state.out.some(([n])=>n===name))continue;
   let T=d.T;for(let i=0;;i++){const F=B.term_wnf(book,T);if(F.$!=='All'){T=F;break;}T=F.B(B.Var(F.k,4000000+i));}
   if(T.$!=='Eql')continue;
   proofNames.push(name);if(refs(B.term_lower(d.T)))relevant.add(name);
  }
  return {proofNames,relevant};
 };
 return {
  ...legacy,
  admission_prepare_book:legacy.admission_prepare_book,
  SafeResourceExhausted:legacy.SafeResourceExhausted,
  admission_safe_emit(book,out,options={}){
   // This is dispatch by typing structure, before any kernel verdict. The
   // legacy payload is complete and unmodified when its route is selected.
   const result=legacy.admission_safe_emit(book,out,options);
   if(result.oos.length)return result;
   const live=legacy.admission_safe_state();live.B=B;
   const emittedNames=new Set(live.state.out.map(([k])=>k));
   for(const key of instanceSourceClaims(book).keys()){
    const guard=live.state.admissionGuards?.get(key);
    if(guard===undefined||!emittedNames.has(guard))throw Error('A mandatory physical source link was omitted: '+key);
   }
   const {proofNames,relevant}=collect(book,live);
   let plan={declarations:[],promotions:[],unresolved:[]},chosen=false;
   if(relevant.size){
    const copy={...live,state:{...live.state,out:structuredClone(live.state.out)}};
    plan=constrainProofViews(copy,proofNames,options);
    chosen=plan.unresolved.some(x=>[...relevant].some(n=>x.path===n||x.path.startsWith(n+'.')))||[...relevant].some(n=>{
      const v=copy.state.admissionTypeViews.get(n);return copy.state.admissionViewOps.key(v.original)!==copy.state.admissionViewOps.key(v.observed);
    });
   }
   if(!chosen)return {...result,correspondence:{route:'physical',sameBook:true}};
   let got;
   try{got=structuralEmitter(B,extended,{executionRoots:['main'],proofRoots:[...relevant].map(n=>[...live.state.names].find(([,v])=>v===n)[0])}).admission_safe_emit(book,out,options);}
   catch(e){
    if(e instanceof extended.SafeResourceExhausted)throw new legacy.SafeResourceExhausted(e.message);
    throw e;
   }
   return {...got,correspondence:{route:'structural',...got.structural,dispatch:{relevant:[...relevant],unresolved:plan.unresolved}}};
  }
 };
}
