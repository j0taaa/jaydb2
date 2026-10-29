import {V,R,lam,app,apps,ann,all,sig,tup,eq,prj,split,K,rfl,rwt} from './structural-syntax.mjs';
import {bound} from './structural-relations.mjs';
import {Reflection} from './structural-reflection.mjs';

// A proof expression is transformed by applying its actual compositional
// evaluator and projecting the exact logical evidence already returned there.
// This is not a theorem search and does not replace it with reflexivity.
export class ProofBody {
 constructor(bodies){this.bodies=bodies;this.gen=bodies.gen;this.source=bodies.source;this.B=bodies.B;this.reflection=new Reflection(this.gen);}
 exact(key){
   const d=this.bodies.book.tlds[key],type=this.source.type(d.T);
   this.gen.sourceName=k=>this.source.name(k);
   // Derive the bundle from this declaration's checked operational evaluator.
   // In particular, an entry whose source body is a case tree does not need a
   // second, syntax-specific proof walker. The evaluator already checks each
   // actual branch and its recursive dependencies.
   const original=this.bodies.safe.logical(key),built=this.representedBundle(this.bodies.reference(key),type,new Map(),original);
   const name=this.gen.prefix+'.Evidence.'+this.source.name(key)+'.evidence_bundle';
   this.gen.emit(name,built.T,built.b);
   const evidence=this.projectBundle(type,R(name),'proof');
   const proofName=this.gen.prefix+'.Evidence.'+this.source.name(key)+'.provided_evidence';
   this.gen.emit(proofName,this.gen.plan(type).l,evidence);
   const preservation=this.projectBundle(type,R(name),'backlink',R(proofName),original);
   const linkName=this.gen.prefix+'.Evidence.'+this.source.name(key)+'.evidence_source_link';
   this.gen.emit(linkName,preservation.T,preservation.b);
   const transport=this.exactEliminate(type,R(proofName),original,R(linkName));
   this.gen.emit(this.gen.prefix+'.Evidence.'+this.source.name(key)+'.evidence_eliminate',transport.T,transport.b);
   return proofName;
 }
 representedBundle(value,type,env,original){
   if(type.tag==='arrow'){
     const argument=this.gen.fresh(),plan=this.gen.plan(type.A,env),next=new Map(env);
     const input={p:V(argument),l:V(argument),r:this.reflection.at(type.A,V(argument)),type:type.A,expression:bound(type.key)};
     next.set(type.key,input);
     const result=this.representedBundle(this.gen.application(value,input,next),type.B,next,app(original,V(argument),type.q));
     return {T:all(type.q,argument,plan.l,result.T),b:lam(type.q,argument,result.b)};
   }
   if(type.tag!=='identity')throw Error('An exact identity evidence result is required');
   const wanted=this.gen.plan(type,env).l,slots=Array.from({length:5},()=>[1,this.gen.fresh()]);
   const out=this.gen.fresh(),input=this.gen.fresh(),actual=this.gen.plan(value.type,env).relation(value.p,value.l);
   const T=sig(2,out,wanted,eq(V(out),original,wanted));
   const projection=ann(split(slots,tup(2,V(slots[1][1]),V(slots[3][1]))),all(1,input,actual,T));
   return {T,b:app(projection,value.r)};
 }
 exactEliminate(type,proof,original,link,env=new Map()){
   const gen=this.gen;
   if(type.tag==='arrow'){
     const x=gen.fresh(),A=gen.plan(type.A,env),next=new Map(env);
     next.set(type.key,{p:V(x),l:V(x),r:this.reflection.at(type.A,V(x)),type:type.A,expression:bound(type.key)});
     const rest=this.exactEliminate(type.B,app(proof,V(x),type.q),app(original,V(x),type.q),app(link,V(x),type.q),next);
     return {T:all(type.q,x,A.l,rest.T),b:lam(type.q,x,rest.b)};
   }
   const A=gen.plan(type,env).l,P=gen.fresh(),v=gen.fresh(),x=gen.fresh(),e=gen.fresh(),z=gen.fresh();
   const motive=all(1,x,A,all(1,e,eq(proof,V(x),A),K(1)));
   const apply=(x,e)=>apps(V(P),[[1,x],[1,e]]);
   return {T:all(0,P,motive,all(1,v,apply(proof,rfl),apply(original,link))),
     b:lam(0,P,lam(1,v,rwt(link,z,apply(V(z),ann(V(z+1),eq(proof,V(z),A))),V(v))))};
 }
 projectBundle(type,bundle,mode,proof,original,env=new Map()){
   const gen=this.gen;
   if(type.tag==='arrow'){
     const x=gen.fresh(),plan=gen.plan(type.A,env),next=new Map(env);
     next.set(type.key,{p:V(x),l:V(x),r:this.reflection.at(type.A,V(x)),type:type.A,expression:bound(type.key)});
     const rest=this.projectBundle(type.B,app(bundle,V(x),type.q),mode,proof&&app(proof,V(x),type.q),original&&app(original,V(x),type.q),next);
     if(mode==='proof')return lam(type.q,x,rest);
     return {T:all(type.q,x,plan.l,rest.T),b:lam(type.q,x,rest.b)};
   }
   const A=gen.plan(type,env).l,p=gen.fresh(),e=gen.fresh(),z=gen.fresh();
   const source=original;
   // For the value projection its source index occurs only in the inferred
   // bundle header. Recover it from the independently emitted declaration.
   let T;
   if(mode==='proof'){
     const head=bundle;let base=head;while(base.$==='App')base=base.f;
     const item=gen.declarations.find(([k])=>k===base.k);let U=item[1],value=head;
     const args=[];while(value.$==='App'){args.unshift(value.x);value=value.f;}
     const replace=(o,l,x)=>o&&typeof o==='object'?(Array.isArray(o)?o.map(v=>replace(v,l,x)):o.$==='Var'&&o.l===l?x:Object.fromEntries(Object.entries(o).map(([k,v])=>[k,replace(v,l,x)]))):o;
     for(const x of args){U=replace(U.B,U.l,x);}T=U;
     return app(ann(prj(lam(2,p,lam(2,e,V(p)))),all(1,z,T,A)),bundle);
   }
   T=sig(2,p,A,eq(V(p),source,A));
   const first=app(ann(prj(lam(2,p,lam(2,e,V(p)))),all(1,z,T,A)),V(z));
   const target=eq(first,source,A);
   const body=app(ann(prj(lam(2,p,lam(2,e,V(e)))),all(1,z,T,target)),bundle);
   return {T:eq(proof,source,A),b:body};
 }
}
