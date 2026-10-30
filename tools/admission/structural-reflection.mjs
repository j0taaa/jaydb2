import {R,V,all,app,apps,ann,prj,mats,split,tuple,let1,bind,rfl} from './structural-syntax.mjs';
import {DataValues} from './structural-data.mjs';

// Construct reflexive input relations only when this type-directed operation
// is justified. An opaque higher-order domain never receives a fictitious R_h.
export class Reflection {
 constructor(gen){this.gen=gen;this.data=new DataValues(gen);this.cache=new Map();this.active=new Set();}
 at(T,value){
   if(T.tag==='family'&&T.args.length===0&&this.data.supports(T.key))
     return app(R(this.data.ensure(T.key).reflect),value);
   if(T.tag==='family')return app(R(this.family(T)),value);
   if(T.tag==='arrow')return this.function(T,value);
   throw Error('An actual closed construction is required at this abstract input; no reflexive relation was assumed: '+T.tag);
 }
 function(T,value){
   const gen=this.gen,bs=[],args=[];let U=T;
   while(U.tag==='arrow'){
     if(U.q===0||U.A.tag!=='family'||U.A.args.length||!this.data.supports(U.A.key))
       throw Error('Opaque function domain has no checked common Data readback');
     const p=this.data.ensure(U.A.key),v=gen.fresh();bs.push([U.q,v,p.D]);args.push([U.q,V(v)]);U=U.B;
   }
   if(U.tag!=='family'||U.args.length||!this.data.supports(U.key))
     throw Error('This opaque result needs a closed construction, not an assumed relation');
   const y=gen.fresh(),call=apps(value,args);
   const output=this.data.ensure(U.key);
   const evaluator=ann(bind('Lam',bs,let1(y,call,tuple([[1,V(y)],[1,rfl],[1,rfl]]))),bind('All',bs,this.data.scalar(output.D,call,call)));
   return this.data.shared(T,value,value,evaluator).r;
 }
 family(T){
   const gen=this.gen,d=gen.families.get(T.key),plan=gen.plan(T);
   const key=gen.termKey(plan.p),old=this.cache.get(key);if(old!==undefined)return old;
   if(T.args.some(x=>x.tag!=='type'&&!(x.tag==='constant'&&/^Q[012]$/.test(x.value.k))))throw Error('An abstract family input needs its actual relation dictionary');
   if(this.active.has(T.key))throw Error('Reflection of a recursive family with changing parameters is not implemented');
   const name=gen.prefix+'.Input.'+gen.sourceName(T.key)+'.reflect_input_'+this.cache.size;
   this.cache.set(key,name);this.active.add(T.key);
   const t=gen.fresh();
   const branches=d.constructors.map(c=>{
     const bs=c.fields.map(f=>[f.q,gen.fresh()]);
     const fields=c.fields.map((f,i)=>{
       let type=f.type;
       d.parameters.forEach((p,j)=>{type=gen.substituteType(type,p.key,T.args[j]);});
       return {p:V(bs[i][1]),l:V(bs[i][1]),r:this.at(type,V(bs[i][1])),type};
     });
     const packet=tuple(fields.flatMap((f,i)=>[[0,f.p],[0,f.l],[c.fields[i].q,f.r]]));
     const record=tuple([[1,{$:'Lab',k:c.kernel}],[1,packet],[1,rfl],[1,rfl]]);
     return [c.kernel,split(bs,record)];
   });
   gen.emit(name,all(1,t,plan.p,plan.relation(V(t),V(t))),prj(mats(branches)));
   this.active.delete(T.key);
   return name;
 }
}
