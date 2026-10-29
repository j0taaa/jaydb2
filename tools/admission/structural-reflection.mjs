import {R,V,all,lam,app,apps,ann,prj,mats,split,tuple,let1,bind,rfl} from './structural-syntax.mjs';
import {DataValues} from './structural-data.mjs';
import {family} from './structural-relations.mjs';

// Construct reflexive input relations only when this type-directed operation
// is justified. An opaque higher-order domain never receives a fictitious R_h.
export class Reflection {
 constructor(gen){this.gen=gen;this.data=new DataValues(gen);this.cache=new Map();}
 at(T,value){
   if(T.tag==='family'&&T.args.length===0&&this.data.supports(T.key))
     return app(R(this.data.ensure(T.key).reflect),value);
   if(T.tag==='family'&&T.args.length===0)return app(R(this.family(T.key)),value);
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
 family(key){
   const old=this.cache.get(key);if(old!==undefined)return old;
   const gen=this.gen,d=gen.families.get(key),T=family(key),plan=gen.plan(T),name=gen.prefix+'.Input.'+gen.sourceName(key)+'.reflect_input';
   if(d.parameters.length)throw Error('An abstract family input needs its actual relation dictionary');
   this.cache.set(key,name);
   const t=gen.fresh();
   const branches=d.constructors.map(c=>{
     const bs=c.fields.map(f=>[f.q,gen.fresh()]);
     const fields=c.fields.map((f,i)=>({p:V(bs[i][1]),l:V(bs[i][1]),r:this.at(f.type,V(bs[i][1])),type:f.type}));
     const packet=tuple(fields.flatMap((f,i)=>[[0,f.p],[0,f.l],[c.fields[i].q,f.r]]));
     const record=tuple([[1,{$:'Lab',k:c.kernel}],[1,packet],[1,rfl],[1,rfl]]);
     return [c.kernel,split(bs,record)];
   });
   gen.emit(name,all(1,t,plan.p,plan.relation(V(t),V(t))),prj(mats(branches)));
   return name;
 }
}
