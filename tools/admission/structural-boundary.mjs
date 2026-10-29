import {Bodies} from './structural-bodies.mjs';
import {R,V,UT,UV,app,all,sig,lam,tup,ann,prj,bind} from './structural-syntax.mjs';
import {bound} from './structural-relations.mjs';
import {positionedTypeView} from './structural-position.mjs';

// An instance uses the exact physical declaration on the left and its ONE
// symbolic original body at the recorded prefix on the right. The operational
// relation is derived from the actual checked physical .e, not a source claim.
export class BoundaryBodies extends Bodies {
 constructor(source,relations,safe) {
   super(source,relations);this.safe=safe;this.origins=new Map();this.generics=new Map();
   relations.erasedReference=(k,views)=>this.erasedReference(k,views);
   relations.resolveMeta=(f,a,expression)=>this.resolveMeta(f,a,expression);
   relations.physicalReference=k=>this.reference(k);
   for(const [k,variants]of Object.entries(this.book.tmps))for(const [encoded,name]of variants)
     if(this.book.tlds[name]!==undefined)this.origins.set(name,[k,encoded.split('\n').map(x=>this.B.term_higher(JSON.parse(x)))]);
 }
 withViews(views,f){const old=this.source.physicalViews;this.source.physicalViews=views;try{return f();}finally{this.source.physicalViews=old;}}
 originalValue(x){
   if(x.tag==='nat-literal')return this.B.Lit('Nat',x.n);
   if(x.sourceTerm!==undefined)return x.sourceTerm;
   return null;
 }
 resolveMeta(f,a,expression){
   const pending=f.metaResolve;if(pending===undefined)return undefined;
   const xs=[...pending.args,expression],d=this.book.tlds[pending.template];
   if(xs.length!==d.x)return undefined;
   const args=xs.map(x=>this.originalValue(x));if(args.some(x=>x===null))return undefined;
   for(const [k,[template,prefix]]of this.origins){
     if(template!==pending.template||!pending.views.has(this.source.name(k)))continue;
     if(args.length===prefix.length&&args.every((x,i)=>this.B.term_compare('EQ',this.book,x,prefix[i])))return this.reference(k);
   }
   return undefined;
 }
 erasedReference(key,views) {
   const origin=this.origins.get(key);
   if(origin) {
     if(views?.has(this.source.name(key)))return this.reference(key);
     let record=this.erasedReference(origin[0]),T=this.book.tlds[origin[0]].T;
     for(const x of origin[1]){
       const F=this.B.term_wnf(this.book,T),arg=this.gen.value(this.source.value(x,F.A,new Map()),new Map());
       record=this.gen.application(record,arg,new Map());T=F.B(x);
     }
     return record;
   }
   const record=this.generic(key);
   return views?.size&&this.book.tlds[key]?.x>0?{...record,metaResolve:{template:key,views,args:[]}}:record;
 }
 generic(key) {
   return this.withViews(undefined,()=>this.buildGeneric(key));
 }
 buildGeneric(key) {
   const prior=this.generics.get(key);if(prior!==undefined)return prior;
   const d=this.book.tlds[key];
   if(d?.$!=='Def'||d.e===undefined)throw Error('A checked symbolic body is required: '+key);
   const type=this.source.type(d.T),p=this.safe.logical(key),l=p,name=this.gen.prefix+'.Function.'+this.source.name(key)+'.symbolic';
   const record={p,l,type,key,r:R(name),metaRqs:[]};this.generics.set(key,record);
   let T=d.T,ir=type,pp=p,ll=l;const env=new Map(),ctx=new Map(),bs=[];
   for(let i=0;i<d.x;i++){
     const F=this.B.term_wnf(this.book,T),A=this.gen.plan(ir.A,env),xp=this.gen.fresh(),xl=this.gen.fresh(),r=this.gen.fresh();
     const rq=A.quantity===2?2:0;record.metaRqs.push(rq);
     bs.push([0,xp,A.p],[0,xl,A.l],[rq,r,A.relation(V(xp),V(xl))]);
     const arg={p:V(xp),l:V(xl),r:V(r),type:ir.A,expression:bound(ir.key)};
     env.set(ir.key,arg);ctx.set('ref:'+key+'~'+F.k,ir.key);
     T=F.B(this.B.Ref(key+'~'+F.k));pp=app(pp,V(xp),ir.q);ll=app(ll,V(xl),ir.q);ir=ir.B;
   }
   const U=bind('All',bs,this.gen.plan(ir,env).relation(pp,ll));
   const live=record.metaRqs.every(q=>q===2);
   if(!live){
     const a=this.gen.fresh(),u=this.gen.fresh(),v=this.gen.fresh();
     record.r=app(ann(prj(lam(0,a,lam(1,u,V(a)))),all(1,v,sig(0,a,U,UT),U)),R(name));
   }
   const previous=this.symbolic;this.symbolic=true;
   let body;
   try{body=this.functionBody(this.B.term_higher(d.e),T,ir,env,ctx,pp,ll);}finally{this.symbolic=previous;}
   if(live)this.gen.emit(name,U,bind('Lam',bs,body));
   else {const a=this.gen.fresh();this.gen.emit(name,sig(0,a,U,UT),tup(0,bind('Lam',bs,body),UV));}
   return record;
 }
 expression(t,env,ctx,expected) {
   const {x}=this.open(t);
   if(x.$==='Ref') {
     const local=ctx.get('ref:'+x.k);if(local!==undefined)return env.get(local);
     if(this.symbolic&&this.book.tlds[x.k]?.$==='Def')return this.erasedReference(x.k);
     if(this.book.tlds[x.k]?.$==='Def'&&this.book.tlds[x.k].x>0)return this.generic(x.k);
   }
   return super.expression(t,env,ctx,expected);
 }
 specializeType(sourceType,ctx,prior,env){
   const type=this.source.type(sourceType,ctx);
   return !this.symbolic&&this.safe.state.admissionViewOps?positionedTypeView(this,type,this.gen.plan(prior,env).p):type;
 }
 render(t,sourceType,side,env,ctx) {
   const {x}=this.open(t);
   if(x.$==='Ref'&&ctx.has('ref:'+x.k))return env.get(ctx.get('ref:'+x.k))[side];
   if(x.$==='Ref'&&this.book.tlds[x.k]?.$==='Def')return (this.symbolic?this.erasedReference(x.k):this.reference(x.k))[side];
   return super.render(t,sourceType,side,env,ctx);
 }
 reference(key) {
   const old=this.functions.get(key);if(old!==undefined)return old;
   return this.withViews(undefined,()=>this.buildReference(key));
 }
 buildReference(key) {
   const old=this.functions.get(key);if(old!==undefined)return old;
   const d=this.book.tlds[key];
   if(d?.$!=='Def'||d.e===undefined||d.x!==0)throw Error('An available checked physical declaration is required: '+key);
   let type=this.source.type(d.T);const p=R(this.source.name(key));let l;
   const view=this.safe.state.admissionTypeViews?.get(this.source.name(key));
   if(view&&this.safe.state.admissionViewOps)type=positionedTypeView(this,type,view.observed);
   const origin=this.origins.get(key);
   if(origin) {
     l=this.safe.logical(origin[0]);let T=this.book.tlds[origin[0]].T;
     for(const x of origin[1]) {
       const F=this.B.term_wnf(this.book,T);
       l=app(l,this.safe.term(this.B.Ann(x,F.A)),this.source.q(F.q));T=F.B(x);
     }
   } else l=this.safe.logical(key);
   const r=R(this.gen.prefix+'.Function.'+this.source.name(key)+'.evaluate');
   const record={p,l,r,type,key};this.functions.set(key,record);
   const T=this.gen.plan(type).relation(p,l);
   const b=this.functionBody(this.B.term_higher(d.e),d.T,type,new Map(),new Map(),p,l);
   this.gen.emit(r.k,T,b);return record;
 }
}
