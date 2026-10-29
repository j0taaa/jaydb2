import {Syntax,V,R,K,UT,UV,all,lam,app,apps,tup,tuple,bind,prj,mats,unit,ann,eq,rfl,split,rwt,let1} from './structural-syntax.mjs';

// Type-directed relations from the checked source structure. Abstract
// relations are explicit parameters, constructed at every closed boundary;
// they are never assumed for an opaque actual callee.
export const scalar = (T,quantity=2) => ({ tag:'scalar',T,quantity });
export const universe = (quantity=1) => ({ tag:'universe',quantity });
export const bound = key => ({ tag:'bound',key });
export const arrow = (q,key,A,B) => ({ tag:'arrow',q,key,A,B });
export const family = (key,args=[]) => ({ tag:'family',key,args });
export const apply = (f,x) => ({ tag:'apply',f,x });
export const typeValue = T => ({ tag:'type',T });
export const identity = (A,a,b) => ({ tag:'identity',A,a,b });

export class Relations {
  constructor({syntax=new Syntax(), families=new Map(), prefix='Representation'}={}) {
    this.syntax=syntax; this.families=families; this.prefix=prefix;
    this.generated=new Map(); this.declarations=[];
  }
  fresh() { return this.syntax.fresh(); }
  emit(k,T,b) { this.declarations.push([k,T,b]); }
  eta(T,value) {
    if(T.tag!=='arrow')return value;
    const v=this.fresh(),argument=this.eta(T.A,V(v));
    return lam(T.q,v,this.eta(T.B,app(value,argument,T.q)));
  }
  carrier(d,env,side) {
    return apps(R(d.kernel),d.parameters.map(p=>[p.q,this.eta(p.type,env.get(p.key)[side])]));
  }
  kind(quantity,env=new Map()){
    if(typeof quantity==='number')return {p:{$:'Lab',k:'Q'+quantity},l:{$:'Lab',k:'Q'+quantity},common:{$:'Lab',k:'Q'+quantity}};
    const q=this.value(quantity,env);return {p:q.p,l:q.l,common:{$:'Min',a:q.p,b:q.l}};
  }
  scalar(T,quantity,p,l) {
    const y=this.fresh(),ep=this.fresh(),el=this.fresh();
    return bind('Sig',[[1,y,T],[1,ep,eq(V(y),p,T)],[1,el,eq(V(y),l,T)]],UT);
  }
  plan(T,env=new Map()) {
    switch(T.tag) {
      case 'scalar': return {p:T.T,l:T.T,quantity:T.quantity,relation:(p,l)=>this.scalar(T.T,T.quantity,p,l)};
      case 'universe': {
        const q=this.kind(T.quantity,env);
        return {p:K(q.p),l:K(q.l),quantity:1,relation:(p,l)=>{
          const a=this.fresh(),b=this.fresh();
          return all(0,a,p,all(0,b,l,K(q.common)));
        }};
      }
      case 'identity': {
        const A=this.plan(T.A,env),a=this.value(T.a,env),b=this.value(T.b,env);
        const ap=this.eta(T.A,a.p),al=this.eta(T.A,a.l),bp=this.eta(T.A,b.p),bl=this.eta(T.A,b.l);
        const P=eq(ap,bp,A.p),L=eq(al,bl,A.l);
        return {p:P,l:L,quantity:2,relation:(p,l)=>{
          const vp=this.fresh(),vl=this.fresh(),ip=this.fresh(),il=this.fresh(),co=this.fresh(),zp=this.fresh(),zl=this.fresh();
          const moveP=rwt(V(vp),zp,A.relation(V(zp),al),a.r);
          const moveL=rwt(V(vl),zl,A.relation(bp,V(zl)),moveP);
          // Keep actual live evidence for each proposition, links to the
          // exact evidence indices, and coherence of the endpoint relation.
          // No proof irrelevance or equality of distinct Fn heads is assumed.
          return bind('Sig',[[1,vp,P],[1,vl,L],[1,ip,eq(V(vp),p,P)],[1,il,eq(V(vl),l,L)],
            [1,co,eq(moveL,b.r,A.relation(bp,bl))]],UT);
        }};
      }
      case 'bound': case 'apply': {
        const v=this.value(T,env);
        if(v.type.tag!=='universe')throw Error('A type must inhabit a known source universe');
        return {p:v.p,l:v.l,quantity:v.type.quantity,relation:(p,l)=>apps(v.r,[[0,p],[0,l]])};
      }
      case 'arrow': {
        const A=this.plan(T.A,env),p=this.fresh(),l=this.fresh(),r=this.fresh();
        const e=new Map(env); e.set(T.key,{p:V(p),l:V(l),r:V(r),type:T.A});
        const B=this.plan(T.B,e), rq=T.q;
        return {
          p:all(T.q,p,A.p,B.p),l:all(T.q,l,A.l,B.l),quantity:1,
          relation:(fp,fl)=>bind('All',[[0,p,A.p],[0,l,A.l],[rq,r,A.relation(V(p),V(l))]],B.relation(app(fp,this.eta(T.A,V(p)),T.q),app(fl,this.eta(T.A,V(l)),T.q))),
          parameters:{p,l,r,A,B,rq,env:e}
        };
      }
      case 'family': {
        const generated=this.generateFamily(T.key),d=this.families.get(T.key);
        if(T.args.length!==d.parameters.length)throw Error('Family arity: '+T.key);
        const values=T.args.map((x,i)=>{const v=this.value(x,env);return {...v,p:this.eta(d.parameters[i].type,v.p),l:this.eta(d.parameters[i].type,v.l)}});
        const p=apps(R(d.kernel),values.map((x,i)=>[d.parameters[i].q,x.p]));
        const l=apps(R(d.kernel),values.map((x,i)=>[d.parameters[i].q,x.l]));
        const rs=values.flatMap(x=>[[0,x.p],[0,x.l],[0,x.r]]);
        return {p,l,quantity:d.quantity??1,relation:(p,l)=>apps(R(generated.name),[...rs,[0,p],[0,l]]),family:generated,values};
      }
      default: throw Error('Unimplemented structural type constructor: '+T.tag);
    }
  }
  value(x,env,expected) {
    if(x.tag==='quantity-minimum')return this.quantityMinimum(this.value(x.a,env),this.value(x.b,env));
    if(x.tag==='physical-reference')return this.physicalReference(x.key);
    if(x.tag==='erased-reference')return this.erasedReference(x.key,x.physicalViews);
    if(x.tag==='nat-literal') {
      let value=this.constructorValue('Nat','Zero',[]);
      for(let i=0;i<x.n;i++)value=this.constructorValue('Nat','Succ',[value]);
      return {...value,expression:x};
    }
    if(x.tag==='source') {
      if(this.sourceValue===undefined)throw Error('A typed source value translator is required');
      return this.sourceValue(x,env,expected);
    }
    if(x.tag==='constant') {
      return {p:x.value,l:x.value,r:tuple([[1,x.value],[1,rfl],[1,rfl]]),type:x.type,expression:x};
    }
    if(x.tag==='bound') {
      const v=env.get(x.key); if(v===undefined)throw Error('Unbound relational parameter '+x.key);
      return v;
    }
    if(x.tag==='type') {
      const T=this.plan(x.T,env),p=this.fresh(),l=this.fresh();
      return {p:T.p,l:T.l,r:lam(0,p,lam(0,l,T.relation(V(p),V(l)))),type:universe(T.quantity),expression:x};
    }
    if(x.tag==='apply') {
      const f=this.value(x.f,env),xv=this.value(x.x,env,f.type.A);
      if(f.type.tag!=='arrow')throw Error('Nonfunction relational application');
      const resolved=this.resolveMeta?.(f,xv,x.x);
      if(resolved!==undefined)return resolved;
      const e=new Map(env);e.set(f.type.key,xv);
      // A dictionary/evaluator is applied once. Physical/logical calls are
      // erased indices. The source quantity also governs the representation.
      const p=this.eta(f.type.A,xv.p),l=this.eta(f.type.A,xv.l);
      return {p:app(f.p,p,f.type.q),l:app(f.l,l,f.type.q),r:apps(f.r,[[0,p],[0,l],[f.metaRqs?.[0]??f.type.q,xv.r]]),metaRqs:f.metaRqs?.slice(1),metaResolve:f.metaResolve&&{...f.metaResolve,args:[...f.metaResolve.args,x.x]},type:this.substituteType(f.type.B,f.type.key,x.x),expression:x};
    }
    throw Error('Unimplemented structural value constructor: '+x.tag);
  }
  quantityMinimum(a,b){
    const Q={$:'Enu',ks:['Q0','Q1','Q2']},type=scalar(Q,2),min=(a,b)=>({$:'Min',a,b});
    const ap=this.fresh(),ae=this.fresh(),al=this.fresh(),bp=this.fresh(),be=this.fresh(),bl=this.fresh(),y=this.fresh();
    const p=min(a.p,b.p),l=min(a.l,b.l);
    const proof=side=>{
      const z=this.fresh(),w=this.fresh(),A=side==='p'?a.p:a.l,B=side==='p'?b.p:b.l;
      const first=rwt(V(side==='p'?ae:al),z,eq(V(y),min(V(z),V(bp)),Q),rfl);
      return rwt(V(side==='p'?be:bl),w,eq(V(y),min(A,V(w)),Q),first);
    };
    let body=let1(y,min(V(ap),V(bp)),tuple([[1,V(y)],[1,proof('p')],[1,proof('l')]]));
    body=app(split([[2,bp],[2,be],[2,bl]],body),b.r);
    body=app(split([[2,ap],[2,ae],[2,al]],body),a.r);
    return {p,l,r:ann(body,this.plan(type).relation(p,l)),type};
  }
  substituteType(T,key,x) {
    if(T.tag==='bound')return T.key===key?(x.tag==='type'?x.T:x):T;
    if(T.tag==='arrow')return {...T,A:this.substituteType(T.A,key,x),B:T.key===key?T.B:this.substituteType(T.B,key,x)};
    if(T.tag==='family')return {...T,args:T.args.map(a=>this.substituteValue(a,key,x))};
    if(T.tag==='apply')return {...T,f:this.substituteValue(T.f,key,x),x:this.substituteValue(T.x,key,x)};
    if(T.tag==='identity')return {...T,A:this.substituteType(T.A,key,x),a:this.substituteValue(T.a,key,x),b:this.substituteValue(T.b,key,x)};
    return T;
  }
  substituteValue(v,key,x) {
    if(v.tag==='bound')return v.key===key?x:v;
    if(v.tag==='type')return {...v,T:this.substituteType(v.T,key,x)};
    if(v.tag==='apply')return {...v,f:this.substituteValue(v.f,key,x),x:this.substituteValue(v.x,key,x)};
    if(v.tag==='quantity-minimum')return {...v,a:this.substituteValue(v.a,key,x),b:this.substituteValue(v.b,key,x)};
    return v;
  }
  parameters(d) {
    let env=new Map();const bs=[];
    for(const param of d.parameters) {
      const plan=this.plan(param.type,env),p=this.fresh(),l=this.fresh(),r=this.fresh();
      bs.push([0,p,plan.p],[0,l,plan.l],[0,r,plan.relation(V(p),V(l))]);
      env.set(param.key,{p:V(p),l:V(l),r:V(r),type:param.type});
    }
    return {env,bs};
  }
  fields(d,c,env) {
    const e=new Map(env),bs=[],records=[];
    for(const field of c.fields) {
      const plan=this.plan(field.type,e),p=this.fresh(),l=this.fresh(),r=this.fresh();
      const record={p:V(p),l:V(l),r:V(r),type:field.type,plan,q:field.q};
      bs.push([0,p,plan.p],[0,l,plan.l],[field.q,r,plan.relation(V(p),V(l))]);
      records.push(record);e.set(field.key,record);
    }
    return {env:e,bs,records};
  }
  construct(c,records,side) {
    // Opaque fields are reconstructed exactly. Eta-long source construction
    // is handled by constructorValue at the source boundary, not postulated
    // for an arbitrary function extracted from an open constructor.
    return tup(1,{$:'Lab',k:c.kernel},tuple(records.map((r,i)=>[c.fields[i].q,r[side]])));
  }
  fieldType(g,tag,env) {
    const params=g.definition.parameters.flatMap(p=>{const x=env.get(p.key);return [[0,x.p],[0,x.l],[0,x.r]]});
    return apps(R(g.fieldsName),[...params,[1,tag]]);
  }
  reconstruct(g,tag,fields,env,side) {
    const t=this.fresh(),fs=this.fresh();
    const branches=g.definition.constructors.map(c=>{
      const f=this.fields(g.definition,c,env);
      return [c.kernel,split(f.bs,this.construct(c,f.records,side))];
    });
    const result=this.carrier(g.definition,env,side);
    const T=all(1,t,g.tags,all(1,fs,this.fieldType(g,V(t),env),result));
    return apps(ann(mats(branches),T),[[1,tag],[1,fields]]);
  }
  generateFamily(key) {
    const old=this.generated.get(key);if(old!==undefined)return old;
    const d=this.families.get(key);if(d===undefined)throw Error('Unknown source family '+key);
    const name=this.prefix+'.Family.'+d.kernel+'.Rel',fieldsName=name+'Fields';
    const g={name,fieldsName,definition:d,tags:{$:'Enu',ks:d.constructors.map(c=>c.kernel)}};
    // Reserve before descending into fields: recursive families refer to the
    // same declaration, never an expansion indexed by ordinary values.
    this.generated.set(key,g);
    const parameters=this.parameters(d),env=parameters.env,bs=parameters.bs;
    const branches=d.constructors.map(c=>[c.kernel,bind('Sig',this.fields(d,c,env).bs,UT)]);
    const tag0=this.fresh();
    const kind=this.kind(d.quantity??1,env).common;
    this.emit(fieldsName,bind('All',bs,all(1,tag0,g.tags,K(kind))),bind('Lam',bs,mats(branches)));
    const P=this.carrier(d,env,'p'),L=this.carrier(d,env,'l');
    const p=this.fresh(),l=this.fresh(),tag=this.fresh(),fs=this.fresh(),ep=this.fresh(),el=this.fresh();
    const T=bind('All',bs,all(0,p,P,all(0,l,L,K(kind))));
    const body=bind('Lam',bs,lam(0,p,lam(0,l,bind('Sig',[
      [1,tag,g.tags],[1,fs,this.fieldType(g,V(tag),env)],
      [1,ep,eq(this.reconstruct(g,V(tag),V(fs),env,'p'),V(p),P)],
      [1,el,eq(this.reconstruct(g,V(tag),V(fs),env,'l'),V(l),L)]
    ],UT))));
    this.emit(name,T,body);
    for(const c of d.constructors)this.generateConstructor(g,c,parameters);
    return g;
  }
  generateConstructor(g,c,parameters) {
    const {env,bs}=parameters,f=this.fields(g.definition,c,env);
    const p=this.construct(c,f.records,'p'),l=this.construct(c,f.records,'l');
    const type=this.plan(family(g.definition.key,g.definition.parameters.map(p=>bound(p.key))),env).relation(p,l);
    const fields=tuple(f.records.flatMap(r=>[[0,r.p],[0,r.l],[r.q,r.r]]));
    const body=tuple([[1,{$:'Lab',k:c.kernel}],[1,fields],[1,rfl],[1,rfl]]);
    this.emit(g.name+'.'+c.kernel,bind('All',[...bs,...f.bs],type),bind('Lam',[...bs,...f.bs],body));
  }
  constructorValue(key,ctor,values,parameterValues=[]) {
    const g=this.generateFamily(key),d=g.definition,c=d.constructors.find(c=>c.key===ctor);
    if(c===undefined||c.fields.length!==values.length||d.parameters.length!==parameterValues.length)throw Error('Typed constructor arity mismatch');
    // The source constructor's instantiated domain may reveal an All which
    // the generic family telescope leaves abstract. Normalize those actual
    // field indices BEFORE packing the generic field representation.
    values=values.map(v=>({...v,p:this.eta(v.type,v.p),l:this.eta(v.type,v.l)}));
    const p=this.construct(c,values,'p'),l=this.construct(c,values,'l');
    const packet=tuple(values.flatMap((r,i)=>[[0,r.p],[0,r.l],[c.fields[i].q,r.r]]));
    return {p,l,r:tuple([[1,{$:'Lab',k:c.kernel}],[1,packet],[1,rfl],[1,rfl]]),type:family(key,parameterValues.map(v=>v.expression))};
  }
  emitCarrier(key) {
    const d=this.families.get(key);if(d===undefined)throw Error('Unknown carrier '+key);
    const env=new Map(),bs=[];
    for(const param of d.parameters) {
      const A=this.plan(param.type,env),v=this.fresh();bs.push([param.q,v,A.p]);
      // Only the physical component is used in a carrier's telescope.
      env.set(param.key,{p:V(v),l:V(v),r:V(this.fresh()),type:param.type});
    }
    const tag=this.fresh(),tags={$:'Enu',ks:d.constructors.map(c=>c.kernel)},armsName=d.kernel+'.arms';
    const branches=d.constructors.map(c=>{
      const e=new Map(env),fields=[];
      for(const field of c.fields) {
        const A=this.plan(field.type,e),v=this.fresh();fields.push([field.q,v,A.p]);
        e.set(field.key,{p:V(v),l:V(v),r:V(this.fresh()),type:field.type});
      }
      return [c.kernel,bind('Sig',fields,UT)];
    });
    const G=K(d.quantity??1),arms=apps(R(armsName),bs.map(([q,l])=>[q,V(l)]));
    return [[armsName,bind('All',bs,all(1,tag,tags,G)),bind('Lam',bs,mats(branches))],
      [d.kernel,bind('All',bs,G),bind('Lam',bs,{$:'Sig',q:1,l:tag,A:tags,B:app(arms,V(tag))})]];
  }
  eliminate(g,env,p,l,motive,handler,{extra=[]}={}) {
    const branches=g.definition.constructors.map(c=>{
      const fs=this.fresh(),ep=this.fresh(),el=this.fresh();
      const field=this.fields(g.definition,c,env),cp=this.construct(c,field.records,'p'),cl=this.construct(c,field.records,'l');
      const pTy=this.plan(family(g.definition.key,g.definition.parameters.map(p=>bound(p.key))),env);
      const packet=tuple(field.records.flatMap(r=>[[0,r.p],[0,r.l],[r.q,r.r]]));
      const record=(ep,el)=>tuple([[1,{$:'Lab',k:c.kernel}],[1,packet],[1,ep],[1,el]]);
      const branchBody=bind('Lam',extra,handler(c,field,extra));
      const ip=this.fresh(),il=this.fresh(),np=this.fresh(),nl=this.fresh();
      const paths=[{index:'p',proof:'ep',A:pTy.p,a:cp},{index:'l',proof:'el',A:pTy.l,a:cl}];
      const goal=s=>bind('All',extra,motive(s.p,s.l,record(s.ep,s.el)));
      const telescope=(s,i)=>{
        if(i===paths.length)return goal(s);
        const path=paths[i],v=this.fresh(),e=this.fresh();
        return all(0,v,path.A,all(1,e,eq(path.a,V(v),path.A),telescope({...s,[path.index]:V(v),[path.proof]:V(e)},i+1)));
      };
      const derive=(s,i)=>{
        if(i===paths.length)return branchBody;
        const path=paths[i],v=this.fresh(),e=this.fresh(),z=this.fresh();
        return lam(0,v,lam(1,e,rwt(V(e),z,telescope({...s,[path.index]:V(z),[path.proof]:V(z+1)},i+1),derive({...s,[path.index]:path.a,[path.proof]:rfl},i+1))));
      };
      const endpoint=ann(derive({},0),telescope({},0));
      const eps=[[1,ip,eq(cp,p,pTy.p)],[1,il,eq(cl,l,pTy.l)]];
      const invoke=apps(endpoint,[[0,p],[1,V(ip)],[0,l],[1,V(il)]]);
      // The motive tracks the WHOLE record, including its exact endpoint
      // evidence. Keeping a fixed old R while changing its indices is invalid.
      const cont=ann(bind('Lam',eps,invoke),bind('All',eps,goal({p,l,ep:V(ip),el:V(il)})));
      const inner=split(field.bs,cont);
      const call=apps(inner,[[1,V(fs)],[1,V(ep)],[1,V(el)],...extra.map(([q,n])=>[q,V(n)])]);
      return [c.kernel,split([[1,fs],[1,ep],[1,el]],bind('Lam',extra,call))];
    });
    return prj(mats(branches));
  }
  generateProjection(key) {
    const g=this.generateFamily(key),d=g.definition;
    if(d.constructors.length!==1||d.constructors[0].fields.length!==1)return null;
    const c=d.constructors[0],field=c.fields[0];
    if(field.q===0)return null; // An erased field cannot become a live value.
    const params=this.parameters(d),env=params.env;
    const valueType=this.plan(field.type,env);
    const originalName=g.name+'.project',name=originalName+'.evaluate';
    // The ordinary projection keeps exactly the source type/field layout.
    // It is a generated kernel helper, never a replacement physical .e.
    const pbs=d.parameters.map(p=>{
      const r=env.get(p.key),A=this.plan(p.type,env);return [p.q,r.p.l,A.p];
    });
    const P=this.plan(family(key,d.parameters.map(p=>bound(p.key))),env);
    const p=this.fresh(),l=this.fresh(),rt=this.fresh(),v=this.fresh();
    this.emit(originalName,bind('All',pbs,all(1,p,P.p,valueType.p)),bind('Lam',pbs,prj(mats([[c.kernel,split([[field.q,v]],V(v))]]))));
    // The logical call has the logical type parameters; its runtime code is
    // the SAME checked source projection, not an independently specialized
    // logical declaration.
    const call=(x,side)=>apps(R(originalName),[...d.parameters.map(p=>[p.q,env.get(p.key)[side]]),[1,x]]);
    const motive=(x,y)=>valueType.relation(call(x,'p'),call(y,'l'));
    const T=bind('All',params.bs,bind('All',[[0,p,P.p],[0,l,P.l],[1,rt,P.relation(V(p),V(l))]],motive(V(p),V(l))));
    const b=this.eliminate(g,env,V(p),V(l),motive,(c,f)=>f.records[0].r);
    this.emit(name,T,bind('Lam',params.bs,lam(0,p,lam(0,l,b))));
    return {name,originalName};
  }
  // Typed evaluator use; result carries the supplied source codomain after
  // substitution. Returning/partially applying a function therefore returns
  // its evaluator, rather than an equality of function heads.
  application(f,x,env=new Map()) {
    if(f.type.tag!=='arrow')throw Error('Expected a represented function');
    const p=this.eta(f.type.A,x.p),l=this.eta(f.type.A,x.l);
    return {
      p:app(f.p,p,f.type.q),l:app(f.l,l,f.type.q),
      r:apps(f.r,[[0,p],[0,l],[f.metaRqs?.[0]??f.type.q,x.r]]),metaRqs:f.metaRqs?.slice(1),
      type:this.substituteType(f.type.B,f.type.key,x.expression??bound(x.key)),
      environment:new Map([...env,[f.type.key,x]])
    };
  }
}
