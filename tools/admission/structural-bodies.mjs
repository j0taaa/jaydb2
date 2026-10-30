import {V,R,tuple,lam,app,apps,bind,ann,eq,rfl,rwt} from './structural-syntax.mjs';
import {bound} from './structural-relations.mjs';

// Typed composition over checked .e. Unsupported syntax fails technically;
// it never supplies a substitute witness or bypasses a physical guard.
export class Bodies {
  constructor(source,relations) {
    this.source=source;this.gen=relations;this.B=source.B;this.book=source.book;this.functions=new Map();this.sequence=0;
    relations.sourceValue=(x,env,expected)=>this.expression(x.expected===null?x.term:this.B.Ann(x.term,x.expected),env,x.context,expected);
  }
  open(t) { let T=null;t=this.B.term_force(t);while(t.$==='Ann'){T??=this.B.term_force(t.T);t=this.B.term_force(t.x);}return {x:t,T}; }
  locals(x,env,ctx,read) {
    const values=x.v.map(read),e=new Map(env),c=new Map(ctx),vars=[],bindings=[];
    for(let i=0;i<values.length;i++) {
      const key='local.'+this.sequence++,id=this.source.depth++,v=this.B.Var(x.k[i],id),r=this.gen.fresh();
      e.set(key,{...values[i],r:V(r),expression:bound(key)});
      c.set(id,key);c.set(x.i[i],key);vars.push(v);bindings.push([this.source.q(x.q[i]),r,values[i]]);
    }
    return {body:x.f(vars),env:e,ctx:c,bindings};
  }
  definitionBody(key,body,sourceType,type,env,ctx,physical,logical) {
    // Independent family instances share deferred opening. Field quantities
    // are preserved unless their checked relation is Data.
    const matched=new Set();
    const depends=x=>{
      if(!x||typeof x!=='object')return false;
      if(x.tag==='bound')return matched.has(x.key);
      if(x.tag==='source')return [...x.context.values()].some(k=>matched.has(k));
      return Object.entries(x).some(([k,v])=>!['sourceTerm','sourceType','sourceContext','physicalViews'].includes(k)&&depends(v));
    };
    // Read binder/pattern shape only. A proof domain depending on an earlier
    // scrutinized value keeps the immediate, dependent transport.
    const consume=(body,n)=>{
      if(n===0)return [body];const {x}=this.open(body);
      if(x.$==='Lam')return consume(x.f(this.B.Var('_',this.source.depth++)),n-1);
      if(x.$==='Efq')return [];
      if(x.$==='Mat'){
        const h=consume(x.h,n-1+this.book.ctrs[x.k].n),m=consume(x.m,n);
        return h===null||m===null?null:[...h,...m];
      }
      return null;
    };
    const independent=(A,seen=new Map())=>{
      if(A.tag==='identity')return independent(A.A,seen)&&!depends(A);
      if(A.tag==='scalar')return A.T.$==='Enu'&&typeof A.quantity==='number';
      if(A.tag==='arrow')return independent(A.A,seen)&&independent(A.B,seen);
      if(A.tag!=='family'||A.args.some(x=>x.tag!=='type'&&!(x.tag==='constant'&&/^Q[012]$/.test(x.value.k))))return false;
      const d=this.gen.families.get(A.key);
      if(!d)return false;
      const plan=this.gen.plan(A);if(![1,2].includes(plan.quantity))return false;
      const key=this.gen.termKey(plan.p);
      if(seen.has(A.key))return seen.get(A.key)===key;
      const next=new Map(seen);next.set(A.key,key);
      return d.constructors.every(c=>c.fields.every(f=>{
        let type=f.type;
        d.parameters.forEach((p,i)=>{type=this.gen.substituteType(type,p.key,A.args[i]);});
        return independent(type,next);
      }));
    };let T=type,n=0;
    let heads=[body];
    while(T.tag==='arrow'&&T.q>0&&['family','identity'].includes(T.A.tag)&&independent(T.A)){
      if(heads===null||heads.some(b=>this.open(b).x.$!=='Lam'))matched.add(T.key);
      if(heads!==null){const next=heads.map(b=>consume(b,1));heads=next.some(x=>x===null)?null:next.flat();}
      n++;T=T.B;
    }
    const cases=n>0&&T.tag==='identity'?{key,physical,logical,type,args:[],frames:[],skip:0}:null;
    const previous=this.caseDefinition;this.caseDefinition=key;
    try{return this.functionBody(body,sourceType,type,env,ctx,physical,logical,cases);}
    finally{this.caseDefinition=previous;}
  }
  caseEnvironment(base,frames,state) {
    const env=new Map(base);
    // Rebuild children before parents, preserving the supplied evidence.
    for(const f of [...frames].reverse()){
      const fields=f.keys.map(key=>env.get(key)),cp=this.gen.construct(f.ctor,fields,'p'),cl=this.gen.construct(f.ctor,fields,'l');
      env.set(f.key,{...base.get(f.key),p:state[f.id+'.p']??cp,l:state[f.id+'.l']??cl,
        r:this.gen.caseRecord(f.ctor,fields,state[f.id+'.ep']??rfl,state[f.id+'.el']??rfl),expression:bound(f.key)});
    }
    return env;
  }
  caseLeaf(body,type,base,ctx,cases) {
    const {frames,args}=cases,goal=env=>this.gen.plan(type,env).relation(
      apps(cases.physical,args.map(([key,q])=>[q,env.get(key).p])),apps(cases.logical,args.map(([key,q])=>[q,env.get(key).l])));
    const canonical=this.caseEnvironment(base,frames,{}),slots=[],oldApply=this.gen.application;
    const key=this.safe?.state.admissionViewOps?.key??JSON.stringify,equal=(a,b)=>key(a)===key(b);
    const build=state=>{
      const env=this.caseEnvironment(base,frames,state),calls=[];let position=0;
      this.gen.application=(f,a,e)=>{
        const result=oldApply.call(this.gen,f,a,e);
        if(this.caseDefinition!==cases.key)return result;
        const chain=f.caseChain??(f.key===cases.key?{head:f,args:[]}:null);
        if(!chain)return result;
        const next={head:chain.head,args:[...chain.args,a]};result.caseChain=next;
        if(result.type.tag==='arrow')return result;
        const actual=next.args.map((arg,i)=>{
          const formal=args[i-this.book.tlds[cases.key].x]?.[0],origin=canonical.get(formal),target=env.get(formal);
          return origin&&equal(arg.p,origin.p)&&equal(arg.l,origin.l)&&equal(arg.r,origin.r)?target:arg;
        });
        let value=next.head;for(const arg of actual)value=oldApply.call(this.gen,value,arg,env);
        const slot=slots[position]??(slots[position]=this.gen.fresh());position++;
        calls.push({slot,value,T:this.gen.plan(value.type,env).relation(value.p,value.l)});
        return {...value,r:V(slot)};
      };
      let value;try{value=this.expression(body,env,ctx,type);}finally{this.gen.application=oldApply;}
      return {value,calls,env};
    };
    const count=build({}).calls.length;
    const describe=state=>{const b=build(state);if(b.calls.length!==count)throw Error('The recursive call inventory changed under endpoint substitution');return b;};
    const paths=[...frames].reverse().flatMap(f=>['p','l'].map(side=>({index:f.id+'.'+side,proof:f.id+'.e'+side,A:f.type[side],q:2,
      value:f[side],evidence:f['e'+side],start:state=>this.gen.construct(f.ctor,f.keys.map(key=>this.caseEnvironment(base,frames,state).get(key)),side)})));
    const final=state=>{const b=describe(state);return bind('All',b.calls.map(c=>[2,c.slot,c.T]),goal(b.env));};
    const derive=state=>{const b=describe(state);return bind('Lam',b.calls.map(c=>[2,c.slot,c.T]),ann(b.value.r,goal(b.env)));};
    const actualState={};for(const f of frames)Object.assign(actualState,{[f.id+'.p']:f.p,[f.id+'.l']:f.l,[f.id+'.ep']:f.ep,[f.id+'.el']:f.el});
    const actual=describe(actualState);
    // Results are dependent J arguments, supplied by actual checked recursive
    // calls outside J with the original ep/el and the real smaller fields.
    return apps(this.gen.transport(paths,final,derive),actual.calls.map(c=>[2,c.value.r]));
  }
  functionBody(body,sourceType,type,env,ctx,physical,logical,cases=null) {
    const {x}=this.open(body);
    if(type.tag!=='arrow') {
      if(cases?.frames.length)return this.caseLeaf(body,type,env,ctx,cases);
      const value=this.expression(body,env,ctx,type);
      return ann(value.r,this.gen.plan(type,env).relation(physical,logical));
    }
    const F=this.B.term_wnf(this.book,sourceType);
    if(F.$!=='All')throw Error('Source and relation telescope disagree');
    const A=this.gen.plan(type.A,env),p=this.gen.fresh(),l=this.gen.fresh(),r=this.gen.fresh();
    const arg={p:V(p),l:V(l),r:V(r),type:type.A,q:type.q,expression:bound(type.key)};
    const e=new Map(env);e.set(type.key,arg);
    const nextCases=cases&&{...cases,type:cases.skip?cases.type:type.B,args:cases.skip?cases.args:[...cases.args,[type.key,type.q]],skip:Math.max(0,cases.skip-1)};
    const remainingType=cases?.skip===1?cases.type:type.B;
    const opened=this.source.open(F,ctx,type.key),cctx=opened.ctx;
    if(x.$==='Lam')cctx.set(x.i,type.key);
    const nextSource=F.B(opened.v),pp=app(physical,this.gen.eta(type.A,V(p)),type.q),ll=app(logical,this.gen.eta(type.A,V(l)),type.q);
    let b;
    if(x.$==='Lam')b=this.functionBody(x.f(opened.v),nextSource,remainingType,e,cctx,pp,ll,nextCases);
    else if((x.$==='Mat'||x.$==='Efq'&&this.gen.families.get(type.A.key)?.constructors.length===0)&&type.A.tag==='family') {
      const familyPlan=this.gen.plan(type.A,env),g=familyPlan.family;
      const familyEnv=new Map(e);
      g.definition.parameters.forEach((p,i)=>familyEnv.set(p.key,familyPlan.values[i]));
      const motive=(p,l,r)=>{
        const t=new Map(e);t.set(type.key,{...arg,p,l,r});
        return this.gen.plan(type.B,t).relation(app(physical,this.gen.eta(type.A,p),type.q),app(logical,this.gen.eta(type.A,l),type.q));
      };
      const eliminator=this.gen.eliminate(g,familyEnv,V(p),V(l),motive,(ctor,fields,extra,frame)=>{
        Object.assign(frame,{key:type.key,keys:[]});
        let branch=x;
        while(branch.$==='Mat'&&branch.k!==ctor.key)branch=this.open(branch.m).x;
        const defaultBranch=branch.$!=='Mat';
        if(defaultBranch&&branch.$!=='Lam')throw Error('A source-tree branch must be an explicit arm or checked default binder');
        let h=defaultBranch?null:branch.h,fieldSource=this.book.ctrs[ctor.key].T;
        const domain=this.B.term_wnf(this.book,F.A);
        fieldSource=this.B.tele_fill(this.book,fieldSource,domain.x,this.B.ctx_nil());
        let fctx=new Map(cctx),fenv=new Map(fields.env);const sourceFields=[];
        const cp=this.gen.construct(ctor,fields.records,'p'),cl=this.gen.construct(ctor,fields.records,'l');
        const rv=this.gen.caseRecord(ctor,fields.records);
        fenv.set(type.key,{...arg,p:cp,l:cl,r:rv});
        for(let i=0;i<ctor.fields.length;i++) {
          const H=this.B.term_wnf(this.book,fieldSource),node=defaultBranch?null:this.open(h).x;
          if(H.$!=='All')throw Error('Structural constructor field lacks its checked All');
          if(!defaultBranch&&node.$!=='Lam')return this.caseFieldBranch(branch.h,ctor,F,physical,logical,cases?familyEnv:env,cctx,fields,nextCases,frame);
          const localKey='pattern.'+this.sequence++,fieldType=this.source.type(H.A,fctx);
          frame.keys.push(localKey);
          const v=this.source.open(H,fctx,localKey);fctx=v.ctx;
          if(!defaultBranch)fctx.set(node.i,localKey);
          sourceFields.push(v.v);
          fenv.set(localKey,{...fields.records[i],type:fieldType,expression:bound(localKey)});
          if(!defaultBranch)h=node.f(v.v);fieldSource=H.B(v.v);
        }
        if(defaultBranch){fctx.set(branch.i,type.key);h=branch.f(this.B.Ctr(ctor.key,sourceFields));}
        const branchSource=F.B(this.B.Ctr(ctor.key,sourceFields));
        // Dependent domains must be read after substituting this actual
        // constructor. Word(n), for example, exposes a different datatype in
        // each Nat branch. Retaining the pre-branch opaque application loses
        // exactly the source checker's dependent reduction.
        // A deferred motive must still vary the original parameter. Reading
        // the branch's source type here would freeze that endpoint to its
        // constructor before J (for example n to Zero).
        const branchType=cases?remainingType:this.specializeType(branchSource,fctx,type.B,fenv);
        const branchCases=nextCases&&{...nextCases,frames:[...nextCases.frames,frame]};
        return this.functionBody(h,branchSource,branchType,fenv,fctx,app(physical,cp,type.q),app(logical,cl,type.q),branchCases);
      },{defer:cases!==null});
      b=app(eliminator,V(r),type.q);
    } else if(x.$!=='Mat'&&x.$!=='Efq') {
      // A returned or partially applied function already has a pointwise
      // representation. Conversion checks its applications; no function
      // equality or duplicate execution is introduced.
      if(cases?.skip)b=this.functionBody(this.B.Ann(this.B.App(body,opened.v),nextSource),nextSource,remainingType,e,cctx,pp,ll,nextCases);
      else {
        if(cases?.frames.length)return this.caseLeaf(body,type,env,ctx,cases);
        const value=this.expression(body,env,ctx,type);
        return ann(value.r,this.gen.plan(type,env).relation(physical,logical));
      }
    } else throw Error('Structural function body not implemented: '+x.$+' over '+type.A.tag);
    const rq=this.gen.useQuantity(type.q,A);
    return bind('Lam',[[0,p,A.p],[0,l,A.l],[rq,r,A.relation(V(p),V(l))]],b);
  }
  specializeType(sourceType,ctx,prior,env){return this.source.type(sourceType,ctx);}
  caseFieldBranch(body,ctor,F,physical,logical,env,ctx,fields,cases=null,frame=null){
    const B=this.B,gen=this.gen,domain=B.term_wnf(this.book,F.A),base=B.tele_fill(this.book,this.book.ctrs[ctor.key].T,domain.x,B.ctx_nil());
    const goal=(T,j,xs)=>{
      if(j===ctor.fields.length)return F.B(B.Ctr(ctor.key,xs));
      const H=B.term_wnf(this.book,T),q=H.q.$==='None'?B.None():H.q.$==='Many'?B.Many():F.q;
      return B.All(q,H.k,H.i,H.A,x=>goal(H.B(x),j+1,[...xs,x]));
    };
    const T=goal(base,0,[]),type=this.source.type(T,ctx);
    const raw=(side,U,records,bindings)=>{
      if(records.length===ctor.fields.length)return bind('Lam',bindings,app(side==='p'?physical:logical,gen.construct(ctor,records,side),this.source.q(F.q)));
      const v=gen.fresh(),r={p:V(v),l:V(v),type:U.A};
      return raw(side,U.B,[...records,r],[...bindings,[U.q,v]]);
    };
    const p=raw('p',type,[],[]),l=raw('l',type,[],[]);
    let staged=cases;
    // Constructor fields are synthetic binders, not additional parameters
    // of the original recursive function.
    if(cases){let U=type;const keys=[];for(const field of ctor.fields){keys.push(U.key);U=U.B;}
      staged={...cases,frames:[...cases.frames,{...frame,keys}],skip:ctor.fields.length};}
    let result=this.functionBody(body,T,type,new Map(env),new Map(ctx),p,l,staged),U=type;
    // Use the common capture-avoiding application to expose actual subfields
    // to the original descent guard, without editing the physical .e.
    for(const field of fields.records){result=gen.applyTerm(gen.applyTerm(gen.applyTerm(result,field.p,0),field.l,0),field.r,U.q);U=U.B;}
    return result;
  }
  expression(t,env,ctx,expected) {
    return {...this.expressionValue(t,env,ctx,expected),sourceTerm:t,sourceContext:new Map(ctx)};
  }
  expressionValue(t,env,ctx,expected) {
    const {x,T}=this.open(t);
    if(x.$==='Var') {
      const key=ctx.get(x.i),record=env.get(key);
      if(record===undefined)throw Error('Unbound checked source value '+x.i);
      return record;
    }
    if(x.$==='Ref') {
      if(this.book.tlds[x.k]?.$==='ADT') {
        const expression={tag:'type',T:this.source.type(x,ctx)};
        return {...this.gen.value(expression,env),expression};
      }
      return this.reference(x.k);
    }
    if(x.$==='Lit') {
      if(x.k!=='Nat')return this.expression(this.B.Ann(this.B.lit_step(x),T??this.B.Ref(x.k)),env,ctx,expected);
      const v=this.source.value(x,T,ctx);return {...this.gen.value(v,env),expression:v};
    }
    if(x.$==='Rfl') {
      const type=T===null?expected:this.source.type(T,ctx);
      if(type===undefined)throw Error('Reflexivity needs its original checked proposition');
      if(type.tag!=='identity')throw Error('Reflexivity needs an identity type');
      return {p:rfl,l:rfl,r:tuple(Array.from({length:5},()=>[1,rfl])),type};
    }
    if(x.$==='Qua'||x.$==='Min'){
      const expression=this.source.value(x,this.B.Qnt(),ctx);return {...this.gen.value(expression,env),expression};
    }
    if(x.$==='Typ'||x.$==='All'||x.$==='ADT'||x.$==='Eql'||x.$==='Qnt') {
      const expression={tag:'type',T:this.source.type(x,ctx)};
      return {...this.gen.value(expression,env),expression};
    }
    if(x.$==='Rwt')return this.rewrite(x,T,env,ctx);
    if(x.$==='Ctr') {
      if(T===null){if(!expected)throw Error('A constructor needs its checked annotation');return this.expression(this.B.Ann(x,this.source.originalType(expected,env,ctx)),env,ctx,expected);}
      const type=this.source.type(T,ctx);
      if(type.tag!=='family')throw Error('A constructor needs its checked family type');
      const plan=this.gen.plan(type,env),values=[];
      const A=this.B.term_wnf(this.book,T);let fieldT=this.B.tele_fill(this.book,this.book.ctrs[x.k].T,A.x,this.B.ctx_nil());
      for(const field of x.x){const F=this.B.term_wnf(this.book,fieldT);values.push(this.expression(this.B.Ann(field,F.A),env,ctx));fieldT=F.B(field);}
      const result=this.gen.constructorValue(type.key,x.k,values,plan.values);result.type=type;
      return result;
    }
    if(x.$==='Lam') {
      if(T===null){if(!expected)throw Error('A lambda needs its checked annotation');return this.expression(this.B.Ann(x,this.source.originalType(expected,env,ctx)),env,ctx,expected);}
      const type=this.source.type(T,ctx),p=this.render(t,T,'p',env,ctx),l=this.render(t,T,'l',env,ctx);
      return {p,l,r:ann(this.functionBody(t,T,type,env,ctx,p,l),this.gen.plan(type,env).relation(p,l)),type};
    }
    if(x.$==='Let') {
      const {body,env:e,ctx:c,bindings}=this.locals(x,env,ctx,v=>this.expression(v,env,ctx));
      const result=this.expression(body,e,c);let r=result.r;
      for(let i=bindings.length-1;i>=0;i--) {
        const [q,l,value]=bindings[i],T=this.gen.plan(value.type,env).relation(value.p,value.l);
        r={$:'Let',q,l,v:ann(value.r,T),f:r};
      }
      return {...result,r};
    }
    if(x.$==='App') {
      const f=this.expression(x.f,env,ctx);let a=this.expression(x.x,env,ctx,f.type.A);
      if(a.expression===undefined){
        const key='argument.'+this.sequence++;
        a={...a,expression:bound(key)};env.set(key,a);
      }
      const record=this.gen.application(f,a,env);
      // This local semantic name is not a Book instance or a numerical
      // specialization. It only binds the typed argument under substitution.
      const key='expression.'+this.sequence++;
      env.set(key,record);record.expression=bound(key);
      return record;
    }
    throw Error('Structural source expression not implemented: '+x.$);
  }
  render(t,sourceType,side,env,ctx) {
    const {x,T}=this.open(t),U=T??sourceType;
    if(x.$==='Let') {
      const locals=this.locals(x,env,ctx,v=>({[side]:this.render(v,this.open(v).T,side,env,ctx),sourceTerm:v,sourceContext:new Map(ctx)}));
      return this.render(locals.body,U,side,locals.env,locals.ctx);
    }
    if(x.$==='Var') {
      const value=env.get(ctx.get(x.i));if(value===undefined)throw Error('Unbound rendering source level '+x.i);
      return value[side];
    }
    if(x.$==='Ref')return R(this.source.name(x.k));
    if(x.$==='Typ'||x.$==='All'||x.$==='ADT'||x.$==='Eql'||x.$==='Qnt')return this.gen.plan(this.source.type(x,ctx),env)[side];
    if(x.$==='Qua'||x.$==='Min')return this.gen.value(this.source.value(x,this.B.Qnt(),ctx),env)[side];
    if(x.$==='Lit')return x.k==='Nat'?this.gen.value(this.source.value(x,U,ctx),env)[side]:this.render(this.B.Ann(this.B.lit_step(x),U??this.B.Ref(x.k)),U,side,env,ctx);
    if(x.$==='Ctr'){
      const A=this.B.term_wnf(this.book,U),type=this.source.type(U,ctx),descriptor=this.source.families.get(type.key),ctor=descriptor.constructors.find(c=>c.key===x.k),values=[];
      let T=this.B.tele_fill(this.book,this.book.ctrs[x.k].T,A.x,this.B.ctx_nil());
      for(const field of x.x){const F=this.B.term_wnf(this.book,T),type=this.source.type(F.A,ctx),value=this.gen.eta(type,this.render(this.B.Ann(field,F.A),F.A,side,env,ctx));values.push(value);T=F.B(field);}
      return {$:'Tup',q:1,a:{$:'Lab',k:ctor.kernel},b:tuple(values.map((v,i)=>[ctor.fields[i].q,v]))};
    }
    if(x.$==='Lam') {
      const F=this.B.term_wnf(this.book,U);if(F.$!=='All')throw Error('A rendered lambda needs a checked function type');
      const key='render.'+this.sequence++,opened=this.source.open(F,ctx,key),v=this.gen.fresh(),e=new Map(env);
      opened.ctx.set(x.i,key);
      e.set(key,{p:V(v),l:V(v),r:V(this.gen.fresh()),type:this.source.type(F.A,ctx)});
      return lam(this.source.q(F.q),v,this.render(x.f(opened.v),F.B(opened.v),side,e,opened.ctx));
    }
    if(x.$==='App') {
      const ft=this.open(x.f).T??this.source.value(x.f,null,ctx).sourceType;if(ft===undefined||ft===null)throw Error('An application needs its checked callee type');
      const F=this.B.term_wnf(this.book,ft);if(F.$!=='All')throw Error('A checked application needs an All');
      let f=this.render(x.f,ft,side,env,ctx);
      if(!['Var','Ref','App','Ann'].includes(f.$))f=ann(f,this.gen.plan(this.source.type(ft,ctx),env)[side]);
      return app(f,this.render(x.x,F.A,side,env,ctx),this.source.q(F.q));
    }
    throw Error('Structural erased expression rendering not implemented: '+x.$);
  }
  rewrite(x,T,env,ctx) {
    if(T===null)throw Error('Equality elimination needs its checked result type');
    const evidence=this.expression(x.e,env,ctx);
    if(evidence.type.tag!=='identity')throw Error('J needs represented identity evidence');
    const motive=this.expression(x.p,env,ctx),base=this.expression(x.f,env,ctx);
    const Id=evidence.type,A=this.gen.plan(Id.A,env),ar=this.gen.value(Id.a,env),br=this.gen.value(Id.b,env);
    const mq=motive.type.q,hq=motive.type.B.q;
    const ap=this.gen.eta(Id.A,ar.p),al=this.gen.eta(Id.A,ar.l),bp=this.gen.eta(Id.A,br.p),bl=this.gen.eta(Id.A,br.l);
    const pCarrier=eq(ap,bp,A.p),lCarrier=eq(al,bl,A.l);
    const J=(side,b,proof)=>{
      const z=this.gen.fresh(),carrier=eq(side==='p'?ap:al,b,A[side]);
      return rwt(ann(proof,carrier),z,apps(motive[side],[[mq,V(z)],[hq,V(z+1)]]),base[side]);
    };
    const p=J('p',bp,evidence.p),l=J('l',bl,evidence.l);
    const mp=this.gen.fresh(),ml=this.gen.fresh(),mr=this.gen.fresh(),ep=this.gen.fresh(),el=this.gen.fresh(),er=this.gen.fresh();
    const P=bind('Lam',[[0,mp],[0,ml],[0,mr],[0,ep],[0,el],[0,er]],
      apps(motive.r,[[0,V(mp)],[0,V(ml)],[mq,V(mr)],[0,V(ep)],[0,V(el)],[hq,V(er)],
        [0,J('p',V(mp),V(ep))],[0,J('l',V(ml),V(el))]]));
    const rp=this.gen.fresh(),rl=this.gen.fresh(),RT=lam(0,rp,lam(0,rl,A.relation(V(rp),V(rl))));
    const r=apps(R(this.gen.prefix+'.Equality.induct'),[[0,A.p],[0,A.l],[0,RT],[0,ap],[0,al],[0,ar.r],
      [0,P],[1,base.r],[0,bp],[0,bl],[0,br.r],[0,evidence.p],[0,evidence.l],[1,evidence.r]]);
    return {p,l,r,type:this.source.type(T,ctx)};
  }
}
