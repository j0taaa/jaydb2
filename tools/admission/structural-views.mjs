// Typed representation: finite, type-directed constraints for an emitted physical
// header. No logical equation is added. Every resulting term/header, exact
// physical source link and representation still goes through both kernels.
// A promotion records the occurrence in the original header, not an inferred
// branch type containing escaped pattern variables.
export function constrainProofViews(safe,names){
 const state=safe.state,items=new Map(state.out.map(x=>[x[0],x])),ids=new WeakMap();let next=0,fresh=50000000;
 const identify=x=>{if(!x||typeof x!=='object')return;if(!Array.isArray(x)&&!ids.has(x))ids.set(x,next++);for(const v of Object.values(x))identify(v);};
 const clone=x=>{
   if(!x||typeof x!=='object')return x;
   const out=Array.isArray(x)?x.map(clone):Object.fromEntries(Object.entries(x).map(([k,t])=>[k,clone(t)]));
   if(ids.has(x))ids.set(out,ids.get(x));return out;
 };
 const V=l=>({$:'Var',l});
 const free=(x,bound=new Set(),out=new Set())=>{
   if(!x||typeof x!=='object')return out;
   if(x.$==='Var'){if(!bound.has(x.l))out.add(x.l);return out;}
   for(const[k,v]of Object.entries(x)){
     let scope=bound;
     if((['All','Sig'].includes(x.$)&&k==='B')||(['Lam','Let'].includes(x.$)&&k==='f'))scope=new Set([...bound,x.l]);
     if(x.$==='Rwt'&&k==='P')scope=new Set([...bound,x.l,x.l+1]);
     free(v,scope,out);
   }
   return out;
 };
 const sub=(x,l,v)=>{
   const fvs=free(v);
   const go=x=>{
     if(!x||typeof x!=='object')return x;
     if(x.$==='Var')return x.l===l?clone(v):x;
     if(Array.isArray(x))return x.map(go);
     let y=x,binders=[];
     if(['All','Sig','Lam','Let'].includes(x.$))binders=[x.l];
     if(x.$==='Rwt')binders=[x.l,x.l+1];
     const field=['All','Sig'].includes(x.$)?'B':x.$==='Rwt'?'P':'f';
     if(binders.length&&!binders.includes(l)&&binders.some(b=>fvs.has(b))){
       const n=fresh;fresh+=binders.length;let body=x[field];
       binders.forEach((b,i)=>{body=sub(body,b,V(n+i));});
       y={...x,l:n,[field]:body};binders=binders.map((_,i)=>n+i);
     }
     const out=Object.fromEntries(Object.entries(y).map(([k,t])=>[k,k===field&&binders.includes(l)?t:go(t)]));
     if(ids.has(x))ids.set(out,ids.get(x));return out;
   };
   return go(x);
 };
 const alpha=(x,ctx=new Map())=>{
   if(!x||typeof x!=='object')return x;
   if(Array.isArray(x))return x.map(v=>alpha(v,ctx));
   if(x.$==='Var')return ['$var',ctx.has(x.l)?ctx.get(x.l):['free',x.l]];
   if(['All','Sig','Lam','Let'].includes(x.$)){
     const c=new Map(ctx);c.set(x.l,ctx.size);const out={};
     for(const[k,v]of Object.entries(x))if(k!=='l')out[k]=alpha(v,['B','f'].includes(k)?c:ctx);
     return out;
   }
   return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,alpha(v,ctx)]));
 };
 const key=x=>JSON.stringify(alpha(x)),same=(x,y)=>key(x)===key(y);
 const protectedLogical=new Set(),protectedPhysical=new Set();
 const preserve=(from,to)=>{if(ids.has(from))ids.set(to,ids.get(from));return to;};
 const unfold=(x,seen=new Set(),typeHead=false)=>{

   if(!typeHead&&(protectedLogical.has(key(x))||(x.$==='Ref'&&protectedPhysical.has(x.k))))return x;
   if(x.$==='Ann')return unfold(x.x,seen,typeHead);
   if(x.$==='Let')return unfold(sub(x.f,x.l,x.v),seen,typeHead);
   if(x.$==='Ref'&&items.has(x.k)&&!seen.has(x.k)){
     const more=new Set(seen);more.add(x.k);return unfold(items.get(x.k)[2],more,typeHead);
   }
   if(x.$==='App'){
     const f=unfold(x.f,seen,typeHead);
     if(f.$==='Lam')return unfold(sub(f.f,f.l,x.x),seen,typeHead);
     if(f.$==='Prj'){
       const a=unfold(x.x,seen,typeHead);
       if(a.$==='Tup')return unfold({$:'App',q:1,f:{$:'App',q:a.q,f:f.h,x:a.a},x:a.b},seen,typeHead);
     }
     if(f.$==='Mat'){
       const a=unfold(x.x,seen,typeHead);
       if(a.$==='Lab')return unfold(a.k===f.k?f.h:{$:'App',q:x.q,f:f.m,x:x.x},seen,typeHead);
     }
     return f===x.f?x:preserve(x,{...x,f});
   }
   return x;
 };
 // Expose a type's actual All/Sig/enum by its defining equations.
 // Protect physical heads only while comparing value indices, never while
 // reading the telescope of a type family such as d1(~p).
 const expose=x=>unfold(x,new Set(),true);
 const originals=new Map(),rules=[];
 for(const name of names){const d=items.get(name);if(!d)throw Error('Missing physical view root '+name);identify(d[1]);originals.set(name,structuredClone(d[1]));}
 // A rule can only select an existing exact declaration with its original
 // prefix. Its logical spelling is read from the very same closed Book.
 for(const [sourceName,kernelName]of state.names){
   const d=state.book.tlds[sourceName];if(d?.$!=='Def'||d.x!==0||d.e===undefined||!items.has(kernelName))continue;
   if(state.inst.has(sourceName)||state.admissionAffected?.has(sourceName))protectedPhysical.add(kernelName);
   const origin=state.inst.get(sourceName);let logical;
   if(origin){
     logical=safe.logical(origin[0]);protectedLogical.add(key(logical));let T=state.book.tlds[origin[0]].T;
     for(const x of origin[1]){
       const B=safe.B,F=B.term_wnf(state.book,T);
       logical={$:'App',q:F.q.$==='None'?0:F.q.$==='Lone'?1:2,f:logical,x:safe.term(B.Ann(x,F.A))};T=F.B(x);
     }
   }else {
     if(!state.admissionBodies?.has(sourceName))continue;
     logical=safe.logical(sourceName);
   }
   rules.push({logical,key:key(logical),physical:{$:'Ref',k:kernelName},sourceName});
 }
 const promotions=[],conflicts=[];
 const normalize=x=>{
   const w=unfold(x);
   if(w.$==='App'){const a=normalize(w.x);return a===w.x?w:preserve(w,{...w,x:a});}
   return w;
 };
 const spine=x=>{const xs=[];while(x.$==='App'){xs.unshift(x.x);x=x.f;}return [x,xs];};
 const refine=(want,got,changes,path)=>{
   if(same(want,got))return;
   const [wf,wx]=spine(want),[gf,gx]=spine(got);
   if(wx.length&&wx.length===gx.length&&same(wf,gf)){
     for(let i=0;i<wx.length;i++)refine(wx[i],gx[i],changes,path+'.argument('+i+')');return;
   }
   // Reduce actual beta/projection/case substitutions (for example an
   // ordinary helper applied to a known Token). Keep template and physical
   // heads visible, so this cannot equate unrelated implementations.
   const wn=normalize(want),gn=normalize(got);
   if(!same(wn,want)||!same(gn,got)){refine(wn,gn,changes,path+'.reduce');return;}
   const rule=got?.$==='Ref'?rules.find(r=>r.physical.k===got.k&&r.key===key(want)):undefined;
   if(rule){
     const id=ids.get(want);if(id===undefined){conflicts.push({path,reason:'A branch-local type expression cannot be promoted into a global header'});return;}
     const old=changes.get(id);if(old&&!same(old,got))throw Error('Conflicting physical type views at '+path);
     changes.set(id,got);promotions.push({path,sourceName:rule.sourceName,physical:got.k});return;
   }
   if(want?.$===got?.$){
     if(['All','Sig'].includes(want.$)){
       refine(want.A,got.A,changes,path+'.A');refine(want.B,sub(got.B,got.l,V(want.l)),changes,path+'.B');return;
     }
     if(want.$==='Lam'){refine(want.f,sub(got.f,got.l,V(want.l)),changes,path+'.f');return;}
     const keys=Object.keys(want).filter(k=>!['$','l'].includes(k));
     if(keys.every(k=>typeof want[k]==='object')){for(const k of keys)refine(want[k],got[k],changes,path+'.'+k);return;}
     if(want.$==='App'){refine(want.f,got.f,changes,path+'.f');refine(want.x,got.x,changes,path+'.x');return;}
     if(want.$==='Eql'){for(const k of ['a','b','T'])refine(want[k],got[k],changes,path+'.'+k);return;}
   }
   // This is a constraint diagnostic. It does not certify conversion; the
   // original checker must accept the final raw body at the resulting header.
   conflicts.push({path,want:want?.$,got:got?.$});
 };
 const replace=(x,changes)=>{
   if(!x||typeof x!=='object')return x;
   const id=ids.get(x);if(changes.has(id)){const out=structuredClone(changes.get(id));ids.set(out,id);return out;}
   const out=Array.isArray(x)?x.map(v=>replace(v,changes)):Object.fromEntries(Object.entries(x).map(([k,v])=>[k,replace(v,changes)]));
   if(id!==undefined)ids.set(out,id);return out;
 };
 const infer=(x,ctx)=>{

   if(x.$==='Ann')return x.T;
   if(x.$==='Var'){if(!ctx.has(x.l))throw Error('Unbound view-inference binder '+x.l);return ctx.get(x.l);}
   if(x.$==='Ref'){if(!items.has(x.k))throw Error('Missing view-inference head '+x.k);return items.get(x.k)[1];}
   if(x.$==='App'){
     const F=expose(infer(x.f,ctx));if(F.$!=='All')throw Error('A view application must expose its All, found '+F.$);
     return sub(F.B,F.l,x.x);
   }
   if(x.$==='Let'){const next=new Map(ctx);next.set(x.l,infer(x.v,ctx));return sub(infer(x.f,next),x.l,x.v);}
   if(x.$==='Rwt')return sub(sub(x.P,x.l,expose(infer(x.e,ctx)).b),x.l+1,x.e);
   throw Error('Physical view inference needs an expected type for '+x.$);
 };
 const walk=(body,expected,ctx,changes,path)=>{

   if(body.$==='Lam'){
     const F=expose(expected);if(F.$!=='All')throw Error('A physical lambda view needs an All');
     const next=new Map(ctx);next.set(body.l,F.A);walk(body.f,sub(F.B,F.l,V(body.l)),next,changes,path+'.lambda');return;
   }
   if(body.$==='Prj'){
     const F=expose(expected),S=F.$==='All'?expose(F.A):null;
     if(S?.$!=='Sig')throw Error('A physical projection view needs an All/Sig');
     const a=fresh++,b=fresh++,pair={$:'Tup',q:S.q,a:V(a),b:V(b)};
     const q=S.q===0?0:S.q===2&&F.q!==0?2:F.q;
     walk(body.h,{$:'All',q,l:a,A:S.A,B:{$:'All',q:F.q,l:b,A:sub(S.B,S.l,V(a)),B:sub(F.B,F.l,pair)}},ctx,changes,path+'.project');return;
   }
   if(body.$==='Mat'){
     const F=expose(expected),E=F.$==='All'?expose(F.A):null;
     if(E?.$!=='Enu')throw Error('A physical tag view needs an All/Enu');
     walk(body.h,sub(F.B,F.l,{$:'Lab',k:body.k}),ctx,changes,path+'.case('+body.k+')');
     walk(body.m,{...F,A:{$:'Enu',ks:E.ks.filter(k=>k!==body.k)}},ctx,changes,path+'.default');return;
   }
   if(body.$==='Efq'||body.$==='Rfl'||body.$==='Tup'||body.$==='Lab')return;
   if(body.$==='Let'){
     const next=new Map(ctx);next.set(body.l,infer(body.v,ctx));walk(body.f,expected,next,changes,path+'.let');return;
   }
   refine(expected,infer(body,ctx),changes,path);
 };
 let rounds=0;
 for(;;){
   rounds++;let changed=false;conflicts.length=0;
   for(const name of names){
     const item=items.get(name),changes=new Map();walk(item[2],item[1],new Map(),changes,name);
     if(changes.size){const next=replace(item[1],changes);if(!same(next,item[1])){item[1]=next;changed=true;}}
   }
   if(!changed)break;
 }
 for(const name of names){
   const sourceName=[...state.names].find(([,n])=>n===name)?.[0];
   const item=items.get(name),link=items.get(state.admissionGuards?.get(sourceName));
   if(!link||link[2].$!=='Let'||link[2].v?.T?.$!=='Eql')throw Error('Missing mandatory physical source link for view '+name);
   link[2].v.T.T=structuredClone(item[1]);
   (state.admissionTypeViews??=new Map()).set(name,{original:originals.get(name),observed:item[1]});
 }
 state.admissionViewOps={normalize,key,spine,sub};
 return {declarations:[...names],rounds,promotions,unresolved:conflicts};
}
