// Match each source TYPE occurrence against its inferred physical typing
// occurrence. A physical head at one endpoint never changes another endpoint.
// Reuse requires the same original template and its checked original EQ prefix.
export function positionedTypeView(bodies,type,observed){
 const {source,safe,B,book}=bodies,ops=safe.state.admissionViewOps;
 if(!ops)throw Error('Positioned type views need the structural inference prepass');
 const inverse=new Map([...safe.state.names].map(([k,n])=>[n,k]));
 const logical=new Map();
 for(const [k]of safe.state.admissionBodies??[])logical.set(ops.key(safe.logical(k)),k);
 const viewValue=(x,o,ctx)=>{
   if(!o)return x;
   const xs=[];let h=x;
   while(h.tag==='apply'){xs.unshift(h.x);h=h.f;}
   if(h.tag==='erased-reference'&&bodies.origins.has(h.key)){
     const [k,prefix]=bodies.origins.get(h.key);let T=book.tlds[k].T,out={...h,key:k};
     for(const p of prefix){const F=B.term_wnf(book,T);out={tag:'apply',f:out,x:source.value(p,F.A,new Map())};T=F.B(p);}
     for(const a of xs)out={tag:'apply',f:out,x:a};
     return viewValue(out,o,ctx);
   }
   let oh=o;const os=[];
   while(oh.$==='App'&&!logical.has(ops.key(oh))){os.unshift(oh.x);oh=oh.f;}
   const canonical=logical.get(ops.key(oh));
   if(h.tag==='erased-reference'&&canonical===h.key&&xs.length===os.length){
     let out=h;for(let i=0;i<xs.length;i++)out={tag:'apply',f:out,x:viewValue(xs[i],os[i],ctx)};return out;
   }
   if(oh.$==='Ref'&&h.tag==='erased-reference'){
     const physical=inverse.get(oh.k),origin=bodies.origins.get(physical),original=origin?.[0]??physical;
     const prefix=origin?.[1]??[],provided=xs.slice(0,prefix.length).map(v=>bodies.originalValue(v));
     if(original===h.key&&xs.length-prefix.length===os.length&&provided.length===prefix.length&&provided.every((v,i)=>v!==null&&B.term_compare('EQ',book,v,prefix[i]))){
       let out={tag:'physical-reference',key:physical};
       for(let i=prefix.length;i<xs.length;i++)out={tag:'apply',f:out,x:viewValue(xs[i],os[i-prefix.length],ctx)};
       return out;
     }
   }
   const normalized=ops.normalize(o);
   if(ops.key(normalized)!==ops.key(o))return viewValue(x,normalized,ctx);
   if(x.tag==='bound'&&o.$==='Var'&&ctx.get(o.l)===x.key)return x;
   if(x.tag==='type')return {...x,T:walk(x.T,o,ctx)};
   return x;
 };
 const walk=(T,o,ctx)=>{
   if(T.tag==='arrow'&&o.$==='All'){
     const next=new Map(ctx);next.set(o.l,T.key);
     return {...T,A:walk(T.A,o.A,ctx),B:walk(T.B,o.B,next)};
   }
   if(T.tag==='identity'&&o.$==='Eql')return {...T,A:walk(T.A,o.T,ctx),a:viewValue(T.a,o.a,ctx),b:viewValue(T.b,o.b,ctx)};
   if(T.tag==='family'){
     const [h,args]=ops.spine(o);
     if(h.$==='Ref'&&h.k===source.name(T.key)&&args.length===T.args.length)return {...T,args:T.args.map((x,i)=>viewValue(x,args[i],ctx))};
   }
   if(T.tag==='bound'||T.tag==='apply')return viewValue(T,o,ctx);
   return T;
 };
 return walk(type,observed,new Map());
}
