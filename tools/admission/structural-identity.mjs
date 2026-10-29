import {V,R,K,UT,all,lam,app,apps,bind,eq,rfl,rwt,tuple,ann,split} from './structural-syntax.mjs';
import {universe,bound,identity} from './structural-relations.mjs';

// A derived induction principle for the complete proof representation. It
// consumes only the original J. Its motive may depend on the ACTUAL proof
// indices and on the entire represented proof. No proof irrelevance, K, or
// equality between function heads is used.
export function identityElimination(gen) {
  const AP=gen.fresh(),AL=gen.fresh(),RT=gen.fresh(),ap=gen.fresh(),al=gen.fresh(),ra=gen.fresh();
  const x=gen.fresh(),y=gen.fresh();
  const relation=(p,l)=>apps(V(RT),[[0,p],[0,l]]);
  const root=[[0,AP,K(1)],[0,AL,K(1)],[0,RT,all(0,x,V(AP),all(0,y,V(AL),K(1)))],
    [0,ap,V(AP)],[0,al,V(AL)],[0,ra,relation(V(ap),V(al))]];
  const bp=gen.fresh(),bl=gen.fresh(),rb=gen.fresh(),pp=gen.fresh(),pl=gen.fresh();
  const args=[[0,bp,V(AP)],[0,bl,V(AL)],[0,rb,relation(V(bp),V(bl))],
    [0,pp,eq(V(ap),V(bp),V(AP))],[0,pl,eq(V(al),V(bl),V(AL))]];
  const idName=gen.prefix+'.Equality.Rel',idRoot=root.map(([q,l])=>[q,V(l)]);
  const idType=(s,p=s.pp,l=s.pl)=>{
    const env=new Map([
      ['A',{p:V(AP),l:V(AL),r:V(RT),type:universe(1)}],
      ['a',{p:V(ap),l:V(al),r:V(ra),type:bound('A')}],
      ['b',{p:s.bp,l:s.bl,r:s.rb,type:bound('A')}]
    ]);
    return gen.plan(identity(bound('A'),bound('a'),bound('b')),env).relation(p,l);
  };
  const state={bp:V(bp),bl:V(bl),rb:V(rb),pp:V(pp),pl:V(pl)};
  gen.emit(idName,bind('All',[...root,...args],K(2)),bind('Lam',[...root,...args],idType(state)));
  const idAt=s=>apps(R(idName),[...idRoot,[0,s.bp],[0,s.bl],[0,s.rb],[0,s.pp],[0,s.pl]]);
  const packet=s=>tuple([[1,s.vp],[1,s.vl],[1,s.ip],[1,s.il],[1,s.co]]);
  const motive=gen.fresh(),base=gen.fresh(),rp=gen.fresh();
  const PType=bind('All',args,all(0,rp,idAt(state),K(1)));
  const pAt=(s,r)=>apps(V(motive),[[0,s.bp],[0,s.bl],[0,s.rb],[0,s.pp],[0,s.pl],[0,r]]);
  const reflexive={bp:V(ap),bl:V(al),rb:V(ra),pp:rfl,pl:rfl,vp:rfl,vl:rfl,ip:rfl,il:rfl,co:rfl};
  const vp=gen.fresh(),vl=gen.fresh(),ip=gen.fresh(),il=gen.fresh(),co=gen.fresh();
  const actual={...state,vp:V(vp),vl:V(vl),ip:V(ip),il:V(il),co:V(co)};
  const transport=s=>{
    const zp=gen.fresh(),zl=gen.fresh();
    const vp=ann(s.vp,eq(V(ap),s.bp,V(AP))),vl=ann(s.vl,eq(V(al),s.bl,V(AL)));
    return rwt(vl,zl,relation(s.bp,V(zl)),rwt(vp,zp,relation(V(zp),V(al)),V(ra)));
  };
  const paths=[
    {endpoint:'bp',proof:'vp',A:s=>V(AP),a:s=>V(ap)},
    {endpoint:'bl',proof:'vl',A:s=>V(AL),a:s=>V(al)},
    {endpoint:'rb',proof:'co',A:s=>relation(s.bp,s.bl),a:transport},
    {endpoint:'pp',proof:'ip',A:s=>eq(V(ap),s.bp,V(AP)),a:s=>s.vp},
    {endpoint:'pl',proof:'il',A:s=>eq(V(al),s.bl,V(AL)),a:s=>s.vl}
  ];
  function telescope(s,i) {
    if(i===paths.length)return pAt(s,packet(s));
    const path=paths[i],v=gen.fresh(),e=gen.fresh();
    return all(0,v,path.A(s),all(1,e,eq(path.a(s),V(v),path.A(s)),telescope({...s,[path.endpoint]:V(v),[path.proof]:V(e)},i+1)));
  }
  function derive(s,i) {
    if(i===paths.length)return V(base);
    const path=paths[i],v=gen.fresh(),e=gen.fresh(),z=gen.fresh();
    const motiveState={...s,[path.endpoint]:V(z),[path.proof]:V(z+1)};
    const baseState={...s,[path.endpoint]:path.a(s),[path.proof]:rfl};
    return lam(0,v,lam(1,e,rwt(V(e),z,telescope(motiveState,i+1),derive(baseState,i+1))));
  }
  const pathType=telescope({},0),pathBody=derive({},0);
  const applied=apps(ann(pathBody,pathType),paths.flatMap(path=>[[0,actual[path.endpoint]],[1,actual[path.proof]]]));
  const endpointArgs=args.map(([q,l])=>[q,l]);
  const T=bind('All',[...root,[0,motive,PType],[1,base,pAt(reflexive,packet(reflexive))],...args,[1,rp,idAt(state)]],pAt(state,V(rp)));
  const b=bind('Lam',[...root,[0,motive],[1,base],...endpointArgs],split([[1,vp],[1,vl],[1,ip],[1,il],[1,co]],applied));
  gen.emit(gen.prefix+'.Equality.induct',T,b);
}
