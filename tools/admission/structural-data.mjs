import {V,R,UT,all,lam,app,apps,tup,tuple,bind,prj,mats,ann,eq,rfl,split,let1,rwt} from './structural-syntax.mjs';
import {family,bound} from './structural-relations.mjs';

// Checked conversions for homogeneous monomorphic Data. This helper is not
// a restriction on source types: other types use their compositional relation.
// In particular an arbitrary higher-order opaque function is NOT assumed to
// preserve a supplied relation merely because it is well typed.
export class DataValues {
  constructor(gen) {this.gen=gen;this.cache=new Map();}
  supports(key,seen=new Set()) {
    if(seen.has(key))return true;
    const d=this.gen.families.get(key);if(d===undefined||d.quantity!==2||d.parameters.length!==0)return false;
    const next=new Set(seen);next.add(key);
    return d.constructors.every(c=>c.fields.every(f=>f.q>0&&f.type.tag==='family'&&f.type.args.length===0&&this.supports(f.type.key,next)));
  }
  scalar(T,p,l) {return this.gen.scalar(T,2,p,l);}
  ensure(key) {
    const old=this.cache.get(key);if(old!==undefined)return old;
    if(!this.supports(key))throw Error('A homogeneous monomorphic Data relation is required: '+key);
    const gen=this.gen,g=gen.generateFamily(key),d=g.definition,D=R(d.kernel),plan=gen.plan(family(key));
    const out={read:g.name+'.read',reflect:g.name+'.reflect',fromScalar:g.name+'.from_scalar',D,plan};this.cache.set(key,out);
    for(const c of d.constructors)for(const f of c.fields)this.ensure(f.type.key);
    // Construct a reflexive representation by the actual Data constructors.
    const y=gen.fresh(),branches=d.constructors.map(c=>{
      const bs=c.fields.map(f=>[f.q,gen.fresh()]);
      const values=bs.map(([q,l],i)=>({p:V(l),l:V(l),r:app(R(this.cache.get(c.fields[i].type.key).reflect),V(l)),type:c.fields[i].type}));
      return [c.kernel,split(bs,gen.constructorValue(key,c.key,values).r)];
    });
    gen.emit(out.reflect,all(1,y,D,plan.relation(V(y),V(y))),prj(mats(branches)));
    const p=gen.fresh(),l=gen.fresh(),r=gen.fresh(),motive=(p,l)=>this.scalar(D,p,l);
    const readBody=gen.eliminate(g,new Map(),V(p),V(l),motive,(c,fields)=>{
      const slots=fields.records.map((f,i)=>({...f,y:gen.fresh(),ep:gen.fresh(),el:gen.fresh(),once:gen.fresh(),read:this.cache.get(c.fields[i].type.key).read}));
      const central=slots.map(s=>({...s,p:V(s.y),l:V(s.y)})),y=gen.fresh();
      const proof=side=>{
        let evidence=rfl,current=[...central];
        for(let i=0;i<slots.length;i++) {
          const z=gen.fresh(),next=[...current];next[i]={...next[i],p:V(z),l:V(z)};
          evidence=rwt(V(slots[i][side==='p'?'ep':'el']),z,eq(V(y),gen.construct(c,next,'p'),D),evidence);
          current[i]={...current[i],p:slots[i][side],l:slots[i][side]};
        }
        return evidence;
      };
      let body=let1(y,ann(gen.construct(c,central,'p'),D),tuple([[1,V(y)],[1,proof('p')],[1,proof('l')]]));
      for(let i=slots.length-1;i>=0;i--) {
        const s=slots[i],value=apps(R(s.read),[[0,s.p],[0,s.l],[1,s.r]]);
        body=let1(s.once,value,app(split([[2,s.y],[2,s.ep],[2,s.el]],body),V(s.once)));
      }
      return body;
    });
    gen.emit(out.read,bind('All',[[0,p,D],[0,l,D],[1,r,plan.relation(V(p),V(l))]],motive(V(p),V(l))),lam(0,p,lam(0,l,readBody)));
    const sp=gen.fresh(),sl=gen.fresh(),sr=gen.fresh(),sy=gen.fresh(),sep=gen.fresh(),sel=gen.fresh(),zp=gen.fresh(),zl=gen.fresh();
    const value=rwt(V(sep),zp,plan.relation(V(zp),V(sl)),rwt(V(sel),zl,plan.relation(V(sy),V(zl)),app(R(out.reflect),V(sy))));
    gen.emit(out.fromScalar,bind('All',[[0,sp,D],[0,sl,D],[1,sr,this.scalar(D,V(sp),V(sl))]],plan.relation(V(sp),V(sl))),
      lam(0,sp,lam(0,sl,split([[2,sy],[2,sep],[2,sel]],value))));
    return out;
  }
  shared(type,physical,logical,evaluator) {
    const gen=this.gen;let T=type;const bs=[],slots=[];
    while(T.tag==='arrow') {
      if(T.A.tag!=='family'||T.A.args.length!==0)throw Error('Shared Data input is not homogeneous');
      const data=this.ensure(T.A.key),p=gen.fresh(),l=gen.fresh(),r=gen.fresh();
      bs.push([0,p,data.D],[0,l,data.D],[T.q,r,data.plan.relation(V(p),V(l))]);
      slots.push({p:V(p),l:V(l),r:V(r),q:T.q,data,y:gen.fresh(),ep:gen.fresh(),el:gen.fresh(),once:gen.fresh()});T=T.B;
    }
    if(T.tag!=='family'||T.args.length!==0)throw Error('Shared Data result is not homogeneous');
    const result=this.ensure(T.key),call=(f,args)=>apps(f,args.map((a,i)=>[slots[i].q,a]));
    const ys=slots.map(s=>V(s.y)),y=gen.fresh(),ep=gen.fresh(),el=gen.fresh(),once=gen.fresh();
    const proof=side=>{
      let evidence=V(side==='p'?ep:el),current=[...ys];
      for(let i=0;i<slots.length;i++) {
        const z=gen.fresh(),next=[...current];next[i]=V(z);
        evidence=rwt(V(slots[i][side==='p'?'ep':'el']),z,eq(V(y),call(side==='p'?physical:logical,next),result.D),evidence);current[i]=slots[i][side];
      }
      return evidence;
    };
    const scalarResult=tuple([[1,V(y)],[1,proof('p')],[1,proof('l')]]);
    const scalarType=this.scalar(result.D,call(physical,slots.map(s=>s.p)),call(logical,slots.map(s=>s.l)));
    const convert=apps(R(result.fromScalar),[[0,call(physical,slots.map(s=>s.p))],[0,call(logical,slots.map(s=>s.l))],[1,ann(scalarResult,scalarType)]]);
    let body=let1(once,call(evaluator,ys),app(split([[2,y],[2,ep],[2,el]],convert),V(once)));
    for(let i=slots.length-1;i>=0;i--) {
      const s=slots[i],read=apps(R(s.data.read),[[0,s.p],[0,s.l],[1,s.r]]);
      body=let1(s.once,read,app(split([[2,s.y],[2,s.ep],[2,s.el]],body),V(s.once)));
    }
    return {p:physical,l:logical,r:ann(bind('Lam',bs,body),gen.plan(type).relation(physical,logical)),type};
  }
}
