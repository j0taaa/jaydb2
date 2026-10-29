import {V,R,all,lam,app,apps,ann,eq,rfl,let1,split,tuple,UT,UV} from './structural-syntax.mjs';
import {DataValues} from './structural-data.mjs';

// Real entry construction, without extra hypotheses: source references must
// denote checked closed values. Ordinary arguments remain ordinary values.
// Every input representation is obtained by translating that value's own .e.
export function closedEntry(bodies,key,argumentKeys=[]) {
 const gen=bodies.gen,book=bodies.book;
 const closed=k=>{
   const d=book.tlds[k];
   if(d?.$!=='Def'||d.e===undefined||d.n!==0||d.x!==0)
     throw Error('An actual closed source entry value is required: '+k);
   return bodies.reference(k);
 };
 let value=closed(key);
 for(const k of argumentKeys){
   const argument=closed(k);
   // This test intentionally applies the original type equality too. The
   // relation helper does not admit a substitute for the actual argument.
   const actual=book.tlds[k].T;
   if(value.sourceT===undefined)value.sourceT=book.tlds[key].T;
   const F=bodies.B.term_wnf(book,value.sourceT);
   if(F.$!=='All'||!bodies.B.term_compare('EQ',book,F.A,actual))
     throw Error('The original source entry argument has the wrong type: '+k);
   const next=F.B(bodies.B.Ref(k));
   value=gen.application(value,argument,new Map());value.sourceT=next;
 }
 return value;
}
export function scalarEntryLink(bodies,entry,name) {
 const gen=bodies.gen;
 if(entry.type.tag!=='family'||entry.type.args.length!==0)
   throw Error('This structural observation needs a homogeneous Data result');
 const data=new DataValues(gen),reader=data.ensure(entry.type.key);
 const y=gen.fresh(),ep=gen.fresh(),el=gen.fresh(),z=gen.fresh(),once=gen.fresh();
 const record=apps(R(reader.read),[[0,entry.p],[0,entry.l],[1,entry.r]]);
 const body=let1(once,record,app(split([[1,y],[1,ep],[1,el]],
   {$:'Rwt',e:V(ep),l:z,P:eq(V(z),entry.l,reader.D),f:V(el)}),V(once)));
 gen.emit(name,eq(entry.p,entry.l,reader.D),body);
}
