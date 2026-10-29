import fs from 'node:fs';
import {instanceClosureFingerprint,instanceSourceClaims} from './closed-instances.mjs';
import {SourceTypes} from './structural-types.mjs';
import {Relations} from './structural-relations.mjs';
import {declarationsText} from './structural-syntax.mjs';
import {BoundaryBodies} from './structural-boundary.mjs';
import {constrainProofViews} from './structural-views.mjs';
import {identityElimination} from './structural-identity.mjs';
import {ProofBody} from './structural-evidence.mjs';
import {orderDeclarations} from './structural-order.mjs';
import {closedEntry,scalarEntryLink} from './structural-entry.mjs';

// Structural integration with the actual checkBook API. It receives the original
// checked Book; it neither parses another source nor installs another Book.
// There is no fallback from a kernel/guard verdict in this adapter.
export function structuralEmitter(B,S,{proofRoots=[],entries=[],executionRoots}={}){
 return {
   SafeResourceExhausted:S.SafeResourceExhausted,
   admission_safe_emit(book,out,options={}){
     const before=instanceClosureFingerprint(B,book),names=Object.keys(book.tlds);
     
     const result=S.admission_safe_emit(book,out,options);
     
     if(result.oos.length)return result;
     const source=new SourceTypes(B,book),safe=S.admission_safe_state();
     const namesInPayload=safe.state.out.map(([k])=>k);
     let serial=0n,prefix='AdmissionRepresentation';
     while(namesInPayload.some(n=>n===prefix||n.startsWith(prefix+'.')))prefix='AdmissionRepresentation'+(++serial);
     const gen=new Relations({families:source.families,prefix});
     safe.B=B;source.kernelNames=safe.state.names;
     const proofNames=[];
     for(const[k,d]of Object.entries(book.tlds))if(d.$==='Def'&&d.x===0&&d.e!==undefined){
       let T=d.T;for(let i=0;;i++){const F=B.term_wnf(book,T);if(F.$!=='All'){T=F;break;}T=F.B(B.Var(F.k,4000000+i));}
       if(T.$==='Eql'&&safe.state.out.some(([name])=>name===source.name(k)))proofNames.push(source.name(k));
     }
     
     const views=constrainProofViews(safe,proofNames,options),guardNames=new Set(safe.state.out.map(([k])=>k));
     
     for(const k of instanceSourceClaims(book).keys()){
       const n=safe.state.admissionGuards?.get(k);
       if(n===undefined||!guardNames.has(n))throw Error('A mandatory physical source link was omitted: '+k);
     }
     const bodies=new BoundaryBodies(source,gen,safe);identityElimination(gen);
     const allProofRoots=new Set(proofRoots),inverse=new Map([...safe.state.names].map(([k,n])=>[n,k]));
     for(const[name,view]of safe.state.admissionTypeViews??[])
       if(safe.state.admissionViewOps.key(view.original)!==safe.state.admissionViewOps.key(view.observed)){
         const key=inverse.get(name);
         if(key===undefined)throw Error('No source declaration for a changed proof header '+name);
         allProofRoots.add(key);
       }
     const identityRoots=[];
     // Every raw physical root and source link remains above. Operational
     // evaluators follow the actual executed/transported roots; dependencies
     // are generated compositionally from their real checked bodies.
     if(executionRoots===undefined){for(const[k,d]of Object.entries(book.tlds))if(!d.b&&d.$==='Def'&&d.x===0)bodies.reference(k);}
     else {
       // No representation transport is needed for a literally unchanged
       // execution root. It remains a mandatory live raw root with its
       // independent physical source link. Any transported root/proof must
       // construct its relation from checked bodies and actual inputs.
       for(const key of executionRoots){
         const name=source.name(key),logical=safe.logical(key),physical={$:'Ref',k:name};
         const raw=safe.state.out.find(([n])=>n===name),view=safe.state.admissionTypeViews?.get(name);
         const sameHeader=!view||safe.state.admissionViewOps.key(view.original)===safe.state.admissionViewOps.key(view.observed);
         // The graph closure inspects source T/v/e and every datatype field,
         // so a dependency that changes representation prevents this cut.
         const identical=raw!==undefined&&!safe.state.admissionAffected?.has(key)&&sameHeader&&JSON.stringify(logical)===JSON.stringify(physical);
         if(!identical)bodies.reference(key);else identityRoots.push(key);
       }
       for(const key of allProofRoots)bodies.reference(key);
     }
     const proofBody=new ProofBody(bodies);
     for(const key of allProofRoots){
       const name=proofBody.exact(key),view=safe.state.admissionTypeViews.get(source.name(key));
       if(!view)throw Error('Missing exact original target '+key);
       gen.declarations.push([gen.prefix+'.Evidence.'+source.name(key)+'.original_target',view.original,{$:'Ref',k:name}]);
     }
     for(const[head,...arguments_]of entries)scalarEntryLink(bodies,closedEntry(bodies,head,arguments_),gen.prefix+'.Entry.'+source.name(head));
     if(instanceClosureFingerprint(B,book)!==before||JSON.stringify(Object.keys(book.tlds))!==JSON.stringify(names))throw Error('The structural emitter changed the final checked Book');
     const ordered=orderDeclarations(gen.declarations);
     const payload=safe.text()+'\n'+declarationsText(ordered);
     fs.writeFileSync(out,payload);
     return {...result,structural:{views,generated:gen.declarations.length,originalTargets:[...allProofRoots],identityRoots,entries:entries.map(x=>[...x]),sameCheckedBook:true}};
   }
 };
}
