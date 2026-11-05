// Runs the actual emitted controller against fault-injected byte effects.
import test from 'node:test';
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {once} from 'node:events';
import {Reader,packet,word,split,writeAll} from '../../host/os.mjs';
const buf=s=>Buffer.from(s), empty=Buffer.alloc(0), limits=Buffer.concat([word(64),word(64),word(256)]);
function error(status) {
  const str=s=>Buffer.concat([Buffer.from([4]),packet(buf(s))]);
  return packet(Buffer.concat([Buffer.from([6]),word(2),str('status'),str(status),str('value'),Buffer.from([0])]));
}
async function run(incoming,{auth=[],outputs=[],cleanupFailure=false,writeFailure=false,random=['keyA']}={}) {
  const child=spawn('target/bend-host/controller',['+RTS','--threads','1','--gpu','off','-RTS'],{stdio:['pipe','pipe','pipe']});
  const done=once(child,'close');const reader=new Reader(child.stdout);let stderr='';child.stderr.on('data',b=>stderr+=b);
  const seen=[],responses=[],states=[],inputs=[];let offset=0,ai=0,oi=0,ri=0;
  try {
    for(;;) {
      const c=await reader.frame();if(c===null)break;const op=c[0],b=c.subarray(1);seen.push(op);let result=empty,good=true;
      if(op===0)result=limits;
      else if(op===1) { const n=Number(b.readBigUInt64BE());result=incoming.subarray(offset,offset+n);offset+=result.length; }
      else if(op===2) {responses.push(b);if(writeFailure){good=false;result=buf('EPIPE');}}
      else if(op===3)result=buf('artifact'+ai);
      else if(op===4)result=Buffer.concat([limits,buf('universal')]);
      else if(op===5) {
        const [id,input]=split(b),name=id.toString();
        if(name==='initial')result=Buffer.concat([Buffer.from([1]),buf('old')]);
        else if(name==='authenticate') {
          const [state,body]=split(input);inputs.push(state);
          const entry=auth[ai++]??{code:'client',proof:'proof'};
          result=Buffer.concat([Buffer.from([1]),packet(buf(entry.code),packet(buf(entry.proof),packet(buf('instance'),buf('bindings'))))]);
        } else result=outputs[oi++]??Buffer.concat([Buffer.from([1]),packet(buf('new'),error('success'))]);
      } else if(op===7) { if(b.toString()!=='initial' && cleanupFailure){good=false;result=buf('HOST_IO');} }
      else if(op===8)result=buf(random[ri++]??'keyB');
      else if(op===9) { const [metadata,state]=split(b.subarray(1));states.push({event:b[0],state}); }
      else if(op!==6&&op!==11&&op!==12)throw Error('unknown effect '+op);
      await writeAll(child.stdin,packet(Buffer.concat([Buffer.from([good?1:0]),result])));
    }
    const [code]=await done;assert.equal(code,0,stderr);return {seen,responses,states,inputs};
  } finally {child.kill('SIGKILL');child.stdin.destroy();}
}
test('framing is byte exact, FIFO, terminal after earlier complete frame',async()=> {
  const r=await run(Buffer.concat([packet(buf('x')),Buffer.alloc(7)]));
  assert.deepEqual(r.responses,[error('success'),error('input')]);
  assert.deepEqual(r.inputs,[buf('old')]);
  const limit=await run(word(65));assert.deepEqual(limit.responses,[error('limit')]);assert.equal(limit.inputs.length,0);
});
test('actual publish waits for cleanup and rejects malformed/oversize proposals',async()=> {
  const ok=await run(Buffer.concat([packet(buf('x')),packet(buf('x'))]));
  assert.deepEqual(ok.inputs,[buf('old'),buf('new')]);
  const removed=ok.seen.indexOf(7,ok.seen.indexOf(4));assert.ok(removed<ok.seen.indexOf(2));
  for(const output of [Buffer.from([2]),Buffer.concat([Buffer.from([1]),packet(Buffer.alloc(65),error('success'))]),
    Buffer.concat([Buffer.from([1]),packet(buf('new'),Buffer.concat([error('success'),buf('trailing')]))])]) {
    const r=await run(Buffer.concat([packet(buf('x')),packet(buf('x'))]),{outputs:[output]});
    assert.deepEqual(r.responses[0],error('failure'));assert.deepEqual(r.inputs[1],buf('old'));
  }
  const failed=await run(Buffer.concat([packet(buf('x')),packet(buf('x'))]),{cleanupFailure:true});
  assert.deepEqual(failed.responses,[error('failure'),error('failure')]);assert.deepEqual(failed.inputs,[buf('old'),buf('old')]);
});
test('delivery failure stops future dispatch; Bend registry invalidates handles',async()=> {
  const stopped=await run(Buffer.concat([packet(buf('x')),packet(buf('x'))]),{writeFailure:true});assert.equal(stopped.inputs.length,1);
  const prepared=await run(Buffer.concat([packet(Buffer.from([7,0,9])),packet(Buffer.from([7,1,9])),packet(Buffer.from([7,2,9])),packet(Buffer.from([7,1,9]))]),
    {auth:[{code:'client',proof:'proof'},{code:'keyA',proof:''},{code:'keyA',proof:''},{code:'keyA',proof:''}]});
  assert.equal(prepared.responses.length,4);assert.deepEqual(prepared.responses[1],error('success'));
  assert.deepEqual(prepared.responses[3],error('failure'));assert.equal(prepared.seen.filter(x=>x===4).length,1);
});
