"""N1 only: local real timer/control observations; never complete memory/K."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import unittest
import sys
import socket
import signal
import time
from tools.accounting.build import build

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(os.environ.get('JAYDB_STAGE_TEST_OUT',ROOT/'tests/accounting/.stage-build'))
RESULTS=[]

class StageControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.library,cls.tracer=build(OUT/'standard')
        _,cls.diagnostic=build(OUT/'diagnostic',test_races=True)
        cls.probe=OUT/'stage_probe'
        command=['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror',
                 '-I',str(ROOT/'native/accounting'),str(ROOT/'tests/accounting/stage_probe.c'),
                 str(ROOT/'native/accounting/counter.c'),str(ROOT/'native/accounting/stage_runtime.c'),'-o',str(cls.probe)]
        subprocess.run(command,check=True)
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-I',str(ROOT/'native/accounting'),str(ROOT/'tests/accounting/stage_inflight.c'),str(ROOT/'native/accounting/counter.c'),str(ROOT/'native/accounting/stage_runtime.c'),'-o',str(OUT/'stage_inflight')],check=True)
        (OUT/'PROBE_BUILD.json').write_text(json.dumps({'command':command,'sha256':hashlib.sha256(cls.probe.read_bytes()).hexdigest()},indent=2)+'\n')

    def run_mode(self,mode,*,hook=None,report=True):
        name=f'{mode}-{hook or "standard"}-{report}';path=OUT/(name+'.jsonl')
        command=[str(self.diagnostic if hook else self.tracer),'--stage-control','--service-window',
                 *(['--report',str(path)] if report else []),'--',str(self.probe),mode]
        result=subprocess.run(command,capture_output=True,timeout=5,env={**os.environ,**({hook:'1'} if hook else {})})
        (OUT/(name+'.stdout')).write_bytes(result.stdout);(OUT/(name+'.stderr')).write_bytes(result.stderr)
        self.assertEqual(result.returncode,0,result.stdout.decode()+result.stderr.decode())
        rows=[json.loads(x) for x in path.read_text().splitlines()] if report else []
        if report:
            self.assertEqual(rows[-1]['type'],'summary');self.assertFalse(rows[-1]['complete'])
            snapshots={int(x['sequence']):x for x in rows if x.get('type')=='snapshot'}
            for x in snapshots.values():
                self.assertTrue(x['flags']&2)
                self.assertEqual(int(x['current']),sum(int(x[k]) for k in ('traced_private_bytes','traced_shared_bytes','fd_payload_bytes','observer_bytes')))
                peak=snapshots[int(x['peak_sequence'])]
                self.assertEqual((x['peak'],x['peak_time_ns'],x['peak_flags']),(peak['current'],peak['time_ns'],peak['flags']))
            stages=[x for x in rows if x.get('type')=='stage']
            for x in stages:
                self.assertFalse(x['memory_observation'])
                if x['event'].startswith('expired') or x['state']==3:
                    self.assertGreaterEqual(int(x['observed_ns']),int(x['deadline_ns']))
            for i,x in enumerate(rows):
                if x.get('type')=='stage' and x['event']=='recovered':
                    self.assertEqual(rows[i-1]['type'],'snapshot')
                    self.assertEqual(rows[i-1]['sequence'],x['recovery_sequence'])
        RESULTS.append({'name':name,'command':command,'status':result.returncode,'stdout':result.stdout.decode(),
                        'reportSha256':hashlib.sha256(path.read_bytes()).hexdigest() if report else None})
        return rows

    def test_01_huge_deadline_original_identity_generation_and_retire(self):
        self.run_mode('huge')

    def test_02_original_deadline_equal_to_original_start_is_expired(self):
        self.run_mode('old')

    def test_03_timer_cancels_automatic_scan_without_until_then_real_retry(self):
        rows=self.run_mode('helper',hook='JAYACCT_TEST_STAGE_SCAN')
        self.assertTrue(any(x.get('event')=='diagnostic_automatic_scan' for x in rows))
        self.assertTrue(any(x.get('type')=='cancellation' and x['discarded_partial_scan'] for x in rows))

    def test_04_timer_interrupts_waitpid_in_automatic_scan_without_until(self):
        rows=self.run_mode('helper',hook='JAYACCT_TEST_STAGE_WAIT')
        self.assertTrue(any(x.get('event')=='diagnostic_automatic_wait' for x in rows))

    def test_05_automatic_scan_and_wait_without_report(self):
        for hook in ('JAYACCT_TEST_STAGE_SCAN','JAYACCT_TEST_STAGE_WAIT'):
            self.run_mode('helper',hook=hook,report=False)

    def test_06_real_helper_kill_cleanup_persistent_receipt_and_active_window(self):
        self.run_mode('helper')

    def test_07_hold_stays_pending_retire_cannot_hide_it_release6_is_real(self):
        rows=self.run_mode('hold')
        self.assertTrue(any(x.get('event')=='expired_pending_recovery' and x['pending_flags']&8 for x in rows))

    def test_08_vfork_borrowed_mm_stays_pending_until_actual_exit(self):
        rows=self.run_mode('vfork')
        self.assertTrue(any(x.get('event')=='expired_pending_recovery' and x['pending_flags']&2 for x in rows))

    def test_09_child_cannot_arm_root_stage(self):
        self.run_mode('auth')

    def test_10_effective_inline_token_cleanup_and_outside_observer(self):
        p=subprocess.run([str(self.probe),'outside'],capture_output=True,timeout=3)
        self.assertEqual(p.returncode,0,p.stderr.decode())
        source=OUT/'inline.c';source.write_text('#include "stage_control.h"\nint f(struct jaystage_request*r,struct jaystage_receipt*s){return jaystage_raw_call(r,s,1);}\n')
        for opt in ('-O2','-O3'):
            target=OUT/(opt+'.s')
            subprocess.run(['/usr/bin/clang-19','-S',opt,'-I',str(ROOT/'native/accounting'),str(source),'-o',str(target)],check=True)
            body=target.read_text();self.assertIn('syscall',body)
            self.assertGreater(body.rfind('xorl\t%edi, %edi'),body.index('syscall'))
            RESULTS.append({'name':'stage_inline_cleanup_'+opt,'asmSha256':hashlib.sha256(target.read_bytes()).hexdigest()})

    def test_11_python_readonly_wrapper_keeps_original_receipt(self):
        code="""import sys,time,os
from tools.accounting.client import Library,Counter
from tools.accounting.stage import StageControl,Request,EXPIRED_RECOVERED
lib=Library(sys.argv[1]);counter=Counter(lib,fd=int(os.environ['JAYDB_ACCOUNTING_FD']));control=StageControl(lib)
assert control.read().state==0
scope=counter.window_read().scope_id;start=time.monotonic_ns();req=Request(scope,1,3,start,start+30000000)
assert control.arm(req).generation==1
time.sleep(.05);lib.barrier();receipt=control.read();assert receipt.state==EXPIRED_RECOVERED
assert receipt.observed_ns>=req.deadline_ns
lib.barrier();assert control.read()==receipt
control.retire(req);lib.window_end();control.close();counter.close()
print('python_stage_original_receipt')
"""
        path=OUT/'python-stage.jsonl'
        p=subprocess.run([str(self.tracer),'--stage-control','--service-window','--report',str(path),'--',sys.executable,'-B','-c',code,str(self.library)],cwd=ROOT,capture_output=True,timeout=5)
        self.assertEqual(p.returncode,0,p.stderr.decode());RESULTS.append({'name':'python_stage_wrapper','status':0,'stdout':p.stdout.decode(),'reportSha256':hashlib.sha256(path.read_bytes()).hexdigest()})

    def test_12_real_inflight_memfd_truncate_is_pending_until_lease_releases(self):
        # A separate local broker releases a REAL lease. It is test control,
        # outside the observed instance; no complete-memory claim is made.
        broker_code="""import socket,array,fcntl,os,signal,time,sys
signal.signal(signal.SIGIO,lambda *_:None)
s=socket.socket(socket.AF_UNIX,socket.SOCK_SEQPACKET);s.bind(sys.argv[1]);s.listen(1)
print('ready',flush=True);c,_=s.accept();_,anc,_,_=c.recvmsg(1,socket.CMSG_SPACE(4))
fds=array.array('i');fds.frombytes(anc[0][2][:4]);fd=fds[0]
fcntl.fcntl(fd,fcntl.F_SETLEASE,fcntl.F_RDLCK);c.send(b'A');assert c.recv(1)==b'T'
time.sleep(.25);fcntl.fcntl(fd,fcntl.F_SETLEASE,fcntl.F_UNLCK);os.close(fd);c.close();s.close()
"""
        address=str(OUT/'lease.sock')
        if Path(address).exists():Path(address).unlink()
        broker=subprocess.Popen([sys.executable,'-B','-c',broker_code,address],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        self.assertEqual(broker.stdout.readline().strip(),'ready')
        path=OUT/'inflight.jsonl'
        try:
            p=subprocess.run([str(self.tracer),'--stage-control','--service-window','--report',str(path),'--',str(OUT/'stage_inflight'),address],capture_output=True,timeout=5)
            self.assertEqual(p.returncode,0,p.stderr.decode())
            out,err=broker.communicate(timeout=2);self.assertEqual(broker.returncode,0,err)
        finally:
            if broker.poll() is None:broker.kill();broker.communicate()
        rows=[json.loads(x) for x in path.read_text().splitlines()]
        expired=[x for x in rows if x.get('event')=='expired_pending_recovery']
        self.assertEqual(len(expired),1);self.assertTrue(expired[0]['pending_flags']&1)
        self.assertTrue(any(x.get('event')=='recovered' for x in rows))
        RESULTS.append({'name':'inflight_pending_real_truncate_lease_release','status':0,'stdout':p.stdout.decode(),'reportSha256':hashlib.sha256(path.read_bytes()).hexdigest()})

    def test_13_irrecoverable_metadata_is_pending_and_does_not_kill_db(self):
        probe=OUT/'stage_metadata';diagnostic=OUT/'stage_metadata_diagnostic'
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-Wall','-Wextra','-Werror','-I',str(ROOT/'native/accounting'),str(ROOT/'tests/accounting/stage_metadata.c'),str(ROOT/'native/accounting/counter.c'),str(ROOT/'native/accounting/stage_runtime.c'),'-o',str(probe)],check=True)
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-pthread','-static','-DJAYACCT_TEST_RACES','-include',str(ROOT/'tests/accounting/metadata_diagnostic.h'),str(ROOT/'native/accounting/counter.c'),str(ROOT/'native/accounting/trace.c'),'-o',str(diagnostic)],check=True)
        path=OUT/'metadata-pending.jsonl'
        p=subprocess.Popen([str(diagnostic),'--stage-control','--service-window','--report',str(path),'--',str(probe)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,env={**os.environ,'JAYACCT_DIAG_METADATA':'regs_release','JAYACCT_DIAG_SKIP':'0','JAYACCT_TEST_KILL_URING_INFO':'1'})
        page=None;fd=None;receipt=None
        try:
            import mmap
            from tools.accounting.stage import NativeReceipt
            end=time.monotonic()+3
            while time.monotonic()<end:
                self.assertIsNone(p.poll(),'observer aborted instead of keeping metadata pending')
                if page is None:
                    for entry in (Path('/proc')/str(p.pid)/'fd').iterdir():
                        try:target=os.readlink(entry)
                        except FileNotFoundError:continue
                        if 'jaydb-stage-control-v1' in target:
                            fd=os.open(entry,os.O_RDONLY);page=mmap.mmap(fd,4096,prot=mmap.PROT_READ);break
                if page is not None:
                    before=int.from_bytes(page[:8],'little');raw=page[8:184];after=int.from_bytes(page[:8],'little')
                    if before!=after or before&1:continue
                    receipt=NativeReceipt.from_buffer_copy(raw)
                    if receipt.state==2 and receipt.pending_flags&4:break
                time.sleep(.005)
            else:self.fail('real expiry with pending essential metadata not observed')
            self.assertGreaterEqual(receipt.observed_ns.integer(),receipt.deadline_ns.integer())
            self.assertTrue((Path('/proc')/str(receipt.owner_pid)).exists(),'DB was killed internally')
            rows=[json.loads(x) for x in path.read_text().splitlines()]
            index=next(i for i,x in enumerate(rows) if x.get('event')=='unrecoverable_metadata')
            self.assertFalse(any(x.get('type') in ('snapshot','summary') for x in rows[index:]))
            RESULTS.append({'name':'irretrievable_metadata_expired_pending_no_internal_DB_kill','status':0,'pendingFlags':receipt.pending_flags,'observedNs':str(receipt.observed_ns.integer()),'deadlineNs':str(receipt.deadline_ns.integer()),'noProgressClaim':True})
        finally:
            if page is not None:page.close()
            if fd is not None:os.close(fd)
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
            out,err=p.communicate(timeout=2)
            (OUT/'metadata-pending.stdout').write_bytes(out);(OUT/'metadata-pending.stderr').write_bytes(err)
        self.assertIn(b'errno 3',err)

    def test_14_passive_page_alias_is_not_double_charged_and_default_stays_idle(self):
        rows=self.run_mode('passive')
        self.assertFalse(any(x.get('type')=='stage' and x.get('event')=='armed' for x in rows))
        text=(OUT/'passive-standard-True.stdout').read_text();_,before,after=text.strip().split()
        self.assertEqual(before,after,'same stage page must not be charged a second time for its readonly alias')
        # Observer baseline precedes the root. The new page is already mapped
        # and written by the observer before that first self-scan.
        baseline=next(x for x in rows if x.get('type')=='snapshot')
        self.assertEqual(baseline['phase'],'observer_counter_ready')
        self.assertEqual(baseline['sequence'],'1')

    def test_15_expiry_defers_until_real_committed_result_has_ownership(self):
        rows=self.run_mode('helper',hook='JAYACCT_TEST_STAGE_COMMIT')
        index=next(i for i,x in enumerate(rows) if x.get('event')=='diagnostic_committed_return')
        before=next(x for x in reversed(rows[:index]) if x.get('type')=='snapshot')
        cancel=next(i for i,x in enumerate(rows[index:],index) if x.get('type')=='cancellation')
        recovered=next(x for x in rows[cancel:] if x.get('type')=='snapshot')
        self.assertEqual(int(recovered['traced_private_bytes'])-int(before['traced_private_bytes']),1048576)
        self.assertFalse(any(x.get('type')=='snapshot' for x in rows[index:cancel]))

    def test_16_passive_opt_in_preserves_inherited_sigchld_mask(self):
        code="import signal; assert signal.SIGCHLD in signal.pthread_sigmask(signal.SIG_BLOCK,[]); assert signal.getsignal(signal.SIGCHLD) is signal.SIG_DFL"
        p=subprocess.run([str(self.tracer),'--stage-control','--',sys.executable,'-B','-c',code],capture_output=True,timeout=5,preexec_fn=lambda:signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGCHLD}))
        self.assertEqual(p.returncode,0,p.stderr.decode());RESULTS.append({'name':'passive_preserves_root_SIGCHLD_mask_and_disposition','status':0})

if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(StageControlTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    (OUT/'RESULTS_STAGE.json').write_text(json.dumps({'successful':result.wasSuccessful(),'methods':result.testsRun,'records':RESULTS,'memoryStatus':'INCOMPLETE','KProved':False},indent=2)+'\n')
    raise SystemExit(not result.wasSuccessful())
