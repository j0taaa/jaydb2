"""Independent accounting tests; does not run the global native/proof suites."""
from __future__ import annotations
import ctypes as C
import errno
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest
import select
import signal
import re
import tempfile
import importlib.util

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.accounting.build import build, DEFAULT_OUTPUT
from tools.accounting.client import Counter, INCOMPLETE, IncompleteCoverage, Library, Snapshot, NativeSnapshot, NativeWindowSnapshot, WindowSnapshot

OUT = DEFAULT_OUTPUT
RESULTS = []


class Accounting(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.library_path, cls.tracer = build()
        cls.library = Library(cls.library_path)
        for name in ('probe', 'counter_probe', 'lifecycle_probe', 'uring_probe', 'window_probe', 'deadline_probe',
                     'retention_probe', 'boundary_probe', 'review_v3/repro_reopen',
                     'review_v3/repro_offsets', 'review_v3/repro_blocking_lock',
                     'mutation_probe', 'review_v4/repro_v4', 'progress_probe',
                     'review_v5/lease_truncate', 'review_v5/fifo_variant', 'startup_probe',
                     'ownership_probe', 'review_v6/private_owner', 'review_v6/anon_ignored_fd',
                     'review_v6/window_extra', 'review_v7/lifecycle', 'availability_probe', 'marker_cleanup_probe',
                     'metadata_probe', 'review_v8/fixtures/committed_matrix'):
            subprocess.run(['/usr/bin/clang-19', '-std=c11', '-O2', '-g', '-fno-builtin',
                            '-Wall', '-Wextra', '-Werror', '-pthread', '-I', str(ROOT/'native/accounting'),
                            str(ROOT/f'tests/accounting/{name}.c'), str(ROOT/'native/accounting/counter.c'),
                            '-o', str(OUT/Path(name).name)], check=True)
        (OUT/'minimal.bendtt').write_text('unit : <()> = ()\n')
        (OUT/'minimal.c').write_text('int main(void) { return 0; }\n')
        (OUT/'not-elf').write_text('invalid executable, intentionally no interpreter\n')
        (OUT/'not-elf').chmod(0o700)

    def trace(self, name, command, timeout=30):
        report = OUT/f'{name}.jsonl'
        started = time.monotonic_ns()
        result = subprocess.run([str(self.tracer), '--report', str(report), '--', *map(str, command)],
                                cwd=ROOT, capture_output=True, timeout=timeout)
        self.assertEqual(result.returncode, 0, result.stderr.decode()+result.stdout.decode())
        records = [json.loads(line) for line in report.read_text().splitlines()]
        summary = records[-1]
        self.assertEqual(summary['type'], 'summary')
        self.assertFalse(summary['complete'])
        self.assertTrue(summary['observer_included'])
        snapshots = [r for r in records if r['type']=='snapshot']
        by_sequence = {int(x['sequence']): x for x in snapshots}
        for r in snapshots:
            self.assertTrue(r['flags'] & INCOMPLETE)
            self.assertGreaterEqual(int(r['current']), int(r['observer_bytes']))
            self.assertEqual(int(r['current']),sum(int(r[k]) for k in
                ('traced_private_bytes','traced_shared_bytes','fd_payload_bytes','observer_bytes')))
            self.assertGreaterEqual(int(r['peak']), int(r['current']))
            witness = by_sequence[int(r['peak_sequence'])]
            self.assertEqual(witness['current'], r['peak'])
            self.assertEqual(witness['time_ns'], r['peak_time_ns'])
            self.assertLessEqual(int(r['peak_sequence']), int(r['sequence']))
            self.assertLessEqual(int(r['peak_time_ns']), int(r['time_ns']))
        self.assertEqual(int(summary['current']), int(snapshots[-1]['observer_bytes']))
        self.assertGreater(int(summary['current']), 0)
        RESULTS.append({'name': name, 'status': 0, 'summary': summary,
                        'elapsed_ns': str(time.monotonic_ns()-started),
                        'report_sha256': hashlib.sha256(report.read_bytes()).hexdigest(),
                        'stdout': result.stdout.decode()})
        return result, snapshots

    def mode(self, name):
        result, records = self.trace(name, [OUT/'probe', name])
        samples = {p[0]: (int(p[1]), int(p[2])) for line in result.stdout.decode().splitlines()
                   if len(p := line.split()) == 3}
        return samples, records

    def test_01_cooperative_real_allocations_threads_processes_owner_death(self):
        r = subprocess.run([str(OUT/'counter_probe')], capture_output=True, timeout=15)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        RESULTS.append({'name': 'cooperative_transactions_real_mmap_threads_fork_robust_death', 'status': 0})

    def test_02_nat_equality_and_wide_counter(self):
        c = Counter(self.library)
        try:
            n = c.change(acquired=2**100)
            self.assertEqual(n.current, 2**100)
            self.assertFalse(n.exceeds(2**100))
            self.assertTrue(n.exceeds(2**100-1))
            self.assertFalse(n.exceeds(10**1000))
            self.assertIsNone(n.excess_witness(2**100))
            c.change(released=2**100)
            later = c.read()
            witness = later.excess_witness(2**100-1)
            self.assertEqual(witness.sequence, n.sequence)
            self.assertEqual(witness.monotonic_ns, n.monotonic_ns)
            self.assertLess(witness.monotonic_ns, later.monotonic_ns)
            with self.assertRaises(IncompleteCoverage):
                later.require_complete()
            with self.assertRaises(OSError):
                c.change(released=1)
            self.assertEqual(c.read().current, 0)
        finally:
            c.close()
        # Numeric ABI test only; 2**100 is not claimed to be a real allocation.
        RESULTS.append({'name': 'numeric_u128_and_arbitrary_Nat_only', 'status': 0})

    def test_03_outside_tracer_is_unsupported(self):
        with self.assertRaises(OSError) as r:
            self.library.barrier()
        self.assertEqual(r.exception.errno, errno.ENOTSUP)

    def test_04_mapping_reservation_activation_revoke_syscall_remap(self):
        self.mode('mappings')
        self.mode('retained_remap')

    def test_05_shared_overlapping_alias_union(self):
        self.mode('aliases')

    def test_06_malloc_realloc_and_allocator_retention(self):
        samples, _ = self.mode('malloc')
        self.assertGreater(samples['malloc'][0], samples['before_malloc'][0]+16*1024**2)
        self.assertGreater(samples['realloc'][0], samples['malloc'][0])
        self.assertLess(samples['free'][0], samples['realloc'][0]-20*1024**2)
        self.assertEqual(samples['small'][0], samples['small_free_retained'][0])

    def test_07_brk(self):
        self.mode('brk')

    def test_08_automatic_stack_and_transient_peak_provenance(self):
        self.mode('stack')
        samples, records = self.mode('transient_stack')
        self.assertGreater(samples['transient_stack_after'][1], samples['transient_stack_after'][0]+60*1024**2)
        self.assertGreater(max(int(r['automatic_stack_bytes']) for r in records), 1024**2)
        _, records = self.mode('transient')
        self.assertLess(int(records[-1]['peak_sequence']), int(records[-1]['sequence']))

    def test_09_threads_fork_vfork_exec_lifetime(self):
        samples, _ = self.mode('threads')
        self.assertLess(samples['thread_active'][0]-samples['thread_before'][0], 10*1024**2)
        samples, _ = self.mode('fork')
        self.assertGreater(samples['fork_child'][0], samples['fork_before'][0])
        self.assertEqual(samples['fork_after'][0], samples['fork_before'][0])
        self.mode('vfork')
        self.mode('fork_storm')

    def test_10_held_window(self):
        _, records = self.mode('hold')
        begin = next(r for r in records if r['phase'] == 'hold_begin')
        end = next(r for r in records if r['phase'] == 'hold_end')
        self.assertEqual(begin['current'], end['current'])
        self.assertLess(int(begin['sequence']), int(end['sequence']))

    def test_11_exec_temporary_mm_visibility_obstacle(self):
        samples, _ = self.mode('exec_fail')
        self.assertEqual(samples['exec_before'][0], samples['exec_failed_same_visible_maps'][0])
        # Linux's separate bprm->mm is invisible in proc maps. This equality
        # demonstrates an observation gap, NOT absence of temporary allocation.

    def test_12_python_host_and_real_node_bendtt_clang_helpers(self):
        kernel = ROOT/'.tools/bendtt-e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18'
        result, records = self.trace('node_bendtt_clang', ['node', ROOT/'tests/accounting/helpers.mjs',
            kernel, OUT/'minimal.bendtt', OUT/'minimal.c', OUT/'minimal.o'], timeout=45)
        data = json.loads(result.stdout)
        self.assertEqual([s['name'] for s in data['stages']], ['bendtt', 'clang'])
        self.assertIn('ALL PROOFS CHECK', data['stages'][0]['stdout'])
        code = ('from tools.accounting.client import Library; import json,os; '
                f'l=Library({str(self.library_path)!r}); s=l.barrier(); '
                'print(json.dumps({"pid":os.getpid(),"current":s.current,"sequence":s.sequence}))')
        result, _ = self.trace('python_host', [sys.executable, '-c', code])
        data = json.loads(result.stdout)
        self.assertGreater(data['current'], 0)
        self.assertGreater(data['sequence'], 0)

    def test_13_nonleader_exec_and_competing_exec(self):
        for mode in ('nonleader', 'exec_race'):
            _, records = self.trace(mode, [OUT/'lifecycle_probe', mode])
            summary = json.loads((OUT/f'{mode}.jsonl').read_text().splitlines()[-1])
            self.assertEqual(summary['nonleader_execs'], 1)
            self.assertEqual(max(int(r['memory_spaces']) for r in records), 1)
            lifecycle = [json.loads(s) for s in (OUT/f'{mode}.jsonl').read_text().splitlines()]
            execs = [r for r in lifecycle if r.get('event')=='exec']
            self.assertEqual(len(execs), 2)
            self.assertNotEqual(execs[0]['mm'], execs[1]['mm'])
            self.assertNotEqual(int(execs[1]['detail']), execs[1]['pid'])

    @staticmethod
    def wait_lifecycle(report, event, pid, timeout=5):
        deadline = time.monotonic()+timeout
        while time.monotonic()<deadline:
            if report.exists():
                for line in report.read_text().splitlines():
                    try:
                        r=json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if r.get('event')==event and r.get('pid')==pid:
                        return
            time.sleep(.005)
        raise AssertionError(f'Missing lifecycle event {event} for {pid}')

    def test_14_job_control_preserves_stop_until_sigcont(self):
        report=OUT/'job_control.jsonl'
        p=subprocess.Popen([str(self.tracer),'--report',str(report),'--',str(OUT/'lifecycle_probe'),'job'],
                           stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                           start_new_session=True)
        try:
            self.assertTrue(select.select([p.stdout],[],[],5)[0])
            ready=p.stdout.readline().decode().split();self.assertEqual(ready[0],'ready');pid=int(ready[1])
            os.kill(pid,signal.SIGSTOP)
            self.wait_lifecycle(report,'group_stop',pid)
            p.stdin.write(b'x');p.stdin.flush()
            self.assertFalse(select.select([p.stdout],[],[],.05)[0], 'Stopped program executed before SIGCONT')
            os.kill(pid,signal.SIGCONT)
            out,err=p.communicate(timeout=10)
            self.assertEqual(p.returncode,0,err.decode())
            self.assertIn(b'resumed',out)
            summary=json.loads(report.read_text().splitlines()[-1])
            self.assertGreater(summary['group_stops'],0)
            self.assertFalse(summary['complete'])
            RESULTS.append({'name':'job_control_SIGSTOP_LISTEN_SIGCONT','status':0,'summary':summary})
        finally:
            if p.poll() is None:p.kill();p.wait()

    def test_15_asynchronous_sigkill_during_barriers(self):
        for attempt in range(4):
            report=OUT/f'async_kill_{attempt}.jsonl'
            p=subprocess.Popen([str(self.tracer),'--report',str(report),'--',str(OUT/'lifecycle_probe'),'victim'],
                               stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
            try:
                self.assertTrue(select.select([p.stdout],[],[],5)[0])
                line=p.stdout.readline().decode().split();self.assertEqual(line[0],'victim');victim=int(line[1])
                if attempt:time.sleep(.005*attempt)
                os.kill(victim,signal.SIGKILL)
                out,err=p.communicate(timeout=10)
                self.assertEqual(p.returncode,0,err.decode())
                self.assertIn(b'victim_retired',out)
                records=[json.loads(s) for s in report.read_text().splitlines()]
                summary=records[-1]
                self.assertEqual(summary['root_status'],0)
                last=[r for r in records if r['type']=='snapshot'][-1]
                self.assertEqual(last['current'],last['observer_bytes'])
                self.assertEqual(last['memory_spaces'],0)
                RESULTS.append({'name':f'asynchronous_SIGKILL_{attempt}','status':0,'summary':summary})
            finally:
                if p.poll() is None:p.kill();p.wait()

    def test_16_real_death_between_maps_and_validation_is_not_published(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/'kill_after_scan.jsonl'
        r=subprocess.run([str(tracer),'--report',str(report),'--','/bin/true'],
                         env={**os.environ,'JAYACCT_TEST_KILL_AFTER_SCAN':'1'},capture_output=True,timeout=10)
        self.assertEqual(r.returncode,128+signal.SIGKILL,r.stderr.decode())
        records=[json.loads(s) for s in report.read_text().splitlines()]
        self.assertEqual(records[-1]['invalidated_observations'],1)
        snapshots=[r for r in records if r['type']=='snapshot']
        self.assertTrue(all(r['memory_spaces']==0 for r in snapshots))
        self.assertEqual(snapshots[-1]['current'],snapshots[-1]['observer_bytes'])
        RESULTS.append({'name':'actual_SIGKILL_after_scan_discards_torn_observation','status':0,'summary':records[-1]})

    def test_17_uring_fd_only_aliases_dup_fork_close_range_and_exec(self):
        for mode in ('lifetime','exec'):
            r,records=self.trace('uring_'+mode,[OUT/'uring_probe',mode])
            self.assertIn('fd_only 28672',r.stdout.decode())
            summary=json.loads((OUT/f'uring_{mode}.jsonl').read_text().splitlines()[-1])
            self.assertEqual(summary['unsupported_object_events'],0)
            self.assertEqual(summary['uring_objects_created'],3 if mode=='lifetime' else 1)
            self.assertEqual(int(records[-1]['fd_payload_bytes']),0)
            self.assertIn(28672,{int(r['fd_payload_bytes']) for r in records})

    def test_18_event_identity_shared_anonymous_alias(self):
        self.mode('shared_anon_event')

    def test_20_unshare_files_preserves_other_threads_fd_payload(self):
        result,records=self.trace('uring_unshare',[OUT/'uring_probe','unshare'])
        stages={line.split()[0]:int(line.split()[1]) for line in result.stdout.decode().splitlines()}
        by_seq={int(r['sequence']):r for r in records}
        self.assertEqual(int(by_seq[stages['unshare_retained']]['fd_payload_bytes']),28672)
        self.assertEqual(int(by_seq[stages['unshare_released']]['fd_payload_bytes']),0)

    def test_21_request_window_real_allocations_global_peak_does_not_mask_new_excess(self):
        self.assertEqual(C.sizeof(NativeSnapshot),120)
        self.assertEqual(C.sizeof(NativeWindowSnapshot),280)
        result,records=self.trace('request_windows',[OUT/'window_probe'])
        lines={p[0]:list(map(int,p[1:])) for line in result.stdout.decode().splitlines() if (p:=line.split())}
        ceiling=lines['ceiling'][0]
        by_seq={int(r['sequence']):r for r in records}
        windows=[]
        for name in ('one','two','three','closed_later'):
            scope,peak,seq,ns,global_peak,current,begin,end,flags,state=lines[name]
            witness=by_seq[seq]
            self.assertEqual(int(witness['current']),peak)
            self.assertEqual(int(witness['time_ns']),ns)
            self.assertEqual(flags,witness['flags'])
            self.assertLessEqual(begin,seq);self.assertLessEqual(seq,end)
            global_snapshot=Snapshot(end,current,global_peak,int(by_seq[end]['time_ns']),0,0,3,3)
            window=WindowSnapshot(global_snapshot,scope,state,begin,0,end,0,peak,ns,seq,flags)
            windows.append(window)
        one,two,three,later=windows
        self.assertGreater(one.peak,two.peak)
        self.assertGreater(two.peak,ceiling)
        self.assertEqual(three.peak,ceiling)
        self.assertIsNone(three.excess_witness(ceiling))
        witness=two.excess_witness(ceiling)
        self.assertEqual(witness.amount,two.peak)
        self.assertGreater(witness.sequence,two.begin_sequence)
        self.assertNotEqual(witness.sequence,one.peak_sequence)
        self.assertEqual((later.peak,later.peak_sequence,later.peak_monotonic_ns),
                         (three.peak,three.peak_sequence,three.peak_monotonic_ns))

    def test_22_python_native_and_helper_read_the_same_request_window(self):
        code='''
from tools.accounting.client import Library,Counter
from dataclasses import asdict
import json,mmap,os
lib=Library(LIBRARY)
counter=Counter(lib,fd=int(os.environ['JAYDB_ACCOUNTING_FD']))
begin=lib.window_begin()
child=os.fork()
if not child:
    view=counter.window_read().require_scope(begin.scope_id)
    assert view.active
    os._exit(0)
assert os.waitpid(child,0)[1]==0
allocation=mmap.mmap(-1,8*1024*1024)
live=lib.window_barrier().require_scope(begin.scope_id)
allocation.close()
end=lib.window_end().require_scope(begin.scope_id)
later=counter.window_read().require_scope(begin.scope_id)
assert not later.active and later.peak==end.peak
assert later.peak_sequence==end.peak_sequence and later.peak_monotonic_ns==end.peak_monotonic_ns
witness=end.excess_witness(end.peak-1)
assert witness.scope_id==begin.scope_id and witness.sequence>=begin.begin_sequence
print(json.dumps({'begin':asdict(begin),'end':asdict(end),'later':asdict(later),'witness':asdict(witness)}))
counter.close()
'''.replace('LIBRARY',repr(str(self.library_path)))
        result,records=self.trace('python_request_window',[sys.executable,'-B','-c',code])
        data=json.loads(result.stdout)
        witness=next(r for r in records if int(r['sequence'])==data['witness']['sequence'])
        self.assertEqual(int(witness['current']),data['witness']['amount'])
        self.assertEqual(int(witness['time_ns']),data['witness']['monotonic_ns'])

    def test_23_static_observer_bootstrap_has_no_delivered_transient_release(self):
        built=json.loads((OUT/'BUILD.json').read_text())
        self.assertIn('-static',built['observer_flags'])
        headers=subprocess.check_output(['readelf','-l',str(self.tracer)],text=True)
        self.assertNotIn('INTERP',headers)
        log=OUT/'static-bootstrap.strace';report=OUT/'static-bootstrap.jsonl'
        result=subprocess.run(['strace','-qq','-o',str(log),'-e',
            'trace=%memory,memfd_create,openat,read,close,execve,write',
            str(self.tracer),'--report',str(report),'--','/bin/true'],capture_output=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        prefix=log.read_text().split('memfd_create("jaydb-allocation-counter"',1)[0]
        self.assertNotIn('mmap(',prefix);self.assertNotIn('munmap(',prefix);self.assertNotIn('mremap(',prefix)
        brks=[int(x,16) for x in re.findall(r'brk\([^\n]*\)\s+= (0x[0-9a-f]+)',prefix)]
        self.assertEqual(brks,sorted(brks))
        self.assertNotIn('PROT_NONE',prefix)
        rows=[json.loads(line) for line in report.read_text().splitlines()]
        self.assertEqual([x['phase'] for x in rows[:3]],
                         ['observer_counter_ready','observer_environment_ready','observer_metadata_ready'])
        self.assertGreater(int(rows[0]['observer_bytes']),0)
        self.assertEqual(rows[-1]['root_status'],0)
        RESULTS.append({'name':'static_observer_monotonic_userspace_bootstrap', 'status':0,
                        'strace_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'summary':rows[-1]})

    def test_24_absolute_deadline_past_and_clock_domain_future(self):
        result,_=self.trace('deadline_past',[OUT/'deadline_probe','past'])
        self.assertIn(b'past_deadline_and_unreachable_future_ok',result.stdout)

    def test_25_timer_interrupts_real_waitpid_and_preserves_window_and_hold(self):
        self.deadline_interruption('wait')

    def test_26_timer_cancels_partial_scan_without_fd_or_bank_leak(self):
        self.deadline_interruption('scan')

    def deadline_interruption(self, phase):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/f'deadline_{phase}.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'deadline_probe'),phase],
            env={**os.environ,'JAYACCT_TEST_DEADLINE_'+phase.upper():'1'},capture_output=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        self.assertIn(('cancelled_'+phase).encode(),result.stdout)
        rows=[json.loads(x) for x in report.read_text().splitlines()]
        cancelled=[r for r in rows if r['type']=='cancellation']
        self.assertEqual(len(cancelled),1)
        self.assertFalse(cancelled[0]['output_valid'])
        self.assertTrue(cancelled[0]['discarded_partial_scan'])
        self.assertGreaterEqual(int(cancelled[0]['observed_ns']),int(cancelled[0]['deadline_ns']))
        self.assertEqual(rows[-1]['root_status'],0)
        self.assertEqual(rows[-1]['deadline_cancellations'],1)
        RESULTS.append({'name':'deadline_cancellation_'+phase,'status':0,'summary':rows[-1],
                        'cancellation':cancelled[0],'stdout':result.stdout.decode()})

    def test_27_dying_uring_owner_commit_recovered_before_mm_and_files_disappear(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/'dying_uring_owner.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'uring_probe'),'dying_shared_files'],
            env={**os.environ,'JAYACCT_TEST_KILL_URING_EXIT':'1'},capture_output=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        rows=[json.loads(x) for x in report.read_text().splitlines()]
        stages={p[0]:int(p[1]) for line in result.stdout.decode().splitlines() if (p:=line.split())}
        by_seq={int(r['sequence']):r for r in rows if r['type']=='snapshot'}
        self.assertEqual(int(by_seq[stages['dying_owner_retained']]['fd_payload_bytes']),28672)
        self.assertEqual(int(by_seq[stages['dying_owner_released']]['fd_payload_bytes']),0)
        self.assertEqual(rows[-1]['recovered_syscall_results'],1)
        self.assertEqual(rows[-1]['uring_objects_created'],1)
        self.assertEqual(rows[-1]['root_status'],0)
        self.assertTrue(any(r.get('event')=='syscall_result_recovered' for r in rows))
        RESULTS.append({'name':'real_SIGKILL_setup_commit_shared_fd_table_different_mm','status':0,
                        'summary':rows[-1],'stdout':result.stdout.decode()})

    def test_19_marker_returns_exit_observation_after_real_observer_growth(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/'marker_exit_growth.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'probe'),'hold'],
                              env={**os.environ,'JAYACCT_TEST_GROW_MARKER_ENTRY':'1'},
                              capture_output=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        records=[json.loads(x) for x in report.read_text().splitlines()]
        entry=next(r for r in records if r.get('phase')=='test_marker_entry_before_growth')
        delivered=next(r for r in records if r.get('phase')=='hold_begin')
        end=next(r for r in records if r.get('phase')=='hold_end')
        self.assertEqual(int(delivered['current'])-int(entry['current']),65536)
        self.assertEqual(int(delivered['observer_bytes'])-int(entry['observer_bytes']),65536)
        self.assertGreater(int(delivered['sequence']),int(entry['sequence']))
        self.assertEqual(delivered['current'],end['current'])
        RESULTS.append({'name':'marker_exit_includes_real_observer_slab_acquired_after_entry',
                        'status':0,'entry':entry,'delivered':delivered,'summary':records[-1]})

    def retention_stages(self,result,records):
        by_seq={int(r['sequence']):r for r in records}
        return {parts[0]:by_seq[int(parts[1])] for line in result.stdout.decode().splitlines()
                if (parts:=line.split())}

    def test_28_vfork_close_keeps_blocked_parents_independent_fd_owner(self):
        for mode in ('vfork_close','vfork_no_close','fork_close','vfork_exec','vfork_kill_parent'):
            result,records=self.trace('retention_'+mode,[OUT/'retention_probe',mode],timeout=5)
            stages=self.retention_stages(result,records)
            before,after=('blocked_parent_retains','killed_parent_released') if mode=='vfork_kill_parent' else ('ring_parent_retains','ring_released')
            self.assertEqual(int(stages[before]['fd_payload_bytes']),28672)
            self.assertEqual(int(stages[after]['fd_payload_bytes']),0)
            summary=json.loads((OUT/f'retention_{mode}.jsonl').read_text().splitlines()[-1])
            self.assertEqual(summary['invalidated_observations'],0)
        result=subprocess.run([str(self.tracer),'--',str(OUT/'retention_probe'),'vfork_close'],
                              capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode())

    def test_29_shared_object_activation_outlives_alias_and_ram_fd_outlives_views(self):
        for mode in ('anon','memfd','regular'):
            result,records=self.trace('retention_'+mode,[OUT/'retention_probe',mode])
            stages=self.retention_stages(result,records)
            base=int(stages['reserved']['traced_shared_bytes'])
            for name in ('reserved','alias_reserved'):
                self.assertEqual(int(stages[name]['traced_shared_bytes']),base)
            for name in ('alias_active','alias_removed','original_reactivated','original_revoked'):
                self.assertEqual(int(stages[name]['traced_shared_bytes'])-base,1024*1024)
            expected=1024*1024 if mode=='memfd' else 0
            self.assertEqual(int(stages['last_view_removed']['traced_shared_bytes'])-base,expected)
            if mode!='anon':
                self.assertEqual(int(stages['fd_copy_retains']['traced_shared_bytes'])-base,expected)
                self.assertEqual(int(stages['last_fd_closed']['traced_shared_bytes']),base)

    def test_30_memfd_write_overlap_shrink_and_virtual_growth(self):
        result,records=self.trace('retention_memfd_writes',[OUT/'retention_probe','memfd_writes'])
        stages=self.retention_stages(result,records);base=int(stages['size_only']['traced_shared_bytes'])
        expected={'pwrite_page':4096,'pwrite_overlap':8192,'shrink_partial':4096,'shrink_zero':0,
                  'grow_reservation_only':0,'writev_pages':8192,'pwritev_page':12288,
                  'pwritev2_current':16384,'append_pwrite':20480,'written_fd_closed':0}
        for name,amount in expected.items():self.assertEqual(int(stages[name]['traced_shared_bytes'])-base,amount,name)

    def test_31_object_offsets_partial_alias_remap_fork_and_fd_cloexec(self):
        result,records=self.trace('retention_partial_alias',[OUT/'retention_probe','partial_alias'])
        stages=self.retention_stages(result,records);base=int(stages['partial_reserved']['traced_shared_bytes'])
        expected={'partial_active':262144,'partial_alias_moved':262144,'partial_only_reservation':262144,
                  'partial_disjoint':266240,'partial_fd_only':266240,'partial_shrink':69632,
                  'partial_extend_none':69632,'partial_closed':0}
        for name,amount in expected.items():self.assertEqual(int(stages[name]['traced_shared_bytes'])-base,amount,name)
        result,records=self.trace('retention_fork_activation',[OUT/'retention_probe','fork_activation'])
        stages=self.retention_stages(result,records);base=int(stages['fork_reserved']['traced_shared_bytes'])
        self.assertEqual(int(stages['fork_child_retired']['traced_shared_bytes'])-base,1048576)
        self.assertEqual(int(stages['fork_parent_reactivated']['traced_shared_bytes'])-base,1048576)
        self.assertEqual(int(stages['fork_last_view_removed']['traced_shared_bytes']),base)
        result,records=self.trace('retention_memfd_fork_exec',[OUT/'retention_probe','memfd_fork_exec'])
        stages=self.retention_stages(result,records)
        self.assertEqual(stages['exec_fd_only']['traced_shared_bytes'],stages['exec_child_only']['traced_shared_bytes'])
        self.assertEqual(int(stages['exec_fd_only']['traced_shared_bytes'])-int(stages['exec_cloexec_released']['traced_shared_bytes']),1048576)

    def test_32_deadline_discards_pending_history_without_losing_committed_retention(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/'retention_cancel.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'retention_probe'),'cancel_retention'],
            env={**os.environ,'JAYACCT_TEST_DEADLINE_RETAINED':'1'},capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        rows=[json.loads(s) for s in report.read_text().splitlines()]
        stages=self.retention_stages(result,[r for r in rows if r['type']=='snapshot'])
        self.assertEqual(stages['cancel_before']['traced_shared_bytes'],stages['cancel_after']['traced_shared_bytes'])
        self.assertEqual(int(stages['cancel_after']['traced_shared_bytes'])-int(stages['cancel_fd_closed']['traced_shared_bytes']),1048576)
        cancellation=[r for r in rows if r['type']=='cancellation'];self.assertEqual(len(cancellation),1)
        self.assertFalse(cancellation[0]['output_valid']);self.assertTrue(cancellation[0]['discarded_partial_scan'])
        self.assertEqual(rows[-1]['deadline_cancellations'],1)
        RESULTS.append({'name':'cancel_pending_retained_history_preserves_committed_object_offsets','status':0,
                        'cancellation':cancellation[0],'summary':rows[-1]})

    @staticmethod
    def boundary_stages(result,records):
        by_seq={int(r['sequence']):r for r in records}
        matches=(re.fullmatch(r'([a-z_]+) ([0-9]+)(?: [0-9]+ [0-9]+)?',line)
                 for line in result.stdout.decode().splitlines())
        return {m[1]:by_seq[int(m[2])] for m in matches if m}

    def shared_deltas(self,stages,baseline,expected):
        base=int(stages[baseline]['traced_shared_bytes'])
        for name,amount in expected.items():
            self.assertEqual(int(stages[name]['traced_shared_bytes'])-base,amount,name)

    def test_33_original_reopen_counterexample_three_runs(self):
        for attempt in range(3):
            result,records=self.trace(f'v3_reopen_{attempt}',[OUT/'repro_reopen'])
            self.assertIn(b'retained_byte 42 same_inode 1',result.stdout)
            self.shared_deltas(self.boundary_stages(result,records),'baseline',{
                'original_fd_owns':1048576,'reopened_fd_owns':1048576,
                'data_still_retained':1048576,'last_fd_closed':0})

    def test_34_original_remap_file_pages_counterexample_three_runs(self):
        for attempt in range(3):
            result,records=self.trace(f'v3_offsets_{attempt}',[OUT/'repro_offsets'])
            self.assertIn(b'retained_bytes 42 43',result.stdout)
            self.shared_deltas(self.boundary_stages(result,records),'baseline',{
                'offset_zero_acquired':1048576,'offset_one_acquired':2097152,
                'both_offsets_fd_only':2097152,'closed':0})

    def test_35_original_blocking_lock_progress_with_and_without_report(self):
        for attempt in range(3):
            result,_=self.trace(f'v3_blocking_lock_{attempt}',[OUT/'repro_blocking_lock'],timeout=5)
            self.assertIn(b'completed',result.stdout)
            for prefix in ([],[str(self.tracer),'--']):
                start=time.monotonic_ns()
                result=subprocess.run([*prefix,str(OUT/'repro_blocking_lock')],
                                      capture_output=True,timeout=5,start_new_session=True)
                self.assertEqual(result.returncode,0,result.stderr.decode())
                self.assertIn(b'completed',result.stdout)
                RESULTS.append({'name':f'v3_blocking_lock_{"no_report" if prefix else "control"}_{attempt}',
                                'status':0,'elapsed_ns':str(time.monotonic_ns()-start),
                                'stdout':result.stdout.decode()})

    def test_36_reopened_fd_identity_dup_cloexec_truncation_and_regular_negative(self):
        for mode in ('open','openat','openat2','path','read','truncate','truncate_openat2','creat'):
            result,records=self.trace('boundary_'+mode,[OUT/'boundary_probe',mode])
            retained=0 if mode.startswith('truncate') or mode=='creat' else 1048576
            self.shared_deltas(self.boundary_stages(result,records),'baseline',{
                'acquired':1048576,'failed_open':1048576,'reopened_only':retained,
                'dup_only':retained,'dup_cloexec_only':retained,'closed':0})
        result,records=self.trace('boundary_regular',[OUT/'boundary_probe','regular'])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',{
            'regular_unmapped':0,'regular_reopened':0,'closed':0})

    def test_37_reopened_fd_survives_fork_exec_according_to_descriptor_flags(self):
        result,records=self.trace('boundary_reopen_exec',[OUT/'boundary_probe','reopen_exec'])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',{
            'child_only':1048576,'after_exec':1048576,'exec_closed':0,'retired':0})

    def test_38_remap_offsets_partial_reserved_replaced_failed_and_shared_anon(self):
        result,records=self.trace('boundary_remap_edges',[OUT/'boundary_probe','remap_edges'])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',{
            'first_offset':1048576,'new_offset':2097152,'old_offset_again':2097152,
            'failed_remap':2097152,'new_reserved_offset':2097152,'partial_activation':2359296,
            'replacement_reserved':2359296,'replacement_active':2363392,
            'fds_only':2363392,'second_fd_only':4096,'closed':0})
        result,records=self.trace('boundary_remap_anon',[OUT/'boundary_probe','remap_anon'])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',{
            'first_offset':1048576,'second_offset':2097152,'reservation_retains':2097152,
            'alias_reactivated':2097152,'closed':0})

    def test_39_fcntl_queries_and_locks_do_not_enter_memory_scheduler(self):
        result,records=self.trace('boundary_queries',[OUT/'boundary_probe','queries'])
        stages=self.boundary_stages(result,records)
        lo=int(stages['before_queries']['sequence']);hi=int(stages['after_queries']['sequence'])
        self.assertFalse([r for r in records if lo<int(r['sequence'])<hi and r['syscall']==72])
        for attempt in range(3):
            result,_=self.trace(f'boundary_ofd_wait_{attempt}',[OUT/'boundary_probe','ofd_wait'],timeout=5)
            self.assertIn(b'completed',result.stdout)

    def test_40_fifo_open_progress_including_ignored_truncate_flag(self):
        for method in ('open','openat','openat2','cwd','dirfd','rooted'):
            for truncate in (0,1):
                command=[OUT/'boundary_probe','fifo',method,str(truncate)]
                control=subprocess.run(list(map(str,command)),capture_output=True,timeout=5)
                self.assertEqual(control.returncode,0,control.stderr.decode())
                self.assertIn(b'completed',control.stdout)
                result,_=self.trace(f'boundary_fifo_{method}_{truncate}',command,timeout=5)
                self.assertIn(b'completed',result.stdout)
                result=subprocess.run([str(self.tracer),'--',*map(str,command)],capture_output=True,timeout=5)
                self.assertEqual(result.returncode,0,result.stderr.decode())
                self.assertIn(b'completed',result.stdout)

    def test_41_successful_open_recovered_in_exit_keeps_shared_fd_table_owner(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        report=OUT/'boundary_open_exit_death.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'boundary_probe'),'open_exit_death'],
            env={**os.environ,'JAYACCT_TEST_KILL_OPEN_EXIT':'1'},capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        rows=[json.loads(line) for line in report.read_text().splitlines()]
        self.shared_deltas(self.boundary_stages(result,[r for r in rows if r['type']=='snapshot']),
                           'baseline',{'recovered_owner_only':1048576,'closed':0})
        self.assertEqual(rows[-1]['recovered_syscall_results'],1)
        self.assertEqual(rows[-1]['unsupported_object_events'],0)
        self.assertEqual(rows[-1]['invalidated_observations'],0)
        self.assertFalse(rows[-1]['complete'])
        RESULTS.append({'name':'open_real_SIGKILL_before_result_recovered_at_EXIT_CLONE_FILES',
                        'status':0,'summary':rows[-1],'stdout':result.stdout.decode(),
                        'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_42_special_fd_types_and_invalid_openat2_arguments(self):
        result,records=self.trace('boundary_special',[OUT/'boundary_probe','special'])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',{'special_closed':0})

    def test_43_reopened_descriptor_installed_cloexec_flag_controls_exec_retention(self):
        for cloexec in (0,1):
            result,records=self.trace(f'boundary_direct_exec_{cloexec}',
                                      [OUT/'boundary_probe','reopen_exec_direct',str(cloexec)])
            self.shared_deltas(self.boundary_stages(result,records),'baseline',{
                'child_only':1048576,'after_exec':0 if cloexec else 1048576,
                'exec_closed':0,'retired':0})

    @staticmethod
    def review_v4_stages(result,records):
        by_seq={int(r['sequence']):r for r in records}
        return {s[1]:by_seq[int(s[2])] for line in result.stdout.decode().splitlines()
                if (s:=line.split()) and s[0]=='STAGE'}

    def test_44_original_v4_counterexamples_raw_fd_path_truncate_and_fallocate(self):
        cases=[('close',['close','1'],{'owned':1048576,'closed':0}),
               ('dup',['dup','1'],{'owned':1048576,'before_exec':1048576,'after_exec':0}),
               ('truncate',['truncate','path'],{'owned':1048576,'truncated':0,'closed':0}),
               ('fallocate',['allocate','fallocate'],{'fd_payload':1048576,'after_read':1048576,'closed':0})]
        for attempt in range(3):
            for name,args,expected in cases:
                result,records=self.trace(f'v4_original_{name}_{attempt}',[OUT/'repro_v4',*args])
                self.shared_deltas(self.review_v4_stages(result,records),'baseline',expected)

    def test_45_original_rooted_absolute_symlink_fifo_with_controls(self):
        for attempt in range(3):
            for link,trunc in ((1,1),(0,1),(1,0)):
                for mode in ('control','report','no-report'):
                    with tempfile.TemporaryDirectory(prefix='v4-fifo-',dir=OUT) as directory:
                        command=[OUT/'repro_v4','rooted_fifo',directory,str(link),str(trunc)]
                        name=f'v4_fifo_{attempt}_{link}_{trunc}_{mode}'
                        if mode=='report':result,_=self.trace(name,command,timeout=5)
                        else:
                            prefix=[str(self.tracer),'--'] if mode=='no-report' else []
                            process=subprocess.Popen([*prefix,*map(str,command)],stdout=subprocess.PIPE,
                                                     stderr=subprocess.PIPE,start_new_session=True)
                            try:out,err=process.communicate(timeout=5)
                            except subprocess.TimeoutExpired:
                                os.killpg(process.pid,signal.SIGKILL);process.communicate();raise
                            self.assertEqual(process.returncode,0,err.decode())
                            result=subprocess.CompletedProcess(command,process.returncode,out,err)
                            RESULTS.append({'name':name,'status':0,'stdout':out.decode()})
                        self.assertIn(b'FACT completed 1',result.stdout)

    def mutation_mode(self,mode,expected,args=()):
        name='mutation_'+mode+('_'+'_'.join(args) if args else '')
        result,records=self.trace(name,[OUT/'mutation_probe',mode,*args])
        self.shared_deltas(self.boundary_stages(result,records),'baseline',expected)
        summary=json.loads((OUT/f'{name}.jsonl').read_text().splitlines()[-1])
        self.assertEqual(summary['unsupported_object_events'],0)
        self.assertEqual(summary['invalidated_observations'],0)

    def test_46_raw_adjacent_types_fd_commands_flags_and_wide_offsets(self):
        self.mutation_mode('raw_fd',{'wide_virtual_size':0,'wide_allocation':4096,'wide_write':8192,
            'raw_read':8192,'wide_vector':12288,'raw_append':16384,'invalid_close_keeps':16384,'closed':0})
        for mode in ('raw_dup2','raw_dup3'):
            self.mutation_mode(mode,{'two_objects':2097152,'replacement':1048576,'alias_only':1048576,'closed':0})
        for operation in ('range','samefd'):
            self.mutation_mode('raw_exec',{'before_exec':1048576,'after_exec':0},[operation])
        self.mutation_mode('raw_unshare',{'parent_retains':1048576,'closed':0})

    def test_47_path_truncate_shrink_growth_failure_and_other_object(self):
        self.mutation_mode('truncate',{'two_objects':1052672,'path_partial_shrink':12288,
            'path_grow_only':12288,'failed_path_keeps':12288,'other_only':4096,'closed':0})

    def test_48_fallocate_real_modes_rounding_union_punch_and_truncate(self):
        self.mutation_mode('extents',{'unaligned':8192,'overlap':8192,'disjoint':12288,
            'punched_first':8192,'partial_kept':8192,'boundary_pages_kept':8192,'punched_second':4096,
            'plain_grows':8192,'keep_beyond':16384,'dup_retains':16384,
            'same_size_truncate':8192,'virtual_grow':8192,'closed':0})

    def test_49_keep_size_beyond_eof_reopen_and_path_same_size_truncate(self):
        self.mutation_mode('beyond',{'beyond_eof':8192,'read_eof':8192,'reopened_keeps':8192,
            'path_keeps':8192,'grow_below_preallocation':8192,'path_same_size_releases':0,
            'plain_inside_size':8192,'shrink_partial':4096,'path_virtual_grow':4096,'closed':0})

    def test_50_real_fallocate_errors_and_regular_file_negative(self):
        self.mutation_mode('errors',{'acquired':4096,'all_errors_keep':4096,'closed':0})
        self.mutation_mode('regular',{'ram_owned':4096,'regular_allocated':4096,
            'regular_truncated':4096,'regular_closed':4096,'closed':0})

    def test_51_preallocated_object_alias_union_and_fork_exec_retention(self):
        self.mutation_mode('aliases',{'allocated':1048576,'aliases_union':1048576,'fd_only':1048576,
            'punched':1044480,'reservation_keeps_hole':1044480,'reactivated':1048576,
            'unmapped_retains':1048576,'closed':0})
        self.mutation_mode('fork_exec',{'child_only':8192,'after_exec':8192,'exec_closed':0,'retired':0})

    def test_52_preallocation_and_hole_history_survive_real_deadline_rollback(self):
        _,tracer=build(OUT/'race-test',test_races=True);report=OUT/'mutation_cancel.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'mutation_probe'),'cancel'],
            env={**os.environ,'JAYACCT_TEST_DEADLINE_RETAINED':'1'},capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        rows=[json.loads(line) for line in report.read_text().splitlines()]
        self.shared_deltas(self.boundary_stages(result,[r for r in rows if r['type']=='snapshot']),
                           'baseline',{'before_cancel':8192,'after_cancel':8192,'closed':0})
        cancellation=[r for r in rows if r['type']=='cancellation'];self.assertEqual(len(cancellation),1)
        self.assertFalse(cancellation[0]['output_valid']);self.assertTrue(cancellation[0]['discarded_partial_scan'])
        RESULTS.append({'name':'fallocate_punch_history_deadline_rollback','status':0,'summary':rows[-1],
                        'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest(),'stdout':result.stdout.decode()})

    def progress_run(self,name,executable,args,mode='report'):
        spec=importlib.util.spec_from_file_location('progress_runner',ROOT/'tests/accounting/review_v4/run_probes.py')
        runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
        runner.P=OUT;runner.EXE=OUT/executable
        result=runner.run(name,args,observed=mode!='control',report=mode=='report',timeout=3,tracer=self.tracer)
        self.assertFalse(result['timed_out'],result)
        self.assertEqual(result['returncode'],0,result)
        if mode=='report':
            self.assertFalse(result['summary']['complete'])
            self.assertEqual(result['summary']['unsupported_object_events'],0)
        RESULTS.append({'name':name,'status':0,'stdout':result['stdout'],
                        **{k:result[k] for k in ('summary','report_sha256') if k in result}})
        return result

    def test_53_original_v5_regular_truncate_read_lease_peer_progress(self):
        for attempt in range(3):
            for mode in ('control','report','no-report'):
                result=self.progress_run(f'v5_lease_{attempt}_{mode}','lease_truncate',['@DIR@'],mode)
                self.assertIn('FACT lease_handler_result 0 errno 0',result['stdout'])
                self.assertIn('FACT completed 1',result['stdout'])

    def test_54_original_v5_fifo_proc_magic_intermediate_nofollow_and_controls(self):
        for attempt in range(3):
            for form,trunc in ((1,1),(2,1),(3,1),(0,1),(1,0),(4,1),(5,1),(6,1)):
                for mode in ('control','report','no-report'):
                    result=self.progress_run(f'v5_fifo_{attempt}_{form}_{trunc}_{mode}','fifo_variant',
                                             ['fifo','@DIR@',form,trunc],mode)
                    self.assertIn('FACT completed 1',result['stdout'])

    def test_55_nofollow_final_symlink_fails_without_truncating_memfd_or_waiting_fifo(self):
        for mode in ('control','report'):
            result=self.progress_run(f'progress_final_link_{mode}','progress_probe',['final_link','@DIR@'],mode)
            if mode=='report':self.shared_deltas(result['stages'],'baseline',
                {'owned':8192,'failed_keeps':8192,'path_keeps':8192,'closed':0})

    def test_56_thread_self_nofollow_fifo_uses_real_distinct_tid(self):
        for attempt in range(3):
            for mode in ('control','report','no-report'):
                result=self.progress_run(f'progress_thread_fifo_{attempt}_{mode}','progress_probe',
                                         ['thread_fifo','@DIR@'],mode)
                self.assertIn('FACT completed 1',result['stdout'])

    def test_57_truncate_known_memfd_and_mapped_regular_stay_exclusive(self):
        result=self.progress_run('progress_targets','progress_probe',['targets','@DIR@'])
        stages=result['stages'];self.shared_deltas(stages,'baseline',{
            'before_ordinary':0,'after_ordinary':0,'before_mapped':4096,'after_mapped':4096,
            'before_private':0,'after_private':0,
            'after_adapted':-8192,'closed':-8192})
        rows=[json.loads(s) for s in (Path(result['directory'])/'trace.jsonl').read_text().splitlines()]
        for begin,end,exclusive in [('before_ordinary','after_ordinary',False),
                                     ('before_mapped','after_mapped',True),
                                     ('before_private','after_private',True),
                                     ('before_adapted','after_adapted',True)]:
            entries=[r for r in rows if r['type']=='snapshot' and r['syscall']==76
                     and int(stages[begin]['sequence'])<int(r['sequence'])<int(stages[end]['sequence'])]
            self.assertEqual(bool(entries),exclusive)

    def test_58_successful_nonserial_truncate_is_recovered_before_exit(self):
        _,tracer=build(OUT/'race-test',test_races=True);report=OUT/'progress_truncate_exit.jsonl'
        with tempfile.TemporaryDirectory(prefix='truncate-exit-',dir=OUT) as directory:
            result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'progress_probe'),
                'truncate_exit',directory],env={**os.environ,'JAYACCT_TEST_KILL_TRUNCATE_EXIT':'1'},
                capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
        rows=[json.loads(line) for line in report.read_text().splitlines()]
        self.shared_deltas(self.review_v4_stages(result,[r for r in rows if r['type']=='snapshot']),
                           'baseline',{'parent_retains':0,'closed':-8192})
        self.assertEqual(rows[-1]['recovered_syscall_results'],1)
        self.assertEqual(rows[-1]['unsupported_object_events'],0)
        self.assertFalse(rows[-1]['complete'])
        RESULTS.append({'name':'nonserial_truncate_real_SIGKILL_result_recovered_at_EXIT',
                        'status':0,'summary':rows[-1],'stdout':result.stdout.decode(),
                        'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_59_memfd_read_lease_real_kernel_control_without_observer_progress_claim(self):
        result=self.progress_run('progress_adapted_lease_control','progress_probe',['adapted_lease'],'control')
        self.assertIn('FACT adapted_read_lease_installed 1',result['stdout'])
        self.assertIn('FACT completed 1',result['stdout'])

    def test_60_truncating_opens_share_nonadapted_lease_progress_classification(self):
        for operation in range(4):
            for mode in ('control','report','no-report'):
                result=self.progress_run(f'progress_open_lease_{operation}_{mode}','progress_probe',
                                         [f'regular_lease{operation}','@DIR@'],mode)
                self.assertIn('FACT completed 1',result['stdout'])

    def test_61_additive_service_window_starts_at_first_observer_baseline_before_main(self):
        from tools.accounting.run import run
        for enabled in (False,True):
            name=f'startup_window_{enabled}';report=OUT/(name+'.jsonl')
            result,rows=run([OUT/'startup_probe','service' if enabled else 'default'],report,
                            output=OUT,service_window=enabled,timeout=5)
            self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
            snapshots={int(x['sequence']):x for x in rows if x['type']=='snapshot'}
            for sample in snapshots.values():
                self.assertTrue(sample['flags']&INCOMPLETE)
                self.assertEqual(int(sample['current']),sum(int(sample[k]) for k in
                    ('traced_private_bytes','traced_shared_bytes','fd_payload_bytes','observer_bytes')))
            opening=[x for x in rows if x['type']=='service_window_begin']
            self.assertEqual(len(opening),int(enabled))
            if enabled:
                baseline=snapshots[1];begin=opening[0]
                self.assertEqual(baseline['phase'],'observer_counter_ready')
                self.assertEqual(begin['begin_sequence'],'1');self.assertEqual(begin['scope_id'],'1')
                self.assertEqual(begin['peak'],baseline['current'])
                self.assertEqual(begin['begin_time_ns'],baseline['time_ns'])
                self.assertEqual(begin['peak_time_ns'],baseline['time_ns'])
                self.assertEqual(begin['peak_flags'],baseline['flags'])
                self.assertEqual(rows[0],baseline);self.assertEqual(rows[1],begin)
                for phase in ('observer_environment_ready','observer_metadata_ready'):
                    self.assertGreater(int(next(x for x in snapshots.values() if x['phase']==phase)['sequence']),1)
            windows={s[1]:list(map(int,s[2:])) for l in result.stdout.decode().splitlines()
                     if (s:=l.split()) and s[0]=='WINDOW'}
            for key,value in windows.items():
                scope,state,begin,end,peak,seq,ns,flags,current=value
                if not scope:continue
                witness=snapshots[seq];self.assertEqual(int(witness['current']),peak)
                self.assertEqual(int(witness['time_ns']),ns);self.assertEqual(witness['flags'],flags)
                self.assertTrue(flags&INCOMPLETE);self.assertGreaterEqual(seq,begin)
                if end:self.assertLessEqual(seq,end)
            if enabled:self.assertEqual(windows['initial'][4:8],windows['closed'][4:8])
            self.assertFalse(rows[-1]['complete'])
            RESULTS.append({'name':name,'status':0,'summary':rows[-1],'stdout':result.stdout.decode(),
                            'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_62_service_window_adopted_by_python_and_helper_then_closed_by_host(self):
        from tools.accounting.run import run
        code='''import os,sys,subprocess,json,mmap
from tools.accounting.client import Library,Counter,INCOMPLETE
lib=Library(sys.argv[1]);fd=int(os.environ['JAYDB_ACCOUNTING_FD']);counter=Counter(lib,fd=fd)
initial=counter.window_read();assert initial.state==1 and initial.scope_id==1 and initial.begin_sequence==1
child="from tools.accounting.client import Library,Counter; import os,sys; c=Counter(Library(sys.argv[1]),fd=int(os.environ['JAYDB_ACCOUNTING_FD'])); w=c.window_read(); assert w.state==1 and w.scope_id==1 and w.begin_sequence==1; print('helper_scope',w.scope_id); c.close()"
p=subprocess.run([sys.executable,'-B','-c',child,sys.argv[1]],pass_fds=(fd,),capture_output=True,text=True)
assert p.returncode==0,p.stderr
live=lib.window_barrier().require_scope(initial.scope_id);closed=lib.window_end().require_scope(initial.scope_id)
assert closed.state==2 and closed.begin_sequence==1 and closed.peak_flags&INCOMPLETE
new=lib.window_begin();assert new.scope_id==2
assert lib.window_end().scope_id==2
print(json.dumps({'initial_scope':initial.scope_id,'initial_begin':initial.begin_sequence,'closed_end':closed.end_sequence,'closed_peak':closed.peak,'peak_sequence':closed.peak_sequence,'peak_ns':closed.peak_monotonic_ns,'helper':p.stdout.strip()}))
counter.close()
'''
        report=OUT/'startup_python.jsonl'
        result,rows=run([sys.executable,'-B','-c',code,OUT/'libjayacct.so'],report,
                        output=OUT,service_window=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
        fact=json.loads(result.stdout);self.assertEqual(fact['helper'],'helper_scope 1')
        witness=next(r for r in rows if r['type']=='snapshot' and int(r['sequence'])==fact['peak_sequence'])
        self.assertEqual(int(witness['current']),fact['closed_peak'])
        self.assertEqual(int(witness['time_ns']),fact['peak_ns']);self.assertFalse(rows[-1]['complete'])
        RESULTS.append({'name':'service_window_python_helper_adopt_existing_scope','status':0,
                        'summary':rows[-1],'stdout':result.stdout.decode(),
                        'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_63_service_window_explicit_cli_orders_no_report_and_unclosed_exit(self):
        for name,flags in (('no_report',['--service-window']),
                           ('first',['--service-window','--report',str(OUT/'startup_order_first.jsonl')]),
                           ('last',['--report',str(OUT/'startup_order_last.jsonl'),'--service-window'])):
            result=subprocess.run([str(self.tracer),*flags,'--',str(OUT/'startup_probe'),'unclosed'],
                                  capture_output=True,timeout=5)
            self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
            self.assertIn(b'WINDOW initial 1 1 1 0',result.stdout)
            self.assertIn(b'FACT completed 1',result.stdout)
            RESULTS.append({'name':'service_window_cli_order_'+name,'status':0,
                            'stdout':result.stdout.decode()})

    def test_64_python_launcher_cli_forwards_explicit_service_window(self):
        report=OUT/'startup_launcher_cli.jsonl'
        result=subprocess.run([sys.executable,'-B','-m','tools.accounting.run','--report',str(report),
            '--service-window','--',str(OUT/'startup_probe'),'service'],capture_output=True,timeout=10)
        self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
        rows=[json.loads(s) for s in report.read_text().splitlines()]
        self.assertEqual(rows[1]['type'],'service_window_begin');self.assertEqual(rows[1]['begin_sequence'],'1')
        self.assertIn(b'WINDOW request 2 2',result.stdout);self.assertFalse(rows[-1]['complete'])
        RESULTS.append({'name':'service_window_python_launcher_CLI','status':0,'summary':rows[-1],
                        'stdout':result.stdout.decode(),'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_65_original_private_file_owner_retention_and_controls_three_runs(self):
        for attempt in range(3):
            for mode in ('private','shared','keepfd','aliases','fork'):
                for run_mode in ('control','report'):
                    result=self.progress_run(f'v6_private_{attempt}_{mode}_{run_mode}','private_owner',[mode],run_mode)
                    self.assertIn('FACT original_bytes 42 43',result['stdout'])
                    if run_mode=='control':continue
                    s=result['stages'];expected={'owned':1048576,'closed':0}
                    if mode=='fork':expected.update(child_only_view=1048576,child_revoked_view=1048576)
                    else:
                        expected.update(revoked_view=1048576)
                        expected['fd_kept' if mode=='keepfd' else 'only_view']=1048576
                        if mode=='keepfd':expected['fd_only']=1048576
                        if mode=='aliases':expected['last_alias']=1048576
                    self.shared_deltas(s,'baseline',expected)
                    before='child_only_view' if mode=='fork' else 'fd_kept' if mode=='keepfd' else 'only_view'
                    after='child_revoked_view' if mode=='fork' else 'revoked_view'
                    self.assertEqual(int(s[after]['traced_private_bytes'])-int(s[before]['traced_private_bytes']),
                                     0 if mode=='shared' else 1048576)

    def test_66_original_anonymous_mmap_ignores_known_fd_and_minus_one_control(self):
        for attempt in range(3):
            for fd in ('memfd','minus1'):
                for mode in ('control','report'):
                    result=self.progress_run(f'v6_anon_{attempt}_{fd}_{mode}','anon_ignored_fd',[fd],mode)
                    self.assertIn('FACT anon_bytes 42 43 memfd_size 0',result['stdout'])
                    if mode=='report':self.shared_deltas(result['stages'],'baseline',
                        {'acquired':1048576,'revoked':1048576,'unmapped':0,'closed':0})

    def ownership_mode(self,mode,shared,private):
        result=self.progress_run('ownership_'+mode,'ownership_probe',[mode]);s=result['stages']
        self.shared_deltas(s,'baseline',shared)
        for name,delta in private.items():
            self.assertEqual(int(s[name]['traced_private_bytes'])-int(s['baseline']['traced_private_bytes']),delta,name)
        return result

    def test_67_private_cow_alias_capacities_are_separate_from_file_retention(self):
        self.ownership_mode('cow',{'private_views_only':8192,'cow_a':8192,'a_revoked':8192,
            'original_b':8192,'a_replaced':8192,'last_file_view_gone':0,'closed':0},
            {'private_views_only':0,'cow_a':4096,'a_revoked':4096,'original_b':8192,
             'a_replaced':4096,'last_file_view_gone':0,'closed':0})

    def test_68_private_file_reference_survives_high_offset_move_and_last_partial_view(self):
        self.ownership_mode('remap',{'private_view':8192,'moved':8192,'activated_edges':8192,
            'revoked_edges':8192,'first_slice_gone':8192,'last_unactivated_slice':8192,'closed':0},
            {'private_view':0,'moved':0,'activated_edges':8192,'revoked_edges':8192,
             'first_slice_gone':4096,'last_unactivated_slice':0,'closed':0})

    def test_69_anonymous_identity_ignores_raw_fd_and_offset_without_retaining_file(self):
        self.ownership_mode('anonymous',{'two_anonymous_objects':8192,'ignored_fd_closed':8192,
            'one_anonymous_object':4096,'anonymous_gone':0,'invalid_fd_ignored':4096,
            'private_anonymous_and_fd':4096,'private_does_not_retain_fd':0,'closed':0},
            {'two_anonymous_objects':0,'invalid_fd_ignored':0,'private_anonymous_and_fd':4096,
             'private_does_not_retain_fd':4096,'closed':0})

    def test_70_exec_releases_last_private_file_reference_in_other_mm(self):
        self.ownership_mode('exec',{'child_view_only':8192,'after_exec':0,'closed':0},{})

    def test_71_private_file_reference_history_survives_real_deadline_rollback(self):
        _,tracer=build(OUT/'race-test',test_races=True);report=OUT/'ownership_cancel.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',str(OUT/'ownership_probe'),'cancel'],
            env={**os.environ,'JAYACCT_TEST_DEADLINE_RETAINED':'1'},capture_output=True,timeout=5)
        self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
        rows=[json.loads(s) for s in report.read_text().splitlines()]
        self.shared_deltas(self.review_v4_stages(result,[r for r in rows if r['type']=='snapshot']),
            'baseline',{'only_private_view':8192,'after_cancel':8192,'activated_after_cancel':8192,
                        'file_view_gone':0,'closed':0})
        cancellation=[x for x in rows if x['type']=='cancellation'];self.assertEqual(len(cancellation),1)
        self.assertTrue(cancellation[0]['discarded_partial_scan']);self.assertFalse(cancellation[0]['output_valid'])
        self.assertFalse(rows[-1]['complete']);self.assertEqual(rows[-1]['unsupported_object_events'],0)
        RESULTS.append({'name':'private_file_reference_deadline_rollback','status':0,'summary':rows[-1],
                        'stdout':result.stdout.decode(),'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_72_original_extra_startup_window_cancel_hold_fork_and_new_scope(self):
        for attempt in range(3):
            for report_enabled in (False,True):
                report=OUT/f'v6_window_extra_{attempt}.jsonl'
                command=[str(self.tracer),*(['--report',str(report)] if report_enabled else []),
                         '--service-window','--',str(OUT/'window_extra')]
                result=subprocess.run(command,capture_output=True,timeout=5)
                self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
                record={'name':f'v6_window_extra_{attempt}_{report_enabled}','status':0,'stdout':result.stdout.decode()}
                if report_enabled:
                    rows=[json.loads(s) for s in report.read_text().splitlines()]
                    self.assertEqual(rows[1]['type'],'service_window_begin');self.assertFalse(rows[-1]['complete'])
                    snaps={int(r['sequence']):r for r in rows if r['type']=='snapshot'}
                    for line in result.stdout.decode().splitlines():
                        p=line.split()
                        if not p or p[0]!='WINDOW':continue
                        witness=snaps[int(p[7])]
                        self.assertEqual(witness['current'],p[6]);self.assertEqual(witness['time_ns'],p[8])
                        self.assertEqual(witness['flags'],int(p[9]));self.assertTrue(int(p[9])&INCOMPLETE)
                    record.update(summary=rows[-1],report_sha256=hashlib.sha256(report.read_bytes()).hexdigest())
                RESULTS.append(record)

    def test_73_original_parent_sigkill_reconciles_last_private_file_owner(self):
        for attempt in range(24):
            for mode in ('report','no-report'):
                result=self.progress_run(f'v7_kill_{attempt}_{mode}','lifecycle',['kill'],mode)
                self.assertIn('FACT child_cow99_parent42 1',result['stdout'])
                if mode=='report':self.shared_deltas(result['stages'],'baseline',{
                    'owner_before_fork':1048576,'fork_cow_distinct':1048576,'only_child_view':1048576,'closed':0})
        for attempt in range(3):
            self.progress_run(f'v7_kill_free_{attempt}','lifecycle',['kill'],'control')

    def test_74_original_failed_and_nonleader_exec_lifecycle_control(self):
        for attempt in range(3):
            for mode in ('control','report','no-report'):
                result=self.progress_run(f'v7_exec_{attempt}_{mode}','lifecycle',['exec'],mode)
                if mode=='report':self.shared_deltas(result['stages'],'baseline',{
                    'owner_before_fork':1048576,'only_child_view':1048576,
                    'failed_exec_keeps_owner':1048576,'after_nonleader_exec':0,'closed':0})

    def test_75_real_sigkill_before_syscall_info_recovers_committed_result_at_exit(self):
        _,tracer=build(OUT/'race-test',test_races=True)
        cases=[('URING',[OUT/'uring_probe','dying_shared_files'],
                {'dying_owner_retained':28672,'dying_owner_released':0}),
               ('OPEN',[OUT/'boundary_probe','open_exit_death'],
                {'recovered_owner_only':1048576,'closed':0}),
               ('TRUNCATE',[OUT/'progress_probe','truncate_exit','@DIR@'],
                {'parent_retains':0,'closed':-8192})]
        for attempt in range(3):
            for kind,command,expected in cases:
                with tempfile.TemporaryDirectory(prefix='info-exit-',dir=OUT) as directory:
                    command=[directory if x=='@DIR@' else str(x) for x in command]
                    report=OUT/f'v8_info_exit_{kind}_{attempt}.jsonl'
                    result=subprocess.run([str(tracer),'--report',str(report),'--',*command],
                        env={**os.environ,f'JAYACCT_TEST_KILL_{kind}_INFO':'1'},capture_output=True,timeout=5)
                self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
                rows=[json.loads(s) for s in report.read_text().splitlines()]
                self.assertGreaterEqual(rows[-1]['unavailable_syscall_stops'],1)
                self.assertEqual(rows[-1]['recovered_syscall_results'],1)
                self.assertEqual(rows[-1]['unsupported_object_events'],0);self.assertFalse(rows[-1]['complete'])
                if kind=='URING':
                    s=self.boundary_stages(result,[r for r in rows if r['type']=='snapshot'])
                    for key,want in expected.items():self.assertEqual(int(s[key]['fd_payload_bytes']),want)
                else:self.shared_deltas(self.review_v4_stages(result,[r for r in rows if r['type']=='snapshot'])
                    if kind=='TRUNCATE' else self.boundary_stages(result,[r for r in rows if r['type']=='snapshot']),
                    'baseline',expected)
                RESULTS.append({'name':f'real_SIGKILL_before_GET_SYSCALL_INFO_{kind}_{attempt}','status':0,
                    'summary':rows[-1],'stdout':result.stdout.decode(),
                    'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()})

    def test_76_sigkill_or_exit_does_not_drop_other_private_file_owner(self):
        for attempt in range(3):
            for operation in ('retained_kill','retained_exit'):
                for mode in ('control','report','no-report'):
                    result=self.progress_run(f'availability_{operation}_{attempt}_{mode}',
                                             'availability_probe',[operation],mode)
                    if mode=='report':self.shared_deltas(result['stages'],'baseline',{
                        'only_children':1048576,'other_child_retains':1048576,'closed':0})

    def test_77_dead_hold_owner_preserves_parent_file_reference_and_initial_scope(self):
        for attempt in range(3):
            for enabled in (False,True):
                report=OUT/f'availability_hold_death_{attempt}.jsonl'
                result=subprocess.run([str(self.tracer),*(['--report',str(report)] if enabled else []),
                    '--service-window','--',str(OUT/'availability_probe'),'hold_death'],capture_output=True,timeout=5)
                self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
                record={'name':f'dead_hold_owner_{attempt}_{enabled}','status':0,'stdout':result.stdout.decode()}
                if enabled:
                    rows=[json.loads(s) for s in report.read_text().splitlines()]
                    self.shared_deltas(self.review_v4_stages(result,[r for r in rows if r['type']=='snapshot']),
                        'baseline',{'parent_view_retains':1048576,'closed':0})
                    self.assertEqual(rows[-1]['deadline_cancellations'],1);self.assertFalse(rows[-1]['complete'])
                    self.assertEqual(rows[1]['type'],'service_window_begin');self.assertEqual(rows[1]['begin_sequence'],'1')
                    record.update(summary=rows[-1],report_sha256=hashlib.sha256(report.read_bytes()).hexdigest())
                RESULTS.append(record)

    def test_78_marker_wrappers_clear_protocol_token_for_ordinary_getpid(self):
        for attempt in range(3):
            for mode in ('control','report','no-report'):
                result=self.progress_run(f'marker_cleanup_{attempt}_{mode}','marker_cleanup_probe',[],mode)
                self.assertIn('FACT unsupported_cleanup_checks 8' if mode=='control' else
                              'FACT marker_cleanup_checks 20',result['stdout'])

    def test_79_optimized_inline_marker_emission_has_final_register_cleanup(self):
        # Keep assembly and disassembly as evidence. Runtime test_78 checks
        # receipt/error paths and sequencing; here inspect all five effective
        # inline variants with two optimizer settings, including dynamic op.
        source=ROOT/'tests/accounting/marker_cleanup_probe.c'
        for level in ('-O2','-O3'):
            assembly=OUT/f'marker_cleanup_{level[1:]}.s'
            command=['/usr/bin/clang-19','-std=c11',level,'-fno-builtin','-Wall','-Wextra','-Werror',
                     '-I',str(ROOT/'native/accounting'),'-S',str(source),'-o',str(assembly)]
            subprocess.run(command,check=True)
            body=assembly.read_text();checked=[]
            for name in ('barrier','window','release','until','dynamic'):
                function='emission_'+name
                match=re.search(r'^'+function+r':.*?^\s*\.size\s+'+function+r',',body,re.M|re.S)
                self.assertIsNotNone(match,function);text=match.group(0)
                self.assertEqual(len(re.findall(r'^\s*syscall\b',text,re.M)),1,function)
                self.assertNotRegex(text,r'\bcallq?\b')
                returns=list(re.finditer(r'^\s*retq?\b',text,re.M));self.assertTrue(returns,function)
                # Each emitted return follows a final asm block that clears
                # RDI after receipt/error validation. This validates
                # emitted operands, not an assumption about C source order.
                for ret in returns:
                    prefix=text[:ret.start()];tail=prefix[prefix.rfind('#APP'):]
                    self.assertRegex(tail,r'xor[lq]?\s+%edi,\s*%edi')
                    self.assertNotRegex(tail.split('#NO_APP',1)[-1],r'\b(?:mov|lea|pop)\w*[^\n]*,\s*%[er]di\b')
                checked.append(function)
            RESULTS.append({'name':'effective_inline_marker_assembly_'+level,'status':0,
                            'command':command,'assembly_sha256':hashlib.sha256(assembly.read_bytes()).hexdigest(),
                            'functions':checked,'no_calls':True,'final_rdi_cleanup':True})

    def metadata_observer(self):
        if hasattr(self.__class__,'metadata_tracer'):return self.metadata_tracer
        target=OUT/'metadata-diagnostic';header=ROOT/'tests/accounting/metadata_diagnostic.h'
        command=['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-pthread',
            '-Wl,-z,now','-static','-DJAYACCT_TEST_RACES','-include',str(header),
            str(ROOT/'native/accounting/counter.c'),str(ROOT/'native/accounting/trace.c'),'-o',str(target)]
        subprocess.run(command,check=True)
        (OUT/'METADATA_BUILD.json').write_text(json.dumps({'command':command,
            'production':False,'headerSha256':hashlib.sha256(header.read_bytes()).hexdigest(),
            'accountingSources':json.loads((OUT/'BUILD.json').read_text())['sources'],
            'artifactSha256':hashlib.sha256(target.read_bytes()).hexdigest()},indent=2)+'\n')
        self.__class__.metadata_tracer=target;return target

    def metadata_run(self,name,fixture,args,*,hook=None,skip=0,env=None,report=True,success=True):
        tracer=self.metadata_observer() if hook else self.tracer;path=OUT/(name+'.jsonl')
        command=[str(tracer),*(['--report',str(path)] if report else []),'--',str(OUT/fixture),*map(str,args)]
        environment={**os.environ,**(env or {})}
        if hook:environment.update(JAYACCT_DIAG_METADATA=hook,JAYACCT_DIAG_SKIP=str(skip))
        p=subprocess.run(command,env=environment,capture_output=True,timeout=6)
        self.assertEqual(p.returncode,0 if success else 125,p.stderr.decode()+p.stdout.decode())
        row={'name':name,'status':p.returncode,'expected_instrument_failure':not success,
             'command':command,'diagnostic_only':bool(hook),'stdout':p.stdout.decode(),'stderr':p.stderr.decode()}
        rows=[json.loads(s) for s in path.read_text().splitlines()] if report else []
        if rows:
            row['report_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
            if success:self.assertFalse(rows[-1]['complete']);row['summary']=rows[-1]
            else:self.assertNotEqual(rows[-1]['type'],'summary')
        if hook and hook!='flags':self.assertIn('errno 3',p.stderr.decode())
        RESULTS.append(row);return p,rows

    def test_80_creation_identity_recovers_from_real_missing_event_message(self):
        modes=[('fork',0,0)]+[(k,v,f) for k in ('clone','clone3') for v in (0,1) for f in (0,1)]+[
            (k,1,f) for k in ('vfork','clone3vfork') for f in (0,1)]
        for attempt in range(3):
            for kind,vm,files in modes:
                for report in (True,False):
                    p,rows=self.metadata_run(f'creation_{kind}_{vm}_{files}_{attempt}_{report}',
                        'metadata_probe',[kind,vm,files],hook='clone',skip=1,report=report)
                    self.assertIn(b'FACT creation_actual_pid_base42_cow99 1',p.stdout)
                    if report:
                        self.shared_deltas(self.review_v4_stages(p,[r for r in rows if r['type']=='snapshot']),
                            'baseline',{'last_descendant':1048576,'closed':0})
                        self.assertEqual(rows[-1]['recovered_event_metadata'],1)
                        self.assertEqual(rows[-1]['unsupported_object_events'],0)

    def test_81_exec_leader_and_nonleader_use_actual_resumed_transaction(self):
        for attempt in range(3):
            for nonleader in (0,1):
                for report in (True,False):
                    p,rows=self.metadata_run(f'exec_metadata_{nonleader}_{attempt}_{report}',
                        'metadata_probe',['exec',nonleader,0],hook='exec',skip=1,report=report)
                    self.assertIn(b'FACT exec_wait_status 9',p.stdout)
                    if report:
                        self.assertEqual(rows[-1]['recovered_event_metadata'],1)
                        self.shared_deltas(self.review_v4_stages(p,[r for r in rows if r['type']=='snapshot']),
                            'baseline',{'owned':1048576,'parent_retains':1048576,'closed':0})

    def test_82_clone_flags_prepared_before_execution_and_real_invalid_inputs(self):
        for kind,vm,files in [('fork',0,0),('clone',1,1),('clone3',0,1),('vfork',1,0),('clone3vfork',1,1)]:
            for mode in ('control','report','no-report'):
                self.progress_run(f'creation_normal_{kind}_{mode}','metadata_probe',[kind,vm,files],mode)
        for attempt in range(3):
            self.metadata_run(f'clone3_real_invalid_{attempt}','metadata_probe',['invalid',0,0])
        # The old post-creation PEEK seam must no longer be visited: flags
        # come from the stopped pre-execution input, not a late dereference.
        p,rows=self.metadata_run('clone3_no_late_flags','metadata_probe',['clone3',0,0],hook='flags')
        self.assertNotIn(b'DIAGNOSTIC',p.stderr);self.assertEqual(rows[-1]['recovered_event_metadata'],0)

    def test_83_real_descriptor_read_survives_fatal_pending_ptrace_freeze(self):
        for attempt in range(3):
            for vm in (0,1):
                for files in (0,1):
                    p,rows=self.metadata_run(f'descriptor_proc_{vm}_{files}_{attempt}',
                        'committed_matrix',[vm,files,0,0,0,'run'],hook='descriptor')
                    self.assertGreaterEqual(rows[-1]['proc_memory_reads'],1)
                    s=self.review_v4_stages(p,[r for r in rows if r['type']=='snapshot'])
                    self.assertEqual(int(s['after_death']['fd_payload_bytes']),28672 if files else 0)
                    self.assertEqual(int(s['closed']['fd_payload_bytes']),0)

    def test_84_cached_real_return_and_alternate_owner_after_exit_mm_files(self):
        for attempt in range(3):
            for op,vm in [(0,1),(1,0),(2,0)]:
                kind=('URING','OPEN','TRUNCATE')[op]
                p,rows=self.metadata_run(f'cached_return_{kind}_{attempt}',
                    'committed_matrix',[vm,1,op,0,0,'run'],hook='regs_release',
                    env={f'JAYACCT_TEST_KILL_{kind}_EXIT':'1'})
                self.assertEqual(rows[-1]['recovered_syscall_results'],1)
                self.assertTrue(any(r.get('event')=='exit_cached_result' for r in rows))
                s=self.review_v4_stages(p,[r for r in rows if r['type']=='snapshot'])
                if op==0:self.assertEqual(int(s['after_death']['fd_payload_bytes']),28672)
                else:
                    self.shared_deltas(s,'baseline',{'after_death':0 if op==2 else 1048576,
                        'original_closed':0 if op==2 else 1048576,'closed':0})
                    if op==1:self.assertGreaterEqual(rows[-1]['alternate_fd_reads'],2)

    def test_85_irretrievable_result_or_descriptor_never_publishes_partial_observation(self):
        for kind,hook in [('unknown_return','INFO'),('lost_descriptor','EXIT')]:
            _,rows=self.metadata_run('metadata_open_gap_'+kind,'committed_matrix',[0,1,0,0,0,'run'],
                hook='regs_release',env={f'JAYACCT_TEST_KILL_URING_{hook}':'1'},success=False)
            self.assertTrue(all(r['flags']&INCOMPLETE for r in rows if r['type']=='snapshot'))
            if kind=='unknown_return':
                index=next(i for i,r in enumerate(rows) if r.get('event')=='exit_result_unavailable')
                self.assertFalse(any(r['type']=='snapshot' for r in rows[index:]))

    def test_86_frozen_service3_C_spawn_lifecycle_and_nodelete_baseline(self):
        source=ROOT/'tests/accounting/profile_service3';library=OUT/'profile_lifecycle.so';probe=OUT/'profile_spawn_probe'
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-fPIC','-shared',
            '-Wl,-z,nodelete','-DJAYDB_LIFECYCLE_BUILD_ID="accounting-v9-local-profile-probe"',
            str(source/'lifecycle.c'),'-o',str(library)],check=True)
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-pthread',
            '-I',str(ROOT/'native/accounting'),str(ROOT/'tests/accounting/profile_spawn_probe.c'),
            str(ROOT/'native/accounting/counter.c'),'-ldl','-o',str(probe)],check=True)
        for attempt in range(3):
            for bad in (0,1):
                for enabled in (False,True):
                    report=OUT/f'profile_spawn_{attempt}_{bad}_{enabled}.jsonl'
                    p=subprocess.run([str(self.tracer),*(['--report',str(report)] if enabled else []),
                        '--service-window','--',str(probe),str(library),str(bad)],capture_output=True,timeout=6)
                    self.assertEqual(p.returncode,0,p.stderr.decode()+p.stdout.decode())
                    self.assertIn(b'FACT source_service3_spawn_setsid_closefrom_WNOWAIT_kill_reap_NODELETE 1',p.stdout)
                    row={'name':f'source_service3_profile_{attempt}_{bad}_{enabled}','status':0,'stdout':p.stdout.decode(),
                         'scope':'literal C source subset only; service3 integrated profile not ratified'}
                    if enabled:
                        rows=[json.loads(s) for s in report.read_text().splitlines()]
                        self.assertFalse(rows[-1]['complete']);self.assertEqual(rows[-1]['unsupported_object_events'],0)
                        self.assertEqual(rows[1]['type'],'service_window_begin');self.assertEqual(rows[1]['begin_sequence'],'1')
                        row.update(summary=rows[-1],report_sha256=hashlib.sha256(report.read_bytes()).hexdigest())
                    RESULTS.append(row)


if __name__ == '__main__':
    original = json.loads((ROOT/'contrato-original.sha256.json').read_text())
    before = {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in original}
    inputs = [p for folder in ('native/accounting','tools/accounting','tests/accounting')
              for p in (ROOT/folder).rglob('*') if p.is_file()
              and p.suffix in ('.c','.h','.py','.mjs')
              and not any(part.startswith('.') or part=='__pycache__' for part in p.relative_to(ROOT).parts)]
    source_before = {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    started = time.monotonic_ns()
    test_run = unittest.main(exit=False)
    after = {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in original}
    assert before == after == original, 'Original contract changed'
    source_after = {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    assert source_before == source_after, 'Accounting sources changed during tests'
    (ROOT/'tests/accounting/RESULTS.json').write_text(json.dumps({
        'complete_service_measurement': False,
        'successful': test_run.result.wasSuccessful(),
        'contract_originals_unchanged': True,
        'suite_methods': test_run.result.testsRun,
        'elapsed_ns': str(time.monotonic_ns()-started),
        'sources_unchanged_during_tests': True,
        'source_sha256': source_before,
        'tests': RESULTS,
        'build': json.loads((OUT/'BUILD.json').read_text()),
        'machine': {'kernel': os.uname().release, 'uid': os.getuid(),
                    'node': subprocess.check_output(['node','--version'], text=True).strip()},
    }, indent=2) + '\n')
    raise SystemExit(0 if test_run.result.wasSuccessful() else 1)
