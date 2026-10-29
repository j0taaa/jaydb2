"""Host framing/publication tests; end-to-end native tests live separately."""
import os
from pathlib import Path
import sys
import threading
import time
import tempfile
import subprocess
import re
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.client import encode, decode, frame, unframe
from tools.service.controller import Database, CompileFailure, StageTimeout, error_frame, exact_read, helper, packet, split
from tools.service.naturals import decimal, parse_decimal
from tools.service.frames import ERROR_FRAMES
from tests.service.runtime_profile import fixture_lifecycle
from tools.service.lifecycle import ProcessOwner


class TransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lifecycle=fixture_lifecycle()
    def test_fragmented_header_and_eof(self):
        r, w = os.pipe()
        def writer():
            for b in b'abcdefgh':
                os.write(w, bytes([b]))
            os.close(w)
        t = threading.Thread(target=writer)
        t.start()
        try:
            self.assertEqual(exact_read(r, 8, time.monotonic_ns() + 10**9), (b'abcdefgh', True))
            self.assertEqual(exact_read(r, 8, time.monotonic_ns() + 10**9), (b'', False))
        finally:
            os.close(r)
            t.join()

    def test_stalled_header_hits_real_deadline(self):
        r, w = os.pipe()
        try:
            with self.assertRaises(StageTimeout):
                exact_read(r, 8, time.monotonic_ns() + 10**6)
        finally:
            os.close(r)
            os.close(w)

    def test_large_nat_deadline_allows_small_actual_io(self):
        r, w = os.pipe()
        try:
            os.write(w, b'actual bytes')
            self.assertEqual(exact_read(r, 12, time.monotonic_ns() + 10**500), (b'actual bytes', True))
        finally:
            os.close(r)
            os.close(w)
        self.assertEqual(helper([sys.executable, '-c', 'print("ready")'],
            time.monotonic_ns() + 10**500, 512 * 1024**2), b'ready\n')

    def test_exception_during_helper_monitoring_kills_and_reaps_child(self):
        children = []
        real_start=ProcessOwner.start
        def spawn(owner):
            result=real_start(owner)
            children.append(owner.pid)
            return result
        def interrupted():
            raise RuntimeError('monitor interrupted')
        window=SimpleNamespace(ceiling=512*1024**2,poll=interrupted)
        with patch.object(ProcessOwner,'start',spawn):
            with self.assertRaisesRegex(RuntimeError, 'monitor interrupted'):
                helper([sys.executable, '-c', 'import time; time.sleep(60)'],
                    time.monotonic_ns() + 10**10, 512 * 1024**2,memory_window=window)
        self.assertEqual(len(children), 1)
        self.assertFalse(Path('/proc', str(children[0])).exists())

    def test_helper_without_allocation_window_does_not_invent_a_memory_witness(self):
        self.assertEqual(helper([sys.executable,'-c','print("ready")'],
            time.monotonic_ns()+10**10,1),b'ready\n')

    def test_helper_checks_window_again_after_transient_helper_exit(self):
        calls=[]
        def poll():
            calls.append(True)
        window=SimpleNamespace(ceiling=512*1024**2,poll=poll)
        self.assertEqual(helper([sys.executable,'-c','print("ready")'],
            time.monotonic_ns()+10**10,window.ceiling,memory_window=window),b'ready\n')
        self.assertGreaterEqual(len(calls),2)

    def test_helper_exit_cleans_detached_stdio_descendant_before_reaping_leader(self):
        script = ('import os,subprocess,sys; '
            'p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"],'
            'stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); '
            'print(p.pid,flush=True); os._exit(int(sys.argv[1]))')
        leader_states=[]
        real_stop=ProcessOwner.stop_and_wait
        def stop_group(owner):
            # The leader remains a waitable zombie until all members have
            # received the kill. Its PID cannot be reused for another group.
            leader_states.append(Path('/proc',str(owner.pid),'stat').read_text().split(') ')[1][0])
            return real_stop(owner)
        for exit_code in (0,1):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as temp:
                pid_file=Path(temp)/'descendant'
                command=[sys.executable,'-c',
                    script.replace('print(p.pid,flush=True)',
                        'open(sys.argv[2],"w").write(str(p.pid)); print("ready",flush=True)'),
                    str(exit_code),str(pid_file)]
                with patch.object(ProcessOwner,'stop_and_wait',stop_group):
                    if exit_code:
                        with self.assertRaises(CompileFailure):
                            helper(command,time.monotonic_ns()+10**10,512*1024**2)
                    else:
                        self.assertEqual(helper(command,time.monotonic_ns()+10**10,
                            512*1024**2),b'ready\n')
                descendant=int(pid_file.read_text())
                until=time.monotonic()+1
                while time.monotonic()<until:
                    status=Path('/proc',str(descendant),'stat')
                    try:
                        state=status.read_text().split(') ')[1][0]
                    except FileNotFoundError:
                        break
                    if state=='Z':
                        break
                    time.sleep(.001)
                else:
                    os.kill(descendant,9)
                    self.fail('Helper descendant remained alive after leader exit')
        self.assertEqual(leader_states,['Z','Z'])

    def test_nat_configuration_has_no_decimal_digit_quota(self):
        quota = sys.get_int_max_str_digits()
        digits = '123456789' * 1200
        self.assertEqual(decimal(parse_decimal(digits)), digits)
        self.assertEqual(sys.get_int_max_str_digits(), quota)
        for invalid in ('', '-1', '1.0', '١'):
            with self.assertRaises(ValueError):
                parse_decimal(invalid)

    def test_error_frames_have_absent_value(self):
        for status in ('entrada', 'autenticacao', 'certificado', 'dados', 'limite', 'falha'):
            self.assertEqual(unframe(error_frame(status)), {'status': status, 'valor': None})

    def test_fixed_host_frames_are_the_exact_artifacts_in_the_bend_proof(self):
        proof=(Path(__file__).resolve().parents[2]/'proof/ErrosFixos.bend').read_text()
        body=proof.split('def bytes(e: Erro)',1)[1].split('\nlaw ',1)[0]
        constructors={'entrada':'Entrada','autenticacao':'Autenticacao','certificado':'Certificado',
                      'dados':'Dados','limite':'Limite','falha':'Falha'}
        for status,constructor in constructors.items():
            match=re.search(r'case '+constructor+r'\{\}:\s*\[([\d,\s]+)\]',body)
            self.assertIsNotNone(match)
            proved_bytes=bytes(int(x.strip()) for x in match.group(1).split(','))
            self.assertEqual(error_frame(status),proved_bytes)
            self.assertIs(error_frame(status),error_frame(status))
        self.assertEqual(set(ERROR_FRAMES),set(constructors))
        with self.assertRaises(TypeError):
            ERROR_FRAMES['limite']=b'changed'

    def test_private_packet_checks_extent(self):
        self.assertEqual(split(packet(b'\0\xff', b'body')), (b'\0\xff', b'body'))
        with self.assertRaises(RuntimeError):
            split((100).to_bytes(8, 'big') + b'truncated')

    def test_private_packet_allocation_failure_discards_the_request(self):
        db = Database.__new__(Database)
        db.state = b'published state'
        db.limits = {'enquadramento': 10**9}
        with patch('tools.service.controller.packet', side_effect=MemoryError('actual host allocation failed')):
            self.assertEqual(unframe(db.request(b'body')), {'status': 'falha', 'valor': None})
        self.assertEqual(db.state, b'published state')
        self.assertEqual(db.last_failure['code'], 'MemoryError')

    def test_expired_absolute_framing_deadline_is_not_replaced(self):
        db = Database.__new__(Database)
        db.state = b'published state'
        db.limits = {'enquadramento': 10**9}
        def preprocess(stage,data,deadline):
            self.assertEqual(deadline,0)
            raise StageTimeout('expired absolute deadline')
        db.preprocess=preprocess
        self.assertEqual(unframe(db.request(b'body',framing_deadline=0)), {'status':'limite','valor':None})
        self.assertEqual(db.state,b'published state')

    def test_dependency_cycle_is_a_certificate_refusal_with_rollback(self):
        db = Database.__new__(Database)
        db.state = b'published state'
        db.limits = dict.fromkeys(('enquadramento', 'autenticacao', 'verificacao'), 10**9)
        db.limits['memoria'] = 512 * 1024**2
        db.environment = db.toolchain = db.runtime = None
        metadata = packet(b'code', packet(b'proof', packet(b'instance', b'bindings')))
        db.preprocess = lambda stage, data, deadline: b'\1' + (metadata if stage == 'authenticate' else b'')
        with tempfile.TemporaryDirectory() as temp:
            db.directory = SimpleNamespace(name=temp)
            with patch('tools.service.controller.build', side_effect=CompileFailure({'code': 'IMPORT_CYCLE'})):
                self.assertEqual(unframe(db.request(b'body')), {'status': 'certificado', 'valor': None})
        self.assertEqual(db.state, b'published state')

    def test_exact_integer_and_unicode_boundaries(self):
        v = {'a': [None, False, True, -(2**63), 2**63-1, '\0\U0010ffff'], 'z': {}}
        self.assertEqual(unframe(frame(v)), v)
        for bad in (2**63, -(2**63)-1, {'a'*65: 1}, {'9x': 1}, '\ud800'):
            with self.assertRaises((ValueError, UnicodeError)):
                encode(bad)

    def test_real_verification_deadline_is_a_limit_with_rollback(self):
        db = Database.__new__(Database)
        db.state = b'published state'
        db.limits = dict.fromkeys(('enquadramento', 'autenticacao', 'verificacao'), 10**9)
        db.limits['memoria'] = 512 * 1024**2
        db.environment = db.toolchain = db.runtime = None
        metadata = packet(b'code', packet(b'proof', packet(b'instance', b'bindings')))
        db.preprocess = lambda stage, data, deadline: b'\1' + (metadata if stage == 'authenticate' else b'')
        with tempfile.TemporaryDirectory() as temp:
            db.directory = SimpleNamespace(name=temp)
            with patch('tools.service.controller.build', side_effect=CompileFailure({'code': 'HOST_VERIFICATION_DEADLINE'})):
                self.assertEqual(unframe(db.request(b'body')), {'status': 'limite', 'valor': None})
        self.assertEqual(db.state, b'published state')

    def test_nested_values_without_recursion_quota(self):
        value = None
        for _ in range(3000):
            value = [value]
        value = decode(encode(value))
        for _ in range(3000):
            self.assertEqual(len(value), 1)
            value = value[0]
        self.assertIsNone(value)


if __name__ == '__main__':
    unittest.main()
