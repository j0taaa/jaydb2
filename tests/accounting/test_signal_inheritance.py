"""V11 launch inheritance: real processes; no complete memory/K claim."""
from pathlib import Path
import errno
import hashlib
import json
import os
import signal
import subprocess
import unittest
from tools.accounting.build import build

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(os.environ.get('JAYDB_SIGNAL_TEST_OUT', ROOT/'tests/accounting/.signal-build'))
RESULTS = []


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class SignalInheritanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.tracer = build(OUT/'standard')
        cls.fixture = OUT/'reviewer-independent'
        cls.launch = OUT/'signal-launch'
        cls.probe = OUT/'signal-probe'
        flags = ['/usr/bin/clang-19', '-std=c11', '-O2', '-g', '-Wall', '-Wextra', '-Werror']
        commands = [
            [*flags, '-I', str(ROOT/'native/accounting'),
             str(ROOT/'tests/accounting/review_v10/fixtures/independent.c'),
             str(ROOT/'native/accounting/counter.c'), str(ROOT/'native/accounting/stage_runtime.c'),
             '-o', str(cls.fixture)],
            [*flags, str(ROOT/'tests/accounting/signal_launch.c'), '-o', str(cls.launch)],
            [*flags, str(ROOT/'tests/accounting/signal_probe.c'), '-o', str(cls.probe)],
        ]
        for command in commands:
            subprocess.run(command, check=True)
        cls.diagnostic = OUT/'restore-failure-diagnostic'
        command = [*flags, '-pthread', '-static', '-include',
                   str(ROOT/'tests/accounting/signal_restore_diagnostic.h'),
                   str(ROOT/'native/accounting/counter.c'), str(ROOT/'native/accounting/trace.c'),
                   '-o', str(cls.diagnostic)]
        subprocess.run(command, check=True)
        commands.append(command)
        (OUT/'PROBE_BUILD.json').write_text(json.dumps({
            'commands': commands, 'artifacts': {p.name: sha(p) for p in
                (cls.fixture, cls.launch, cls.probe, cls.diagnostic)},
            'literalReviewerFixtureSha256': sha(ROOT/'tests/accounting/review_v10/fixtures/independent.c'),
            'diagnosticScope': 'separate ELF; real EFAULT only at child restore; production has no hook',
        }, indent=2)+'\n')

    def run_command(self, name, command, *, preexec_fn=None, expected_status=0):
        p = subprocess.run(command, capture_output=True, timeout=5, preexec_fn=preexec_fn)
        (OUT/(name+'.stdout')).write_bytes(p.stdout)
        (OUT/(name+'.stderr')).write_bytes(p.stderr)
        self.assertEqual(p.returncode, expected_status, p.stdout.decode()+p.stderr.decode())
        facts = [json.loads(x) for x in p.stdout.splitlines()]
        record = {'name': name, 'command': command, 'status': p.returncode, 'facts': facts,
                  'stdoutSha256': sha(OUT/(name+'.stdout')),
                  'stderrSha256': sha(OUT/(name+'.stderr'))}
        path = OUT/(name+'.jsonl')
        if path.exists():
            rows = [json.loads(x) for x in path.read_text().splitlines()]
            self.assertEqual(rows[-1]['type'], 'summary')
            self.assertFalse(rows[-1]['complete'])
            self.assertEqual(rows[-1]['root_status'], expected_status)
            self.assertFalse(any(x.get('event') == 'armed' for x in rows))
            record['reportSha256'] = sha(path)
        RESULTS.append(record)
        return facts, p

    def reviewer(self, name, *, stage, ignored, blocked, window, report):
        def setup():
            signal.signal(signal.SIGCHLD, signal.SIG_IGN if ignored else signal.SIG_DFL)
            signal.pthread_sigmask(signal.SIG_SETMASK,
                                  {signal.SIGCHLD, signal.SIGUSR1} if blocked else set())
        command = [str(self.tracer), *(['--stage-control'] if stage else []),
                   *(['--service-window'] if window else []),
                   *(['--report', str(OUT/(name+'.jsonl'))] if report else []),
                   '--', str(self.fixture), 'inherit']
        facts, _ = self.run_command(name, command, preexec_fn=setup)
        self.assertEqual(facts[0], {'sigchld_ignored': int(ignored),
            'sigchld_default': int(not ignored), 'chld_blocked': int(blocked),
            'usr1_blocked': int(blocked), 'stage_env': int(stage)})
        self.assertEqual(facts[1], {'wait_result': -1 if ignored else 1,
                                 'wait_errno': errno.ECHILD if ignored else 0})

    def test_01_literal_reviewer_fixture_disposition_and_masks(self):
        for stage in (False, True):
            for ignored in (False, True):
                for blocked in (False, True):
                    self.reviewer(f'literal-{stage}-{ignored}-{blocked}', stage=stage,
                                  ignored=ignored, blocked=blocked, window=True, report=True)

    def test_02_literal_three_pairs_without_window_or_report(self):
        for repeat in range(3):
            for stage in (False, True):
                self.reviewer(f'literal-no-window-{repeat}-{stage}', stage=stage,
                              ignored=True, blocked=False, window=False, report=False)

    def test_03_c_launcher_direct_default_passive_full_masks_and_exec_flags(self):
        for mode in (0, 1, 2):
            for mask in range(4):
                prefix = [str(self.launch), str(mode), str(mask)]
                expected, _ = self.run_command(f'launch-{mode}-{mask}-direct',
                                               [*prefix, str(self.probe), 'probe'])
                self.assertEqual(expected[0]['ignored'], int(mode == 1))
                self.assertEqual(expected[0]['default'], int(mode != 1))
                self.assertEqual(int(expected[0]['process_mask']),
                                 ((1 << (signal.SIGCHLD-1)) if mask & 1 else 0) |
                                 ((1 << (signal.SIGUSR1-1)) if mask & 2 else 0))
                self.assertEqual(expected[1]['wait_errno'], errno.ECHILD if mode == 1 else 0)
                for stage in (False, True):
                    name = f'launch-{mode}-{mask}-stage{stage}'
                    facts, _ = self.run_command(name, [*prefix, str(self.tracer),
                        *(['--stage-control'] if stage else []), '--service-window',
                        '--report', str(OUT/(name+'.jsonl')), '--', str(self.probe)])
                    self.assertEqual(facts, expected,
                        'exec-root must match direct Linux exec, including action flags and masks')

    def test_04_real_restore_failure_exits_before_exec_instead_of_default_fallback(self):
        name = 'real-restore-efault'
        facts, p = self.run_command(name, [str(self.launch), '1', '3',
            str(self.diagnostic), '--stage-control', '--service-window', '--report',
            str(OUT/(name+'.jsonl')), '--', str(self.probe)], expected_status=126)
        self.assertEqual(facts, [])
        self.assertIn(b'diagnostic child restore raw_result=-1 errno=14', p.stderr)

    def test_05_failed_exec_keeps_normal_exit_status(self):
        for stage in (False, True):
            name = f'failed-exec-stage{stage}'
            facts, _ = self.run_command(name, [str(self.launch), '1', '3', str(self.tracer),
                *(['--stage-control'] if stage else []), '--report', str(OUT/(name+'.jsonl')),
                '--', str(OUT/'does-not-exist')], expected_status=127)
            self.assertEqual(facts, [])


if __name__ == '__main__':
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(SignalInheritanceTests))
    (OUT/'RESULTS_SIGNAL.json').write_text(json.dumps({
        'successful': result.wasSuccessful(), 'methods': result.testsRun, 'records': RESULTS,
        'memoryStatus': 'INCOMPLETE', 'KProved': False,
    }, indent=2)+'\n')
    raise SystemExit(not result.wasSuccessful())
