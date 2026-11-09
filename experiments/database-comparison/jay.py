"""Real certified-program service adapter. No engine emulation or SQL translation."""
from __future__ import annotations
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
SUITE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from tools.client import prepared_frame, unframe

TOKEN = 'comparison-token'


def literal(s):
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\' else
                         f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in s) + '"'


def configuration(s):
    kinds = {'text': 'TextValue', 'integer': 'Integer', 'boolean': 'Boolean'}
    tables = []
    for t in sorted(s['tables'], key=lambda t: t['name']):
        cols = ', '.join(f'D.Column{{{literal(c["name"])}, D.{kinds[c["type"]]}{{}}, False{{}}}}'
                         for c in sorted(t['columns'], key=lambda c: c['name']))
        tables.append(f'D.SchemaTable{{{literal(t["name"])}, "id", [{cols}]}}')
    return '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[''' + ',\n    '.join(tables) + ''']}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
'''


def seed(s):
    tables = ', '.join(f'D.Table{{{literal(t["name"])}, []}}' for t in sorted(s['tables'], key=lambda t: t['name']))
    return '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[''' + tables + '''], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
'''


def proof(depth):
    return '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B
def B.certificate(ctx, args, s, valid, identity, n):
  L.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), S.environment(I.config()), s, ctx, B.code(), args)
def finite(ctx: D.Context, args: D.Value) ->
  T.Finite(''' + str(depth) + '''n, S.start(Client.program(), ctx, args)):
  ''' + ''.join(f'r{i} => ' for i in range(depth-1)) + '''Unit{}
def B.terminates(s, ctx, args):
  +context = ctx
  +arguments = args
  T.program_finite(''' + str(depth) + '''n, Client.program(), C.schema(), s, context, arguments,
    finite(context, arguments))
'''


class JayError(RuntimeError):
    def __init__(self, result):
        self.result = result
        super().__init__(str(result))


class Jay:
    def __init__(self, scenario, folder, binary, env):
        self.s, self.folder, self.binary, self.env = scenario, folder, binary, env
        self.handles = {}
        self.setup = {}
        folder.mkdir(parents=True, exist_ok=True)
        (folder/'Configuration.bend').write_text(configuration(scenario))
        (folder/'Seed.bend').write_text(seed(scenario))
        for name, depth in [('Access', 2), ('Batch', 3), ('ReadRow', 7)]:
            (folder/f'{name}.bend').write_bytes((SUITE/f'{name}.bend').read_bytes())
            (folder/f'{name}Proof.bend').write_text(proof(depth))
        try:
            self.start(False)
            self.prepare()
        except BaseException:
            if hasattr(self, 'process'):
                self.close()
            raise

    def start(self, reopen):
        argv = [str(self.binary), '--configuration', str(self.folder/'Configuration.bend'),
                '--threads', '1', '--storage', str(self.folder/'storage'),
                '--storage-mode', 'open' if reopen else 'create']
        if not reopen:
            argv += ['--seed', str(self.folder/'Seed.bend')]
        self.log = (self.folder/('reopen.log' if reopen else 'server.log')).open('wb')
        self.process = subprocess.Popen(argv, cwd=ROOT, env=self.env, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.log, start_new_session=True)
        start = time.perf_counter_ns()
        result = self.exchange(1, 'no-handle', credential='invalid')
        if result != {'status': 'authentication', 'value': None}:
            raise JayError(result)
        self.setup['reopen_ns' if reopen else 'startup_ns'] = time.perf_counter_ns() - start

    def read(self, size, deadline):
        result = bytearray()
        while len(result) < size:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                raise TimeoutError(f'JayDB2 response timeout; {self.log.name}')
            part = os.read(self.process.stdout.fileno(), size-len(result))
            if not part:
                raise RuntimeError(f'JayDB2 exited {self.process.poll()}; see {self.log.name}')
            result.extend(part)
        return bytes(result)

    def exchange(self, opcode, code, args=None, proof='', credential=TOKEN):
        packet = prepared_frame(opcode, code, credential, args, proof)
        self.process.stdin.write(packet)
        self.process.stdin.flush()
        deadline = time.monotonic() + 300
        header = self.read(8, deadline)
        size = int.from_bytes(header, 'big')
        if size > 262144:
            raise RuntimeError('Oversized service reply')
        return unframe(header + self.read(size, deadline))

    def prepare(self):
        for name in ('Access', 'Batch', 'ReadRow'):
            start = time.perf_counter_ns()
            result = self.exchange(0, (self.folder/f'{name}.bend').read_text(),
                                   proof=(self.folder/f'{name}Proof.bend').read_text())
            if result['status'] != 'prepared':
                raise JayError(result)
            self.handles[name] = result['value']
            self.setup[f'prepare_{name.lower()}_ns'] = time.perf_counter_ns()-start

    def execute(self, args, name='Access'):
        result = self.exchange(1, self.handles[name], args)
        if result['status'] != 'success':
            raise JayError(result)
        return result['value']

    def put(self, table, row):
        return self.execute(['put', table, row['id'], row])

    def get(self, table, key, column):
        return self.execute(['read', table, key, column])

    def keys(self, table):
        return self.execute(['keys', table])

    def update(self, table, key, column, value):
        return self.execute(['update', table, key, column, value])

    def delete(self, table, key):
        return self.execute(['delete', table, key])

    def batch(self, changes):
        assert len(changes) == 2
        return self.execute([list(c) for c in changes], 'Batch')

    def aggregate(self, table, column):
        return sum(self.get(table, k, column) for k in self.keys(table))

    def join(self, j):
        return [[k, self.get(j['to_table'], self.get(j['from_table'], k, j['fk']), j['column'])]
                for k in self.keys(j['from_table'])]

    def dump(self):
        result = {}
        for t in self.s['tables']:
            columns = [c['name'] for c in t['columns']]
            assert len(columns) <= 6
            padded = columns + [columns[0]] * (6-len(columns))
            result[t['name']] = [dict(zip(columns, self.execute([t['name'], k, *padded], 'ReadRow')))
                                  for k in self.keys(t['name'])]
        return result

    def reopen(self):
        self.close()
        self.start(True)
        self.prepare()

    def size_bytes(self):
        return sum(p.stat().st_size for p in (self.folder/'storage').rglob('*') if p.is_file())

    def close(self):
        try:
            if self.process.poll() is None:
                self.process.stdin.close()
                self.process.wait(timeout=20)
        finally:
            if self.process.poll() is None:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
            self.process.stdin.close()
            self.process.stdout.close()
            self.log.close()
