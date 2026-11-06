"""Real persistent Python/TypeScript task workflow; run under the heavy-work lock."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from applications.tasks.app import ROOT, database


class PersistentTaskWorkflowTests(unittest.TestCase):
    def ts(self, workspace, mode, command, *, credential='alice-token', status=0):
        result = subprocess.run(['node', str(ROOT/'applications/tasks/tasks.ts'),
            '--workspace', str(workspace), '--storage-mode', mode,
            '--credential', credential, '--command', *command], cwd=ROOT,
            capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, status, result.stderr + '\n' + result.stdout)
        return json.loads(result.stdout) if result.stdout else result

    def test_saved_tasks_survive_reopen_across_ts_and_python_clients(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-task-workflow-') as tmp:
            workspace = Path(tmp)/'personal'
            self.assertEqual(self.ts(workspace, 'create', ['save','review','Review polished docs']),
                             {'status':'success','value':'review'})
            configuration = (workspace/'app/Configuration.bend').read_bytes()
            (workspace/'app/Seed.bend').unlink()
            with tempfile.TemporaryFile() as errors:
                try:
                    with database(workspace=workspace, storage_mode='open', threads=1, stderr=errors) as db:
                        self.assertEqual(db.call('alice-token',['list']), {'status':'success','value':['review']})
                        self.assertEqual(db.call('alice-token',['conclude','review']), {'status':'success','value':'review'})
                        self.assertEqual(db.call('alice-token',['cancel','review','Discard this title',False]),
                                         {'status':'refusal','value':'cancelled'})
                        self.assertEqual(db.call('bob-token',['list']), {'status':'success','value':[]})
                        self.assertEqual(db.call('bob-token',['save','review','Bob separate task',False]),
                                         {'status':'success','value':'review'})
                        self.assertEqual(db.call('invalid-token',['list']), {'status':'authentication','value':None})
                except BaseException:
                    errors.seek(0)
                    print(errors.read().decode('utf-8','replace'))
                    raise
            self.assertEqual(self.ts(workspace, 'open', ['view','review']), {'status':'success','value':{
                'completed':True,'id':'review','owner':'alice','title':'Review polished docs'}})
            self.assertEqual(self.ts(workspace, 'open', ['view','review'], credential='bob-token'),
                             {'status':'success','value':{
                'completed':False,'id':'review','owner':'bob','title':'Bob separate task'}})
            self.assertEqual(self.ts(workspace, 'open', ['list'], credential='invalid-token', status=2),
                             {'status':'authentication','value':None})
            image = (workspace/'db/snapshot').read_bytes()
            refusal = self.ts(workspace, 'open', ['cancel','review','No publication'], status=2)
            self.assertEqual(refusal, {'status':'refusal','value':'cancelled'})
            self.assertEqual((workspace/'db/snapshot').read_bytes(), image)
            rejected = self.ts(workspace, 'create', ['list'], status=1)
            self.assertIn('EEXIST', rejected.stderr)
            self.assertEqual((workspace/'db/snapshot').read_bytes(), image)
            self.assertEqual((workspace/'app/Configuration.bend').read_bytes(), configuration)
            self.assertFalse((workspace/'app/Seed.bend').exists(), 'open must not copy or read the seed')


if __name__ == '__main__':
    unittest.main(verbosity=2)
