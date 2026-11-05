"""Same real checked applications through Rust reference and Bend controllers."""
import os
from unittest.mock import patch
import unittest
from pathlib import Path
from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof

class DifferentialTests(unittest.TestCase):
    def test_host_owned_runtime_options_ignore_environment(self):
        folder=ROOT/'examples/access'
        with patch.dict(os.environ, {'JAYDB2_TEST_HOST':str(ROOT/'jaydb2')}):
            host=Server(folder,threads=1,env=dict(os.environ,BENDRTS='--gpu-build'))
        self.addCleanup(host.close)
        self.assertEqual(host.call((folder/'Client.bend').read_text(),
                                  (folder/'ClientProof.bend').read_text(),
                                  'alice-token','alice-new'),
                         {'status':'success','value':'alice-new'},host.diagnostics())
        host.finish()

    def test_ordinary_prepared_fresh_auth_and_invalidation(self):
        folder=ROOT/'examples/access'
        code=(folder/'Client.bend').read_text()
        proof=(folder/'ClientProof.bend').read_text()
        hosts=[]
        for name in ('jaydb2-rust-reference','jaydb2'):
            with patch.dict(os.environ, {'JAYDB2_TEST_HOST':str(ROOT/name)}):
                host=Server(folder,threads=1)
            hosts.append(host);self.addCleanup(host.close)
        def compare(operation):
            results=[operation(host) for host in hosts]
            self.assertEqual(results[0],results[1], '\n'.join(h.diagnostics() for h in hosts))
            return results[0]
        self.assertEqual(compare(lambda h:h.call('not Bend','not proof','invalid'))['status'],'authentication')
        self.assertEqual(compare(lambda h:h.call('not Bend','not proof','alice-token'))['status'],'certificate')
        self.assertEqual(compare(lambda h:h.call(code,proof,'alice-token','alice-new')),
                         {'status':'success','value':'alice-new'})
        self.assertEqual(compare(lambda h:h.call(code,proof,'alice-token'))['status'],'authentication')
        self.assertEqual(compare(lambda h:h.call(code,proof,'alice-new'))['status'],'refusal')
        handles=[]
        for host in hosts:
            receipt=host.prepared(0,code,'alice-new',proof=universal_access_proof(proof))
            self.assertEqual(receipt['status'],'prepared',host.diagnostics());handles.append(receipt['value'])
        results=[host.prepared(1,key,'alice-new','alice-final') for host,key in zip(hosts,handles)]
        self.assertEqual(results,[{'status':'success','value':'alice-final'}]*2)
        results=[host.prepared(2,key,'alice-final') for host,key in zip(hosts,handles)]
        self.assertEqual(results,[{'status':'invalidated','value':None}]*2)
        results=[host.prepared(1,key,'alice-final') for host,key in zip(hosts,handles)]
        self.assertEqual(results,[{'status':'failure','value':None}]*2)
        self.assertEqual(compare(lambda h:h.call(code,proof,'alice-final'))['status'],'refusal')
        for host in hosts:host.finish()
