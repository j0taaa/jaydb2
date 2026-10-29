"""Private channel composition; complete observations remain fixtures."""
from __future__ import annotations
from pathlib import Path
from types import SimpleNamespace
import os
import tempfile
import time
import unittest
from unittest.mock import patch

from tools.client import unframe
from tools.service.build_commit import build
from tools.service.channel import CountedChannel
from tools.service.frames import error_frame
from tools.service.receiving import FirstByte,ReceivedFrame,IncompleteReceiving
from tests.service import test_completion as completion_fixtures

ROOT=Path(__file__).resolve().parents[2]

class ChannelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-channel-tests-')
        cls.library=Path(cls.temp.name)/'commit-fixture.so'
        build(cls.library,test_fixture=ROOT/'tests/service/commit_fixture.c')
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()

    def scenario(self,*,status=None,peak=100):
        db,root,counter,_,compile_request,paths,events,response=completion_fixtures.CompletionTests.setup_request(self,peak=peak)
        db.limits['mensagem']=1000
        window=counter.window_read()
        now=time.monotonic_ns()
        start=FirstByte(0,now,now,now+10**9,window)
        frame=ReceivedFrame(start,bytes(8),b'body' if status is None else b'',status,status is not None)
        frames=[frame,None]
        receiver=SimpleNamespace(counter=counter,receive=lambda *args,**kwargs:frames.pop(0))
        channel=CountedChannel(db,root,counter,receiver,instrument_deadline_ns=10**30)
        return channel,db,root,compile_request,events,response

    def output(self):
        r,w=os.pipe()
        self.addCleanup(os.close,r);self.addCleanup(os.close,w)
        return r,w

    def test_success_delivers_only_after_c_completion_and_cleanup(self):
        channel,db,root,compile_request,events,response=self.scenario()
        r,w=self.output()
        with patch('tools.service.controller.build',side_effect=compile_request):
            self.assertTrue(channel.once(0,w))
        self.assertEqual(events,['decode','authenticate','build','execute','close'])
        self.assertEqual(os.read(r,len(response)),response)
        self.assertEqual(db.state,b'new state')
        self.assertTrue(channel.last_completion.completed)
        self.assertEqual(root.native.published,channel.last_completion.prepared.address)
        self.assertFalse(channel.ended)
        self.assertFalse(channel.once(0,w))
        self.assertTrue(channel.ended)

    def test_header_error_completes_without_running_or_publishing(self):
        for status in ('entrada','limite','falha'):
            with self.subTest(status=status):
                channel,db,root,compile_request,events,_=self.scenario(status=status)
                before=root.native.published
                r,w=self.output()
                self.assertFalse(channel.once(0,w))
                self.assertEqual(os.read(r,1000),error_frame(status))
                self.assertEqual(events,[])
                self.assertEqual(root.native.published,before)
                self.assertEqual(root.state,db.state)
                self.assertTrue(channel.last_completion.completed)
                with self.assertRaisesRegex(RuntimeError,'ended'):channel.once(0,w)

    def test_error_after_complete_frame_keeps_channel_without_publication(self):
        for status in ('limite','falha'):
            with self.subTest(status=status):
                channel,db,root,compile_request,events,_=self.scenario(status=status)
                old=channel.receiver.receive(0)
                frame=ReceivedFrame(old.start,(3).to_bytes(8,'big'),b'abc',status,False)
                remaining=[frame,None]
                channel.receiver.receive=lambda *a,**k:remaining.pop(0)
                before=root.native.published
                r,w=self.output()
                self.assertTrue(channel.once(0,w))
                self.assertEqual(os.read(r,1000),error_frame(status))
                self.assertEqual(events,[])
                self.assertEqual(root.native.published,before)
                self.assertFalse(channel.ended)
                self.assertFalse(channel.once(0,w))

    def test_complete_malformed_body_keeps_channel_synchronized(self):
        channel,db,root,compile_request,events,response=self.scenario()
        db.modules['decode'].run_accounted=lambda *args,**kwargs:b'\0'+error_frame('entrada')
        before=root.native.published
        r,w=self.output()
        self.assertTrue(channel.once(0,w))
        self.assertEqual(unframe(os.read(r,1000)),{'status':'entrada','valor':None})
        self.assertEqual(root.native.published,before)
        self.assertFalse(channel.once(0,w))

    def test_delivery_failure_cannot_undo_a_completed_publication(self):
        channel,db,root,compile_request,events,response=self.scenario()
        r,w=os.pipe();os.close(r);self.addCleanup(os.close,w)
        with patch('tools.service.controller.build',side_effect=compile_request):
            with self.assertRaises(BrokenPipeError):channel.once(0,w)
        self.assertTrue(channel.last_completion.completed)
        self.assertEqual(channel.last_completion.response,response)
        self.assertEqual(db.state,b'new state')
        self.assertEqual(root.native.published,channel.last_completion.prepared.address)
        self.assertTrue(channel.ended)

    def test_current_scope_excess_selects_limit_before_delivery(self):
        channel,db,root,compile_request,events,response=self.scenario(peak=101)
        before=root.native.published
        r,w=self.output()
        with patch('tools.service.controller.build',side_effect=compile_request):
            self.assertTrue(channel.once(0,w))
        self.assertEqual(os.read(r,1000),error_frame('limite'))
        self.assertEqual(root.native.published,before)
        self.assertEqual(db.state,b'published')

    def test_interrupted_delivery_keeps_completed_root_and_closes_channel(self):
        channel,db,root,compile_request,events,response=self.scenario()
        r,w=self.output()
        def interrupted(fd,frame):
            os.write(fd,frame[:17])
            raise InterruptedError('handler after a committed delivery prefix')
        with patch('tools.service.controller.build',side_effect=compile_request), \
                patch('tools.service.channel.deliver',side_effect=interrupted):
            with self.assertRaises(InterruptedError):channel.once(0,w)
        self.assertEqual(os.read(r,len(response)),response[:17])
        self.assertTrue(channel.last_completion.completed)
        self.assertEqual(channel.last_completion.response,response)
        self.assertEqual(db.state,b'new state')
        self.assertEqual(root.native.published,channel.last_completion.prepared.address)
        self.assertTrue(channel.ended)
        with self.assertRaisesRegex(RuntimeError,'ended'):channel.once(0,w)

    def test_instrument_refusal_does_not_prepare_a_public_response(self):
        channel,db,root,compile_request,events,response=self.scenario()
        channel.receiver.receive=lambda *a,**k:(_ for _ in ()).throw(IncompleteReceiving('coverage'))
        before=root.native.published
        with self.assertRaises(IncompleteReceiving):channel.once()
        self.assertEqual(root.native.published,before)
        self.assertFalse(root.native.completed)
        self.assertIsNone(channel.last_completion)
        self.assertTrue(channel.ended)

if __name__=='__main__':unittest.main()
