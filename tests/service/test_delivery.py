"""Real signal/pipe delivery tests. No allocation-coverage fixture is used."""
from __future__ import annotations

import array
import fcntl
import os
from pathlib import Path
import select
import signal
import tempfile
import termios
import time
import unittest
from unittest.mock import patch

from tools.service.controller import deliver,exact_read


class DeliveryTests(unittest.TestCase):
    def exchange(self, raises):
        """Interrupt an actual blocked write after the pipe acquired a prefix.

        The consumer is a separate process. It observes FIONREAD without
        consuming, sends SIGALRM only once the pipe is full, then waits for the
        producer's exception acknowledgement or a short harness-only timeout.
        This is a transport fixture, not a service deadline or memory measure.
        """
        with tempfile.TemporaryDirectory(prefix='jaydb-delivery-signal-') as temp:
            received_path=Path(temp)/'received.bin'
            r,w=os.pipe()
            ack_r,ack_w=os.pipe()
            capacity=fcntl.fcntl(w,fcntl.F_GETPIPE_SZ)
            data=bytes(range(251))*max(8192,capacity//251*4+1)
            parent=os.getpid()
            def handler(*_):
                if raises:
                    raise InterruptedError('signal after the kernel accepted a prefix')
            previous=signal.signal(signal.SIGALRM,handler)
            child=None
            try:
                child=os.fork()
                if child==0:
                    try:
                        os.close(w);os.close(ack_w)
                        deadline=time.monotonic()+5
                        while True:
                            available=array.array('i',[0])
                            fcntl.ioctl(r,termios.FIONREAD,available,True)
                            if available[0]>=capacity:
                                break
                            if time.monotonic()>=deadline:
                                os._exit(2)
                            time.sleep(.001)
                        os.kill(parent,signal.SIGALRM)
                        # The exception case acknowledges before any drain.
                        # The returning-handler control completes after drain.
                        select.select([ack_r],[],[],.1)
                        chunks=[]
                        while True:
                            chunk=os.read(r,65536)
                            if not chunk:break
                            chunks.append(chunk)
                        received_path.write_bytes(b''.join(chunks))
                        os._exit(0)
                    except BaseException:
                        os._exit(3)
                os.close(r);r=None
                os.close(ack_r);ack_r=None
                error=None
                try:
                    deliver(w,data)
                except BaseException as caught:
                    error=caught
                finally:
                    os.write(ack_w,b'ack')
                    os.close(w);w=None
                    os.close(ack_w);ack_w=None
                status=None
                deadline=time.monotonic()+5
                while time.monotonic()<deadline:
                    pid,status=os.waitpid(child,os.WNOHANG)
                    if pid:
                        child=None
                        break
                    time.sleep(.001)
                self.assertIsNone(child,'Consumer did not terminate')
                self.assertEqual(status,0,'Consumer failed before observing delivery')
                return data,received_path.read_bytes(),error,capacity
            finally:
                signal.signal(signal.SIGALRM,previous)
                for fd in (r,w,ack_r,ack_w):
                    if fd is not None:os.close(fd)
                if child:
                    os.kill(child,signal.SIGKILL)
                    os.waitpid(child,0)

    def test_raised_interruption_does_not_repeat_a_committed_prefix(self):
        data,received,error,capacity=self.exchange(True)
        self.assertIsInstance(error,InterruptedError)
        self.assertEqual(len(received),capacity)
        self.assertEqual(received,data[:capacity])

    def test_returning_signal_handler_allows_complete_exact_delivery(self):
        data,received,error,_=self.exchange(False)
        self.assertIsNone(error)
        self.assertEqual(received,data)

    def test_successive_reported_short_writes_advance_once(self):
        r,w=os.pipe()
        data=bytes(range(251))
        original=os.write
        def short(fd,view):
            return original(fd,view[:17])
        try:
            with patch('tools.service.controller.os.write',side_effect=short):
                deliver(w,data)
            os.close(w);w=None
            self.assertEqual(os.read(r,1000),data)
        finally:
            os.close(r)
            if w is not None:os.close(w)

    def test_legacy_read_does_not_repeat_after_a_raised_handler(self):
        r,w=os.pipe()
        os.write(w,b'abcDEF');os.close(w)
        original=os.read
        quantities=[]
        def after_read(fd,quantity):
            chunk=original(fd,quantity)
            quantities.append(len(chunk))
            signal.raise_signal(signal.SIGUSR1)
            return chunk
        previous=signal.signal(signal.SIGUSR1,
            lambda *_:(_ for _ in ()).throw(InterruptedError('after read committed')))
        try:
            with patch('tools.service.controller.os.read',side_effect=after_read):
                with self.assertRaises(InterruptedError):
                    exact_read(r,3)
            self.assertEqual(quantities,[3])
            self.assertEqual(os.read(r,3),b'DEF')
        finally:
            signal.signal(signal.SIGUSR1,previous)
            os.close(r)


if __name__=='__main__':unittest.main()
