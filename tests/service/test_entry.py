"""Selected loader profile and OS-stack preparation, without global changes."""
from pathlib import Path
import os
import resource
import signal
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.service.entry import EXTERNAL_LOADERS,prepare_entry


class EntryTests(unittest.TestCase):
    def test_selected_profile_removes_only_our_process_stack_capacity(self):
        with patch.dict('os.environ',{},clear=True),patch('tools.service.entry.resource.setrlimit') as limits:
            prepare_entry()
        self.assertEqual(limits.call_args_list[0].args,
            (resource.RLIMIT_STACK,(resource.RLIM_INFINITY,resource.RLIM_INFINITY)))
        self.assertEqual(limits.call_args_list[1].args,
            (resource.RLIMIT_CORE,(0,resource.getrlimit(resource.RLIMIT_CORE)[1])))

    def test_external_loader_is_rejected_before_start_without_disclosing_value(self):
        for name in EXTERNAL_LOADERS:
            with self.subTest(name=name),patch.dict('os.environ',{name:'private host value'},clear=True),patch('tools.service.entry.resource.setrlimit') as limits:
                with self.assertRaises(RuntimeError) as error:
                    prepare_entry()
                self.assertIn(name,str(error.exception))
                self.assertNotIn('private host value',str(error.exception))
                limits.assert_not_called()

    def test_empty_loader_options_are_supported(self):
        with patch.dict('os.environ',{name:'' for name in EXTERNAL_LOADERS},clear=True),patch('tools.service.entry.resource.setrlimit') as limits:
            prepare_entry()
        self.assertEqual(limits.call_count,2)

    def test_sigchld_auto_reaping_is_rejected_before_changes(self):
        with patch('tools.service.entry.signal.getsignal',return_value=signal.SIG_IGN), \
                patch('tools.service.entry.resource.setrlimit') as limits:
            with self.assertRaisesRegex(RuntimeError,'sole waiter'):
                prepare_entry()
            limits.assert_not_called()

    def test_non_main_thread_cannot_enter_the_selected_stack_mode(self):
        with patch('tools.service.entry.threading.get_native_id',return_value=os.getpid()+1),patch('tools.service.entry.resource.setrlimit') as limits:
            with self.assertRaisesRegex(RuntimeError,'main Linux thread'):
                prepare_entry()
            limits.assert_not_called()


if __name__=='__main__':
    unittest.main()
