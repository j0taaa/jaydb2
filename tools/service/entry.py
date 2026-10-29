"""Conditions of the selected local runtime entry, before any database starts.

This domain fixes the tools that are inventoried and compiled. It imposes no
condition on an admitted Bend program. Another host/tool-loader profile needs
its own environment identity and a checked compiler/runtime correspondence.
"""
import os
import platform
import resource
import signal
import sys
import threading

# These options can add loader modules, compiler plugins, headers or libraries
# outside the selected entry closure. Empty and absent have the same effect.
# Values are never included in errors (they may contain private host paths).
EXTERNAL_LOADERS = frozenset({
    'NODE_OPTIONS', 'NODE_PATH', 'LD_PRELOAD', 'LD_AUDIT', 'LD_LIBRARY_PATH',
    'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONINSPECT', 'PYTHONUSERBASE',
    'CCC_OVERRIDE_OPTIONS', 'CCC_ADD_ARGS', 'CLANG_CONFIG_FILE_SYSTEM_DIR',
    'CLANG_CONFIG_FILE_USER_DIR', 'COMPILER_PATH', 'LIBRARY_PATH', 'CPATH',
    'C_INCLUDE_PATH', 'CPLUS_INCLUDE_PATH',
})


def prepare_entry():
    if sys.platform!='linux' or platform.machine()!='x86_64' or os.sysconf('SC_PAGE_SIZE')!=4096:
        raise RuntimeError('The selected service entry requires Linux x86_64 and 4096-byte pages')
    if threading.get_native_id()!=os.getpid():
        raise RuntimeError('Database must run on the main Linux thread')
    if signal.getsignal(signal.SIGCHLD) is not signal.SIG_DFL:
        raise RuntimeError('The selected entry requires the sole waiter and default SIGCHLD disposition')
    added=sorted(name for name in EXTERNAL_LOADERS if os.environ.get(name))
    if added:
        raise RuntimeError('The selected entry does not include external tool loaders: '+', '.join(added))
    # Main-stack growth is an OS operation, not a private evaluator capacity.
    # This changes only this process and reserves no corresponding backing.
    resource.setrlimit(resource.RLIMIT_STACK,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))
    # This is the selected helper core-dump profile, not an allocation quota.
    # Preserve the hard limit for trusted compiler helpers.
    _, hard_core = resource.getrlimit(resource.RLIMIT_CORE)
    resource.setrlimit(resource.RLIMIT_CORE,(0,hard_core))
