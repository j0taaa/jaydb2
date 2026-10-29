#!/usr/bin/env python3
"""Host launcher: growing OS stack and V8 limits above reachable resources.

The Linux x86_64 / 4 KiB deployment domain is checked explicitly. No address
space limit is installed. The caller still enforces the original public
deadline and aggregate allocated bytes for this whole process tree.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import resource
import sys


if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def flags(memory_bytes=None):
    if sys.platform != 'linux' or platform.machine() != 'x86_64' or os.sysconf('SC_PAGESIZE') != 4096:
        raise RuntimeError('Frontend resource domain requires Linux x86_64 with 4096-byte pages')
    if int(Path('/proc/sys/vm/mmap_min_addr').read_text()) < 65536:
        raise RuntimeError('Frontend address domain requires vm.mmap_min_addr >= 65536')
    fields = {key: int(value.split()[0]) for key, value in
              (line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())}
    physical_bytes = (fields['MemTotal'] + fields['SwapTotal']) * 1024
    if memory_bytes is not None and memory_bytes <= 0:
        raise ValueError('Host memory budget must be positive')
    reachable = min(memory_bytes, physical_bytes) if memory_bytes is not None else physical_bytes
    return ['--jitless', '--require', str(Path(__file__).resolve().with_name('stack.cjs')),
            f'--max-old-space-size={(reachable + 1048575) // 1048576}']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--memory-bytes', type=int)
    parser.add_argument('--resources-json', type=Path)
    parser.add_argument('--describe', action='store_true')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.resources_json:
        if args.memory_bytes is not None:
            parser.error('choose --resources-json or --memory-bytes')
        value = json.loads(args.resources_json.read_text())['compiler_memory_bytes']
        if not isinstance(value, str) or not value.isascii() or not value.isdecimal():
            raise ValueError('compiler_memory_bytes must be an exact decimal string')
        args.memory_bytes = int(value)
    node_flags = flags(args.memory_bytes)
    if args.describe:
        print(json.dumps({'nodeFlags': node_flags, 'stack': 'RLIM_INFINITY + V8 lowest user address 65536',
                          'domain': 'Linux x86_64, 4096-byte pages, vm.mmap_min_addr >= 65536'}))
        return
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if len(command) < 2:
        parser.error('expected -- NODE SCRIPT [ARGS...]')
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    os.execvp(command[0], [command[0], *node_flags, *command[1:]])


if __name__ == '__main__':
    try:
        main()
    except (OSError, RuntimeError, ValueError) as error:
        print(json.dumps({'code': 'FRONTEND_INFRASTRUCTURE', 'phase': 'bootstrap',
                          'message': str(error)}), file=sys.stderr)
        raise SystemExit(3)
