#!/usr/bin/env python3
"""Host launcher: growing OS stack and V8 limits above reachable resources.

The Linux x86_64 / 4 KiB deployment domain is checked explicitly. No address
space limit is installed. The active contract contains only the three logical message, state
and response sizes and imposes no physical memory or time quota.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import resource
import sys


def flags():
    if sys.platform != 'linux' or platform.machine() != 'x86_64' or os.sysconf('SC_PAGESIZE') != 4096:
        raise RuntimeError('Frontend resource domain requires Linux x86_64 with 4096-byte pages')
    if int(Path('/proc/sys/vm/mmap_min_addr').read_text()) < 65536:
        raise RuntimeError('Frontend address domain requires vm.mmap_min_addr >= 65536')
    fields = {key: int(value.split()[0]) for key, value in
              (line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())}
    physical_bytes = (fields['MemTotal'] + fields['SwapTotal']) * 1024
    return ['--jitless', '--require', str(Path(__file__).resolve().with_name('stack.cjs')),
            f'--max-old-space-size={(physical_bytes + 1048575) // 1048576}']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--describe', action='store_true')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    node_flags = flags()
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
