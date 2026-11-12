#!/usr/bin/env python3
"""CPU-only application check; caller holds the common heavy lock."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

if __name__ == '__main__':
    subprocess.run([sys.executable, '-B', '-m', 'unittest',
                    'tests.service.test_simulation.SimulationCpuTests',
                    'tests.service.test_simulation.SimulationSqlTests', '-v'], cwd=ROOT, check=True)
