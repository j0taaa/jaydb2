#!/usr/bin/env python3
"""Additional labelled application profile; original benchmark runner is unchanged.

Caller holds the repository heavy-work lock. Every logical workload, oracle,
negative check, durable setting and timing boundary comes from the legacy runner.
Only JayDB2's application access strategy changes, and all setup is measured.
"""
from __future__ import annotations
import copy
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import jay as base
import run as legacy

PROFILE = 'single-call-queries-v1'
PROGRAMS = (('Access', 0), ('Batch', 0), ('ReadRow', 3),
            ('Reader', 3), ('Sum', 0), ('Join', 0))
PROFILE_METADATA = {
    'logical_workloads': 'Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.',
    'point_reads_and_keys': 'One separately read-only-certified Reader program; normal fresh authentication and artifact checks.',
    'full_data_validation': 'Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.',
    'sum': 'One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal.',
    'join': 'One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.',
    'query_registration': 'SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.',
    'durability': 'Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.',
    'setup': 'All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.',
    'comparison': 'Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.',
}


def read_row_proof():
    # Six actual ReadCell operations followed by Finish; every continuation is
    # covered by the additional read-only witness, not inferred from the name.
    evidence = 'Unit{}'
    for i in reversed(range(6)):
        evidence = f'Logic.Both{{Unit{{}}, r{i} => {evidence}}}'
    return (base.proof(7).replace('import Base\n', 'import Base\nimport ./Logic.bend as Logic\nimport ./ReadOnly.bend as RO\n', 1)
            + '\ndef B.read_only(ctx, args):\n  (7n, ' + evidence + ')\n')


class OptimizedJay(base.Jay):
    def __init__(self, scenario, folder, binary, env):
        folder = Path(folder)
        folder.mkdir(parents=True, exist_ok=True)
        for source, target in (('Read', 'Reader'), ('Sum', 'Sum'), ('Join', 'Join')):
            for suffix in ('', 'Proof'):
                (folder/f'{target}{suffix}.bend').write_bytes((HERE/f'{source}{suffix}.bend').read_bytes())
        # Base creates the same configuration, empty seed and original programs;
        # its dynamic prepare() call reaches the override once, not twice.
        super().__init__(scenario, folder, binary, env)

    def prepare(self):
        (self.folder/'ReadRowProof.bend').write_text(read_row_proof())
        self.handles.clear()
        for name, opcode in PROGRAMS:
            started = time.perf_counter_ns()
            result = self.exchange(opcode, (self.folder/f'{name}.bend').read_text(),
                                   proof=(self.folder/f'{name}Proof.bend').read_text())
            if result['status'] != 'prepared':
                raise base.JayError(result)
            self.handles[name] = result['value']
            self.setup[f'prepare_{name.lower()}_ns'] = time.perf_counter_ns()-started

    def get(self, table, key, column):
        return self.execute(['read', table, key, column], 'Reader')

    def keys(self, table):
        return self.execute(['keys', table], 'Reader')

    def aggregate(self, table, column):
        return self.execute(['sum', table, column], 'Sum')

    def join(self, spec):
        return self.execute(['join', spec['from_table'], spec['fk'], spec['to_table'], spec['column']], 'Join')


def profile_save(original_save, path, value):
    # Tag every root save, including running and failed manifests, before bytes
    # reach disk. Individual engine records and raw timing samples are untouched.
    if isinstance(value, dict) and 'settings' in value and 'results' in value:
        value['settings']['profile'] = PROFILE
        value['settings']['profile_metadata'] = copy.deepcopy(PROFILE_METADATA)
        value['profile_metadata'] = copy.deepcopy(PROFILE_METADATA)
    original_save(path, value)


def main():
    original_jay, original_save = legacy.Jay, legacy.save
    try:
        legacy.Jay = OptimizedJay
        legacy.save = lambda path, value: profile_save(original_save, path, value)
        return legacy.main()
    finally:
        legacy.Jay, legacy.save = original_jay, original_save


if __name__ == '__main__':
    raise SystemExit(main())
