"""Checks on the fresh evidence and controls for plausible data corruption."""
import copy
import importlib.util
from pathlib import Path
import re
import statistics
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('paper_evidence',Path(__file__).with_name('evidence.py'))
evidence=importlib.util.module_from_spec(spec);spec.loader.exec_module(evidence)


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.data=evidence.load()

    def corrupt(self,edit,message):
        data=copy.deepcopy(self.data);edit(data)
        with self.assertRaisesRegex(ValueError,message):evidence.validate(data)

    def test_fresh_inputs_and_rendered_macros(self):
        previous=evidence.OUT
        try:
            with tempfile.TemporaryDirectory() as folder:
                evidence.OUT=Path(folder)
                macros=evidence.derive(self.data)
                self.assertIn('OrdinaryMedianSeconds',macros)
                self.assertIn('PreparedMedianMs',macros)
                self.assertIn('BreakEvenCalls',macros)
                self.assertTrue(all(re.fullmatch('[A-Z][a-zA-Z]*',name) for name in macros))
                self.assertTrue((Path(folder)/'scaling-coordinates.tex').is_file())
                self.assertAlmostEqual(macros['ProofToImplementationRatio'][0],
                    self.data['verification']['sizes']['proof']['nonblank_lines']/
                    self.data['verification']['sizes']['src']['nonblank_lines'])
                for policy in ('Point','Owner'):
                    for workload in ('Read','Update'):
                        for baseline in ('Postgres','Sqlite'):
                            self.assertAlmostEqual(macros['Jay'+policy+workload+'Over'+baseline][0],
                                macros['Jay'+policy+workload+'MedianMs'][0]/
                                macros[baseline+policy+workload+'MedianMs'][0])
                for record in self.data['ordinary']['records']:
                    prefix='Ordinary'+evidence.PROGRAMS[record['program']]
                    rows=record['samples']
                    self.assertAlmostEqual(macros[prefix+'CheckingSeconds'][0],
                        statistics.median([s['phases_ns']['primary_check']+
                            s['phases_ns']['bendtt_translate_check'] for s in rows])/1e9)
                    self.assertAlmostEqual(macros[prefix+'WorkerSharePercent'][0],
                        statistics.median([100*s['phases_ns']['ordinary_worker']/s['elapsed_ns'] for s in rows]))
                    self.assertAlmostEqual(macros[prefix+'OtherSeconds'][0],statistics.median([
                        s['elapsed_ns']-sum(s['phases_ns'][p] for p in
                            ('primary_check','bendtt_translate_check','c_emission','c_compilation','ordinary_worker'))
                        for s in rows])/1e9)
                self.assertGreater(macros['StateFirstExcessBytes'][0],macros['StateLimitBytes'][0])
                self.assertLessEqual(macros['StateMaximumBytes'][0],macros['StateLimitBytes'][0])
                # Plot x values are actual canonical bytes, and whiskers are quartiles.
                for mode in ('volatile','persistent'):
                    lines=(Path(folder)/f'scaling-{mode}_read.dat').read_text().splitlines()
                    for line,record in zip(lines[1:],[r for r in self.data['scaling']['records']
                            if r['persistent']==(mode=='persistent')]):
                        count,size,median,lower,upper=map(float,line.split())
                        stats=evidence.samples(record,50,'read')
                        self.assertEqual((count,size),(record['rows'],record['state_bytes']))
                        self.assertAlmostEqual(median-lower,stats['qone']/1e6,places=5)
                        self.assertAlmostEqual(median+upper,stats['qthree']/1e6,places=5)
                readme=(evidence.ROOT/'paper/README.md').read_text()
                for name in macros:self.assertIn('`\\'+name+'`',readme)
        finally:evidence.OUT=previous

    def test_integration_derivations_and_table_units(self):
        previous=evidence.OUT
        try:
            with tempfile.TemporaryDirectory() as folder:
                evidence.OUT=Path(folder)
                macros=evidence.derive(self.data)
                records=[r for r in self.data['scaling']['records'] if not r['persistent']]
                xs=[r['rows'] for r in records]
                ys=[statistics.median(s['elapsed_ns'] for s in r['samples']
                    if s['workload']=='read')/1000 for r in records]
                xm,ym=statistics.mean(xs),statistics.mean(ys)
                slope=sum((x-xm)*(y-ym) for x,y in zip(xs,ys))/sum((x-xm)**2 for x in xs)
                self.assertAlmostEqual(macros['ScalingVolatileReadSlopeUsPerRow'][0],slope)
                indexed=next(r for r in self.data['prepared']['records']
                    if r['persistent'] and r['program']=='indexed')
                medians=[statistics.median(s['elapsed_ns'] for s in z['samples'])/1e6
                    for z in indexed['sessions']]
                self.assertEqual(macros['PreparedIndexedPersistentSessionMinMs'][0],min(medians))
                self.assertEqual(macros['PreparedIndexedPersistentSessionMaxMs'][0],max(medians))
                self.assertEqual(macros['PreparedBatchCalls'][0],len(indexed['sessions'][0]['samples']))
                self.assertEqual(macros['ThroughputBlocks'][0]*macros['ThroughputBlockCalls'][0],
                    len(indexed['samples']))
                prepared=(Path(folder)/'prepared-table.tex').read_text()
                self.assertIn('Preparation s',prepared)
                self.assertIn('7.51',prepared)
                comparison=(Path(folder)/'database-comparison-table.tex').read_text()
                self.assertIn('Read ms',comparison)
                self.assertIn('0.003',comparison)
                spread=(Path(folder)/'session-spread-table.tex').read_text()
                self.assertIn('17.201--50.658',spread)
                self.assertEqual(spread.count('E2 '),6)
        finally:evidence.OUT=previous

    def test_duplicate_iteration(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][1].update(iteration=1),'samples')

    def test_wrong_result_even_with_checked_flag(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][0].update(actual={'status':'success','value':999}),'incorrect output')

    def test_boolean_is_not_integer(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][0].update(actual={'status':'success','value':False}),'incorrect output')

    def test_missing_metadata(self):
        self.corrupt(lambda d:d['prepared']['metadata'].pop('commit'),'Missing metadata')

    def test_missing_prepared_mode(self):
        self.corrupt(lambda d:d['prepared']['records'].pop(),'Prepared program/mode')

    def test_policy_is_actually_checked(self):
        self.corrupt(lambda d:d['comparison']['policy_checks'].pop(),'policy refusal')

    def test_superuser_does_not_establish_rls(self):
        self.corrupt(lambda d:d['comparison']['settings']['postgresql']['role'].__setitem__(1,True),'durability/RLS')

    def test_durable_settings(self):
        self.corrupt(lambda d:d['comparison']['settings']['sqlite'].update(synchronous=1),'SQLite durability')

    def test_missing_update_readback(self):
        def edit(d):
            row=next(s for r in d['comparison']['records'] if r['engine']=='jaydb2' for s in r['samples'] if s['workload']=='update')
            row.pop('stored_value_checked')
        self.corrupt(edit,'stored update')

    def test_missing_scaling_mode(self):
        self.corrupt(lambda d:d['scaling']['records'].pop(),'scaling population/mode')

    def test_failed_gate_is_not_valid_paper_evidence(self):
        self.corrupt(lambda d:d['verification']['commands'][0].update(returncode=1),'verification gate failed')

    def test_summary_uses_inclusive_quartiles(self):
        result=evidence.summary([dict(elapsed_ns=x) for x in (1,2,3,4,100)])
        self.assertEqual((result['median'],result['qone'],result['qthree']),(3,2,4))

    def test_mixed_engine_revision(self):
        self.corrupt(lambda d:d['comparison']['metadata'].update(source_sha256='0'*64),'Mixed engine fingerprints')

    def test_missing_session(self):
        self.corrupt(lambda d:d['prepared']['records'][0]['sessions'].pop(),'independent sessions')

    def test_raw_and_pooled_views_cannot_diverge(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['sessions'][0]['samples'][0].update(elapsed_ns=1),'Pooled samples')

    def test_frequency_policy_is_required(self):
        def edit(d):
            settings=d['prepared']['metadata']['frequency']['settings']
            key=next(k for k in settings if k.endswith('/scaling_governor'))
            settings[key]='powersave'
        self.corrupt(edit,'CPU frequency policy')

    def test_sampled_frequencies_required(self):
        self.corrupt(lambda d:d['comparison']['metadata']['frequency']['scaling_cur_freq_khz'].clear(),'sampled CPU frequencies')

    def test_missing_large_state_arm(self):
        self.corrupt(lambda d:d['comparison']['records'].__delitem__(next(i for i,r in enumerate(d['comparison']['records']) if r['rows']>10)),'engine/policy coverage')

    def test_missing_first_key_observations(self):
        self.corrupt(lambda d:d['scaling']['records'][0]['first_key_samples'].pop(),'samples')

    def test_scaling_uses_same_service_across_sizes(self):
        self.corrupt(lambda d:d['scaling']['records'][0].update(service_pid=-1),'service not reused')

    def test_size_inventory_and_new_macro_contract(self):
        sizes=self.data['verification']['detailed_sizes']
        self.assertEqual(sizes['rust_production_lines']+sizes['rust_test_lines'],self.data['verification']['sizes']['server']['nonblank_lines'])
        for app in sizes['applications'].values():
            self.assertEqual(app['client_lines'],sum(app['program_files'].values()))
            self.assertEqual(app['proof_lines'],sum(app['proof_files'].values()))
            for path,count in {**app['program_files'],**app['proof_files']}.items():
                self.assertEqual(count,sum(bool(x.strip()) for x in (evidence.ROOT/path).read_text().splitlines()))
        previous=evidence.OUT
        try:
            with tempfile.TemporaryDirectory() as folder:
                evidence.OUT=Path(folder)
                macros=evidence.derive(self.data)
                names='CpuGovernor CpuClockGHz TurboSetting SessionCount RustProductionLines RustTestLines IndexedClientLines IndexedProofLines IndexedProofRatio VoucherClientLines VoucherProofLines VoucherProofRatio ComparisonLargeRows ScalingFirstKeySmallMs ScalingFirstKeyLargeMs'.split()
                names += ['Large'+policy+engine+operation+'Ms' for policy in ('','Owner') for engine in ('Jay','Pg','Sq') for operation in ('Read','Write')]
                for name in names:self.assertIn(name,macros)
                self.assertEqual(macros['SessionCount'][0],3)
                self.assertEqual(macros['ComparisonLargeRows'][0],1104)
                self.assertIn('65{,}536',(Path(folder)/'numbers.tex').read_text())
                self.assertIn('Min s',(Path(folder)/'registration-table.tex').read_text())
                self.assertTrue((Path(folder)/'session-spread-table.tex').is_file())
                for row in evidence.report_rows(self.data):
                    if row['metric'].startswith(('E1','E2','E3')):self.assertEqual(len(row['session_medians']),3)
        finally:evidence.OUT=previous

if __name__=='__main__':unittest.main(verbosity=2)
