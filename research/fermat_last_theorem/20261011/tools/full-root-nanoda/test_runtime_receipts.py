"""Receipt/interface regression checks; fixtures are not Lean proof evidence.

Two cases read actual saved native and current gate make/kernel receipts. Other cases
use synthetic files to ensure stale or incomplete runtime evidence is rejected.
No compiler, exporter, Nanoda, or mathematical controller is launched.
"""
from pathlib import Path
import importlib.util
import json
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('full_root_consumer', HERE / 'run_full_root_nanoda.py')
consumer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(consumer)


class RuntimeReceipts(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='receipt-fixture-', dir=HERE)
        self.addCleanup(self.temporary.cleanup)
        self.package = Path(self.temporary.name) / 'package'
        self.directory = self.package / 'runtime'
        self.submitted = self.package / 'source-only'
        self.codec = self.submitted / '.lake/build/lib/lean'
        for directory in [self.directory / 'lib/lean', self.codec / 'Submission', self.directory / 'root-native-host']:
            directory.mkdir(parents=True, exist_ok=True)
        self.write(self.submitted / 'Submission.lean', b'synthetic packed source fixture')
        self.write(self.package / 'original-sources.xz', b'synthetic archive fixture')
        self.write(self.codec / 'Submission/Dependency.olean', b'synthetic decoded object')
        self.write(self.codec / 'Submission/Dependency.olean.private', b'synthetic private facet')
        root_source_sha = '1' * 64
        self.manifest = {
            'root_source_sha256': root_source_sha,
            'source_pins': {'Submission': root_source_sha, 'Submission.Dependency': '2' * 64},
            'source_count': 2,
            'submission_file_pins': {'Submission.lean': consumer.sha(self.submitted / 'Submission.lean')},
            'submitted_source_bytes': (self.submitted / 'Submission.lean').stat().st_size,
            'submitted_lean_source_bytes': (self.submitted / 'Submission.lean').stat().st_size,
            'source_cap': 100000000,
            'xz_sha256': consumer.sha(self.package / 'original-sources.xz'),
            'xz_bytes': (self.package / 'original-sources.xz').stat().st_size,
        }
        import hashlib
        self.manifest['source_closure_sha256'] = hashlib.sha256(json.dumps(self.manifest['source_pins'], sort_keys=True).encode()).hexdigest()
        self.store(self.package / 'manifest.json', self.manifest)
        self.audit = {'audit_source_sha256': consumer.sha(consumer.LANE / 'ExactRootAudit.lean')}
        self.configs = []
        self.kernels = []
        self.stages = []
        root_cfg = self.compile_stage('root', self.submitted / 'Submission.lean', 'Submission.olean', 1, 2, [])
        facets = {str(p): consumer.sha(p) for p in self.codec.rglob('*') if p.is_file()}
        self.decoded = {
            'module_count': 1,
            'modules': {'Submission.Dependency': {
                'path': str(self.codec / 'Submission/Dependency.olean'),
                'sha256': consumer.sha(self.codec / 'Submission/Dependency.olean'),
                'original_source_sha256': '2' * 64,
            }},
            'output_facets': facets,
        }
        self.store(self.directory / 'decoded-object-bindings.json', self.decoded)
        dependencies = [{'path': root_cfg['object'], 'sha256': self.kernels[0]['object_sha256']}]
        dependencies += [{'path': p, 'sha256': h} for p, h in facets.items()]
        self.compile_stage('exact-root', consumer.LANE / 'ExactRootAudit.lean', 'ExactRootAudit.olean', 3, 4, dependencies)
        runner = consumer.LANE / 'recovery-20261010/run_full_root_runtime.py'
        self.prepared = {
            'package_manifest': str(self.package / 'manifest.json'),
            'manifest_sha256': consumer.sha(self.package / 'manifest.json'),
            'literal_original_root_sha256': root_source_sha,
            'submitted_source_bindings': self.manifest['submission_file_pins'],
            'scientific_supplier_cache_excluded': True,
            'runtime_configuration': str(self.directory / 'root-configuration.json'),
            'runtime_configuration_sha256': consumer.sha(self.directory / 'root-configuration.json'),
            'runtime_runner': str(runner), 'runtime_runner_sha256': consumer.sha(runner),
        }
        self.store(self.directory / 'prepared.json', self.prepared)
        self.runtime = {
            'at': self.time(0), 'ended_at': self.time(5), 'runner_pid': 888,
            'package_manifest_sha256': self.prepared['manifest_sha256'],
            'literal_original_root_sha256': root_source_sha,
            'scientific_supplier_cache_excluded': True, 'stages': self.stages,
            'runtime_root_olean_sha256': self.kernels[0]['object_sha256'],
            'audit_olean_sha256': self.kernels[1]['object_sha256'],
            'recursive_axioms': ['propext', 'Quot.sound'],
            'decoded_object_bindings': str(self.directory / 'decoded-object-bindings.json'),
            'decoded_object_bindings_sha256': consumer.sha(self.directory / 'decoded-object-bindings.json'),
            'decoded_module_count': 1,
        }
        self.store(self.directory / 'result.json', self.runtime)
        job = {
            'run': str(self.directory / 'root-native-host'), 'cwd': str(self.submitted),
            'number_of_files': 65536, 'env': {'LEAN_NUM_THREADS': '1'},
            'command': ['/usr/bin/python3', '-u', str(runner), str(self.package)],
        }
        job_path = self.directory / 'root-native-job.json'
        self.store(job_path, job)
        self.native_running = dict(job, config_path=str(job_path), config_sha256=consumer.sha(job_path),
            host_pid=777, child_pid=888, started_at=self.time(0), nofile_after=[65536, 9223372036854775807])
        self.native_terminal = dict(self.native_running, exit=0, ended_at=self.time(6))
        self.store(self.directory / 'root-native-host/running.json', self.native_running)
        self.store(self.directory / 'root-native-host/terminal.json', self.native_terminal)

    @staticmethod
    def time(second):
        return '2026-10-10T00:00:%02d+00:00' % second

    @staticmethod
    def write(path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    @staticmethod
    def store(path, value):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2) + '\n')

    def compile_stage(self, label, source, object_name, start, end, dependencies):
        original = consumer.load(consumer.LANE / 'recovery-20261010/ideal-zero-prime-api-check-r2/configuration.json')
        cfg = dict(original, source=str(source), source_sha256=consumer.sha(source),
            source_root=str(source.parent), object=str(self.directory / 'lib/lean' / object_name),
            evidence=str(self.directory / (label + '-kernel')),
            required_cached_objects=dependencies,
            make_running_receipt=str(self.directory / (label + '-make-running.json')),
            make_terminal_receipt=str(self.directory / (label + '-make-terminal.json')),
            lean_path=str(self.directory / 'lib/lean') + ':' + str(self.codec))
        path = self.directory / (label + '-configuration.json')
        self.store(path, cfg)
        self.write(Path(cfg['object']), ('synthetic object ' + label).encode())
        door = consumer.RESEARCH / 'canonical-flt-make-door'
        make = {'at': self.time(start), 'command': ['make', 'lean', 'LEAN_TARGETS=-d ' + str(door) + ' -f lakefile.lean configuredCheck'],
            'configuration': str(path), 'configuration_sha256': consumer.sha(path),
            'worktree': cfg['worktree'], 'official_dependency_partition': cfg['official_dependency_partition'],
            'phase': 'compile_source', 'build_admission': 'omega-gate; sole FLT source job', 'make_pid': 999 + start}
        self.store(Path(cfg['make_running_receipt']), make)
        self.store(Path(cfg['make_terminal_receipt']), dict(make, exit=0, ended_at=self.time(end)))
        kernel = dict(make, exit=0, source=str(source), source_sha256=consumer.sha(source), source_unchanged=True,
            object_sha256=consumer.sha(cfg['object']), make_entry_required=True,
            command=['/Users/macstudio/.local/omega-shims/lean', '-j1', '--trust=0', '-Ddebug.skipKernelTC=false', '-R', cfg['source_root'], '-o', cfg['object'], cfg['source']],
            toolchain=cfg['toolchain'], mathlib_revision=cfg['mathlib_revision'], canonical_common=cfg['canonical_common'], ended_at=self.time(end))
        self.store(Path(cfg['evidence']) / 'result.json', kernel)
        self.write(Path(cfg['evidence']) / 'stdout.log', b"'Submission.fermat_last_theorem' depends on axioms: [propext, Quot.sound]\n")
        self.configs.append(cfg)
        self.kernels.append(kernel)
        self.stages.append({'stage': label, 'dispatcher_exit': 0, 'make_exit': 0, 'kernel_exit': 0,
            'make_terminal': cfg['make_terminal_receipt'], 'kernel_terminal': str(Path(cfg['evidence']) / 'result.json')})
        return cfg

    def check(self):
        return consumer.runtime_inputs(self.package, self.manifest, self.runtime, self.audit)

    def reject(self):
        with self.assertRaises((AssertionError, KeyError, ValueError, TypeError, FileNotFoundError)):
            self.check()

    def test_coherent_runtime_with_all_decoded_facets(self):
        inputs = self.check()
        self.assertIn(str(self.directory / 'root-native-host/terminal.json'), inputs)
        self.assertIn(str(self.codec / 'Submission/Dependency.olean.private'), inputs)
        self.assertEqual(len(consumer.submitted_file_inputs(self.submitted, self.manifest)), 1)

    def test_actual_saved_api_r2_native_receipts(self):
        directory = consumer.LANE / 'recovery-20261010/ideal-zero-prime-api-check-r2'
        job = consumer.load(directory / 'native-job.json')
        terminal = consumer.load(directory / 'native-host/terminal.json')
        make = consumer.load(directory / 'make-terminal.json')
        native, _ = consumer.waited_native_inputs(directory / 'native-job.json', directory / 'native-host',
            consumer.LANE, job['command'], terminal['child_pid'], make['at'], make['ended_at'])
        self.assertEqual(native['exit'], 0)

    def test_actual_saved_gate_make_kernel_receipts(self):
        configuration = consumer.LANE / ('flt-coordinator-ready-pipeline-20261006-logs/'
            '25c1d464612b97b60835cfc0-1791912883949987000.configuration.json')
        cfg, kernel, inputs = consumer.kernel_inputs(configuration)
        self.assertEqual(kernel['exit'], 0)
        self.assertIn(cfg['object'], inputs)
        self.assertIn(str(configuration), inputs)

    def test_missing_or_wrong_gate_admission(self):
        paths = [Path(self.configs[0][key]) for key in ('make_running_receipt', 'make_terminal_receipt')]
        originals = [consumer.load(path) for path in paths]
        for admission in (None, 'direct compiler'):
            with self.subTest(admission=admission):
                for path, original in zip(paths, originals):
                    receipt = dict(original)
                    if admission is None:
                        del receipt['build_admission']
                    else:
                        receipt['build_admission'] = admission
                    self.store(path, receipt)
                self.reject()

    def test_kernel_command_cannot_bypass_gate_or_kernel_checks(self):
        path = Path(self.configs[0]['evidence']) / 'result.json'
        original = consumer.load(path)
        for index, argument in ((0, self.configs[0]['lean']), (1, '-j2'),
                                (2, '--trust=1'), (3, '-Ddebug.skipKernelTC=true')):
            with self.subTest(argument=argument):
                receipt = dict(original, command=list(original['command']))
                receipt['command'][index] = argument
                self.store(path, receipt)
                self.reject()

    def test_kernel_requires_make_entry(self):
        path = Path(self.configs[0]['evidence']) / 'result.json'
        receipt = consumer.load(path)
        receipt['make_entry_required'] = False
        self.store(path, receipt)
        self.reject()

    def test_failed_make_or_kernel(self):
        paths = [Path(self.configs[0]['make_terminal_receipt']), Path(self.configs[0]['evidence']) / 'result.json']
        for path in paths:
            with self.subTest(path=path.name):
                receipt = consumer.load(path)
                self.store(path, dict(receipt, exit=1))
                self.reject()
                self.store(path, receipt)

    def test_missing_native_terminal(self):
        (self.directory / 'root-native-host/terminal.json').unlink()
        self.reject()

    def test_different_waited_child(self):
        self.native_running['child_pid'] = self.native_terminal['child_pid'] = 889
        self.store(self.directory / 'root-native-host/running.json', self.native_running)
        self.store(self.directory / 'root-native-host/terminal.json', self.native_terminal)
        self.reject()

    def test_failed_native_after_successful_stage_flags(self):
        self.native_terminal['exit'] = 1
        self.store(self.directory / 'root-native-host/terminal.json', self.native_terminal)
        self.reject()

    def test_changed_job_without_same_invocation_receipt(self):
        path = self.directory / 'root-native-job.json'
        job = consumer.load(path)
        job['cwd'] = str(self.package)
        self.store(path, job)
        self.reject()

    def test_mismatched_native_running_receipt(self):
        self.native_running['host_pid'] += 1
        self.store(self.directory / 'root-native-host/running.json', self.native_running)
        self.reject()

    def test_runtime_finishes_after_waited_native(self):
        self.runtime['ended_at'] = self.time(7)
        self.reject()

    def test_stages_outside_this_runtime(self):
        self.runtime['at'] = self.time(2)
        self.reject()

    def test_inconsistent_make_running_and_terminal(self):
        path = Path(self.configs[0]['make_running_receipt'])
        make = consumer.load(path)
        make['make_pid'] += 1
        self.store(path, make)
        self.reject()

    def test_decoder_receipt_missing_module(self):
        self.decoded['modules'] = {}
        self.store(self.directory / 'decoded-object-bindings.json', self.decoded)
        self.runtime['decoded_object_bindings_sha256'] = consumer.sha(self.directory / 'decoded-object-bindings.json')
        self.reject()

    def test_decoder_receipt_omits_private_facet(self):
        del self.decoded['output_facets'][str(self.codec / 'Submission/Dependency.olean.private')]
        self.store(self.directory / 'decoded-object-bindings.json', self.decoded)
        self.runtime['decoded_object_bindings_sha256'] = consumer.sha(self.directory / 'decoded-object-bindings.json')
        self.reject()

    def test_unbound_decoded_output(self):
        self.write(self.codec / 'unbound.txt', b'extra')
        self.reject()

    def test_unsubmitted_source_hidden_in_lake(self):
        self.write(self.submitted / '.lake/unbound.lean', b'extra')
        with self.assertRaises(AssertionError):
            consumer.submitted_file_inputs(self.submitted, self.manifest)

    def test_exact_stage_dependency_inventory_missing_facet(self):
        path = self.directory / 'exact-root-configuration.json'
        cfg = consumer.load(path)
        cfg['required_cached_objects'].pop()
        self.store(path, cfg)
        for p in [Path(cfg['make_running_receipt']), Path(cfg['make_terminal_receipt']), Path(cfg['evidence']) / 'result.json']:
            receipt = consumer.load(p)
            receipt['configuration_sha256'] = consumer.sha(path)
            self.store(p, receipt)
        self.reject()


if __name__ == '__main__':
    unittest.main(verbosity=2)
