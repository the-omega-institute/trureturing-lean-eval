"""Admission regressions only; no Lean, exporter or Nanoda process is launched."""
from pathlib import Path
import importlib.util
import json
import os
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('nanoda_gate_consumer', HERE / 'run_full_root_nanoda.py')
consumer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(consumer)


class ReachedPreflight(Exception):
    pass


class NanodaGate(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='gate-fixture-', dir=HERE)
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.pipeline = consumer.load(consumer.LANE / 'recovery-20261010/canonical-original-pipeline/configuration.json')
        self.ready = {'ready': True, 'goal': consumer.GOAL, 'pipeline': self.pipeline, 'inputs': {}}

    def test_queue_accepts_current_host_policy_and_reenters_gate(self):
        host = {'LEAN_SKIP_LOCK': '1', 'OMEGA_GATE_HELD': '1',
                'OMEGA_GATE_REAL_DIR': '/other/toolchain/bin', 'OMEGA_GATE_REQUEST_GB': '8',
                'LAKE_BIN': '/other/lake', 'PATH': '/other/toolchain/bin:/usr/bin'}
        with mock.patch.dict(os.environ, host, clear=True), \
             mock.patch.object(consumer, 'preflight', return_value=self.ready), \
             mock.patch.object(consumer.subprocess, 'Popen') as child, \
             mock.patch('builtins.print'):
            child.return_value.wait.return_value = 0
            child.return_value.pid = 1234
            code = consumer.queue(self.directory / 'package', self.directory / 'evidence')
        command = child.call_args.args[0]
        environment = child.call_args.kwargs['env']
        self.assertEqual(command[:2], ['make', 'lean'])
        self.assertEqual(child.call_args.kwargs['cwd'], self.pipeline['worktree'])
        self.assertEqual(environment['LEAN_SKIP_LOCK'], '1')
        self.assertEqual(environment['LEAN_NUM_THREADS'], '1')
        self.assertNotIn('OMEGA_GATE_HELD', environment)
        self.assertEqual(environment['LAKE_BIN'], '/Users/macstudio/.local/omega-shims/lake')
        self.assertEqual(environment['PATH'].split(os.pathsep)[0], '/Users/macstudio/.local/omega-shims')
        self.assertEqual(environment['OMEGA_GATE_REAL_DIR'], str(Path(self.pipeline['lake']).parent))
        self.assertEqual(environment['OMEGA_GATE_REQUEST_GB'], '35')
        # A mocked make success cannot certify an absent actual tool result.
        self.assertEqual(code, 1)
        joined = consumer.load(self.directory / 'evidence/joined-result.json')
        self.assertFalse(joined['full_root_nanoda_verified'])

    def test_queue_rejects_disabled_gate_before_launch(self):
        with mock.patch.dict(os.environ, {'OMEGA_GATE_DISABLE': '1'}, clear=True), \
             mock.patch.object(consumer, 'preflight', return_value=self.ready), \
             mock.patch.object(consumer.subprocess, 'Popen') as child:
            child.return_value.wait.return_value = 0
            child.return_value.pid = 1234
            with self.assertRaises(AssertionError):
                consumer.queue(self.directory / 'package', self.directory / 'evidence')
        child.assert_not_called()

    def executor_configuration(self):
        path = self.directory / 'configuration.json'
        cfg = {'pipeline': self.pipeline, 'package': str(self.directory / 'package'),
               'executor_sha256': consumer.sha(HERE / 'run_full_root_nanoda.py'),
               'lakefile_sha256': consumer.sha(HERE / 'lakefile.lean')}
        path.write_text(json.dumps(cfg) + '\n')
        environment = {'FLT_FULL_ROOT_NANODA_CONFIG': str(path), 'LEAN_NUM_THREADS': '1',
                       'LEAN_SKIP_LOCK': '1', 'OMEGA_GATE_HELD': '1',
                       'OMEGA_GATE_REAL_DIR': str(Path(self.pipeline['lean']).parent)}
        return path, environment

    def test_inside_make_accepts_gate_under_current_host_policy(self):
        path, environment = self.executor_configuration()
        with mock.patch.dict(os.environ, environment, clear=True), \
             mock.patch.object(consumer, 'preflight', side_effect=ReachedPreflight), \
             mock.patch.object(consumer.subprocess, 'Popen') as child:
            with self.assertRaises(ReachedPreflight):
                consumer.execute(path)
        child.assert_not_called()

    def test_inside_make_rejects_missing_gate_or_wrong_toolchain(self):
        path, environment = self.executor_configuration()
        for changes in ({'OMEGA_GATE_HELD': '0'}, {'OMEGA_GATE_REAL_DIR': '/other/toolchain/bin'},
                        {'OMEGA_GATE_DISABLE': '1'}):
            with self.subTest(changes=changes), \
                 mock.patch.dict(os.environ, dict(environment, **changes), clear=True), \
                 mock.patch.object(consumer, 'preflight', side_effect=ReachedPreflight) as preflight, \
                 mock.patch.object(consumer.subprocess, 'Popen') as child:
                with self.assertRaises(AssertionError):
                    consumer.execute(path)
                preflight.assert_not_called()
                child.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
