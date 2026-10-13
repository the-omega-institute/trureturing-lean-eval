"""Whole submitted Fermat root only; queue through canonical make, never rebuild tools.

--readiness [PACKAGE] observes prerequisites without launching a process.
--queue PACKAGE EVIDENCE exports the exact root then checks every export in Nanoda.
The internal --inside-make mode is used by the Lake target under omega-gate.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
LANE = Path('/Users/macstudio/omega/.lean-eval-recovery-20261007/flt')
ORDER = LANE.parent / 'single-problem-order-20261010.json'
STANDARD = {'propext', 'Quot.sound', 'Classical.choice'}
GOAL = 'Submission.fermat_last_theorem : FermatLastTheorem'
NAME = 'Submission.fermat_last_theorem'
EXPORTER_PIN = '076e8e57707e813375e8f9da8bf989799ace9680'
NANODA_PIN = '68d5ca9db226849b41a6fff59d796ff19d0a8840'
EXACT_AUDIT_SHA256 = '9d72a9e4aaa03a3450332f58fdfecbcce53f7788f5937c8c864ec3ae1491d8e6'

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for part in iter(lambda: handle.read(1048576), b''):
            digest.update(part)
    return digest.hexdigest()

def load(path):
    path = Path(path)
    return json.loads(path.read_text()) if path.is_file() and path.stat().st_size else None

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def timestamp(value):
    parsed = datetime.datetime.fromisoformat(value)
    assert parsed.tzinfo is not None, 'receipt timestamp lacks timezone'
    return parsed

def save(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)

def waited_native_inputs(job_path, run_directory, cwd, command, child_pid, started_at, ended_at):
    """Bind a completed runtime to its actual waited native child."""
    job_path, run_directory = Path(job_path), Path(run_directory)
    job = load(job_path)
    running_path, terminal_path = run_directory / 'running.json', run_directory / 'terminal.json'
    running, terminal = load(running_path), load(terminal_path)
    assert job and running and terminal and terminal['exit'] == 0
    assert job['run'] == str(run_directory) and job['cwd'] == str(cwd)
    assert job['command'] == command and job['number_of_files'] == 65536
    assert terminal['config_path'] == str(job_path) and terminal['config_sha256'] == sha(job_path)
    assert all(terminal[key] == value for key, value in job.items())
    assert all(terminal[key] == value for key, value in running.items())
    assert terminal['host_pid'] > 0 and terminal['child_pid'] == child_pid > 0
    assert terminal['host_pid'] != child_pid and terminal['nofile_after'][0] == 65536
    assert timestamp(terminal['started_at']) <= timestamp(started_at) <= timestamp(ended_at) <= timestamp(terminal['ended_at'])
    return terminal, {str(path): sha(path) for path in [job_path, running_path, terminal_path]}

def exporter_inputs(exporter_dir):
    """Join the actual native, make and seven tool steps from one configuration."""
    configuration = exporter_dir / 'configuration.json'
    cfg = load(configuration)
    native_job_path = exporter_dir / 'native-job.json'
    job = load(native_job_path)
    native_running = load(exporter_dir / 'native-host/running.json')
    native = load(exporter_dir / 'native-host/terminal.json')
    make_running = load(exporter_dir / 'make-running.json')
    make = load(exporter_dir / 'make-terminal.json')
    result_path = exporter_dir / 'build-evidence/result.json'
    result = load(result_path)
    assert cfg and job and native_running and native and make_running and make and result
    assert native['exit'] == make['exit'] == result['exit'] == 0
    configuration_sha = sha(configuration)
    assert cfg['official_source_pin'] == result['official_source_pin'] == EXPORTER_PIN
    assert result['source_inputs_unchanged'] and result['actual_scoped_build']
    assert result['source_pins'] == cfg['source_pins']
    assert result['configuration'] == make['configuration'] == str(configuration)
    assert result['configuration_sha256'] == make['configuration_sha256'] == configuration_sha
    for key, value in make_running.items():
        assert make[key] == value, ('exporter make receipt changed', key)
    expected_make = ['make', 'lean', 'LEAN_TARGETS=-d ' + str(exporter_dir) + ' -f lakefile.lean restorePinnedExporter']
    assert make['command'] == expected_make and make['nested_lock'] is False
    assert make['lean_num_threads'] == 1
    assert job['run'] == str(exporter_dir / 'native-host')
    assert job['command'] == ['/usr/bin/python3', '-u', str(exporter_dir / 'run_make_restore.py'), str(configuration)]
    for key, value in native_running.items():
        assert native[key] == value, ('exporter native receipt changed', key)
    assert native['config_path'] == str(native_job_path)
    assert native['config_sha256'] == sha(native_job_path)
    assert all(native[key] == value for key, value in job.items())
    assert native['host_pid'] > 0 and native['child_pid'] > 0
    assert native['started_at'] <= make['started_at'] <= make['ended_at'] <= native['ended_at']
    assert make['started_at'] <= result['started_at'] <= result['ended_at'] <= make['ended_at']
    targets = ['+Export:olean', '+Export.Parse:olean', '+Main:olean',
               '+Export:o', '+Export.Parse:o', '+Main:o', 'lean4export']
    assert load(exporter_dir / 'build-evidence/steps.json') == result['steps']
    assert [step['target'] for step in result['steps']] == targets
    for step in result['steps']:
        assert step['exit'] == 0 and step['lean_num_threads'] == 1 and step['pid'] > 0
        assert step['command'] == [cfg['lake'], '--no-cache', 'build', step['target']]
    assert sha(cfg['executor']) == cfg['executor_sha256']
    assert sha(cfg['lakefile']) == cfg['lakefile_sha256']
    assert sha(cfg['lean']) == cfg['lean_sha256']
    revision = subprocess.check_output(['git', '-C', cfg['tool_root'], 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == EXPORTER_PIN
    inputs = {}
    for path, expected in cfg['source_pins'].items():
        assert sha(path) == expected, path
        inputs[path] = expected
    for path in [configuration, native_job_path, exporter_dir / 'native-host/running.json',
                 exporter_dir / 'native-host/terminal.json', exporter_dir / 'make-running.json',
                 exporter_dir / 'make-terminal.json', exporter_dir / 'build-evidence/steps.json',
                 result_path, cfg['executor'], cfg['lakefile'], exporter_dir / 'run_make_restore.py']:
        inputs[str(path)] = sha(path)
    binary = Path(result['retained_binary'])
    assert sha(binary) == result['retained_binary_sha256'] == result['binary_sha256']
    assert os.access(binary, os.X_OK)
    inputs[str(binary)] = sha(binary)
    return result, inputs

def kernel_inputs(configuration):
    """Read the real make/kernel join, rather than an aggregate accepted flag."""
    configuration = Path(configuration)
    cfg = load(configuration)
    assert cfg['phase'] == 'compile_source' and cfg['selected_problem'] == 'fermat_last_theorem'
    assert cfg['canonical_common'] == '/Users/macstudio/omega/trureturing/.git'
    assert cfg['toolchain'] == 'leanprover/lean4:v4.35.0-rc3'
    assert cfg['mathlib_revision'] == '5e0c4e5239cb0a2d86d68a884bf52cfd963fce22'
    make_path = Path(cfg['make_terminal_receipt'])
    make_running_path = Path(cfg['make_running_receipt'])
    kernel_path = Path(cfg['evidence']) / 'result.json'
    make_running, make, kernel = load(make_running_path), load(make_path), load(kernel_path)
    assert make_running and make and kernel and make['exit'] == kernel['exit'] == 0
    assert all(make[key] == value for key, value in make_running.items())
    door = RESEARCH / 'canonical-flt-make-door'
    assert make['command'] == ['make', 'lean', 'LEAN_TARGETS=-d ' + str(door) + ' -f lakefile.lean configuredCheck']
    assert make['make_pid'] > 0 and make['worktree'] == cfg['worktree']
    assert make['official_dependency_partition'] == cfg['official_dependency_partition']
    assert timestamp(make['at']) <= timestamp(kernel['at']) <= timestamp(kernel['ended_at']) <= timestamp(make['ended_at'])
    assert make['phase'] == kernel['phase'] == 'compile_source'
    assert make['configuration'] == kernel['configuration'] == str(configuration)
    assert make['configuration_sha256'] == kernel['configuration_sha256'] == sha(configuration)
    assert make['build_admission'] == 'omega-gate; sole FLT source job'
    assert kernel['make_entry_required'] is True
    assert kernel['source'] == cfg['source']
    assert kernel['source_sha256'] == cfg['source_sha256'] == sha(cfg['source'])
    assert kernel['source_unchanged'] is True
    assert kernel['object_sha256'] == sha(cfg['object'])
    assert sha(cfg['lean']) == cfg['lean_sha256']
    assert kernel['command'] == ['/Users/macstudio/.local/omega-shims/lean', '-j1', '--trust=0', '-Ddebug.skipKernelTC=false',
                                 '-R', cfg['source_root'], '-o', cfg['object'], cfg['source']]
    assert kernel['toolchain'] == cfg['toolchain'] and kernel['mathlib_revision'] == cfg['mathlib_revision']
    assert kernel['canonical_common'] == cfg['canonical_common']
    inputs = {}
    for item in cfg['required_cached_objects']:
        assert sha(item['path']) == item['sha256'], item['path']
        inputs[item['path']] = item['sha256']
    for path in [configuration, make_running_path, make_path, kernel_path, cfg['source'], cfg['object'], cfg['lean'],
                 Path(cfg['evidence']) / 'stdout.log']:
        inputs[str(path)] = sha(path)
    return cfg, kernel, inputs

def exact_audit_inputs(audit, state):
    configuration = Path(audit['canonical_configuration'])
    cfg, kernel, inputs = kernel_inputs(configuration)
    root_source = LANE / 'flt-official-port-20261006-src/Submission.lean'
    root_object = LANE / 'flt-official-port-20261006-build/lib/lean/Submission.olean'
    audit_source = LANE / 'ExactRootAudit.lean'
    assert cfg['source'] == str(audit_source)
    assert cfg['object'] == str(LANE / 'exact-root-audit/ExactRootAudit.olean')
    assert audit['make_exit'] == audit['exit'] == 0
    assert audit['canonical_kernel_result'] == str(Path(cfg['evidence']) / 'result.json')
    assert audit['audit_source_sha256'] == sha(audit_source)
    assert sha(audit_source) == EXACT_AUDIT_SHA256, 'unabbreviated original audit source changed'
    assert audit['audit_olean_sha256'] == kernel['object_sha256']
    root_receipt = state['records']['Submission']
    assert root_receipt['exit'] == 0 and root_receipt['source_unchanged'] is True
    assert root_receipt['sha256'] == audit['root_source_sha256'] == sha(root_source)
    assert root_receipt['olean_sha256'] == audit['root_olean_sha256'] == sha(root_object)
    assert {'path': str(root_object), 'sha256': sha(root_object)} in cfg['required_cached_objects']
    axioms = recursive_axioms(Path(cfg['evidence']) / 'stdout.log')
    assert axioms == audit['recursive_axioms'] and set(axioms) <= STANDARD
    for path in [root_source, root_object, LANE / 'exact-root-audit/result.json']:
        inputs[str(path)] = sha(path)
    return inputs

def recursive_axioms(stdout):
    match = re.search(r"'Submission\.fermat_last_theorem' depends on axioms:\s*\[([^\]]*)\]", Path(stdout).read_text())
    assert match, 'missing recursive axiom output for the exact root'
    return [name.strip() for name in match[1].split(',') if name.strip()]

def runtime_inputs(package, manifest, runtime, audit):
    directory = package / 'runtime'
    prepared_path = directory / 'prepared.json'
    prepared = load(prepared_path)
    manifest_sha = sha(package / 'manifest.json')
    assert runtime['package_manifest_sha256'] == prepared['manifest_sha256'] == manifest_sha
    assert prepared['package_manifest'] == str(package / 'manifest.json')
    assert prepared['submitted_source_bindings'] == manifest['submission_file_pins']
    assert prepared['literal_original_root_sha256'] == runtime['literal_original_root_sha256'] == manifest['root_source_sha256']
    assert prepared['scientific_supplier_cache_excluded'] is True
    assert runtime['scientific_supplier_cache_excluded'] is True
    root_configuration = directory / 'root-configuration.json'
    exact_configuration = directory / 'exact-root-configuration.json'
    assert prepared['runtime_configuration'] == str(root_configuration)
    assert sha(root_configuration) == prepared['runtime_configuration_sha256']
    assert sha(prepared['runtime_runner']) == prepared['runtime_runner_sha256']
    expected_runner = LANE / 'recovery-20261010/run_full_root_runtime.py'
    assert prepared['runtime_runner'] == str(expected_runner)
    native, inputs = waited_native_inputs(directory / 'root-native-job.json', directory / 'root-native-host',
        package / 'source-only', ['/usr/bin/python3', '-u', str(expected_runner), str(package)],
        runtime['runner_pid'], runtime['at'], runtime['ended_at'])
    assert native['env']['LEAN_NUM_THREADS'] == '1'
    assert [stage['stage'] for stage in runtime['stages']] == ['root', 'exact-root']
    configs, kernels = [], []
    for configuration, stage in zip([root_configuration, exact_configuration], runtime['stages']):
        cfg, kernel, bindings = kernel_inputs(configuration)
        assert stage['dispatcher_exit'] == stage['make_exit'] == stage['kernel_exit'] == 0
        assert stage['make_terminal'] == cfg['make_terminal_receipt']
        assert stage['kernel_terminal'] == str(Path(cfg['evidence']) / 'result.json')
        make = load(cfg['make_terminal_receipt'])
        assert timestamp(runtime['at']) <= timestamp(make['at']) <= timestamp(make['ended_at']) <= timestamp(runtime['ended_at'])
        assert str(LANE / 'flt-official-port-20261006-build/lib/lean') not in cfg['lean_path'].split(os.pathsep)
        inputs.update(bindings)
        configs.append(cfg)
        kernels.append(kernel)
    root_cfg, exact_cfg = configs
    assert timestamp(load(root_cfg['make_terminal_receipt'])['ended_at']) <= timestamp(load(exact_cfg['make_terminal_receipt'])['at'])
    codec = package / 'source-only/.lake/build/lib/lean'
    assert root_cfg['source'] == str(package / 'source-only/Submission.lean')
    assert root_cfg['object'] == str(directory / 'lib/lean/Submission.olean')
    assert root_cfg['source_sha256'] == manifest['submission_file_pins']['Submission.lean']
    assert exact_cfg['source'] == str(LANE / 'ExactRootAudit.lean')
    assert exact_cfg['source_sha256'] == audit['audit_source_sha256']
    assert exact_cfg['object'] == str(directory / 'lib/lean/ExactRootAudit.olean')
    assert exact_cfg['lean_path'].split(os.pathsep)[0] == str(directory / 'lib/lean')
    assert str(codec) in exact_cfg['lean_path'].split(os.pathsep), 'decoded dependency objects missing from exact audit path'
    assert exact_cfg['lean_path'].split(os.pathsep)[1] == str(codec)
    assert {'path': root_cfg['object'], 'sha256': kernels[0]['object_sha256']} in exact_cfg['required_cached_objects']
    assert kernels[0]['object_sha256'] == runtime['runtime_root_olean_sha256']
    assert kernels[1]['object_sha256'] == runtime['audit_olean_sha256']
    axioms = recursive_axioms(Path(exact_cfg['evidence']) / 'stdout.log')
    assert axioms == runtime['recursive_axioms'] and set(axioms) <= STANDARD
    archive = package / 'original-sources.xz'
    assert sha(archive) == manifest['xz_sha256'] and archive.stat().st_size == manifest['xz_bytes']
    assert len(manifest['source_pins']) == manifest['source_count']
    assert manifest['source_pins']['Submission'] == manifest['root_source_sha256']
    closure = hashlib.sha256(json.dumps(manifest['source_pins'], sort_keys=True).encode()).hexdigest()
    assert closure == manifest['source_closure_sha256']
    expected_modules = {str(Path(*module.split('.')).with_suffix('.olean'))
                        for module in manifest['source_pins'] if module != 'Submission'}
    actual_modules = {str(p.relative_to(codec)) for p in codec.rglob('*.olean')}
    assert actual_modules == expected_modules, 'decoded runtime dependency module set differs'
    decoded_path = directory / 'decoded-object-bindings.json'
    decoded = load(decoded_path)
    assert runtime['decoded_object_bindings'] == str(decoded_path)
    assert runtime['decoded_object_bindings_sha256'] == sha(decoded_path)
    assert decoded['module_count'] == runtime['decoded_module_count'] == manifest['source_count'] - 1
    assert set(decoded['modules']) == set(manifest['source_pins']) - {'Submission'}
    for module, binding in decoded['modules'].items():
        path = codec / Path(*module.split('.')).with_suffix('.olean')
        assert binding['path'] == str(path) and binding['sha256'] == sha(path)
        assert binding['original_source_sha256'] == manifest['source_pins'][module]
    actual_facets = {}
    for path in codec.rglob('*'):
        if path.is_file():
            assert not path.is_symlink(), 'decoded runtime object is a symlink'
            assert path.resolve().is_relative_to(codec.resolve()), 'decoded runtime object escapes its package'
            relative = str(path.relative_to(codec))
            base = relative.split('.olean', 1)[0] if '.olean' in relative else relative.split('.ir', 1)[0]
            assert base + '.olean' in expected_modules
            assert relative[len(base):] in {'.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'}
            actual_facets[str(path)] = sha(path)
    assert decoded['output_facets'] == actual_facets
    assert all({'path': path, 'sha256': digest} in exact_cfg['required_cached_objects']
               for path, digest in actual_facets.items())
    inputs.update(actual_facets)
    for path in [decoded_path, prepared_path, prepared['runtime_runner'], archive, directory / 'result.json']:
        inputs[str(path)] = sha(path)
    return inputs

def submitted_file_inputs(submitted, manifest):
    """Count the submitted inventory; .lake is the loader's generated output."""
    actual_files = {str(p.relative_to(submitted)) for p in submitted.rglob('*')
                    if p.is_file() and p.relative_to(submitted).parts[0] != '.lake'}
    assert actual_files == set(manifest['submission_file_pins']), 'unbound submitted file'
    assert not any(Path(relative).parts[0] == '.lake' for relative in manifest['submission_file_pins'])
    codec = submitted / '.lake/build/lib/lean'
    for path in (submitted / '.lake').rglob('*'):
        if path.is_file():
            assert not path.is_symlink() and path.resolve().is_relative_to(codec.resolve())
            assert path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'))
    inputs = {}
    total = lean_total = 0
    for relative, expected in manifest['submission_file_pins'].items():
        path = (submitted / relative).resolve()
        assert path.is_relative_to(submitted.resolve()) and sha(path) == expected, relative
        total += path.stat().st_size
        if path.suffix == '.lean':
            lean_total += path.stat().st_size
        inputs[str(path)] = expected
    assert total == manifest['submitted_source_bytes'] <= manifest['source_cap'] == 100000000
    assert lean_total == manifest['submitted_lean_source_bytes']
    return inputs

def preflight(package):
    """No prerequisite absence is represented as a mathematical failure."""
    reasons = []
    state = load(LANE / 'flt-coordinator-ready-pipeline-20261006-state.json')
    audit = load(LANE / 'exact-root-audit/result.json')
    if not state or not state.get('root_compiled'):
        reasons.append('complete original source root has not compiled')
    if not audit or audit.get('exit') != 0 or not audit.get('accepted_standard_recursive_axioms') or not audit.get('inputs_unchanged'):
        reasons.append('complete original exact-type and recursive-standard-axiom audit is not verified')
    exporter_dir = RESEARCH / 'restore-pinned-exporter'
    exporter = load(exporter_dir / 'build-evidence/result.json')
    for name in ['native-host/terminal.json', 'make-terminal.json', 'build-evidence/result.json']:
        receipt = load(exporter_dir / name)
        if not receipt or receipt.get('exit') != 0:
            reasons.append('pinned exporter has no successful ' + name)
    if package is None:
        reasons.append('owner has not supplied the completed stable source package')
        manifest = runtime = None
    else:
        package = Path(package).resolve()
        manifest = load(package / 'manifest.json')
        runtime = load(package / 'runtime/result.json')
        if not manifest or manifest.get('goal') != GOAL:
            reasons.append('stable source package manifest for the exact original is missing')
        if not runtime or runtime.get('exit') != 0 or not runtime.get('accepted_literal_original_and_standard_recursive_axioms'):
            reasons.append('actual complete submitted-source runtime and exact-type/axiom checks are missing')
    if reasons:
        return {'ready': False, 'at': now(), 'reasons': reasons, 'goal': GOAL, 'full_root_nanoda_verified': False}
    assert state['root_compiled'] and not state['running'] and not state['external_writers']
    assert set(audit['recursive_axioms']) <= STANDARD
    assert set(runtime['recursive_axioms']) <= STANDARD
    assert manifest['root_source_sha256'] == audit['root_source_sha256'] == runtime['literal_original_root_sha256'] == sha(LANE / 'flt-official-port-20261006-src/Submission.lean')
    assert manifest['submitted_source_bytes'] <= manifest['source_cap'] == 100000000
    assert manifest['source_count'] == state['sources'] == state['compiled']
    submitted = package / 'source-only'
    inputs = submitted_file_inputs(submitted, manifest)
    inputs.update(exact_audit_inputs(audit, state))
    inputs.update(runtime_inputs(package, manifest, runtime, audit))
    packed_object = package / 'runtime/lib/lean/Submission.olean'
    assert sha(packed_object) == runtime['runtime_root_olean_sha256']
    original_object = LANE / 'flt-official-port-20261006-build/lib/lean/Submission.olean'
    assert sha(original_object) == audit['root_olean_sha256']
    root_config = load(package / 'runtime/root-configuration.json')
    scientific_cache = str(LANE / 'flt-official-port-20261006-build/lib/lean')
    assert scientific_cache not in root_config['lean_path'].split(os.pathsep)
    exporter, bound_exporter_inputs = exporter_inputs(exporter_dir)
    inputs.update(bound_exporter_inputs)
    exporter_binary = Path(exporter['retained_binary'])
    assert sha(exporter_binary) == exporter['retained_binary_sha256'] == exporter['binary_sha256'] and os.access(exporter_binary, os.X_OK)
    pointer_path = Path('/Users/macstudio/omega/lean-eval-trusted-tools/flt-v435/retained-bin/nanoda-current.json')
    nanoda = load(pointer_path)
    nanoda_receipt = load(nanoda['source_receipt'])
    assert nanoda_receipt['exit'] == 0
    assert nanoda['official_pin'] == nanoda_receipt['official_pin'] == NANODA_PIN
    assert nanoda_receipt['inputs_unchanged'] is True
    for path, expected in nanoda_receipt['inputs'].items():
        assert sha(path) == expected, path
        inputs[path] = expected
    nanoda_binary = Path(nanoda['binary'])
    assert sha(nanoda_binary) == nanoda['binary_sha256'] == nanoda_receipt['binary_sha256'] and os.access(nanoda_binary, os.X_OK)
    pipeline = load(LANE / 'recovery-20261010/canonical-original-pipeline/configuration.json')
    policy = load(ORDER)
    assert policy['selected_problem'] == 'fermat_last_theorem'
    assert all(policy['lean_execution_limit'][key] == 1 for key in
               ['max_active_heavy_jobs', 'max_active_compilers', 'max_lean_threads'])
    common = subprocess.check_output(['git', '-C', pipeline['worktree'], 'rev-parse', '--path-format=absolute', '--git-common-dir'], text=True).strip()
    assert common == '/Users/macstudio/omega/trureturing/.git'
    revision = subprocess.check_output(['git', '-C', str(LANE / 'official-deps/.lake/packages/mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == pipeline['mathlib_revision'] == '5e0c4e5239cb0a2d86d68a884bf52cfd963fce22'
    sysroot = Path(pipeline['lean']).parent.parent
    assert sha(pipeline['lean']) == pipeline['lean_sha256']
    for path in [packed_object, original_object, exporter_binary, nanoda_binary, pointer_path,
                 package / 'manifest.json', package / 'runtime/result.json',
                 package / 'runtime/root-configuration.json', nanoda['source_receipt'],
                 LANE / 'exact-root-audit/result.json', sysroot / 'lib/lean/Init.olean', sysroot / 'lib/lean/Lean.olean']:
        inputs[str(path)] = sha(path)
    return {'ready': True, 'at': now(), 'goal': GOAL, 'package': str(package), 'pipeline': pipeline,
            'root_source': str(submitted / 'Submission.lean'), 'runtime_object': str(packed_object),
            'lean_sysroot': str(sysroot), 'lean_path': os.pathsep.join([
                str(packed_object.parent), str(submitted / '.lake/build/lib/lean'), root_config['lean_path']]),
            'exporter': str(exporter_binary), 'nanoda': str(nanoda_binary), 'inputs': inputs,
            'original_root_source_sha256': manifest['root_source_sha256'], 'full_root_nanoda_verified': False}

def execute(configuration):
    cfg = load(configuration)
    assert os.environ.get('FLT_FULL_ROOT_NANODA_CONFIG') == str(configuration)
    assert os.environ.get('OMEGA_GATE_HELD') == '1' and os.environ.get('LEAN_NUM_THREADS') == '1'
    assert os.environ.get('OMEGA_GATE_DISABLE') != '1'
    assert os.environ.get('OMEGA_GATE_REAL_DIR') == str(Path(cfg['pipeline']['lean']).parent)
    assert sha(__file__) == cfg['executor_sha256'] and sha(HERE / 'lakefile.lean') == cfg['lakefile_sha256']
    current = preflight(cfg['package'])
    assert current['ready'] and current['inputs'] == cfg['inputs']
    spec = importlib.util.spec_from_file_location('full_root_resource_guard', LANE.parent / 'adaptive-memory-guard.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    evidence = Path(cfg['evidence'])
    result = {'at': now(), 'goal': GOAL, 'configuration': str(configuration),
              'configuration_sha256': sha(configuration), 'inputs': cfg['inputs'], 'steps': [],
              'resource_guard_sha256': sha(LANE.parent / 'adaptive-memory-guard.py'),
              'resource_policy': guard.policy(),
              'full_root_nanoda_verified': False, 'official_comparator_run': False, 'official_acceptance': False}
    export = evidence / 'Fermat.export'
    nanoda_config = evidence / 'nanoda.json'
    settings = {'export_file_path': str(export), 'use_stdin': False, 'permitted_axioms': sorted(STANDARD),
                'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
                'num_threads': 1, 'nat_extension': True, 'string_extension': True,
                'pp_declars': [NAME], 'unknown_pp_declar_hard_error': True,
                'pp_output_path': str(evidence / 'exact-root.txt'), 'print_success_message': True, 'print_axioms': True}
    save(nanoda_config, settings)
    environment = dict(os.environ, LEAN_SYSROOT=cfg['lean_sysroot'], LEAN_PATH=cfg['lean_path'])
    environment['PATH'] = os.pathsep.join(['/Users/macstudio/.local/omega-shims',
        str(Path(cfg['lean_sysroot']) / 'bin'), environment.get('PATH', '')])
    def run(label, command, output):
        stage_dir = evidence / label
        stage_dir.mkdir()
        admission = guard.wait_for_admission(cfg['root_source'])
        assert admission['workers'] == 1, 'whole-root verification must run alone'
        step = {'label': label, 'command': command, 'at': now(), 'memory_admission': admission,
                'configuration_sha256': result['configuration_sha256']}
        start = time.monotonic()
        with output.open('xb') as stdout, (stage_dir / 'stderr.log').open('xb') as stderr:
            child = subprocess.Popen(command, cwd=cfg['package'], env=environment, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
            step['pid'] = child.pid
            save(stage_dir / 'running.json', step)
            code, memory = guard.monitor(child, stage_dir)
        step.update(exit=code, seconds=time.monotonic() - start, memory_guard=memory)
        save(stage_dir / 'terminal.json', step)
        result['steps'].append(step)
        if code:
            raise subprocess.CalledProcessError(code, command)
    try:
        run('export', [cfg['exporter'], 'Submission', '--', NAME], export)
        assert export.stat().st_size > 0
        export_sha = sha(export)
        # The pinned Nanoda opens its PP destination without create(true).
        # Start from a fresh empty file so stale output cannot certify this run.
        with (evidence / 'exact-root.txt').open('xb'):
            pass
        run('nanoda', [cfg['nanoda'], str(nanoda_config)], evidence / 'nanoda.stdout')
        text = (evidence / 'nanoda.stdout').read_text()
        match = re.search(r'Checked (\d+) declarations with no errors(?:\r?\n|$)', text)
        assert match and int(match[1]) > 0 and 'skipping exported but unpermitted axioms' not in text
        assert (evidence / 'exact-root.txt').is_file() and (evidence / 'exact-root.txt').stat().st_size > 0
        assert sha(export) == export_sha
        assert load(nanoda_config) == settings
        assert all(sha(path) == expected for path, expected in cfg['inputs'].items())
        result.update(exit=0, full_root_nanoda_verified=True, exact_exported_root=NAME,
                      checked_declarations=int(match[1]), export_sha256=export_sha,
                      nanoda_configuration_sha256=sha(nanoda_config), inputs_unchanged=True)
        result['artifact_pins'] = {str(export): export_sha,
            **{str(path): sha(path) for path in [nanoda_config, evidence / 'nanoda.stdout',
                evidence / 'exact-root.txt', evidence / 'export/terminal.json',
                evidence / 'nanoda/terminal.json']}}
    except Exception as error:
        result.update(exit=getattr(error, 'returncode', 1), failure=str(error), full_root_nanoda_verified=False)
    result['ended_at'] = now()
    save(evidence / 'result.json', result)
    return result['exit']

def joined_result(configuration, make_receipt, result):
    """A successful make cannot lend its result to a different tool invocation."""
    cfg = load(configuration)
    expected_sha = sha(configuration)
    evidence = Path(cfg['evidence'])
    expected_artifacts = {str(evidence / name) for name in [
        'Fermat.export', 'nanoda.json', 'nanoda.stdout', 'exact-root.txt',
        'export/terminal.json', 'nanoda/terminal.json']}
    coherent = bool(result and
        make_receipt.get('configuration') == str(configuration) and
        make_receipt.get('configuration_sha256') == expected_sha and
        result.get('configuration') == str(configuration) and
        result.get('configuration_sha256') == expected_sha and
        result.get('goal') == GOAL and result.get('inputs') == cfg['inputs'] and
        result.get('exact_exported_root') == NAME and result.get('inputs_unchanged') is True and
        result.get('full_root_nanoda_verified') is True and
        set(result.get('artifact_pins', {})) == expected_artifacts and
        all(sha(path) == expected for path, expected in result['artifact_pins'].items()) and
        [step.get('label') for step in result.get('steps', [])] == ['export', 'nanoda'] and
        all(step.get('exit') == 0 and step.get('configuration_sha256') == expected_sha
            for step in result.get('steps', [])) and
        all(sha(path) == expected for path, expected in cfg['inputs'].items()))
    return {'at': now(), 'goal': GOAL, 'configuration': str(configuration),
            'configuration_sha256': expected_sha, 'inputs': cfg['inputs'],
            'make_exit': make_receipt.get('exit'), 'tool_exit': (result or {}).get('exit'),
            'coherent_make_and_tool_results': coherent,
            'full_root_nanoda_verified': coherent and make_receipt.get('exit') == result.get('exit') == 0,
            'official_comparator_run': False, 'official_acceptance': False}

def queue(package, destination):
    cfg = preflight(package)
    if not cfg['ready']:
        print(json.dumps(cfg, indent=2))
        return 2
    evidence = Path(destination).resolve()
    assert evidence.is_relative_to(RESEARCH) or evidence.is_relative_to(LANE)
    evidence.mkdir(exist_ok=False)
    cfg.update(evidence=str(evidence), executor_sha256=sha(__file__), lakefile_sha256=sha(HERE / 'lakefile.lean'))
    configuration = evidence / 'configuration.json'
    save(configuration, cfg)
    pipeline = cfg['pipeline']
    environment = dict(os.environ, FLT_FULL_ROOT_NANODA_CONFIG=str(configuration), FLT_FULL_ROOT_NANODA_EXECUTOR=str(Path(__file__).resolve()),
                       STRATALINT_LEAN_CACHE_DONOR_REPOSITORY=pipeline['canonical_repository'], STRATALINT_LEAN_PRODUCER_DLL=pipeline['producer_dll'],
                       ELAN_TOOLCHAIN=pipeline['toolchain'], LEAN_NUM_THREADS='1')
    assert environment.get('OMEGA_GATE_DISABLE') != '1'
    environment.pop('OMEGA_GATE_HELD', None)
    gate_shims = Path('/Users/macstudio/.local/omega-shims')
    environment.update(LEAN_SKIP_LOCK='1', LAKE_BIN=str(gate_shims / 'lake'),
                       OMEGA_GATE_REAL_DIR=str(Path(pipeline['lake']).parent), OMEGA_GATE_REQUEST_GB='35')
    environment['PATH'] = os.pathsep.join([str(gate_shims), str(Path(pipeline['lake']).parent),
        str(Path(pipeline['dotnet']).parent), environment.get('PATH', '')])
    command = ['make', 'lean', 'LEAN_TARGETS=-d ' + str(HERE) + ' -f lakefile.lean forcedRootNanoda']
    start = time.monotonic()
    with (evidence / 'make.stdout').open('xb') as stdout, (evidence / 'make.stderr').open('xb') as stderr:
        child = subprocess.Popen(command, cwd=pipeline['worktree'], env=environment, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
        receipt = {'at': now(), 'command': command, 'make_pid': child.pid,
                   'configuration': str(configuration), 'configuration_sha256': sha(configuration)}
        save(evidence / 'make-running.json', receipt)
        code = child.wait()
    receipt.update(exit=code, seconds=time.monotonic() - start, ended_at=now())
    save(evidence / 'make-terminal.json', receipt)
    result = load(evidence / 'result.json')
    joined = joined_result(configuration, receipt, result)
    save(evidence / 'joined-result.json', joined)
    print(json.dumps(joined, indent=2))
    return 0 if joined['full_root_nanoda_verified'] else code or 1

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--readiness', action='store_true')
    modes.add_argument('--queue', action='store_true')
    modes.add_argument('--inside-make', type=Path)
    parser.add_argument('paths', nargs='*', type=Path)
    args = parser.parse_args()
    if args.inside_make:
        return execute(args.inside_make.resolve())
    if args.readiness:
        result = preflight(args.paths[0] if args.paths else None)
        print(json.dumps(result, indent=2))
        return 0 if result['ready'] else 2
    if len(args.paths) != 2:
        parser.error('--queue requires PACKAGE EVIDENCE')
    return queue(*args.paths)

if __name__ == '__main__':
    sys.exit(main())
