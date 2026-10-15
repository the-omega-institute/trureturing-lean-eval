#!/usr/bin/env python3
"""Join completed canonical receipts to current inputs, without starting a build."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(root, module, suffix):
    return root / Path(*module.split('.')).with_suffix(suffix)


def verify(base, state, module, record):
    src = base / 'flt-official-port-20261006-src'
    obj = base / 'flt-official-port-20261006-build/lib/lean'
    kernel_path = Path(record['kernel_terminal_receipt'])
    make_path = Path(record['canonical_make_terminal_receipt'])
    kernel = json.loads(kernel_path.read_text())
    make = json.loads(make_path.read_text())
    config_path = Path(kernel['configuration'])
    config = json.loads(config_path.read_text())
    source_hash = sha(module_path(src, module, '.lean'))
    object_hash = sha(module_path(obj, module, '.olean'))
    assert kernel['source'] == str(module_path(src, module, '.lean'))
    assert kernel['command'] == record['command']
    assert kernel['command'][-1] == kernel['source']
    assert kernel['command'][kernel['command'].index('-o') + 1] == str(module_path(obj, module, '.olean'))
    assert record['exit'] == record['make_exit'] == kernel['exit'] == make['exit'] == 0
    assert record['source_unchanged'] and record['cache_binding_valid'] and kernel['source_unchanged']
    assert source_hash == record['sha256'] == config['source_sha256'] == kernel['source_sha256']
    assert object_hash == record['olean_sha256'] == kernel['object_sha256']
    assert sha(config_path) == kernel['configuration_sha256'] == make['configuration_sha256']
    assert config['canonical_common'] == '/Users/macstudio/omega/trureturing/.git'
    assert config['toolchain'] == 'leanprover/lean4:v4.35.0-rc3'
    assert config['mathlib_revision'] == '5e0c4e5239cb0a2d86d68a884bf52cfd963fce22'
    assert make['command'][:2] == ['make', 'lean']
    assert all(flag in kernel['command'] for flag in ['-j1', '--trust=0', '-Ddebug.skipKernelTC=false'])
    stdout, stderr = (Path(record[key]).read_text() for key in ['stdout', 'stderr'])
    assert not re.search(r'\berror(?:\([^)]*\))?:', stdout + stderr)
    dependencies = []
    for dep in record['direct_dependencies']:
        dep_source = sha(module_path(src, dep['module'], '.lean'))
        dep_object = sha(module_path(obj, dep['module'], '.olean'))
        assert dep_source == dep['source_sha256']
        if dep['object_sha256'] is not None:
            assert dep_object == dep['object_sha256']
            rec = state['records'][dep['module']]
            assert rec['exit'] == 0 and rec['sha256'] == dep_source and rec['olean_sha256'] == dep_object
        dependencies.append(dict(module=dep['module'], source_sha256=dep_source,
            object_sha256=dep_object, individual_controller_receipt=dep['object_sha256'] is not None))
    axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', stdout)
    return dict(module=module, source_sha256=source_hash, object_sha256=object_hash,
        make_exit=0, kernel_exit=0, warning_count=len(re.findall(r'\bwarning:', stdout + stderr)),
        stderr_nonempty=bool(stderr.strip()), configuration=str(config_path),
        configuration_sha256=sha(config_path), canonical_make_terminal=str(make_path),
        canonical_kernel_result=str(kernel_path), kernel_result_sha256=sha(kernel_path),
        canonical_make_terminal_sha256=sha(make_path),
        stdout_sha256=sha(Path(record['stdout'])), stderr_sha256=sha(Path(record['stderr'])),
        recursive_axioms_printed=[[a.strip() for a in group.split(',')] for group in axioms] or None,
        direct_dependency_hashes_current=True, direct_dependencies=dependencies,
        proof_checks=dict(threads=1, trust=0, skipKernelTC=False), official_acceptance=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--after', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    checkpoint = json.loads(args.after.read_text())
    selection = checkpoint.get('continuation_receipt_selection', {})
    floor_path = Path(selection.get('event_floor_checkpoint', args.after))
    floor = json.loads(floor_path.read_text())
    since = datetime.datetime.fromisoformat(floor['checkpoint_at']).timestamp()
    prior_progress_paths = selection.get('exclude_verified_progress_files', [])
    excluded_invocations = set()
    for prior_path in prior_progress_paths:
        prior_progress = json.loads(Path(prior_path).read_text())
        excluded_invocations.update(row['canonical_kernel_result']
            for row in prior_progress['new_verified_canonical_invocations'])
    state = json.loads((base / 'flt-coordinator-ready-pipeline-20261006-state.json').read_text())
    latest_events = {}
    for line in (base / 'flt-coordinator-ready-pipeline-20261006-events.jsonl').read_text().splitlines():
        event = json.loads(line)
        if (event.get('time', 0) > since and event.get('event') == 'compiled'
                and event.get('exit') == 0
                and event.get('kernel_terminal_receipt') not in excluded_invocations):
            latest_events[event['module']] = event
    verified, pending_publication = [], []
    for module, event in latest_events.items():
        record = state['records'].get(module)
        if (record is None or record.get('kernel_terminal_receipt')
                != event['kernel_terminal_receipt']):
            pending_publication.append(dict(module=module,
                kernel_terminal_receipt=event['kernel_terminal_receipt']))
            continue
        assert event['sha256'] == record['sha256'] and event['olean_sha256'] == record['olean_sha256']
        assert event['kernel_terminal_receipt'] == record['kernel_terminal_receipt']
        verified.append(verify(base, state, module, record))
    evidence = dict(observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        previous_checkpoint=str(args.after), graph_snapshot={k: state[k] for k in
            ['compiled', 'ready', 'failed', 'root_compiled']}, running_snapshot=state.get('running'),
        invocation_selection=dict(event_floor_checkpoint=str(floor_path),
            exclude_verified_progress_files=prior_progress_paths,
            excluded_invocation_count=len(excluded_invocations),
            identity_key='canonical_kernel_result'),
        new_verified_canonical_invocations=verified, shared_sources_edited_by_this_verifier=False,
        events_awaiting_matching_state_record=pending_publication,
        warning_scope='Warning counts belong to the exact unmodified supplier inputs; absent axiom output is not a root audit.',
        root_or_official_acceptance=False)
    with args.output.open('x') as handle:
        json.dump(evidence, handle, indent=2)
        handle.write('\n')
    print(json.dumps(dict(output=str(args.output), verified=len(verified),
        graph=evidence['graph_snapshot'], warning_counts=[dict(module=v['module'], count=v['warning_count'])
            for v in verified if v['warning_count']]), indent=2))


if __name__ == '__main__':
    main()
