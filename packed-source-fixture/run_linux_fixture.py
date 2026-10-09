from pathlib import Path
import subprocess, os, json, datetime, time, hashlib, sys

project = Path(__file__).resolve().parent
evidence = Path(os.environ['FIXTURE_EVIDENCE_DIR'])
evidence.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources = {str(p.relative_to(project)): sha(p) for p in project.rglob('*')
           if p.is_file() and '.lake' not in p.parts}
tool_dir = Path(os.environ['FIXTURE_TOOL_DIR'])
tool_pins = {}
for name in ['lean4export', 'comparator', 'nanoda']:
    tool_pins[name] = subprocess.check_output(
        ['git', '-C', str(tool_dir/name), 'rev-parse', 'HEAD'], text=True).strip()
assert tool_pins == {
    'lean4export': '076e8e57707e813375e8f9da8bf989799ace9680',
    'comparator': 'd03acab154d269c06e60e4de7e4cc85deebff94b',
    'nanoda': '68d5ca9db226849b41a6fff59d796ff19d0a8840',
}
binary_pins = {name: {'path': os.environ[name], 'sha256': sha(os.environ[name])}
               for name in ['COMPARATOR_BIN', 'COMPARATOR_LANDRUN',
                            'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_NANODA']}
assert sources['WorkspaceTest.lean'] == '17bd1978ec5ec46b151a616ae626d14cef01fcb6ce90a2d104dffae9a95e40df'
assert not (project/'Fixture/ModuleA.lean').exists()
assert not (project/'Fixture/ModuleB.lean').exists()
command = ['lake', 'test']
started = time.monotonic()
log = evidence/'official-fixture.log'
with log.open('w') as handle:
    child = subprocess.Popen(command, cwd=project, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
    print('official_fixture_native_pid', child.pid, flush=True)
    for line in child.stdout:
        handle.write(line)
        handle.flush()
        print(line, end='', flush=True)
    code = child.wait()
contents = log.read_text()
markers = ['Running nanoda kernel on solution', 'nanoda kernel accepts the solution',
           'Lean default kernel accepts the solution', 'Your solution is okay!']
markers_found = {s: s in contents for s in markers}
unchanged = all(sha(project/p) == h for p,h in sources.items())
objects = {str(p.relative_to(project)): sha(p) for p in (project/'.lake/build/lib/lean').rglob('*')
           if p.is_file() and any(p.name.endswith(ext) for ext in
                                  ['.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'])}
accepted = code == 0 and unchanged and all(markers_found.values())
receipt = {
    'ended_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_commit': os.environ['FIXTURE_SOURCE_COMMIT'],
    'command': command, 'native_pid': child.pid, 'exit': code,
    'elapsed_seconds': time.monotonic()-started,
    'sources': sources, 'sources_unchanged': unchanged, 'objects': objects,
    'tool_source_pins': tool_pins,
    'landrun_source_pin': '5ed4a3db3a4ad930d577215c6b9abaa19df7f99f',
    'tool_binary_pins': binary_pins,
    'log_sha256': sha(log), 'required_acceptance_markers': markers_found,
    'original_forced_nanoda_harness': True,
    'fixture_only': True, 'actual_Submission_entry': True,
    'landrun_official_comparator_and_full_root_nanoda_fixture_chain_passed': accepted,
    'full_original_FLT_kernel_tested': False, 'official_solve_credit': 0,
}
receipt_path = evidence/'official-fixture-receipt.json'
receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
print('receipt_sha256', sha(receipt_path), flush=True)
sys.exit(0 if accepted else (code or 1))
