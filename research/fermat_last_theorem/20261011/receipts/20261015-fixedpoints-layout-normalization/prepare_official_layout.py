#!/usr/bin/env python3
"""Preserve the recovered FLT proof while making its imports overlay-compatible.

The original Definitions/P2M/Theorems sources remain canonical and untouched.
Adapt import module tokens and the module-generated FixedPoints instance names.
Run while the sole compiler controller is drained; retain every old object.
"""
import argparse
import datetime
import errno
import hashlib
import json
from pathlib import Path
import re
import time

BASE = Path(__file__).resolve().parent
SRC = BASE / 'flt-official-port-20261006-src'
PREFIX = 'Submission.Supplier.'
LOCAL = ('Definitions.', 'P2M.', 'Theorems.')
IMPORT = re.compile(r'^([ \t]*import[ \t]+)([^\n]*)(\n|$)', re.MULTILINE)
TOKEN = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')
INSTANCE_RENAMES = {
    'FixedPoints.' + name + '_definitions': 'FixedPoints.' + name + '_submission'
    for name in (
        'instMulActionElemFixedPointsOfSMulCommClass',
        'instSMulElemFixedPointsOfSMulCommClass',
        'instAddCommMonoidElemFixedPoints',
    )
}
OPTIONS = (
    '\n-- Elaborator settings from the recovered exact-pin FLT controller.\n'
    'set_option autoImplicit false\n'
    'set_option maxHeartbeats 4000000\n'
    'set_option synthInstance.maxHeartbeats 400000\n'
    'set_option backward.isDefEq.respectTransparency.types false\n'
    'set_option debug.skipKernelTC false\n'
    '-- End recovered elaborator settings.\n'
)


def access(operation):
    while True:
        try:
            return operation()
        except OSError as error:
            if error.errno not in (errno.ENFILE, errno.EMFILE):
                raise
            time.sleep(5)


def source_path(module):
    return SRC / Path(*module.split('.')).with_suffix('.lean')


def transform(text):
    dependencies = []

    def line(match):
        body = match[2]
        # Preserve trailing comments exactly.
        end = len(body)
        for marker in ('--', '/-'):
            offset = body.find(marker)
            if offset >= 0:
                end = min(end, offset)

        def token(part):
            module = part[0]
            if module.startswith(LOCAL):
                dependencies.append(module)
                return PREFIX + module
            return module

        return match[1] + TOKEN.sub(token, body[:end]) + body[end:] + match[3]

    converted = IMPORT.sub(line, text)
    for original_name, submission_name in INSTANCE_RENAMES.items():
        converted = converted.replace(original_name, submission_name)
    imports = list(IMPORT.finditer(converted))
    if not imports:
        raise RuntimeError('Expected an import header in every supplier module')
    offset = imports[-1].end()
    converted = converted[:offset] + OPTIONS + converted[offset:]
    return converted, dependencies


def write_atomic(path, data):
    access(lambda: path.parent.mkdir(parents=True, exist_ok=True))
    if path.exists() and access(path.read_bytes) == data:
        return
    temp = path.with_suffix(path.suffix + '.layout.tmp')
    access(lambda: temp.write_bytes(data))
    access(lambda: temp.replace(path))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--module', help='Synchronize one canonical module after an API repair')
    args = parser.parse_args()
    evidence = BASE / 'official-layout'
    evidence.mkdir(exist_ok=True)
    saved_root = evidence / 'original-Submission.lean'
    if not saved_root.exists():
        write_atomic(saved_root, access((SRC / 'Submission.lean').read_bytes))
    original_root = access(saved_root.read_bytes)
    if args.apply:
        state = json.loads(access((BASE / 'flt-coordinator-ready-pipeline-20261006-state.json').read_text))
        if state.get('running') and not args.module:
            raise RuntimeError('Drain the sole controller before changing the root import layout')
        if args.module and PREFIX + args.module in state.get('running', {}):
            raise RuntimeError('Do not change the source of a running compiler')
    queue = [args.module] if args.module else ['Submission']
    seen = set()
    rows = []
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        original = original_root if module == 'Submission' else access(source_path(module).read_bytes)
        converted, dependencies = transform(original.decode('utf-8'))
        packaged = converted.encode('utf-8')
        # Undo only the layout adaptations to recover the source byte for byte.
        restored = IMPORT.sub(lambda match: match[0].replace(PREFIX, ''),
                              converted.replace(OPTIONS, '', 1))
        for original_name, submission_name in INSTANCE_RENAMES.items():
            if original_name in original.decode('utf-8'):
                restored = restored.replace(submission_name, original_name)
        if restored.encode('utf-8') != original:
            raise RuntimeError(f'Non-import source change in {module}')
        target_module = module if module == 'Submission' else PREFIX + module
        target = source_path(target_module)
        if args.apply:
            write_atomic(target, packaged)
        rows.append({'original_module': module, 'submission_module': target_module,
                     'original_sha256': hashlib.sha256(original).hexdigest(),
                     'submission_sha256': hashlib.sha256(packaged).hexdigest(),
                     'proof_body_preserved': True, 'dependencies': dependencies})
        if not args.module:
            queue.extend(dependencies)
        if len(rows) % 5000 == 0:
            print(json.dumps({'processed': len(rows), 'queued': len(queue), 'apply': args.apply}), flush=True)
    payload = {'at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'supplier': 'anthropics/fermats-last-theorem',
               'supplier_commit': '6e837e75355538c7f80bab5b956861e86c4eacc2',
               'official_mathlib': '5e0c4e5239cb0a2d86d68a884bf52cfd963fce22',
               'toolchain': 'leanprover/lean4:v4.35.0-rc3',
               'elaborator_options': OPTIONS,
               'generated_instance_renames': INSTANCE_RENAMES,
               'applied': args.apply, 'proofs_compiled_in_this_step': False,
               'source_count': len(rows), 'rows': rows}
    manifest = evidence / ('manifest.json' if not args.module else 'last-module-sync.json')
    write_atomic(manifest, (json.dumps(payload, indent=2) + '\n').encode())
    print(json.dumps({k: v for k, v in payload.items() if k != 'rows'}), flush=True)


if __name__ == '__main__':
    main()
