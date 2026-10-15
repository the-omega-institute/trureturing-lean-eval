#!/usr/bin/env python3
"""Read existing canonical results; never launch Lean or change its sources."""
import datetime
import json
from pathlib import Path

repairs = Path(__file__).resolve().parent
helper = repairs / 'verify-neben-transfer-r5.py'
namespace = {'__file__': str(helper)}
definitions = helper.read_text().split(
    "\nassert sha(path(src, module, '.lean')) == expected")[0]
exec(compile(definitions, str(helper), 'exec'), namespace)
verify = namespace['verify']
state = namespace['state']
source_path = lambda module: namespace['path'](namespace['src'], module, '.lean')

for name in (
    'AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero',
    'AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact',
):
    module = 'Submission.Supplier.P2M.Sol.S_' + name
    card_module = 'Submission.Supplier.Theorems.Thm_' + name
    accepted_path = repairs / ('S_' + name + '-r1-accepted.json')
    if accepted_path.exists():
        print('Preserved accepted receipt:', accepted_path)
        continue
    preparations = [json.loads((repairs / (prefix + name + '-r1-repair.json')).read_text())
                    for prefix in ('S_', 'Thm_')]
    if not all(state['records'].get(mod, {}).get('exit') == 0
               and state['records'][mod]['sha256'] == preparation['candidate_sha256']
               for mod, preparation in zip((module, card_module), preparations)):
        print('Pending original controller:', name)
        continue
    source = verify(module)
    card = verify(card_module)
    for mod, preparation, start in zip(
            (module, card_module), preparations,
            ('theorem solution', 'theorem AutomorphicForm.')):
        baseline = Path(preparation['baseline']).read_text()
        current = source_path(mod).read_text()
        tail = lambda text: text[text.index(start):].split('#print axioms')[0].strip()
        assert tail(baseline) == tail(current), mod
    binding = next(item for item in card['direct_dependency_checks'] if item['module'] == module)
    assert binding['source_sha256'] == source['source_sha256']
    assert binding['object_sha256'] == source['object_sha256']
    accepted = dict(
        source, candidate_revision='r1-accepted',
        accepted_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        accepted_source_sha256=source['source_sha256'],
        accepted_object_sha256=source['object_sha256'], card_validation=card,
        proof_checks=dict(threads=1, trust=0, skipKernelTC=False),
        public_statement_and_proof_body_preserved=True,
        repair_scope='Three attribute names changed from _definitions to _submission; recursive axiom prints added.',
        source_owner_git_index_touched=False,
        full_original_proof_verified=False, official_solve_credit=0)
    with accepted_path.open('x') as handle:
        json.dump(accepted, handle, indent=2)
        handle.write('\n')
    print('Verified source and card:', accepted_path)
