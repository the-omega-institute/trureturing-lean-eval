#!/usr/bin/env python3
"""Archive an existing FLT receipt manifest without touching the source index."""
import argparse
import base64
import concurrent.futures
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess


REPOSITORY = 'the-omega-institute/trureturing-lean-eval'
CHECKOUT = Path('/Users/macstudio/omega/research/lean-eval-01a124c1-52fb-7761-a67c-75fc0610196f/flt-source-checkpoint')
BRANCH = 'checkpoint/flt-canonical-progress-01a124be-20261015-r16'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def git(args, data=None, env=None):
    return subprocess.run(['git', '-C', str(CHECKOUT), *args], input=data,
        capture_output=True, env=env, check=True).stdout.decode().strip()


def api(path):
    return json.loads(subprocess.run(['gh', 'api', 'repos/' + REPOSITORY + '/' + path],
        capture_output=True, check=True).stdout)


def owner_index():
    path = Path(git(['rev-parse', '--git-path', 'index']))
    return path if path.is_absolute() else CHECKOUT / path


def entries_for(archive, manifest):
    entries = list(manifest['files'])
    prefixes = {str(Path(row['path']).parent) for row in entries}
    assert len(prefixes) == 1, 'Use one receipt directory per manifest.'
    path = archive / 'manifest.json'
    entries.append(dict(path=prefixes.pop() + '/manifest.json', local_path=str(path),
        sha256=digest(path.read_bytes()), bytes=path.stat().st_size))
    assert len({row['path'] for row in entries}) == len(entries)
    for row in entries:
        data = Path(row['local_path']).read_bytes()
        assert len(data) == row['bytes'] and digest(data) == row['sha256'], row['path']
    return entries


def push_archive(archive, manifest, entries):
    parent = manifest['previous_archive_commit']
    assert git(['rev-parse', 'refs/heads/' + BRANCH]) == parent
    head, index_hash = git(['rev-parse', 'HEAD']), digest(owner_index().read_bytes())
    env = dict(os.environ, GIT_INDEX_FILE=str(archive / 'isolated.index'))
    git(['read-tree', parent], env=env)
    updates, blobs = [], {}
    for row in entries:
        oid = git(['hash-object', '-w', '--stdin'], Path(row['local_path']).read_bytes())
        blobs[row['path']] = oid
        updates.append('100644 ' + oid + '\t' + row['path'] + '\n')
    git(['update-index', '--index-info'], ''.join(updates).encode(), env)
    tree = git(['write-tree'], env=env)
    message = manifest['commit_message'].rstrip() + '\n'
    commit = git(['commit-tree', tree, '-p', parent], message.encode())
    git(['update-ref', 'refs/heads/' + BRANCH, commit, parent])
    pushed = subprocess.run(['git', '-C', str(CHECKOUT), 'push', 'origin',
        commit + ':refs/heads/' + BRANCH], capture_output=True, text=True)
    result = dict(pushed_at=now(), commit=commit, tree=tree, branch=BRANCH, parent=parent,
        push_exit=pushed.returncode, push_stdout=pushed.stdout, push_stderr=pushed.stderr,
        owner_head_before=head, owner_index_sha256_before=index_hash,
        owner_head_unchanged=git(['rev-parse', 'HEAD']) == head,
        owner_real_index_unchanged=digest(owner_index().read_bytes()) == index_hash,
        files=[row['path'] for row in entries], blob_map=blobs,
        url='https://github.com/' + REPOSITORY + '/commit/' + commit)
    write(archive / 'pushed.json', result)
    assert pushed.returncode == 0, pushed.stderr
    assert result['owner_head_unchanged'] and result['owner_real_index_unchanged']
    return result


def verify_remote(archive, manifest, entries, pushed):
    commit = pushed['commit']
    assert pushed['push_exit'] == 0
    assert api('git/ref/heads/' + BRANCH)['object']['sha'] == commit
    remote = api('git/commits/' + commit)
    assert remote['tree']['sha'] == pushed['tree']
    assert [p['sha'] for p in remote['parents']] == [pushed['parent']]

    def fetch(row):
        remote = api('contents/' + row['path'] + '?ref=' + commit)
        assert remote['encoding'] == 'base64'
        assert remote['sha'] == pushed['blob_map'][row['path']]
        data = base64.b64decode(remote['content'])
        assert data == Path(row['local_path']).read_bytes()
        assert len(data) == row['bytes'] and digest(data) == row['sha256']
        return dict(path=row['path'], blob=remote['sha'], sha256=digest(data),
            bytes=len(data)), data

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        downloaded = list(pool.map(fetch, entries))
    raw_count, invocations = 0, 0
    for row, data in downloaded:
        if Path(row['path']).name.startswith('canonical-evidence-'):
            raw = json.loads(data)
            invocations += len(raw['invocations'])
            for invocation in raw['invocations']:
                for item in invocation['files']:
                    content = item['utf8_text'].encode('utf-8')
                    assert len(content) == item['bytes'] and digest(content) == item['sha256']
                    raw_count += 1
    assert raw_count == manifest['exact_terminal_configuration_and_log_files_embedded']
    assert invocations == manifest['canonical_invocations']
    result = dict(verified_at=now(), repository=REPOSITORY, branch=BRANCH, commit=commit,
        previous_commit=pushed['parent'], remote_branch_sha_verified=True,
        remote_commit_tree_and_parent_verified=True,
        remote_files_downloaded_and_byte_verified=[row for row, _ in downloaded],
        embedded_raw_files_sha256_verified=raw_count,
        owner_head_unchanged=git(['rev-parse', 'HEAD']) == pushed['owner_head_before'],
        owner_real_index_unchanged=digest(owner_index().read_bytes()) == pushed['owner_index_sha256_before'],
        shared_sources_edited_by_this_archiver=False, url=pushed['url'],
        full_original_or_official_acceptance=False)
    write(archive / 'remote-verified.json', result)
    assert result['owner_head_unchanged'] and result['owner_real_index_unchanged']
    (archive / 'isolated.index').unlink(missing_ok=True)
    print(json.dumps(dict(commit=commit, url=result['url'],
        remote_files_byte_verified=len(downloaded), embedded_raw_files_verified=raw_count,
        canonical_invocations=invocations, owner_head_and_index_unchanged=True,
        full_original_or_official_acceptance=False), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path)
    args = parser.parse_args()
    archive = args.archive.resolve()
    manifest = read(archive / 'manifest.json')
    entries = entries_for(archive, manifest)
    pushed_path = archive / 'pushed.json'
    pushed = read(pushed_path) if pushed_path.exists() else push_archive(archive, manifest, entries)
    verify_remote(archive, manifest, entries, pushed)


if __name__ == '__main__':
    main()
