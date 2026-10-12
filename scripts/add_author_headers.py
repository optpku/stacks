#!/usr/bin/env python3
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: ReasBook team
"""Add publication license and author credits while preserving existing source bodies.

Author credits can be updated to reflect individual contributions.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

LEAN_HEADER = b'/-\nReleased under Apache 2.0 license as described in the file LICENSE.\nStatement formalization authors: ReasBook team\nProof formalization authors: ReasBook team\n-/\n\n'
PYTHON_HEADER = b'# Released under Apache 2.0 license as described in the file LICENSE.\n# Authors: ReasBook team\n'


def main():
    root = Path(__file__).resolve().parents[1]
    manifest_path = root / 'docs/import-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    imported = {entry['path']: entry for entry in manifest['files']}
    paths = sorted(root.glob('*.lean'))
    for prefix in ('ReasLib', 'stacks_project', 'M2FQualityAudits'):
        paths.extend(sorted((root / prefix).rglob('*.lean')))
    records = []
    for path in paths:
        relative = path.relative_to(root).as_posix()
        source = path.read_bytes()
        # Leave later personalized credits intact; never rewrite existing notices.
        if source.startswith(b'/-\n') and b'Statement formalization authors:' in source.split(b'-/', 1)[0]:
            continue
        original_hash = hashlib.sha256(source).hexdigest()
        if relative in imported and original_hash != imported[relative]['sha256']:
            raise ValueError(f'Source differs from import manifest: {relative}')
        published = LEAN_HEADER + source
        path.write_bytes(published)
        assert path.read_bytes()[len(LEAN_HEADER):] == source
        records.append({'path': relative, 'original_sha256': original_hash,
                        'published_sha256': hashlib.sha256(published).hexdigest(),
                        'added_header_bytes': len(LEAN_HEADER)})
    for path in sorted((root / 'scripts').rglob('*.py')):
        source = path.read_bytes()
        if b'# Authors:' in b'\n'.join(source.splitlines()[:6]):
            continue
        if source.startswith(b'#!'):
            first, separator, body = source.partition(b'\n')
            published = first + separator + PYTHON_HEADER + body
        else:
            published = PYTHON_HEADER + source
        path.write_bytes(published)
    if records:
        (root / 'docs/author-header-manifest.json').write_text(json.dumps({
            'modification': 'Prepended Apache-2.0 license and author-credit block comments; original imported Lean bytes preserved after the header.',
            'statement_formalization_authors': 'ReasBook team',
            'proof_formalization_authors': 'ReasBook team',
            'lean_files_modified': len(records),
            'local_compilation_performed': False,
            'files': records,
        }, indent=2) + '\n')
        manifest['lean_sources_modified'] = True
        manifest['publication_modifications'] = 'Author-credit block comments prepended; original source bodies and dependency pins preserved. Original files entries describe the remote import, not the modified publication bytes.'
        manifest['author_header_manifest'] = 'author-header-manifest.json'
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'lean_headers_added': len(records), 'python_files': len(list((root/'scripts').rglob('*.py')))}))


if __name__ == '__main__':
    main()
