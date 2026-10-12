#!/usr/bin/env python3
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: ReasBook team
"""List explicit sorry placeholders without invoking Lean or Lake.

This is a source inventory, not a parser, compiler, or proof certificate.
Comments, ordinary string literals, and escaped identifiers are skipped.
"""
from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from pathlib import Path

TOKEN = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\])*"|«[^»]*»|(?<![\w\'])sorry(?![\w\'])')
COMMENT = re.compile(r'/-|-/')


def sorry_locations(text: str) -> list[int]:
    positions = []
    pos = 0
    while match := TOKEN.search(text, pos):
        token = match.group()
        pos = match.end()
        if token == '/-':
            depth = 1
            while depth and (marker := COMMENT.search(text, pos)):
                depth += 1 if marker.group() == '/-' else -1
                pos = marker.end()
            if depth:
                break
        elif token == 'sorry':
            positions.append(match.start())
    lines = []
    last_pos, line = 0, 1
    for pos in positions:
        line += text.count('\n', last_pos, pos)
        lines.append(line)
        last_pos = pos
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path('docs'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output_dir if args.output_dir.is_absolute() else root / args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    stats = Counter()
    for prefix in ('ReasLib', 'stacks_project', 'M2FQualityAudits'):
        for path in sorted((root / prefix).rglob('*.lean')):
            lines = sorry_locations(path.read_text(encoding='utf-8'))
            stats[f'{prefix}_lean_files'] += 1
            stats['lean_files'] += 1
            if lines:
                stats['files_with_explicit_sorry'] += 1
                stats['explicit_sorry_occurrences'] += len(lines)
                rows.append((path.relative_to(root).as_posix(), len(lines), lines[0]))
    # Include the imported root modules in the source-file total.
    for path in sorted(root.glob('*.lean')):
        lines = sorry_locations(path.read_text(encoding='utf-8'))
        stats['lean_files'] += 1
        if lines:
            stats['files_with_explicit_sorry'] += 1
            stats['explicit_sorry_occurrences'] += len(lines)
            rows.append((path.name, len(lines), lines[0]))
    with (output / 'proof-debt.tsv').open('w', encoding='utf-8', newline='') as handle:
        writer = csv.writer(handle, delimiter='\t', lineterminator='\n')
        writer.writerow(('file', 'explicit_sorry_count', 'first_sorry_line'))
        writer.writerows(sorted(rows))
    result = {
        'method': 'Lexical source scan; comments, strings and escaped identifiers skipped.',
        'local_compilation_performed': False,
        'counts': dict(stats),
        'limitations': 'No elaboration or transitive axiom analysis. Absence of explicit sorry is not proof certification.',
    }
    (output / 'source-inventory.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
