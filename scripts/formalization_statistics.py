#!/usr/bin/env python3
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: ReasBook team
"""Generate static source statistics without invoking Lean or Lake.

Counts explicit declaration commands, not elaborated declarations or certificates.
"""
from __future__ import annotations

import argparse
import collections
import csv
import json
from pathlib import Path
import re

TOKEN = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\])*"|«[^»]*»')
COMMENT = re.compile(r'/-|-/')
DECL = re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)[ \t]+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)\b', re.M)
HOLE = re.compile(r"(?<![\w'])\b(sorry|admit)\b(?![\w'])")
TAG = re.compile(r'@\[[^\]]*\bstacks\s+([0-9A-Z]{4})\b')

def clean(text):
    parts = []
    pos = 0
    for_unused = None
    while match := TOKEN.search(text, pos):
        start, end = match.span()
        parts.append(text[pos:start])
        if match.group() == '/-':
            depth = 1
            while depth:
                marker = COMMENT.search(text, end)
                if marker is None:
                    end = len(text)
                    break
                depth += 1 if marker.group() == '/-' else -1
                end = marker.end()
        elif match.group().startswith('«'):
            # Escaped identifiers are identifiers, never hole keywords.
            parts.append('I' * (end - start))
            pos = end
            continue
        fragment = text[start:end]
        parts.append(re.sub(r'[^\n]', ' ', fragment))
        pos = end
    parts.append(text[pos:])
    return ''.join(parts)


def measures(text):
    code = clean(text)
    declarations = list(DECL.finditer(code))
    holes = list(HOLE.finditer(code))
    result = collections.Counter(lean_files=1, declarations=len(declarations),
                                 explicit_placeholders=len(holes))
    j = 0
    for i, declaration in enumerate(declarations):
        end = declarations[i + 1].start() if i + 1 < len(declarations) else len(code)
        while j < len(holes) and holes[j].start() < declaration.start():
            j += 1
        unfinished = j < len(holes) and holes[j].start() < end
        result['declarations_with_explicit_placeholder'] += int(unfinished)
        result['declarations_without_explicit_placeholder'] += int(not unfinished)
        kind = declaration.group(1)
        if kind in ('theorem', 'lemma', 'example'):
            result['proof_commands'] += 1
            result['proof_commands_with_explicit_placeholder'] += int(unfinished)
            result['proof_commands_without_explicit_placeholder'] += int(not unfinished)
        result['axiom_commands'] += int(kind == 'axiom')
    return result, set(TAG.findall(code))


FIELDS = ('lean_files', 'unique_stacks_tags', 'declarations',
          'declarations_without_explicit_placeholder', 'declarations_with_explicit_placeholder',
          'proof_commands', 'proof_commands_without_explicit_placeholder',
          'proof_commands_with_explicit_placeholder', 'explicit_placeholders', 'axiom_commands')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path('docs'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output_dir if args.output_dir.is_absolute() else root / args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    totals = collections.Counter()
    regions = collections.defaultdict(collections.Counter)
    chapters = {n: collections.Counter() for n in range(1, 112)}
    region_tags = collections.defaultdict(set)
    chapter_tags = collections.defaultdict(set)
    all_tags = set()
    chapter_support = collections.Counter()
    chapter_support_tags = set()
    group_counts = collections.defaultdict(collections.Counter)
    group_tags = collections.defaultdict(set)
    paths = sorted(root.glob('*.lean'))
    for prefix in ('ReasLib', 'stacks_project', 'M2FQualityAudits'):
        paths.extend(sorted((root / prefix).rglob('*.lean')))
    for path in paths:
        counts, tags = measures(path.read_text(encoding='utf-8'))
        totals.update(counts)
        all_tags.update(tags)
        relative = path.relative_to(root)
        region = relative.parts[0] if len(relative.parts) > 1 else 'Root modules'
        regions[region].update(counts)
        region_tags[region].update(tags)
        if region == 'stacks_project':
            match = re.fullmatch(r'Chap(\d+)', relative.parts[1])
            if match:
                chapter = int(match[1])
                chapters.setdefault(chapter, collections.Counter()).update(counts)
                chapter_tags[chapter].update(tags)
                group = "01–26" if chapter <= 26 else "27–34" if chapter <= 34 else "35–111"
                group_counts[group].update(counts)
                group_tags[group].update(tags)
            else:
                chapter_support.update(counts)
                chapter_support_tags.update(tags)
    def row(counts, tags):
        return {field: len(tags) if field == 'unique_stacks_tags' else counts[field]
                for field in FIELDS}
    result = {
        'method': 'Static Lean source scan; nested comments, strings and escaped identifiers excluded. Counts explicit declaration commands and theorem/lemma/example commands.',
        'limitations': 'No elaboration, compilation, source correspondence review or transitive axiom analysis. Placeholder-free commands are proof candidates, not verified completed proofs. #check bridges do not add declarations. Chapter counts cover chapter-local source only; proofs moved to ReasLib appear in the library totals. Tags are deduplicated per scope and are not necessarily additive.',
        'local_compilation_performed': False,
        'total': row(totals, all_tags),
        'regions': {name: row(counts, region_tags[name]) for name, counts in sorted(regions.items())},
        'chapter_support_modules': row(chapter_support, chapter_support_tags),
        'chapter_groups': {name: row(counts, group_tags[name]) for name, counts in sorted(group_counts.items())},
        'chapters': [{'chapter': n, **row(counts, chapter_tags[n])} for n, counts in sorted(chapters.items())],
    }
    (output / 'formalization-statistics.json').write_text(json.dumps(result, indent=2) + '\n')
    with (output / 'chapter-statistics.tsv').open('w', encoding='utf-8', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=('chapter', *FIELDS), delimiter='\t', lineterminator='\n')
        writer.writeheader()
        writer.writerows(result['chapters'])
    print(json.dumps(result['total'], indent=2))


if __name__ == '__main__':
    main()
