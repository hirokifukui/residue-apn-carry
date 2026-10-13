#!/usr/bin/env python3
"""check_blueprint.py -- verify BLUEPRINT.md against a release tree.

usage: python3 -I -B tools/check_blueprint.py ROOT [--paper-dir DIR] [--labels-file FILE] [--blueprint FILE]

Label source (at least one is used):
  --paper-dir DIR    TeX sources; every \\label{...} in DIR/*.tex counts (default: ROOT/paper if it exists);
  --labels-file FILE tab-separated "label<TAB>number" (generated from the .aux of the build that the reader has);
                     with it, the "no." column of every row must also equal the printed number.
Relative paths are taken from the current directory.
Checks every table row: the label exists; every Lean entry Module.decl names ROOT/lean/ApnCipher/Module.lean
declaring `decl`; every finite entry names an existing file under ROOT; kind is one of paper, paper+lean,
lean-negative. Exit 0 = all rows pass; 1 = any failure, no rows, or no label source.
"""
import pathlib, re, sys


def parse(argv):
    root, opts, i = None, {}, 1
    while i < len(argv):
        a = argv[i]
        if a in ('--paper-dir', '--labels-file', '--blueprint'):
            opts[a] = argv[i + 1]; i += 2
        elif root is None:
            root = a; i += 1
        else:
            sys.exit('usage: check_blueprint.py ROOT [--paper-dir DIR] [--labels-file FILE] [--blueprint FILE]')
    if root is None:
        sys.exit('usage: check_blueprint.py ROOT [--paper-dir DIR] [--labels-file FILE] [--blueprint FILE]')
    return pathlib.Path(root), opts


root, opts = parse(sys.argv)
bp = pathlib.Path(opts.get('--blueprint', root / 'BLUEPRINT.md'))
labels, numbers, sources = set(), {}, []
pdir = pathlib.Path(opts['--paper-dir']) if '--paper-dir' in opts else (root / 'paper')
if pdir.is_dir() and list(pdir.glob('*.tex')):
    tex = ''.join(p.read_text(encoding='utf-8') for p in sorted(pdir.glob('*.tex')))
    labels |= set(re.findall(r'\\label\{([^}]*)\}', tex))
    sources.append('tex:%s' % pdir)
elif '--paper-dir' in opts:
    print('FAIL paper-dir has no .tex files:', pdir)
    sys.exit(1)
if '--labels-file' in opts:
    lf = pathlib.Path(opts['--labels-file'])
    if not lf.is_file():
        print('FAIL labels-file missing:', lf); sys.exit(1)
    for line in lf.read_text(encoding='utf-8').splitlines():
        if line and not line.startswith('#'):
            lab, _, num = line.partition('\t')
            labels.add(lab); numbers[lab] = num
    sources.append('labels:%s' % lf)
if not sources:
    print('FAIL no label source (give --paper-dir or --labels-file)'); sys.exit(1)
fails, rows = [], 0
for line in bp.read_text(encoding='utf-8').splitlines():
    if not line.startswith('| ') or line.startswith('| label') or line.startswith('|---'):
        continue
    cells = [c.strip() for c in line.strip('|').split('|')]
    if len(cells) != 7:
        fails.append(('malformed', line)); continue
    rows += 1
    label, no, _, lean, _, finite, kind = cells
    if not label.startswith('('):
        if label not in labels:
            fails.append(('label', label))
        elif numbers and no != '-' and numbers.get(label) != no:
            fails.append(('number', '%s: blueprint %s, paper %s' % (label, no, numbers.get(label))))
    if lean != '-':
        for ent in [e.strip() for e in lean.split(';')]:
            mod, _, decl = ent.partition('.')
            f = root / 'lean' / 'ApnCipher' / (mod + '.lean')
            if not f.is_file():
                fails.append(('lean_file', ent)); continue
            if not re.search(r'^(theorem|lemma|def|structure|noncomputable def|abbrev)\s+' + re.escape(decl) + r'\b',
                             f.read_text(encoding='utf-8'), re.M):
                fails.append(('lean_decl', ent))
    if finite != '-':
        for ent in [e.strip() for e in finite.split(';')]:
            if not (root / ent).is_file():
                fails.append(('finite_file', ent))
    if kind not in ('paper', 'paper+lean', 'lean-negative'):
        fails.append(('kind', kind))
print('BLUEPRINT rows=%d failures=%d labels_from=%s' % (rows, len(fails), ','.join(sources)))
for f in fails:
    print('FAIL', *f)
sys.exit(1 if fails or rows == 0 else 0)
