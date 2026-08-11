#!/usr/bin/env python3
"""
Scope scanner for the `last()` unsoundness (attacks/01, attacks/02).

The bug requires `last()` to appear in a RESTRICTION. This script classifies
every occurrence of `last(` across a corpus of .spthy files as being inside a
restriction/axiom, inside a lemma, or elsewhere, so the practical impact can
be stated accurately instead of guessed.

Result on tamarin-prover develop @ ef3f0468, over examples/ (1042 files):

    files containing 'last('        : 36
    occurrences in restrictions     : 0
    occurrences in lemma blocks     : 36 files

and manual inspection of those 36 shows the hits are inside Tamarin's own
machine-generated proof text saved into analyzed outputs, e.g.

    solve( (last(#i)) | (Ex #j. Update(k,r) @ #j & !(last(#j)) & #j < #i) )

not user-written syntax. Conclusion: no shipped case study is affected.

Usage:
    python3 lastscan.py [ROOT]        # default ROOT = ../../examples
"""
import re
import sys
import os
import glob

DEFAULT_ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "..", "..", "examples")

# Top-level theory keywords. A `last(` occurrence is attributed to the block
# opened by the nearest preceding keyword.
KW = re.compile(r"^\s*(restriction|axiom|lemma|rule|process|end)\b", re.M)


def classify(path):
    """Yield (kind, first_line_of_block) for each block containing 'last('."""
    try:
        src = open(path, errors="ignore").read()
    except OSError:
        return
    if "last(" not in src:
        return
    marks = [(m.start(), m.group(1)) for m in KW.finditer(src)]
    marks.append((len(src), "EOF"))
    for i in range(len(marks) - 1):
        start, kind = marks[i]
        end = marks[i + 1][0]
        seg = src[start:end]
        if "last(" in seg:
            yield kind, seg.strip().split("\n")[0][:80]


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_ROOT
    files = glob.glob(os.path.join(root, "**", "*.spthy"), recursive=True)
    if not files:
        print(f"no .spthy files under {root}", file=sys.stderr)
        return 2

    with_last, in_restriction, in_lemma, other = set(), [], set(), []
    for f in files:
        hits = list(classify(f))
        if hits:
            with_last.add(f)
        for kind, head in hits:
            rel = os.path.relpath(f, root)
            if kind in ("restriction", "axiom"):
                in_restriction.append((rel, head))
            elif kind == "lemma":
                in_lemma.add(rel)
            else:
                other.append((rel, kind))

    print(f"scanned                      : {len(files)} .spthy files under {root}")
    print(f"files containing 'last('     : {len(with_last)}")
    print(f"occurrences in RESTRICTIONS  : {len(in_restriction)}   <-- the only ones that can trigger the bug")
    print(f"files with 'last(' in lemmas : {len(in_lemma)}")
    print(f"other/unclassified           : {len(other)}")
    if in_restriction:
        print("\nRESTRICTIONS USING last() -- these WOULD be affected:")
        for rel, head in sorted(set(in_restriction)):
            print(f"  {rel}\n    {head}")
    else:
        print("\nNo restriction anywhere in the corpus uses last().")
        print("=> no shipped case study is affected by attacks/01 and attacks/02.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
