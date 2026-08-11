#!/usr/bin/env python3
"""
Observational equivalence is symmetric: P ~ Q iff Q ~ P.

For a --diff theory, swapping the arguments of every diff(x,y) term yields a
theory stating exactly the mirrored equivalence. Tamarin's verdict must be
identical. Any file where the original and the swapped version disagree
(verified vs falsified) is a bug, with no need to know which answer is right.

Usage: diffsym.py FILE...
"""
import subprocess, sys, re, os

TAMARIN = os.environ.get("TAMARIN", "tamarin-prover")
TIMEOUT = int(os.environ.get("TIMEOUT", "600"))
OUT = "/tmp/tamdeep/swapped"

VERDICT = re.compile(r"DiffLemma:\s*(\S+)\s*:\s*(verified|falsified|analysis incomplete)")


def split_top_comma(s):
    """Split 'a, b' at the top-level comma, respecting nesting of ()<>[]."""
    depth = 0
    for i, ch in enumerate(s):
        if ch in "(<[":
            depth += 1
        elif ch in ")>]":
            depth -= 1
        elif ch == "," and depth == 0:
            return s[:i], s[i + 1:]
    return None


def swap_diffs(src):
    """Rewrite every diff(x,y) as diff(y,x). Returns (text, count)."""
    out = []
    i = 0
    count = 0
    while True:
        m = re.compile(r"\bdiff\s*\(").search(src, i)
        if not m:
            out.append(src[i:])
            break
        out.append(src[i:m.start()])
        # find the matching close paren
        depth = 0
        j = m.end() - 1
        while j < len(src):
            if src[j] in "(<[":
                depth += 1
            elif src[j] in ")>]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        inner = src[m.end():j]
        parts = split_top_comma(inner)
        if parts is None:
            out.append(src[m.start():j + 1])
        else:
            a, b = parts
            out.append(f"diff({b.strip()}, {a.strip()})")
            count += 1
        i = j + 1
    return "".join(out), count


def run(path):
    try:
        p = subprocess.run([TAMARIN, "--prove", "--diff", path],
                           capture_output=True, text=True, timeout=TIMEOUT)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return {"__timeout__": "timeout"}
    if "error" in out.lower() and not VERDICT.search(out):
        first = [l for l in out.splitlines() if l.strip()][:3]
        return {"__error__": " / ".join(first)}
    return {name: v for name, v in VERDICT.findall(out)}


def main():
    files = sys.argv[1:]
    os.makedirs(OUT, exist_ok=True)
    disagree = []
    for f in files:
        src = open(f, errors="ignore").read()
        swapped, n = swap_diffs(src)
        if n == 0:
            print(f"SKIP  {f}  (no diff() terms)")
            continue
        base = os.path.basename(f).replace(".spthy", "")
        # theory name must stay unique
        swapped = re.sub(r"^theory\s+(\S+)", r"theory \1_swapped", swapped, count=1, flags=re.M)
        sp = os.path.join(OUT, base + "_swapped.spthy")
        with open(sp, "w") as fh:
            fh.write(swapped)
        a = run(f)
        b = run(sp)
        keys = set(a) | set(b)
        bad = False
        for k in keys:
            va, vb = a.get(k, "missing"), b.get(k, "missing")
            if va in ("verified", "falsified") and vb in ("verified", "falsified") and va != vb:
                bad = True
        tag = "*** ASYMMETRY ***" if bad else "ok"
        print(f"{tag:<18} {f}  ({n} diff terms)")
        print(f"                   original: {a}")
        print(f"                   swapped : {b}")
        if bad:
            disagree.append((f, sp, a, b))
    print()
    print("=" * 70)
    if disagree:
        print(f"{len(disagree)} ASYMMETRIC RESULT(S):")
        for f, sp, a, b in disagree:
            print(f"  {f}\n    orig={a}\n    swap={b}\n    swapped file: {sp}")
    else:
        print("no asymmetries")
    return 1 if disagree else 0


if __name__ == "__main__":
    sys.exit(main())
