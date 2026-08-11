#!/usr/bin/env python3
"""
Configuration-differential tester for tamarin-prover.

Every option below is documented as affecting only HOW the proof search runs,
never WHAT is true:

  --heuristic     goal ranking (order only)
  --stop-on-trace search strategy
  -s / -c         precomputation saturation / open-chain limits
  -d              derivation-check timeout
  --auto-sources  generates helper sources lemmas

So for a fixed theory, every configuration must agree on every lemma's
verdict. Any lemma where one configuration says `verified` and another says
`falsified` is a soundness bug, with no need to know the right answer.

Verdicts that are neither verified nor falsified (incomplete, timeout,
bound reached) are ignored: those are termination differences, which are
expected and legitimate.
"""
import subprocess, sys, re, os, json
from concurrent.futures import ThreadPoolExecutor

TAMARIN = os.environ.get("TAMARIN", "tamarin-prover")
TIMEOUT = int(os.environ.get("TIMEOUT", "300"))
JOBS = int(os.environ.get("JOBS", "4"))

SUMMARY = re.compile(
    r"^\s{2}(\S+)\s*\((all-traces|exists-trace)\):\s*(verified|falsified|analysis incomplete)",
    re.M)

CONFIGS = {
    "base":     [],
    "heur_S":   ["--heuristic=S"],
    "heur_c":   ["--heuristic=c"],
    "heur_C":   ["--heuristic=C"],
    "heur_i":   ["--heuristic=i"],
    "heur_I":   ["--heuristic=I"],
    "heur_p":   ["--heuristic=p"],
    "heur_P":   ["--heuristic=P"],
    "bfs":      ["--stop-on-trace=BFS"],
    "seqdfs":   ["--stop-on-trace=SEQDFS"],
    "sat1":     ["-s=1"],
    "sat10":    ["-s=10"],
    "oc3":      ["-c=3"],
    "oc20":     ["-c=20"],
    "noderiv":  ["-d=0"],
    "autosrc":  ["--auto-sources"],
}


def run_one(args):
    path, cfg, flags = args
    cmd = [TAMARIN, "--prove"] + flags + [path]
    if "--diff" in open(path, errors="ignore").read()[:400]:
        pass
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return path, cfg, None
    res = {}
    for name, quant, verdict in SUMMARY.findall(out):
        res[name] = verdict
    return path, cfg, res


def main():
    files = sys.argv[1:]
    if not files:
        print("usage: differ.py FILE...", file=sys.stderr)
        return 2

    tasks = [(f, cfg, flags) for f in files for cfg, flags in CONFIGS.items()]
    results = {}
    done = 0
    with ThreadPoolExecutor(max_workers=JOBS) as ex:
        for path, cfg, res in ex.map(run_one, tasks):
            results.setdefault(path, {})[cfg] = res
            done += 1
            print(f"\r  {done}/{len(tasks)} runs", end="", file=sys.stderr, flush=True)
    print("", file=sys.stderr)

    disagreements = []
    for path, byconf in sorted(results.items()):
        base = byconf.get("base")
        if not base:
            continue
        lemmas = set()
        for res in byconf.values():
            if res:
                lemmas |= set(res)
        for lem in sorted(lemmas):
            seen = {}
            for cfg, res in byconf.items():
                if not res:
                    continue
                v = res.get(lem)
                if v in ("verified", "falsified"):
                    seen.setdefault(v, []).append(cfg)
            if len(seen) > 1:
                disagreements.append((path, lem, seen))

    print()
    print("=" * 78)
    if not disagreements:
        print("NO VERDICT DISAGREEMENTS across %d configurations" % len(CONFIGS))
    else:
        print("%d VERDICT DISAGREEMENT(S) FOUND" % len(disagreements))
        for path, lem, seen in disagreements:
            print()
            print(f"  file : {path}")
            print(f"  lemma: {lem}")
            for v, cfgs in seen.items():
                print(f"    {v:<10} <- {', '.join(sorted(cfgs))}")
    print("=" * 78)

    with open("/tmp/tamdeep/differ_results.json", "w") as f:
        json.dump(results, f, indent=1)
    print("raw results: /tmp/tamdeep/differ_results.json")
    return 1 if disagreements else 0


if __name__ == "__main__":
    sys.exit(main())
