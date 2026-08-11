#!/usr/bin/env python3
"""
Consistency oracle aimed at stateful protocols: injective fact instances,
monotonic state, SAPIC state cells and locks.

Same invariant as oracle.py: in one theory,
    lemma all_phi   : all-traces   phi
    lemma ex_notphi : exists-trace not phi
must disagree. verified/verified or falsified/falsified is a self-contradiction.
"""
import subprocess, sys, re, os, textwrap

TAMARIN = os.environ.get("TAMARIN", "tamarin-prover")
TIMEOUT = int(os.environ.get("TIMEOUT", "180"))
OUT = "/tmp/tamdeep/gen2"
SUMMARY = re.compile(r"^\s{2}(\w+)\s*\((?:all-traces|exists-trace)\):\s*(.+?)\s*$", re.M)


def verdict(text, name):
    for n, v in SUMMARY.findall(text):
        if n == name:
            return "verified" if v.startswith("verified") else \
                   "falsified" if v.startswith("falsified") else v
    return "missing"


CASES = []


def case(name, body, phi, notphi, liveness, flags=()):
    CASES.append((name, body, phi, notphi, liveness, list(flags)))


# ---- injective fact, constant position, two independent threads -------------
case("inj_const_two_threads", """
rule Create: [ Fr(id), Fr(v) ] --[ Create(id, v) ]-> [ S(id, v, 'c') ]
rule Step:   [ S(id, v, c) ] --[ Step(id, v) ]-> [ S(id, v, c) ]
rule Reveal: [ S(id, v, c) ] --[ Rev(id, v) ]-> [ Out(v) ]
""",
     phi="All id1 id2 v1 v2 #i #j. Create(id1,v1) @ i & Create(id2,v2) @ j & not(#i = #j) ==> not(v1 = v2)",
     notphi="Ex id1 id2 v1 v2 #i #j. Create(id1,v1) @ i & Create(id2,v2) @ j & not(#i = #j) & v1 = v2",
     liveness="Ex id v #i. Create(id, v) @ i")

# ---- injective fact, strictly increasing position ---------------------------
case("inj_strict_incr", """
rule Create: [ Fr(id), Fr(a) ] --[ Create(id, a) ]-> [ S(id, a) ]
rule Grow:   [ S(id, a), Fr(b) ] --[ Grow(id, a, b) ]-> [ S(id, <a, b>) ]
rule Out1:   [ S(id, a) ] --[ Emit(id, a) ]-> [ Out(a) ]
""",
     phi="All id a b #i #j. Emit(id,a) @ i & Emit(id,b) @ j & #i < #j ==> not(a = b)",
     notphi="Ex id a b #i #j. Emit(id,a) @ i & Emit(id,b) @ j & #i < #j & a = b",
     liveness="Ex id a #i. Emit(id, a) @ i")

# ---- counter monotonicity with natural numbers ------------------------------
case("inj_nat_counter", """
builtins: natural-numbers
rule Create: [ Fr(id) ] --[ Create(id) ]-> [ S(id, %1) ]
rule Incr:   [ S(id, n) ] --[ Tick(id, n) ]-> [ S(id, n %+ %1) ]
""",
     phi="All id n #i #j. Tick(id,n) @ i & Tick(id,n) @ j ==> #i = #j",
     notphi="Ex id n #i #j. Tick(id,n) @ i & Tick(id,n) @ j & not(#i = #j)",
     liveness="Ex id n #i. Tick(id, n) @ i")

# ---- injective fact whose first term is NOT fresh ---------------------------
case("inj_pub_id", """
rule Create: [ In(id), Fr(v) ] --[ Create(id, v) ]-> [ S(id, v) ]
rule Read:   [ S(id, v) ] --[ Read(id, v) ]-> [ Out(v) ]
""",
     phi="All id v1 v2 #i #j. Read(id,v1) @ i & Read(id,v2) @ j ==> v1 = v2",
     notphi="Ex id v1 v2 #i #j. Read(id,v1) @ i & Read(id,v2) @ j & not(v1 = v2)",
     liveness="Ex id v #i. Read(id, v) @ i")

# ---- tuple state expanded to the right (the documented under-approx) --------
case("inj_tuple_growth", """
rule Create: [ Fr(id), Fr(a), Fr(b) ] --[ Create(id,a,b) ]-> [ S(id, <a, b>) ]
rule Grow:   [ S(id, <a, b>), Fr(c) ] --[ Grow(id) ]-> [ S(id, <a, b, c>) ]
rule Leak:   [ S(id, x) ] --[ Leak(id, x) ]-> [ Out(x) ]
""",
     phi="All id x y #i #j. Leak(id,x) @ i & Leak(id,y) @ j & #i < #j ==> not(x = y)",
     notphi="Ex id x y #i #j. Leak(id,x) @ i & Leak(id,y) @ j & #i < #j & x = y",
     liveness="Ex id x #i. Leak(id, x) @ i")

# ---- SAPIC: state cell + lock ----------------------------------------------
case("sapic_lock_state", """
process:
!( new id; insert <'cell', id>, 'zero';
   ( lock <'cell', id>; lookup <'cell', id> as v in
       ( event Read(id, v); insert <'cell', id>, 'one'; unlock <'cell', id> )
     else ( event Miss(id); unlock <'cell', id> ) ) )
""",
     phi="All id #i #j. Read(id,'one') @ i & Read(id,'one') @ j ==> #i = #j",
     notphi="Ex id #i #j. Read(id,'one') @ i & Read(id,'one') @ j & not(#i = #j)",
     liveness="Ex id v #i. Read(id, v) @ i")

# ---- SAPIC: unlocked concurrent state --------------------------------------
case("sapic_nolock_state", """
process:
!( new id; insert <'cell', id>, 'zero';
   ( ( lookup <'cell', id> as v in event Read(id, v) )
   || ( insert <'cell', id>, 'one' ) ) )
""",
     phi="All id #i. Read(id,'one') @ i ==> F",
     notphi="Ex id #i. Read(id,'one') @ i",
     liveness="Ex id v #i. Read(id, v) @ i")


def main():
    only = sys.argv[1:] or None
    os.makedirs(OUT, exist_ok=True)
    print(f"{'case':<26} {'all_phi':<11} {'ex_notphi':<11} status")
    print("-" * 82)
    bad = []
    for name, body, phi, notphi, liveness, flags in CASES:
        if only and name not in only:
            continue
        src = textwrap.dedent(f"""\
            theory {name} begin
            {body}
            lemma liveness: exists-trace
              "{liveness}"

            lemma all_phi:
              "{phi}"

            lemma ex_notphi: exists-trace
              "{notphi}"

            end
            """)
        path = os.path.join(OUT, name + ".spthy")
        with open(path, "w") as f:
            f.write(src)
        try:
            p = subprocess.run([TAMARIN, "--prove"] + flags + [path],
                               capture_output=True, text=True, timeout=TIMEOUT)
            out = p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            print(f"{name:<26} {'-':<11} {'-':<11} TIMEOUT")
            continue
        live, a, e = (verdict(out, x) for x in ("liveness", "all_phi", "ex_notphi"))
        if live != "verified":
            status = f"SKIP (liveness={live})"
        elif a == "verified" and e == "verified":
            status = "*** CONTRADICTION (both verified) ***"
            bad.append((name, path))
        elif a == "falsified" and e == "falsified":
            status = "*** CONTRADICTION (both falsified) ***"
            bad.append((name, path))
        elif "missing" in (a, e):
            status = "inconclusive (parse/translation error?)"
        else:
            status = "consistent"
        print(f"{name:<26} {a:<11} {e:<11} {status}")
    print("-" * 82)
    print(f"{len(bad)} contradiction(s)" if bad else "no contradictions")
    for n, p in bad:
        print(f"  {n} -> {p}")


if __name__ == "__main__":
    main()
