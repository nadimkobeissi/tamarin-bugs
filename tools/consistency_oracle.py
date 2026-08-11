#!/usr/bin/env python3
"""
Ground-truth-free consistency oracle for tamarin-prover.

For one theory we emit two lemmas over the same formula phi:

    lemma all_phi   : all-traces   "phi"
    lemma ex_notphi : exists-trace "not phi"

Semantics forces these to disagree:

    all_phi verified   <=> every trace satisfies phi  <=> ex_notphi falsified
    all_phi falsified  <=> some trace violates phi    <=> ex_notphi verified

So verified/verified and falsified/falsified are both self-contradictions of
the tool, provable without knowing what the right answer is.

A third lemma (liveness) guards against the degenerate case of an empty trace
set, where both readings collapse.
"""
import subprocess, sys, re, os, textwrap

TAMARIN = os.environ.get("TAMARIN", "tamarin-prover")
TIMEOUT = int(os.environ.get("TIMEOUT", "120"))
OUT = "/tmp/tamdeep/gen"

SUMMARY = re.compile(r"^\s{2}(\w+)\s*\((?:all-traces|exists-trace)\):\s*(.+?)\s*$", re.M)


def verdict(text, name):
    for n, v in SUMMARY.findall(text):
        if n == name:
            if v.startswith("verified"):
                return "verified"
            if v.startswith("falsified"):
                return "falsified"
            return v
    return "missing"


def run(case):
    name, preamble, rules, restrictions, phi, notphi, liveness = case
    body = textwrap.dedent(f"""\
        theory {name} begin

        {preamble}

        {rules}

        {restrictions}

        lemma liveness: exists-trace
          "{liveness}"

        lemma all_phi:
          "{phi}"

        lemma ex_notphi: exists-trace
          "{notphi}"

        end
        """)
    os.makedirs(OUT, exist_ok=True)
    path = os.path.join(OUT, name + ".spthy")
    with open(path, "w") as f:
        f.write(body)
    try:
        p = subprocess.run([TAMARIN, "--prove", path], capture_output=True,
                           text=True, timeout=TIMEOUT)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return name, "TIMEOUT", "-", "-", path
    live = verdict(out, "liveness")
    a = verdict(out, "all_phi")
    e = verdict(out, "ex_notphi")
    if live != "verified":
        status = f"SKIP (liveness={live})"
    elif a == "verified" and e == "verified":
        status = "*** CONTRADICTION (both verified) ***"
    elif a == "falsified" and e == "falsified":
        status = "*** CONTRADICTION (both falsified) ***"
    elif "missing" in (a, e) or "TIMEOUT" in (a, e):
        status = "inconclusive"
    else:
        status = "consistent"
    return name, status, a, e, path


CASES = []


def case(name, phi, notphi, liveness, rules, preamble="", restrictions=""):
    CASES.append((name, preamble, rules, restrictions, phi, notphi, liveness))


# ---------------------------------------------------------------- control ----
case("ctl_plain",
     phi="All k #i #j. Gen(k) @ i & KU(k) @ j ==> F",
     notphi="Ex k #i #j. Gen(k) @ i & KU(k) @ j",
     liveness="Ex k #i. Gen(k) @ i",
     rules="rule Gen: [ Fr(k) ] --[ Gen(k) ]-> [ Out(k) ]")

case("ctl_secret",
     phi="All k #i #j. Gen(k) @ i & KU(k) @ j ==> F",
     notphi="Ex k #i #j. Gen(k) @ i & KU(k) @ j",
     liveness="Ex k #i. Gen(k) @ i",
     rules="rule Gen: [ Fr(k) ] --[ Gen(k) ]-> [ St(k) ]")

# -------------------------------------------------------------------- xor ----
case("xor_self_cancel",
     preamble="builtins: xor",
     phi="All a #i #j. Gen(a) @ i & KU(a) @ j ==> F",
     notphi="Ex a #i #j. Gen(a) @ i & KU(a) @ j",
     liveness="Ex a #i. Gen(a) @ i",
     rules=("rule Gen: [ Fr(a) ] --[ Gen(a) ]-> [ Out(a XOR a) ]"))

case("xor_one_pad",
     preamble="builtins: xor",
     phi="All a b #i #j. Gen(a,b) @ i & KU(a) @ j ==> F",
     notphi="Ex a b #i #j. Gen(a,b) @ i & KU(a) @ j",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules=("rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ Out(a XOR b), Out(b) ]"))

case("xor_two_pads",
     preamble="builtins: xor",
     phi="All a b c #i #j. Gen(a,b,c) @ i & KU(a) @ j ==> F",
     notphi="Ex a b c #i #j. Gen(a,b,c) @ i & KU(a) @ j",
     liveness="Ex a b c #i. Gen(a,b,c) @ i",
     rules=("rule Gen: [ Fr(a), Fr(b), Fr(c) ] --[ Gen(a,b,c) ]-> "
            "[ Out(a XOR b), Out(b XOR c), Out(c) ]"))

case("xor_zero",
     preamble="builtins: xor",
     phi="All a #i #j. Gen(a) @ i & KU(a) @ j ==> F",
     notphi="Ex a #i #j. Gen(a) @ i & KU(a) @ j",
     liveness="Ex a #i. Gen(a) @ i",
     rules=("rule Gen: [ Fr(a) ] --[ Gen(a) ]-> [ Out(a XOR zero) ]"))

# ---------------------------------------------------------------- multiset ---
case("mset_union_leak",
     preamble="builtins: multiset",
     phi="All a b #i #j. Gen(a,b) @ i & KU(a) @ j ==> F",
     notphi="Ex a b #i #j. Gen(a,b) @ i & KU(a) @ j",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules="rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ Out(a+b) ]")

case("mset_eq",
     preamble="builtins: multiset",
     phi="All a b #i. Gen(a,b) @ i ==> not(a+b = b+a)",
     notphi="Ex a b #i. Gen(a,b) @ i & a+b = b+a",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules="rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ ]")

# --------------------------------------------------------------------- dh ----
case("dh_shared",
     preamble="builtins: diffie-hellman",
     phi="All a b #i #j. Gen(a,b) @ i & KU('g'^(a*b)) @ j ==> F",
     notphi="Ex a b #i #j. Gen(a,b) @ i & KU('g'^(a*b)) @ j",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules="rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ Out('g'^a), Out('g'^b) ]")

case("dh_exp_leak",
     preamble="builtins: diffie-hellman",
     phi="All a b #i #j. Gen(a,b) @ i & KU('g'^(a*b)) @ j ==> F",
     notphi="Ex a b #i #j. Gen(a,b) @ i & KU('g'^(a*b)) @ j",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules="rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ Out('g'^a), Out(b) ]")

# --------------------------------------------------------------- subterm -----
case("subterm_pair",
     phi="All a b #i. Gen(a,b) @ i ==> not(a << <a,b>)",
     notphi="Ex a b #i. Gen(a,b) @ i & a << <a,b>",
     liveness="Ex a b #i. Gen(a,b) @ i",
     rules="rule Gen: [ Fr(a), Fr(b) ] --[ Gen(a,b) ]-> [ ]")

# ------------------------------------------------------------------- nat -----
case("nat_order",
     preamble="builtins: natural-numbers",
     phi="All x #i. Gen(x) @ i ==> not(x %+ %1 = x)",
     notphi="Ex x #i. Gen(x) @ i & x %+ %1 = x",
     liveness="Ex x #i. Gen(x) @ i",
     rules="rule Gen: [ In(x) ] --[ Gen(x) ]-> [ ]")

# ------------------------------------------------------- hashing / symenc ----
case("hash_preimage",
     preamble="builtins: hashing",
     phi="All k #i #j. Gen(k) @ i & KU(k) @ j ==> F",
     notphi="Ex k #i #j. Gen(k) @ i & KU(k) @ j",
     liveness="Ex k #i. Gen(k) @ i",
     rules="rule Gen: [ Fr(k) ] --[ Gen(k) ]-> [ Out(h(k)) ]")

case("senc_nokey",
     preamble="builtins: symmetric-encryption",
     phi="All m k #i #j. Gen(m,k) @ i & KU(m) @ j ==> F",
     notphi="Ex m k #i #j. Gen(m,k) @ i & KU(m) @ j",
     liveness="Ex m k #i. Gen(m,k) @ i",
     rules="rule Gen: [ Fr(m), Fr(k) ] --[ Gen(m,k) ]-> [ Out(senc(m,k)) ]")

case("senc_withkey",
     preamble="builtins: symmetric-encryption",
     phi="All m k #i #j. Gen(m,k) @ i & KU(m) @ j ==> F",
     notphi="Ex m k #i #j. Gen(m,k) @ i & KU(m) @ j",
     liveness="Ex m k #i. Gen(m,k) @ i",
     rules="rule Gen: [ Fr(m), Fr(k) ] --[ Gen(m,k) ]-> [ Out(senc(m,k)), Out(k) ]")


def main():
    only = sys.argv[1:] or None
    print(f"{'case':<22} {'all_phi':<11} {'ex_notphi':<11} status")
    print("-" * 78)
    bad = []
    for c in CASES:
        if only and c[0] not in only:
            continue
        name, status, a, e, path = run(c)
        print(f"{name:<22} {a:<11} {e:<11} {status}")
        if "CONTRADICTION" in status:
            bad.append((name, path))
    print("-" * 78)
    if bad:
        print(f"{len(bad)} CONTRADICTION(S):")
        for n, p in bad:
            print(f"  {n}  ->  {p}")
    else:
        print("no contradictions")


if __name__ == "__main__":
    main()
