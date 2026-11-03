#!/usr/bin/env python3
"""The honest double-dual twist of a pointed self-dual datum, and the check
that dimension multiplicativity pins it.

Setting.  A pointed fusion datum in skeletal form: labels G, associator
F^{abc}_d = omega(a,b,c) with `Finv = 1/omega`, channels (a,b) -> a+b,
evaluation/coevaluation scalars E_a (on X_{a*} (x) X_a) and C_a, and
kappa_a = C_a E_a, which the left snake fixes as

    kappa_g * omega(g,-g,g) = 1.

The double-dual twist.  (-)** is the identity on objects here, so J is a
scalar per channel.  It is the composite

    ((a (x) b)*)*  --(phi_{a,b}*)^{-1}-->  (b* (x) a*)*  --phi_{b*,a*}-->  a** (x) b**,

with phi_{a,b} : (a (x) b)* -> b* (x) a* the canonical iso, characterised by
commuting with the evaluation.  Evaluating phi through the partial evaluation
((a (x) b)* (x) a) -> b* gives

    phi(a,b) = C_a * omega(-(a+b),a,-a)^{-1} * omega(-(a+b),a,b) * E_{a+b}/E_b

and the E's and C's collapse into kappa's, so

    J(a,b;c) = (kappa_b/kappa_a) * [omega(-c,b,-b)^{-1} omega(-c,b,a)]
                                    / [omega(-c,a,-a)^{-1} omega(-c,a,b)]

(the self-dual case of J = phi(b*,a*;c*)/phi(a,b;c)).

Why it is pinned.  For a self-dual simple the categorical dimension is the loop
1 --coev--> X (x) X --(p (x) id)--> X (x) X --ev--> 1, with no associator in it,
so dim X = p_X kappa_X.  The dimension is multiplicative in any pivotal
category, so on every channel

    (M)   kappa_a kappa_b = J(a,b) kappa_{a+b},

i.e. J = kappa_a kappa_b / kappa_{a+b} =: delta(kappa).  This is a function of F
alone, through kappa_g = 1/omega(g,-g,g).

What the script shows: on G = (Z/2)^2 with omega = (-1)^{a1 b2 c1}, delta(kappa)
is -1 on six channels, and the phi evaluation derived from the defining property
returns exactly that (all 16 channels, 0 mismatches).  So J = delta(kappa), and
the trivial-twist reading is what fails: J = 1 holds iff kappa is a character.
Two reconstructions went wrong here and it is worth keeping them apart: the
plan's Omega formula *as written* (entry (c*,b), inverse-block index (0,c))
evaluates to +1 on that datum, so its transcription is defective, while the
construction implemented with the full associator bookkeeping reproduces
delta(kappa) (swarm smvzybdp8, m6, three independent assemblies); and m1's
scalar psi formula also returns +1 there and is wrong.  Since delta(kappa) = 1
on every cyclic group in the standard gauge, and Fibonacci and Ising have
kappa = FPdim, a census of those examples cannot see the difference.

Run:  python3 FusionCategory/docs/honest_twist_check.py
"""
from itertools import product


def honest_j(G, add, neg, om, kappa):
    """J(a,b;c) from the phi evaluation, for self-dual labels."""
    out = {}
    for a in G:
        for b in G:
            c = add(a, b)
            out[(a, b, c)] = (kappa[b] / kappa[a]) * (
                om(neg(c), b, neg(b)) ** -1 * om(neg(c), b, a)
            ) / (
                om(neg(c), a, neg(a)) ** -1 * om(neg(c), a, b)
            )
    return out


def report(name, G, add, neg, om):
    one = tuple(0 for _ in G[0])
    assert all(neg(g) == g for g in G), "self-dual labels only"
    kappa = {g: 1 / om(g, neg(g), g) for g in G}
    J = honest_j(G, add, neg, om, kappa)
    print(f"--- {name} ---")
    print(f"  kappa = {[kappa[g] for g in G]}")
    bad = 0
    for (a, b, c), v in J.items():
        forced = kappa[a] * kappa[b] / kappa[c]      # (M)
        ok = abs(v - forced) < 1e-9
        bad += not ok
        print(f"  J({a},{b};{c}) = {v:+.1f}    (M) forces {forced:+.1f}    {ok}")
    print(f"  disagreements with (M): {bad}")
    print(f"  distinct values of delta(kappa): "
          f"{sorted({kappa[a]*kappa[b]/kappa[c] for (a,b,c) in J})}")
    print()


def group(n, d):
    return (lambda x, y: tuple((a + b) % n for a, b in zip(x, y)),
            lambda x: tuple((-a) % n for a in x))


if __name__ == "__main__":
    sq = list(product(range(2), repeat=2))
    add, neg = group(2, 2)
    report("Vec^omega_{(Z/2)^2}, omega = (-1)^{a1 b2 c1}", sq, add, neg,
           lambda x, y, z: (-1.0) ** (x[0] * y[1] * z[0]))

    two = list(product(range(2), repeat=1))
    add2, neg2 = group(2, 1)
    report("Vec^omega_{Z/2} = sVec, omega = (-1)^{abc}", two, add2, neg2,
           lambda x, y, z: (-1.0) ** (x[0] * y[0] * z[0]))

    report("Vec_{(Z/2)^2}, omega = 1", sq, add, neg, lambda x, y, z: 1.0)
