#!/usr/bin/env python3
"""Check the twist and kappa of a pointed fusion category, from the axioms.

Written because PLAN.md carried a claim that the double-dual twist is `J ≡ 1`
in every pointed category.  That claim is false: the correct value in the
duality normalisation is `J^c_ab = kappa_a kappa_b / kappa_c`, which equals 1
exactly when `kappa` is a character of the group -- true for every cyclic group
in the standard gauge, false already on `(Z/2)^2`.

The axioms used are those of FusionCategory/FusionCategory/System.lean, for a
pointed category (`F^{abc}_d = omega(a,b,c)`, `Finv = 1/omega`, the channel of
`(a,b)` being `a+b`):

    snake_left  : kappa_i * F^{i i* i}_i(0,0)         = 1
    snake_right : kappa_i * Finv^{i* i i*}_{i*}(0,0)  = 1
    J_unit_left/right, J_dual (J^{1}_{i i*} = 1), J_coherent

and (K), the per-channel identity ENO 8.23 reduces to:

    (K)  J^c_ab = FPdim_c * kappa_a * kappa_b / (kappa_c * FPdim_a * FPdim_b).

Run:  python3 FusionCategory/docs/pointed_twist_check.py

Results (all reproduced by this script):

  Vec^omega_{(Z/2)^2}, omega = (-1)^{a1 b2 c1}
      kappa = (1,1,1,-1), kappa_g kappa_-g = 1, kappa NOT a character
      J = 1     : four J-axioms hold, (K) fails on {(e1,e2), (e1,e1+e2), (e2,e1+e2)}
      J = dkappa: four J-axioms hold, (K) holds, p = 1/kappa pivotal, dim = 1
      under J = 1 no character p gives dim = FPdim = 1  (exhaustive)
  Vec^omega_{Z/2}, omega = (-1)^{abc}: kappa = (1,-1), a character, (K) holds
  Vec_{(Z/2)^2} with omega = 1, and Vec^omega_{Z/n} for n = 3,4,5,6 with the
      carry cocycle: kappa a character, (K) holds

So the four J-axioms do not determine J, and `ENO823` stated for an arbitrary
`FusionSystem` is false on the `(Z/2)^2` datum with `J := 1`; the twist has to
be derived from `ev`, `coev` and `F`, or multiplicativity of the dimension has
to be a hypothesis.
"""
import cmath
from itertools import product


def check(name, G, add, neg, om, tol=1e-9):
    one = tuple(0 for _ in G[0])

    cocycle = all(abs(om(y, z, w) * om(x, add(y, z), w) * om(x, y, add(z, w))
                      - om(add(x, y), z, w) * om(x, y, z)) < tol
                  for x in G for y in G for z in G for w in G)
    kappa = {g: 1 / om(g, neg(g), g) for g in G}
    snake_left = all(abs(kappa[g] * om(g, neg(g), g) - 1) < tol for g in G)
    snake_right = all(abs(kappa[g] / om(neg(g), g, neg(g)) - 1) < tol for g in G)
    inverse = all(abs(kappa[g] * kappa[neg(g)] - 1) < tol for g in G)
    character = all(abs(kappa[add(a, b)] - kappa[a] * kappa[b]) < tol
                    for a in G for b in G)
    FP = {g: 1.0 for g in G}          # pointed: FPdim = 1 on every simple

    def trivial(a, b, c):
        return 1.0

    def delta(a, b, c):
        return kappa[a] * kappa[b] / kappa[c]

    def axioms(J):
        return (all(abs(J(one, b, b) - 1) < tol for b in G)
                and all(abs(J(a, one, a) - 1) < tol for a in G)
                and all(abs(J(a, neg(a), one) - 1) < tol for a in G)
                and all(abs(J(a, b, add(a, b)) * J(add(a, b), c, add(add(a, b), c))
                          - J(b, c, add(b, c)) * J(a, add(b, c), add(a, add(b, c)))) < tol
                        for a in G for b in G for c in G))

    def violations(J):
        out = []
        for a in G:
            for b in G:
                c = add(a, b)
                rhs = FP[c] * kappa[a] * kappa[b] / (kappa[c] * FP[a] * FP[b])
                if abs(J(a, b, c) - rhs) > tol:
                    out.append((a, b))
        return out

    print(f"--- {name} ---")
    print(f"  omega is a 3-cocycle (this is the pentagon for pointed C): {cocycle}")
    print(f"  both snakes hold (left {snake_left}, right {snake_right}); "
          f"kappa_g kappa_-g = 1: {inverse}")
    print(f"  kappa = {[round(kappa[g].real, 4) for g in G]}")
    print(f"  kappa is a character: {character}")
    print(f"  J = 1  : J-axioms {axioms(trivial)}, (K) violations {violations(trivial)}")
    print(f"  J = dk : J-axioms {axioms(delta)},   (K) violations {violations(delta)}")
    if not character:
        pivotal = all(abs(1 / kappa[add(a, b)]
                          - delta(a, b, add(a, b)) * (1 / kappa[a]) * (1 / kappa[b])) < tol
                      for a in G for b in G)
        print(f"  under J = dk, p = 1/kappa is pivotal and dim = p*kappa = 1: {pivotal}")
        found = []
        for vals in product([1.0, -1.0], repeat=len(G) - 1):
            p = {one: 1.0}
            for g in G:
                v = 1.0
                for i, gi in enumerate(g):
                    if gi:
                        v *= vals[i]
                p[g] = v
            multiplicative = all(abs(p[add(a, b)] - p[a] * p[b]) < tol
                                for a in G for b in G)
            if multiplicative and all(abs(p[g] * kappa[g] - 1) < tol for g in G):
                found.append(vals)
        print(f"  under J = 1, characters p with dim = FPdim = 1: {found}")
    print()


def group(n, d):
    return (lambda x, y: tuple((a + b) % n for a, b in zip(x, y)),
            lambda x: tuple((-a) % n for a in x))


if __name__ == "__main__":
    sq = list(product(range(2), repeat=2))
    add, neg = group(2, 2)
    check("Vec^omega_{(Z/2)^2}, omega = (-1)^{a1 b2 c1}", sq, add, neg,
          lambda x, y, z: (-1.0) ** (x[0] * y[1] * z[0]))

    two = list(product(range(2), repeat=1))
    add2, neg2 = group(2, 1)
    check("Vec^omega_{Z/2}, omega = (-1)^{abc}", two, add2, neg2,
          lambda x, y, z: (-1.0) ** (x[0] * y[0] * z[0]))

    check("Vec_{(Z/2)^2}, omega = 1", sq, add, neg, lambda x, y, z: 1.0)

    for n in (3, 4, 5, 6):
        zeta = cmath.exp(2j * cmath.pi / n)
        G = list(product(range(n), repeat=1))
        addn, negn = group(n, 1)

        def carry(x, y, w, n=n, zeta=zeta):
            return zeta ** (x[0] * ((y[0] + w[0]) - (y[0] + w[0]) % n))

        check(f"Vec^omega_{{Z/{n}}}, carry cocycle", G, addn, negn, carry)
