#!/usr/bin/env python3
"""Yang-Lee: a complete rigid skeletal datum on which (K) fails for every J.

Rank 2, labels 0 = 1 and 1 = tau, with tau (x) tau = 1 + tau, so FPdim_tau = phi
(d^2 = 1 + d, positive root).  The pentagon has two branches: Fibonacci
F^{tau tau tau}_tau = [[1/phi, 1], [1/phi, -1/phi]] with kappa_tau = phi, and
Yang-Lee F^{tau tau tau}_tau = [[-phi, 1], [-phi, phi]] with
kappa_tau = -1/phi.  Both are checked here on all 2^9 label tuples in the
repo's index conventions (FusionCategory/FusionCategory/System.lean):

    pentagon    sum_k F^{a b c}_x(e,k) F^{a k d}_r(x,j) F^{b c d}_j(k,i)
                  = F^{e c d}_r(x,i) F^{a b i}_r(e,j)
    snake_left  (coev_i ev_i) F^{i i* i}_i(0,0)            = 1
    snake_right (coev_i ev_i) (F^{i* i i*}_{i*})^{-1}(0,0) = 1

Why (K) fails on Yang-Lee for every J.  On the coevaluation channel
(i, i*; 1) the axiom J^{1}_{i i*} = 1 is used, so (K) there reads

    kappa_i kappa_{i*} = FPdim_i^2 ,

with no J in it.  On Yang-Lee that is 1/phi^2 against phi^2, so no choice of J
makes (K) hold -- while every other axiom of FusionSystem is satisfied.  So
(K) is not a consequence of the axioms, and it is exactly the pseudo-unitarity
of the datum: (K) => kappa_i kappa_{i*} = FPdim_i^2 is J-free, and the
converse is ENO 8.23.

Run:  python3 FusionCategory/docs/yang_lee_check.py
"""
import sympy as sp

phi = (1 + sp.sqrt(5)) / 2
# tau (x) tau = 1 + tau
N = {(0, 0): [0], (0, 1): [1], (1, 0): [1], (1, 1): [0, 1]}
ONE, ZERO = sp.Integer(1), sp.Integer(0)


def supported(a, b, e):
    return e in N[(a, b)]


def F(B, a, b, c, d, e, f):
    """F^{abc}_d(e,f); unit-normalised outside the tau^3 block."""
    if not (supported(a, b, e) and supported(e, c, d)
            and supported(b, c, f) and supported(a, f, d)):
        return ZERO
    if (a, b, c, d) == (1, 1, 1, 1):
        return B[e][f]
    return ONE


def check(name, B):
    bad = []
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                for d in (0, 1):
                    for e in (0, 1):
                        for i in (0, 1):
                            for j in (0, 1):
                                for r in (0, 1):
                                    for x in (0, 1):
                                        lhs = sum(F(B, a, b, c, x, e, k)
                                                  * F(B, a, k, d, r, x, j)
                                                  * F(B, b, c, d, j, k, i)
                                                  for k in (0, 1))
                                        rhs = F(B, e, c, d, r, x, i) * F(B, a, b, i, r, e, j)
                                        if sp.simplify(lhs - rhs) != 0:
                                            bad.append((a, b, c, d, e, i, j, r, x))
    kappa_tau = 1 / F(B, 1, 1, 1, 1, 0, 0)          # left snake
    kappa_dual = 1 / sp.Matrix(B).inv()[0, 0]        # right snake: (F^{i* i i*}_{i*})^{-1}(0,0)
    assert sp.simplify(kappa_tau - kappa_dual) == 0, "the two snakes disagree"
    print(f"{name}: pentagon on all 512 tuples: {'OK' if not bad else 'FAIL ' + str(bad[:3])}")
    print(f"   kappa_tau = {sp.simplify(kappa_tau)} from both snakes "
          f"(tau is self-dual, so kappa_tau* = kappa_tau)")
    print(f"   (K) on (tau,tau*;1) with J = 1: kappa_tau kappa_tau* = "
          f"{sp.simplify(kappa_tau ** 2)} vs FPdim_tau^2 = {sp.simplify(phi ** 2)}")
    ok = sp.simplify(kappa_tau ** 2 - phi ** 2) == 0
    print(f"   -> (K) on that channel {'holds' if ok else 'FAILS for every J'}")
    print()


if __name__ == "__main__":
    check("Fibonacci", [[sp.nsimplify(1 / phi), ONE], [sp.nsimplify(1 / phi), sp.nsimplify(-1 / phi)]])
    check("Yang-Lee ", [[sp.nsimplify(-phi), ONE], [sp.nsimplify(-phi), sp.nsimplify(phi)]])
