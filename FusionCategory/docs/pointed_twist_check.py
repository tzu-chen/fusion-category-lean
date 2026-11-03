#!/usr/bin/env python3
"""Cocycle census for pointed fusion categories -- repaired (WP3 Task 3.4).

This is a drop-in replacement for ``FusionCategory/docs/pointed_twist_check.py``.
It checks, exactly and from the axioms of ``FusionCategory/FusionCategory/System.lean``,
which twists ``J`` a pointed skeletal datum admits and whether the honest
(double-dual, i.e. computed-from-ev/coev/F) twist can be told apart from the
trivial one.

WHY IT WAS REPAIRED.  The proposal's Remark ("a third witness, at script
level", sec. refute) records that the cyclic families of the old census ran a
"carry cocycle" whose exponent is a multiple of ``n`` and which is therefore
*identically* 1.  Running the old script confirms it: for ``Z/3``, ``Z/4``,
``Z/5``, ``Z/6`` it prints ``kappa = [1.0, ...]`` and both twists satisfy (K),
so those families exercise ``Vec_{Z/n}``, not ``Vec^omega_{Z/n}``.  Repairing
the cocycle exposes a *second*, independent defect in the same script: its
pentagon check

    om(y,z,w) * om(x,yz,w) * om(x,y,zw) = om(xy,z,w) * om(x,y,z)          (S)

is the standard cocycle condition ``delta omega = 1`` with ``om(x,y,zw)`` and
``om(x,y,z)`` on the wrong sides.  ``System.lean``'s ``pentagon`` field,
instantiated on a pointed datum (``F a b c d e f = omega(a,b,c)`` on the unique
channel), reads

    om(x,y,z) * om(x,yz,w) * om(y,z,w) = om(xy,z,w) * om(x,y,zw)          (R)

-- the same three terms as the standard condition, and (R) *is* the standard
one.  (S) and (R) agree only when ``omega`` takes values in 2-torsion, which is
why the old check passed on ``(Z/2)^2`` and on the identically-1 family and
*does* fail on a genuine odd-order cocycle (see ``selftest`` case
``old_convention_fails`` and ``Z3sqTwist.lean``'s ``old_convention_fails``).
Both conditions are computed here; (R) is the one that must hold.

WHAT THE CENSUS CHECKS (exact integer arithmetic mod N, no floating point;
``omega`` takes values in ``mu_N`` and is stored as an exponent map):

  pentagon   (R) for all quadruples
  snakes     kappa_g = 1/omega(g,g*,g) (left snake) = omega(g*,g,g*) (right
             snake, the 1x1 block of the *inverse* associator) and
             kappa_g kappa_{g*} = 1
  J laws     J_unit_left, J_unit_right, J_dual, J_coherent (System.lean)
  (M)/(K)    J(a,b;a+b) = kappa_a kappa_b / kappa_{a+b}, i.e. multiplicativity
             of the dimension in the pointed case (FusionSystem has FPdim = 1
             on every simple)
  pivotal    p_mon: p_{a+b} = J(a,b) p_a p_b   (Pivotal.lean)
  spherical  dim g* = dim g with dim g = p_g kappa_g, and dim = FPdim = 1
  genuine    the class of omega: decided exactly by ``is_coboundary`` (linear
             elimination over Z/N), and, when non-zero, certified by a *cycle* z
             in the kernel of the normalised boundary d_3 -- a formal integer
             combination of triples of non-identity elements, NOT a single triple
             -- on which omega does not vanish.  Q/Z is injective, so a cocycle
             vanishing on all of ker d_3 is a coboundary: a non-vanishing cycle
             is a rigorous certificate of non-triviality, and the exact
             elimination is a complete decision either way.

THE FAMILIES (the four the proposal asks for, plus a fifth non-abelian one; two
controls):

  (Z/2)^2   omega = (-1)^{a1 b2 c1}       = pi1 u pi2 u pi1, values in mu_2
  (Z/3)^2   omega = zeta^{a1 b2 c1}       = pi1 u pi2 u pi1, values in mu_3 --
            a COBOUNDARY (see RESULTS), kept because it is the proposal's example
  (Z/3)^2   omega = carry x carry x zeta^{a1 b2 c1}, the genuinely twisted row
            that carries the J^2 != 1 witness
  Z/3       omega = zeta^{a floor((b+c)/3)}   the standard generator of
            H^3(Z/3) = Z/3 -- the *genuine* carry cocycle.  The old script had
            zeta = exp(2 pi i / n) with an exponent that is a multiple of n,
            hence omega = 1; the correct normalisation is exp(2 pi i / n^2)
            times that exponent, equivalently zeta^{a floor((b+c)/n)}.
  D8        omega = (-1)^{i(x) j(y) i(z)}  = alpha u beta u alpha, alpha =
            r-exponent mod 2, beta = s-exponent, values in mu_2 (non-abelian)
  S3        omega = s(x) s(y) s(z)         = sigma u sigma u sigma, values in
            mu_2 (non-abelian)

  controls: (Z/2)^2 with omega = 1, and Vec^omega_{Z/2} with omega =
  (-1)^{abc}.  Both have kappa a character, so on both J = 1 and J = delta(kappa)
  agree -- as they do on every family where kappa is a character (Z/3 carry, S3,
  and these two).  The (Z/2)^2 control is the one where omega itself is trivial,
  and it is kept so that the census is not one-sided.

RESULTS.  On (Z/2)^2, Z/2, Z/3, D8, S3 and the twisted (Z/3)^2 row the class of
omega is non-zero (exact elimination over Z/N: no 2-cochain mu with
delta mu = omega), and a 3-cycle witnessing it is exhibited.  On (Z/2)^2, D8 and
the twisted (Z/3)^2 row kappa is *not* a character: J = 1 violates (M) on some
channels and J = delta(kappa) violates it on none, so those families separate the
honest twist from the trivial one.  On Z/2, Z/3 and S3 the associator is
non-trivial but kappa *is* a character, so J = 1 is the honest twist there: a
non-trivial associator does not force a non-trivial twist.

THE PROPOSAL'S (Z/3)^2 EXAMPLE IS A COBOUNDARY.  omega = zeta^{a1 b2 c1} on
(Z/3)^2 satisfies omega = delta mu for an explicit mu (this script prints one;
`Z3sqTwist.lean` kernel-checks the identity), so that datum is *gauge*-trivial:
as a fusion category it is Vec_(Z/3)^2.  The row is kept -- its J^2 != 1 is real
for that datum, and it is the example the proposal's Remark quotes -- but the
J^2 != 1 witness that survives as a statement about a genuinely twisted cocycle
is the row `carry x carry x zeta^{a1 b2 c1}`: the product of the two cyclic carry
cocycles (a non-zero class) with that coboundary, which is what makes kappa a
non-character.  There J^2 is a primitive cube root of unity on 36 of the 81
channels *and* the associator is not a coboundary, so J^2 = 1 must not be added
as an axiom -- for a stronger reason than the proposal records.

THE HARNESS FAILS LOUDLY.  Every family is compared against the reference
table REFERENCE below (values recorded once, from this script, and reviewed by
hand -- see REPORT.md); any disagreement prints FAIL and the process exits 1.
``selftest`` runs negative fixtures for every check -- a non-cocycle, the old
vacuous carry cocycle, the old pentagon convention, a coboundary (which must
yield *no* non-triviality witness), J = 1 where (M) fails, a single flipped J
channel, p = 1 where p is not pivotal, an inverse twist, a non-spherical
pivotal structure -- and the harness exits 1 if any fixture is *accepted*.  It
also checks that the reference mechanism itself catches a perturbed fingerprint,
so "green" cannot come from a comparison that never fires.

WHAT THE CENSUS DOES NOT DO.  It does not *derive* the twist from `(F, ev, coev)`:
that is WP3 Task 3.2 and it is held.  `delta(kappa)` is the twist for which the
dimension is multiplicative -- equivalently the twist for which `p = 1/kappa` is
pivotal -- and in the self-dual case `docs/honest_twist_check.py` evaluates the
defining property of the comparison map and returns exactly `delta(kappa)`.
What is checked here is only arithmetic about the two candidate twists `1` and
`delta(kappa)`: that they satisfy the same four laws, that only the second
satisfies (M)/(K), and what the pivotal structures and dimensions then are.

Run:  python3 pointed_census.py            # census + selftest, exit 0 iff all green
      python3 pointed_census.py --record   # print the reference table
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from itertools import product
import sys

import sympy as sp


# ---------------------------------------------------------------------------
# datum
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Pointed:
    """A pointed skeletal datum: G, and a cocycle omega with values in mu_N.

    ``om`` returns an exponent in ``Z/N``: the value of omega is exp(2 pi i e / N).
    """
    name: str
    els: tuple
    mul: object
    inv: object
    N: int
    om: object

    @property
    def one(self):
        return self.els[0]


# ---------------------------------------------------------------------------
# the checks; each returns a list of failures, empty meaning "passes"
# ---------------------------------------------------------------------------

def pentagon_failures(S, convention="repo"):
    """(R) is System.lean's pentagon on a pointed datum; (S) is the old script's."""
    bad = []
    for x in S.els:
        for y in S.els:
            for z in S.els:
                for w in S.els:
                    yz, zw, xy = S.mul(y, z), S.mul(z, w), S.mul(x, y)
                    if convention == "repo":
                        lhs = S.om(x, y, z) + S.om(x, yz, w) + S.om(y, z, w)
                        rhs = S.om(xy, z, w) + S.om(x, y, zw)
                    else:
                        lhs = S.om(y, z, w) + S.om(x, yz, w) + S.om(x, y, zw)
                        rhs = S.om(xy, z, w) + S.om(x, y, z)
                    if (lhs - rhs) % S.N:
                        bad.append((x, y, z, w))
    return bad


def kappa(S):
    """kappa_g = coev_g ev_g, fixed by the left snake: kappa_g omega(g,g*,g) = 1."""
    return {g: (-S.om(g, S.inv(g), g)) % S.N for g in S.els}


def snake_failures(S):
    k = kappa(S)
    bad = []
    for g in S.els:
        gi = S.inv(g)
        if (k[g] + S.om(g, gi, g)) % S.N:            # left snake
            bad.append(("left", g))
        if (k[g] - S.om(gi, g, gi)) % S.N:           # right snake (1x1 block)
            bad.append(("right", g))
        if (k[g] + k[gi]) % S.N:                     # kappa_g kappa_{g*} = 1
            bad.append(("inverse", g))
    return bad


def j_law_failures(S, j):
    """The four J laws of System.lean, on a self-dual pointed datum (j is a
    map (a,b) -> exponent of J on the channel (a, a+b))."""
    bad = []
    for b in S.els:
        if j[(S.one, b)] % S.N:
            bad.append(("unit_left", b))
    for a in S.els:
        if j[(a, S.one)] % S.N:
            bad.append(("unit_right", a))
        if j[(a, S.inv(a))] % S.N:
            bad.append(("dual", a))
    for a in S.els:
        for b in S.els:
            for c in S.els:
                ab, abc, bc = S.mul(a, b), S.mul(S.mul(a, b), c), S.mul(b, c)
                if (j[(a, b)] + j[(ab, c)] - j[(b, c)] - j[(a, bc)]) % S.N:
                    bad.append(("coherent", a, b, c))
    return bad


def K_failures(S, j):
    """(M)/(K): J(a,b) = kappa_a kappa_b / kappa_{a+b} on every channel."""
    k = kappa(S)
    return [(a, b) for a in S.els for b in S.els
            if (j[(a, b)] + k[S.mul(a, b)] - k[a] - k[b]) % S.N]


def pivotal_failures(S, j, p):
    """p_mon: p_{a+b} = J(a,b) p_a p_b on every channel."""
    return [(a, b) for a in S.els for b in S.els
            if (p[S.mul(a, b)] - j[(a, b)] - p[a] - p[b]) % S.N]


def spherical_failures(S, p):
    """dim g* = dim g, with dim g = p_g kappa_g:  kappa_{g*} = p_g^2 kappa_g."""
    k = kappa(S)
    return [g for g in S.els
            if (k[S.inv(g)] - 2 * p[g] - k[g]) % S.N]


def dims(S, p):
    k = kappa(S)
    return {g: (p[g] + k[g]) % S.N for g in S.els}


def homomorphisms(S):
    """All homomorphisms G -> mu_N, as exponent maps (characters, additively)."""
    gens, H = [], {S.one}
    for g in S.els:
        if g in H:
            continue
        gens.append(g)
        changed = True
        while changed:
            changed = False
            for x in list(H):
                for s in gens:
                    for y in (S.mul(x, s), S.mul(s, x)):
                        if y not in H:
                            H.add(y)
                            changed = True
    out, seen = [], set()
    for imgs in product(range(S.N), repeat=len(gens)):
        vals = {S.one: 0}
        stack, ok = [S.one], True
        while stack and ok:
            x = stack.pop()
            for s, a in zip(gens, imgs):
                for y, inc in ((S.mul(x, s), a), (S.mul(s, x), a)):
                    cand = (vals[x] + inc) % S.N
                    if y in vals:
                        if vals[y] != cand:
                            ok = False
                            break
                    else:
                        vals[y] = cand
                        stack.append(y)
                if not ok:
                    break
        if not ok or len(vals) != len(S.els):
            continue
        if all((vals[S.mul(a, b)] - vals[a] - vals[b]) % S.N == 0
               for a in S.els for b in S.els):
            key = tuple(vals[g] for g in S.els)
            if key not in seen:
                seen.add(key)
                out.append(vals)
    return out


def is_character(S, e):
    """Is the exponent function e : G -> Z/N a homomorphism?"""
    return all((e[S.mul(a, b)] - e[a] - e[b]) % S.N == 0
               for a in S.els for b in S.els)


def trivial_twist(S):
    return {(a, b): 0 for a in S.els for b in S.els}


def honest_twist(S):
    """delta(kappa): the twist forced by multiplicativity of the dimension."""
    k = kappa(S)
    return {(a, b): (k[a] + k[b] - k[S.mul(a, b)]) % S.N
            for a in S.els for b in S.els}


def inverse_kappa(S):
    """p = 1/kappa, with exponent map (the pivotal structure paired with delta(kappa))."""
    k = kappa(S)
    return {g: (-k[g]) % S.N for g in S.els}


def is_coboundary(S):
    """Is `omega` a coboundary, i.e. is `omega = delta mu` for a 2-cochain `mu`?

    Exact elimination over `Z/N` on the system
    `mu(y,z) - mu(xy,z) + mu(x,yz) - mu(x,y) = omega(x,y,z)` (all `|G|^3` equations,
    `|G|^2` unknowns).  `N` is prime in every family here (`2` or `3`), so every
    pivot is invertible.  Returns `(True, mu)` or `(False, None)`.

    This is the complete test for triviality of the class of `omega` among
    `mu_N`-valued cochains.  A coboundary `omega = delta mu` is a *gauge*
    transformation of the associator: the pointed datum is monoidally trivial,
    which is why a family can satisfy every law and still be a coboundary (see
    the `(Z/3)^2` rows below).
    """
    N = S.N
    pairs = [(a, b) for a in S.els for b in S.els]
    idx = {p: i for i, p in enumerate(pairs)}
    rows, rhs = [], []
    for x in S.els:
        for y in S.els:
            for z in S.els:
                row = [0] * len(pairs)
                for c, (u, v) in ((1, (y, z)), (-1, (S.mul(x, y), z)),
                                  (1, (x, S.mul(y, z))), (-1, (x, y))):
                    row[idx[(u, v)]] = (row[idx[(u, v)]] + c) % N
                rows.append(row)
                rhs.append(S.om(x, y, z) % N)
    m, n = len(rows), len(pairs)
    for i in range(m):
        rows[i].append(rhs[i])
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if rows[i][c] % N), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = pow(rows[r][c], -1, N)
        rows[r] = [(v * inv) % N for v in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] % N:
                f = rows[i][c]
                rows[i] = [(a - f * b) % N for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    if any(rows[i][n] % N for i in range(r, m)):
        return False, None
    sol = [0] * n
    for i, c in enumerate(piv):
        sol[c] = rows[i][n]
    mu = {pairs[i]: sol[i] for i in range(n)}
    return True, mu


def delta(S, mu, x, y, z):
    """`(delta mu)(x,y,z)`, the standard inhomogeneous coboundary (exponents)."""
    return (mu[(y, z)] - mu[(S.mul(x, y), z)] + mu[(x, S.mul(y, z))] - mu[(x, y)]) % S.N


def pivotal_structures(S, j):
    """Every pivotal structure under the twist `j`.

    If `p` is pivotal then so is `p * chi` for any character `chi` of `G`
    (Kashina's torsor: `p_mon` is linear in `p`), so with `p = 1/kappa` pivotal
    for `j = delta(kappa)` the complete list is `chi / kappa` over the characters
    `chi` -- enumerated exhaustively and re-tested, not assumed.
    """
    k = kappa(S)
    out = []
    for chi in homomorphisms(S):
        p = {g: (chi[g] - k[g]) % S.N for g in S.els}
        if not pivotal_failures(S, j, p):
            out.append(p)
    return out


def j_sq_report(S, j):
    """Multiset of the orders of J(a,b) (as values in mu_N), and of J^2."""
    def order(e):
        e %= S.N
        if e == 0:
            return 1
        from math import gcd
        return S.N // gcd(e, S.N)
    ords = sorted({order(v) for v in j.values()})
    ords2 = sorted({order(2 * v) for v in j.values()})
    return ords, ords2, [(a, b, j[(a, b)]) for a in S.els for b in S.els
                         if order(2 * j[(a, b)]) > 1]


# ---------------------------------------------------------------------------
# non-triviality witness: a 3-cycle on which the cocycle does not vanish
# ---------------------------------------------------------------------------

def normalised_d3(H, mul):
    """The normalised bar differential d_3 : C_3 -> C_2 of the subgroup H
    (homogeneous-identity-free basis), as an integer matrix."""
    elts = [h for h in H if h != H[0]]
    idx_e = {h: i for i, h in enumerate(elts)}
    C3 = [(i, j, k) for i in range(len(elts)) for j in range(len(elts)) for k in range(len(elts))]
    C2 = [(i, j) for i in range(len(elts)) for j in range(len(elts))]
    idx2 = {c: n for n, c in enumerate(C2)}
    M = sp.zeros(len(C3), len(C2))
    for n, (i, j, k) in enumerate(C3):
        x, y, z = elts[i], elts[j], elts[k]
        for coef, (u, v) in ((1, (y, z)), (-1, (mul(x, y), z)),
                             (1, (x, mul(y, z))), (-1, (x, y))):
            if u == H[0] or v == H[0]:
                continue
            col = idx2[(idx_e[u], idx_e[v])]
            M[n, col] = M[n, col] + coef
    return C3, C2, M


def cyclic_subgroups(S):
    """Distinct cyclic subgroups of S, each as an ordered tuple of elements."""
    seen, out = set(), []
    for g in S.els:
        H = {S.one}
        x = g
        while x not in H:
            H.add(x)
            x = S.mul(x, g)
        key = frozenset(H)
        if key in seen:
            continue
        seen.add(key)
        out.append(tuple(S.els[i] for i in range(len(S.els)) if S.els[i] in H))
    return out


def _witness_on(S, H):
    """A 3-cycle of the subgroup H on which omega does not vanish, or None."""
    if len(H) < 2:
        return None
    elts = [h for h in H if h != H[0]]
    C3, C2, M = normalised_d3(H, S.mul)
    # M has rows indexed by C_3 and columns by C_2: d_3 z is M^T z, so the
    # 3-cycles are the kernel of M^T (NOT of M -- the transposed kernel is the
    # kernel of d_3 on 2-chains, and vectors from it are not cycles).
    for v in M.T.nullspace():
        dens = [sp.denom(x) for x in v] or [sp.Integer(1)]
        L = reduce(sp.ilcm, dens)
        z = [int(x * L) for x in v]
        val = sum(coef * S.om(elts[C3[t][0]], elts[C3[t][1]], elts[C3[t][2]])
                  for t, coef in enumerate(z) if coef) % S.N
        if val:
            return {"subgroup": tuple(H), "generator_order": len(H),
                    "cycle": [(coef, tuple(elts[i] for i in C3[t]))
                              for t, coef in enumerate(z) if coef],
                    "omega_exponent_on_cycle": val}
    return None


def nontriviality_witness(S):
    """Find a cycle z in ker d_3 with omega(z) != 0.

    `System.lean`'s pentagon (R) is the standard inhomogeneous cocycle condition
    `delta omega = 0`, so `omega` is a 3-cocycle of the normalised bar complex.
    That complex computes H_3(G,Z), and `Q/Z` is injective, so `omega` is a
    coboundary if and only if it vanishes on ker d_3.  A *cycle* here is an
    integer combination of triples of non-identity elements in the kernel of
    d_3 -- not a single triple: a single triple is never a cycle, and "omega
    does not vanish on some triple" says nothing.  A non-vanishing cycle is a
    certificate that the class is non-zero (no completeness claim is needed for
    that direction; the complete decision is `is_coboundary`).  Cyclic subgroups
    are tried first because their certificates are small; a class can be
    invisible on every cyclic subgroup -- `(Z/3)^2` with `zeta^{a1 b2 c1}` is
    one -- so the whole group is tried as well.
    """
    for H in cyclic_subgroups(S):
        w = _witness_on(S, H)
        if w is not None:
            return w
    return _witness_on(S, S.els)


# ---------------------------------------------------------------------------
# one family's full fingerprint
# ---------------------------------------------------------------------------

def fingerprint(S):
    fp = {}
    fp["N"] = S.N
    fp["pentagon"] = not pentagon_failures(S, "repo")
    fp["old_convention"] = not pentagon_failures(S, "old")
    fp["snakes"] = not snake_failures(S)
    k = kappa(S)
    fp["kappa"] = tuple(k[g] for g in S.els)
    fp["kappa_char"] = is_character(S, k)
    j1, jdk = trivial_twist(S), honest_twist(S)
    kv1, kvdk = K_failures(S, j1), K_failures(S, jdk)
    fp["J1_laws"] = not j_law_failures(S, j1)
    fp["J1_Kviol_count"] = len(kv1)
    fp["J1_Kviol_channels"] = tuple(sorted({tuple(sorted((a, b))) for a, b in kv1}))
    fp["Jdk_laws"] = not j_law_failures(S, jdk)
    fp["Jdk_Kviol_count"] = len(kvdk)
    p = inverse_kappa(S)
    fp["p_pivotal"] = not pivotal_failures(S, jdk, p)
    fp["spherical"] = not spherical_failures(S, p)
    fp["dim_all_one"] = all(e == 0 for e in dims(S, p).values())
    fp["chars_with_dim_1_under_J1"] = tuple(
        tuple(c[g] for g in S.els) for c in homomorphisms(S)
        if all((c[g] + k[g]) % S.N == 0 for g in S.els))
    fp["J_orders"], fp["Jsq_orders"], _ = j_sq_report(S, jdk)
    piv = pivotal_structures(S, jdk)
    fp["num_pivotal"] = len(piv)
    fp["num_spherical"] = sum(1 for p in piv if not spherical_failures(S, p))
    fp["num_dim_FPdim"] = sum(1 for p in piv if all(e == 0 for e in dims(S, p).values()))
    fp["class_trivial"], mu = is_coboundary(S)
    if fp["class_trivial"]:
        assert all(delta(S, mu, x, y, z) == S.om(x, y, z) % S.N
                   for x in S.els for y in S.els for z in S.els), "mu does not trivialise omega"
    w = nontriviality_witness(S)
    fp["genuine"] = w is not None
    fp["witness_order"] = None if w is None else w["generator_order"]
    return fp


# ---------------------------------------------------------------------------
# the families
# ---------------------------------------------------------------------------

def zn(n):
    els = tuple((a,) for a in range(n))
    mul = lambda x, y: ((x[0] + y[0]) % n,)
    inv = lambda x: ((-x[0]) % n,)
    return els, mul, inv


def znk(n, k):
    els = tuple(product(range(n), repeat=k))
    mul = lambda x, y: tuple((a + b) % n for a, b in zip(x, y))
    inv = lambda x: tuple((-a) % n for a in x)
    return els, mul, inv


def d8():
    """D8 = <r,s | r^4 = s^2 = 1, s r s = r^-1>, elements (i,j) = r^i s^j."""
    els = tuple((i, j) for i in range(4) for j in range(2))
    mul = lambda x, y: ((x[0] + (y[0] if x[1] == 0 else -y[0])) % 4, (x[1] + y[1]) % 2)
    inv = lambda x: ((-x[0]) % 4, 0) if x[1] == 0 else ((x[0]) % 4, 1)
    return els, mul, inv


def s3():
    """S3 as the six permutations of (0,1,2), composed as x after y."""
    els = tuple(p for p in product(range(3), repeat=3) if len(set(p)) == 3)
    mul = lambda x, y: tuple(x[y[i]] for i in range(3))
    def inv(x):
        r = [0, 0, 0]
        for i, p in enumerate(x):
            r[p] = i
        return tuple(r)
    return els, mul, inv


def sign(p):
    return sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j]) % 2


def families():
    out = []

    els, mul, inv = znk(2, 2)
    out.append(Pointed("Vec^omega_(Z/2)^2, omega = (-1)^{a1 b2 c1}", els, mul, inv, 2,
                       lambda x, y, z: (x[0] * y[1] * z[0]) % 2))

    els, mul, inv = znk(3, 2)
    out.append(Pointed("Vec^omega_(Z/3)^2, omega = zeta^{a1 b2 c1} "
                       "(the proposal's example: a COBOUNDARY)", els, mul, inv, 3,
                       lambda x, y, z: (x[0] * y[1] * z[0]) % 3))

    # the same group, but a genuinely twisted cocycle: the product of the two
    # carry cocycles (the generator of H^3((Z/3)^2; mu_3), non-zero class)
    # multiplied by the coboundary above, which is what makes kappa a
    # non-character.  This is the honest J^2 != 1 witness.
    els, mul, inv = znk(3, 2)
    out.append(Pointed("Vec^omega_(Z/3)^2, omega = carry x carry x zeta^{a1 b2 c1} "
                       "(genuinely twisted)", els, mul, inv, 3,
                       lambda x, y, z: (x[0] * ((y[0] + z[0]) // 3)
                                        + x[1] * ((y[1] + z[1]) // 3)
                                        + x[0] * y[1] * z[0]) % 3))

    els, mul, inv = zn(3)
    out.append(Pointed("Vec^omega_Z/3, omega = zeta^{a floor((b+c)/3)} (carry)", els, mul, inv, 3,
                       lambda x, y, z: (x[0] * ((y[0] + z[0]) // 3)) % 3))

    els, mul, inv = d8()
    out.append(Pointed("Vec^omega_D8, omega = (-1)^{i(x) j(y) i(z)}", els, mul, inv, 2,
                       lambda x, y, z: (x[0] * y[1] * z[0]) % 2))

    els, mul, inv = s3()
    out.append(Pointed("Vec^omega_S3, omega = (-1)^{s(x) s(y) s(z)}", els, mul, inv, 2,
                       lambda x, y, z: (sign(x) * sign(y) * sign(z)) % 2))

    # controls
    els, mul, inv = znk(2, 2)
    out.append(Pointed("Vec_(Z/2)^2, omega = 1 (control)", els, mul, inv, 2,
                       lambda x, y, z: 0))

    els, mul, inv = zn(2)
    out.append(Pointed("Vec^omega_Z/2, omega = (-1)^{abc} (control)", els, mul, inv, 2,
                       lambda x, y, z: (x[0] * y[0] * z[0]) % 2))
    return out


# ---------------------------------------------------------------------------
# reference values, recorded once from this script and reviewed by hand
# ---------------------------------------------------------------------------

REFERENCE = {
    'Vec^omega_(Z/2)^2, omega = (-1)^{a1 b2 c1}': {
        'N': 2,
        'pentagon': True,
        'old_convention': True,
        'snakes': True,
        'kappa': (0, 0, 0, 1),
        'kappa_char': False,
        'J1_laws': True,
        'J1_Kviol_count': 6,
        'J1_Kviol_channels': (((0, 1), (1, 0)), ((0, 1), (1, 1)), ((1, 0), (1, 1))),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': (),
        'J_orders': [1, 2],
        'Jsq_orders': [1],
        'num_pivotal': 4,
        'num_spherical': 4,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 2,
    },
    "Vec^omega_(Z/3)^2, omega = zeta^{a1 b2 c1} (the proposal's example: a COBOUNDARY)": {
        'N': 3,
        'pentagon': True,
        'old_convention': False,
        'snakes': True,
        'kappa': (0, 0, 0, 0, 1, 2, 0, 1, 2),
        'kappa_char': False,
        'J1_laws': True,
        'J1_Kviol_count': 36,
        'J1_Kviol_channels': (((0, 1), (1, 0)), ((0, 1), (1, 1)), ((0, 1), (1, 2)), ((0, 1), (2, 0)), ((0, 1), (2, 1)), ((0, 1), (2, 2)), ((0, 2), (1, 0)), ((0, 2), (1, 1)), ((0, 2), (1, 2)), ((0, 2), (2, 0)), ((0, 2), (2, 1)), ((0, 2), (2, 2)), ((1, 0), (2, 1)), ((1, 0), (2, 2)), ((1, 1), (2, 0)), ((1, 1), (2, 1)), ((1, 2), (2, 0)), ((1, 2), (2, 2))),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': (),
        'J_orders': [1, 3],
        'Jsq_orders': [1, 3],
        'num_pivotal': 9,
        'num_spherical': 1,
        'num_dim_FPdim': 1,
        'class_trivial': True,
        'genuine': False,
        'witness_order': None,
    },
    'Vec^omega_(Z/3)^2, omega = carry x carry x zeta^{a1 b2 c1} (genuinely twisted)': {
        'N': 3,
        'pentagon': True,
        'old_convention': False,
        'snakes': True,
        'kappa': (0, 2, 1, 2, 2, 2, 1, 1, 1),
        'kappa_char': False,
        'J1_laws': True,
        'J1_Kviol_count': 36,
        'J1_Kviol_channels': (((0, 1), (1, 0)), ((0, 1), (1, 1)), ((0, 1), (1, 2)), ((0, 1), (2, 0)), ((0, 1), (2, 1)), ((0, 1), (2, 2)), ((0, 2), (1, 0)), ((0, 2), (1, 1)), ((0, 2), (1, 2)), ((0, 2), (2, 0)), ((0, 2), (2, 1)), ((0, 2), (2, 2)), ((1, 0), (2, 1)), ((1, 0), (2, 2)), ((1, 1), (2, 0)), ((1, 1), (2, 1)), ((1, 2), (2, 0)), ((1, 2), (2, 2))),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': (),
        'J_orders': [1, 3],
        'Jsq_orders': [1, 3],
        'num_pivotal': 9,
        'num_spherical': 1,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 3,
    },
    'Vec^omega_Z/3, omega = zeta^{a floor((b+c)/3)} (carry)': {
        'N': 3,
        'pentagon': True,
        'old_convention': False,
        'snakes': True,
        'kappa': (0, 2, 1),
        'kappa_char': True,
        'J1_laws': True,
        'J1_Kviol_count': 0,
        'J1_Kviol_channels': (),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': ((0, 1, 2),),
        'J_orders': [1],
        'Jsq_orders': [1],
        'num_pivotal': 3,
        'num_spherical': 1,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 3,
    },
    'Vec^omega_D8, omega = (-1)^{i(x) j(y) i(z)}': {
        'N': 2,
        'pentagon': True,
        'old_convention': True,
        'snakes': True,
        'kappa': (0, 0, 0, 1, 0, 0, 0, 1),
        'kappa_char': False,
        'J1_laws': True,
        'J1_Kviol_count': 24,
        'J1_Kviol_channels': (((0, 1), (1, 0)), ((0, 1), (1, 1)), ((0, 1), (3, 0)), ((0, 1), (3, 1)), ((1, 0), (1, 1)), ((1, 0), (2, 1)), ((1, 0), (3, 1)), ((1, 1), (2, 1)), ((1, 1), (3, 0)), ((2, 1), (3, 0)), ((2, 1), (3, 1)), ((3, 0), (3, 1))),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': (),
        'J_orders': [1, 2],
        'Jsq_orders': [1],
        'num_pivotal': 4,
        'num_spherical': 4,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 2,
    },
    'Vec^omega_S3, omega = (-1)^{s(x) s(y) s(z)}': {
        'N': 2,
        'pentagon': True,
        'old_convention': True,
        'snakes': True,
        'kappa': (0, 1, 1, 0, 0, 1),
        'kappa_char': True,
        'J1_laws': True,
        'J1_Kviol_count': 0,
        'J1_Kviol_channels': (),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': ((0, 1, 1, 0, 0, 1),),
        'J_orders': [1],
        'Jsq_orders': [1],
        'num_pivotal': 2,
        'num_spherical': 2,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 2,
    },
    'Vec_(Z/2)^2, omega = 1 (control)': {
        'N': 2,
        'pentagon': True,
        'old_convention': True,
        'snakes': True,
        'kappa': (0, 0, 0, 0),
        'kappa_char': True,
        'J1_laws': True,
        'J1_Kviol_count': 0,
        'J1_Kviol_channels': (),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': ((0, 0, 0, 0),),
        'J_orders': [1],
        'Jsq_orders': [1],
        'num_pivotal': 4,
        'num_spherical': 4,
        'num_dim_FPdim': 1,
        'class_trivial': True,
        'genuine': False,
        'witness_order': None,
    },
    'Vec^omega_Z/2, omega = (-1)^{abc} (control)': {
        'N': 2,
        'pentagon': True,
        'old_convention': True,
        'snakes': True,
        'kappa': (0, 1),
        'kappa_char': True,
        'J1_laws': True,
        'J1_Kviol_count': 0,
        'J1_Kviol_channels': (),
        'Jdk_laws': True,
        'Jdk_Kviol_count': 0,
        'p_pivotal': True,
        'spherical': True,
        'dim_all_one': True,
        'chars_with_dim_1_under_J1': ((0, 1),),
        'J_orders': [1],
        'Jsq_orders': [1],
        'num_pivotal': 2,
        'num_spherical': 2,
        'num_dim_FPdim': 1,
        'class_trivial': False,
        'genuine': True,
        'witness_order': 2,
    },
}


def verify_against_reference(fps):
    bad = []
    for name, fp in fps.items():
        ref = REFERENCE.get(name)
        if ref is None:
            bad.append((name, "no reference record"))
            continue
        for key, want in ref.items():
            if fp.get(key) != want:
                bad.append((name, key, fp.get(key), want))
    return bad


# ---------------------------------------------------------------------------
# self-test: negative fixtures, every check must reject at least one
# ---------------------------------------------------------------------------

def selftest():
    """Every fixture is (label, check, is_rejected) with is_rejected required True."""
    results = []

    els, mul, inv = znk(2, 2)
    # a cochain that is not a cocycle: flip one value of the (Z/2)^2 cocycle
    bad_om = lambda x, y, z: ((x[0] * y[1] * z[0]) + (1 if (x, y, z) == ((1, 0), (0, 1), (1, 0)) else 0)) % 2
    S = Pointed("non-cocycle", els, mul, inv, 2, bad_om)
    results.append(("non_cocycle_rejected", "pentagon", bool(pentagon_failures(S, "repo"))))

    # the old script's carry cocycle on Z/3 is identically 1
    els, mul, inv = zn(3)
    old = Pointed("old carry", els, mul, inv, 3,
                  lambda x, y, z: 0)  # zeta = exp(2 pi i/3), exponent a(b+c-[b+c]) is a multiple of 3
    results.append(("old_carry_is_vacuous", "genuinely non-trivial",
                    not fingerprint(old)["genuine"] and
                    len(set(old.om(g, h, i) for g in old.els for h in old.els for i in old.els)) == 1))

    # the genuine carry cocycle fails the *old* pentagon convention but passes (R)
    els, mul, inv = zn(3)
    carry = Pointed("carry", els, mul, inv, 3,
                    lambda x, y, z: (x[0] * ((y[0] + z[0]) // 3)) % 3)
    results.append(("old_convention_fails", "pentagon (R) accepted, (S) rejected",
                    not pentagon_failures(carry, "repo") and bool(pentagon_failures(carry, "old"))))

    # a coboundary: omega = delta(mu) with mu(a,b) = a^2 b on Z/3 (in exponents,
    # delta(mu)(a,b,c) = -2abc = abc).  It IS a cocycle, so the pentagon must pass,
    # and the non-triviality search must find NO witness (it is a coboundary).
    els, mul, inv = zn(3)
    mu = lambda a, b: (a[0] * a[0] * b[0]) % 3
    cob_om = lambda a, b, c: (mu(b, c) - mu(mul(a, b), c) + mu(a, mul(b, c)) - mu(a, b)) % 3
    S = Pointed("coboundary", els, mul, inv, 3, cob_om)
    results.append(("coboundary_has_no_witness", "pentagon accepted, no witness",
                    not pentagon_failures(S, "repo")
                    and cob_om((1,), (1,), (1,)) != 0
                    and nontriviality_witness(S) is None))

    # the (Z/2)^2 datum, used by the fixtures below
    els, mul, inv = znk(2, 2)
    S = Pointed("Vec^omega_(Z/2)^2, omega = (-1)^{a1 b2 c1}", els, mul, inv, 2,
                lambda x, y, z: (x[0] * y[1] * z[0]) % 2)

    # J = 1 where (M) fails: the (K) check must reject it
    j1, jdk = trivial_twist(S), honest_twist(S)
    results.append(("trivial_twist_rejected", "(K) on (Z/2)^2",
                    bool(K_failures(S, j1)) and not K_failures(S, jdk)))

    # a single flipped channel of the honest twist must break a J law
    flipped = dict(jdk)
    flipped[((1, 0), (0, 1))] = 1 - flipped[((1, 0), (0, 1))]
    results.append(("flipped_J_rejected", "J laws",
                    bool(j_law_failures(S, flipped)) or bool(K_failures(S, flipped))))

    # p = 1 must fail p_mon under the honest twist, p = 1/kappa must pass
    p_one = {g: 0 for g in S.els}
    p_honest = inverse_kappa(S)
    results.append(("wrong_p_rejected", "p_mon",
                    bool(pivotal_failures(S, jdk, p_one)) and
                    not pivotal_failures(S, jdk, p_honest)))

    # a twist other than delta(kappa) must fail (K): on (Z/3)^2, J and J^-1 differ
    els, mul, inv = znk(3, 2)
    S3sq = Pointed("z3sq", els, mul, inv, 3, lambda x, y, z: (x[0] * y[1] * z[0]) % 3)
    jdk3 = honest_twist(S3sq)
    inv_twist = {(a, b): (-v) % S3sq.N for (a, b), v in jdk3.items()}
    results.append(("inverse_twist_rejected", "(K) on (Z/3)^2",
                    bool(K_failures(S3sq, inv_twist))))

    # sphericity is not automatic once labels are not self-dual: on the Z/3
    # carry datum p = 1 is pivotal (J = 1) but dim g != dim g*
    els, mul, inv = zn(3)
    S3cyc = Pointed("z3carry", els, mul, inv, 3,
                    lambda x, y, z: (x[0] * ((y[0] + z[0]) // 3)) % 3)
    results.append(("nonspherical_p_rejected", "spherical",
                    not pivotal_failures(S3cyc, trivial_twist(S3cyc),
                                         {g: 0 for g in S3cyc.els})
                    and bool(spherical_failures(S3cyc, {g: 0 for g in S3cyc.els}))))

    # the reference mechanism itself must fire on a perturbed fingerprint
    fp = fingerprint(S)
    fp_bad = dict(fp)
    fp_bad["kappa"] = tuple((v + 1) % S.N for v in fp["kappa"])
    saved = dict(REFERENCE)
    REFERENCE[S.name] = dict(fp)
    caught = bool(verify_against_reference({S.name: fp_bad}))
    REFERENCE.clear()
    REFERENCE.update(saved)
    results.append(("reference_check_is_live", "reference comparison", caught))

    return results


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------

def describe(S, fp):
    k = kappa(S)
    print(f"--- {S.name} ---")
    print(f"  order {len(S.els)}, omega in mu_{S.N}, "
          f"pentagon (R): {fp['pentagon']}, old convention (S): {fp['old_convention']}")
    print(f"  snakes (left/right, kappa kappa* = 1): {fp['snakes']}")
    print(f"  kappa exponents {list(fp['kappa'])}; kappa a character: {fp['kappa_char']}")
    w = nontriviality_witness(S)
    triv, mu = is_coboundary(S)
    if triv:
        print("  the class of omega is ZERO: omega = delta mu (exact elimination over "
              f"Z/{S.N}) -- a gauge-trivial associator")
    else:
        print("  the class of omega is NON-ZERO (no 2-cochain trivialises it)")
    if w is None:
        print("  no non-vanishing 3-cycle found: consistent with a trivial class")
    else:
        print(f"  non-triviality witness: cyclic subgroup of order {w['generator_order']}, "
              f"3-cycle with omega-exponent {w['omega_exponent_on_cycle']} (mod {S.N})")
    print(f"  J = 1      : J laws {fp['J1_laws']}, (K)/(M) violations "
          f"{fp['J1_Kviol_count']} ordered pairs"
          f" ({len(fp['J1_Kviol_channels'])} channels)"
          + (f" {list(fp['J1_Kviol_channels'])}" if fp['J1_Kviol_channels'] else ""))
    print(f"  J = dkappa : J laws {fp['Jdk_laws']}, (K)/(M) violations {fp['Jdk_Kviol_count']}")
    print(f"  p = 1/kappa: p_mon {fp['p_pivotal']}, spherical {fp['spherical']}, "
          f"dim = FPdim = 1 on every simple {fp['dim_all_one']}")
    print(f"  pivotal structures under J = dkappa: {fp['num_pivotal']} "
          f"(spherical {fp['num_spherical']}, dim = FPdim {fp['num_dim_FPdim']}) "
          f"-- ENO 8.23 picks out the last one")
    if not fp["kappa_char"]:
        print(f"  under J = 1, characters p with dim = FPdim = 1: "
              f"{len(fp['chars_with_dim_1_under_J1'])} (exhaustive)")
    print(f"  orders of the honest J on its channels {fp['J_orders']}, "
          f"of J^2 {fp['Jsq_orders']}")
    print()


def main(argv):
    fams = families()
    fps = {}
    for S in fams:
        fp = fingerprint(S)
        fps[S.name] = fp
        describe(S, fp)

    if "--record" in argv:
        print("REFERENCE = {")
        for name, fp in fps.items():
            print(f"    {name!r}: {{")
            for key, val in fp.items():
                print(f"        {key!r}: {val!r},")
            print("    },")
        print("}")
        return 0

    ok = True
    print("=== reference comparison ===")
    if not REFERENCE:
        print("FAIL: no reference table")
        ok = False
    bad = verify_against_reference(fps)
    for row in bad:
        print(f"FAIL: {row}")
    if not bad and REFERENCE:
        print(f"  all {len(fps)} families agree with the reference table")
    ok = ok and not bad

    print()
    print("=== self-test (negative fixtures) ===")
    for label, what, rejected in selftest():
        status = "rejected as required" if rejected else "ACCEPTED -- checker is broken"
        print(f"  {label:28s} [{what}] {status}")
        ok = ok and rejected

    print()
    # the census conclusion, as assertions
    concl = [
        ("at least four genuinely non-trivial cocycles (non-zero class)",
         sum(1 for fp in fps.values() if not fp["class_trivial"]) >= 4),
        ("the witness search and the exact triviality test agree on every family",
         all(fp["genuine"] == (not fp["class_trivial"]) for fp in fps.values())),
        ("every family satisfies the repo pentagon (R)",
         all(fp["pentagon"] for fp in fps.values())),
        ("every family satisfies both snakes",
         all(fp["snakes"] for fp in fps.values())),
        ("J = dkappa satisfies (K)/(M) everywhere",
         all(fp["Jdk_Kviol_count"] == 0 for fp in fps.values())),
        ("some family separates J = 1 from J = dkappa",
         any(fp["J1_Kviol_count"] > 0 for fp in fps.values())),
        ("at least one family has a non-zero class and a non-character kappa",
         any(not fp["class_trivial"] and not fp["kappa_char"] for fp in fps.values())),
        ("some family has a non-zero class but kappa a character",
         any(not fp["class_trivial"] and fp["kappa_char"] for fp in fps.values())),
        ("some family has J^2 != 1 (J^2 a primitive cube root)",
         any(3 in fp["Jsq_orders"] for fp in fps.values())),
        ("the J^2 != 1 witness has a genuinely non-trivial cocycle",
         any(3 in fp["Jsq_orders"] and not fp["class_trivial"] for fp in fps.values())),
        ("every family has exactly one pivotal structure with dim = FPdim = 1",
         all(fp["num_dim_FPdim"] == 1 for fp in fps.values())),
        ("no family admits a character p with dim = FPdim under J = 1 where kappa is not a character",
         all(not fp["chars_with_dim_1_under_J1"] for fp in fps.values()
             if not fp["kappa_char"])),
    ]
    print("=== census conclusions ===")
    for label, holds in concl:
        print(f"  {'PASS' if holds else 'FAIL'}  {label}")
        ok = ok and holds

    print()
    print("OVERALL:", "GREEN" if ok else "RED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
