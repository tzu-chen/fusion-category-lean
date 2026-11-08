#!/usr/bin/env python3
"""Bartlett comparison (WP3 Task 3.5): his closed form for the double-dual
tensorator against ours, index by index, in exact arithmetic.

WHAT IS COMPARED.  Two independent closed forms for the same object.

(1) Bartlett, *Fusion categories via string diagrams*, arXiv:1502.02882v2.

  * Definition (apex associators, his sec. 4.3): in a trivalent basis
        (S_ijk)_{ba} = (F^1_{ijk})^{eta_k k* b}_{eta_{i*} i* a},
    the associator matrix element with the top strand the identity.  In a
    multiplicity-free datum both internal channels are forced, so S_ijk is a
    scalar.  The *apex associator monodromy* is A_ijk = S_jki S_kij S_ijk.
  * Theorem 4.17: in a *fair basis* the pivotal operator is
        T^i_jk = p_i p_j p_k Y^{-1} A_{i* j k} Y,
    with p_i the pivotal indicator (the sign of a_i = F^{i i* i}_i(0,0), his
    Def 4.9) and Y trivial in the multiplicity-free case.
  * Theorem 5.4: pivotal structures <-> gamma in U(1)^I with
        gamma_j gamma_k = gamma_i T^i_jk    on every fusion channel.      (B)
  * Corollary 3.26: pivotal symbols satisfy the F-free coherence law
        eps^i_{jk,a} eps^m_{kl,b} = eps^i_{nl,c} eps^n_{jk,d}
    *whenever* (F^i_{jkl})^{c n d}_{a m b} != 0 -- his own nonzero-entry
    qualification.  Corollary 3.30: the quadruple-dual functor is monoidally
    the identity (the tree's `J` is the double-dual tensorator, so this is the
    paper's counterpart of the tree's `FusionSystem`, not of its `J` alone).
    Published values used as checks below: Yang-Lee p(tau) = -1 (Ex 4.10),
    S_ttt = 1 (Ex 4.13), T^tau_tt = -1 (Ex 4.19), d_tau = (sqrt 5 - 1)/2
    (Ex 3.4).

(2) The tree: `DerivedJScalar.comparisonScalar` / `derivedJGen` (the channel
    scalar of the comparison psi_{x,y} : (x (x) y)* -> y* (x) x*, and the ratio
    psi_{a,b}|_c / psi_{b*,a*}|_{c*}), `DoubleDualTensorator.omegaCoeff` (the
    ev-free form of the same, `derivedJGen_eq_omegaCoeff`), and the pivotal law
    of `Pivotal.lean`:

        pi c = J a b c * pi a * pi b   on every channel,                 (T)

    so the tree's J sits exactly where Bartlett's 1/T sits: J^c_ab =
    pi_c/(pi_a pi_b) against his T^i_jk = gamma_j gamma_k / gamma_i.  (pi is
    the library's pivotal scalar; p_i below is Bartlett's *indicator*, a
    different symbol -- they must not be confused.)

THE DICTIONARY, index by index.  With d_i = sqrt(kappa_i kappa_{i*}) the
positive fusion dimension, sigma_i = d_i/kappa_i, delta(sigma)^c_ab =
sigma_c/(sigma_a sigma_b) and pi_i = gamma_i sigma_i (the two frameworks'
pivotal structures differ by the dimension normalisation -- both compute the
same categorical dimension, dim = pi_i kappa_i = gamma_i d_i):

        J^c_ab = delta(sigma)^c_ab / T^c_ab .                            (D)

On all six data sets of the tree `dual = id`, kappa is real, d_i = |kappa_i|
and sigma_i = p_i in {+-1}, so (D) collapses to

        J^c_ab = 1 / A_{c* a b}      (c* = dual c),                      (E)

and, expanded through `omegaCoeff` (which is what the tree proves, so that the
ev factors cancel), to the F/Finv identity

  F a b c* 0 c a* . Finv b b* a* a* c* 0 . A_{c* a b}
              = F b* a* c 0 c* b . Finv a* a b b c 0 .                (F)

I.e. the F/Finv product in `comparisonScalar`'s denominator is *exactly* the
product of the other two apex associators.  (D), (E), (F) and the omegaCoeff
identity are what this script checks, channel by channel.

WHY a_i = 1/kappa_i IS NOT AN ASSUMPTION.  The tree's left snake is
`FusionSystem.kappa_loop`: kappa_i * F^{i i* i}_i(0,0) = 1, which is exactly
Bartlett's a_i = F^{i i* i}_i(0,0) = 1/kappa_i (his (28a)); the script checks
that relation on every data set.  A datum is a *fair basis* (his hypothesis for
Thm 4.17) iff a_i = +-1/d_i; the script decides that exactly, per datum.

RESULTS (exact arithmetic: every equality below is a decision in Q(sqrt D),
no floating point enters one; floats are used for display and as candidates
only, and candidates are verified exactly before use).
  * All six data sets of the tree agree with Bartlett's formula on every
    supported channel -- 44 channels, 0 mismatches, for (D), (E), (F) and the
    omegaCoeff identity.
  * His published Yang-Lee numbers are reproduced from `YangLee.F`/`coev`.
  * The F-free coherence law of his Cor 3.26 holds on every pentagon instance
    with F != 0 (146 of them).
  * A control datum `Vec^omega_{Z/4}` with i* != i and a nontrivial cocycle
    (not in the tree) also agrees on all 16 channels.
  * Negative controls, i.e. the comparison is shown to be able to fail: drop
    the `Finv` factor from `comparisonScalar`, drop one of the three apex
    factors from the monodromy, or negate one composite-0 `F` entry, and the
    run reports mismatches.  (Only *composite-0* `F` entries can matter: they
    are the ones `comparisonScalar` and the apex associator read.)

WHAT THIS CENSUS CANNOT DECIDE, and what does decide it.  Every apex
monodromy on the six tree data sets is +-1, so `J = T` and `J = 1/T` agree
there: the reciprocal of Bartlett's convention is fixed by the *law* -- his
Thm 5.4 `gamma_j gamma_k = gamma_i T^i_jk` against the tree's `p_mon`
`p_c = J a b c * p_a * p_b` -- and not by these numbers.  For the same reason
(table values are +-1 or units of Q(sqrt d)) the census cannot separate
`psi_{a,b}` from `psi_{b,a}` inside the ratio; what separates them is the
derivation of `comparisonScalar` from the mate equation, which the tree proves
as `comparisonScalar_spec` against the six-index tensor-structure pairing.
See `.ultramath/smw7dod9a/m6/FINDINGS.md` for the write-up and for the two
limitations this census cannot remove: (i) `dual = id` on every tree datum
makes the apex entry insensitive to which of the two channel slots carries i*
(they coincide), and the control is the cheapest datum that separates them;
(ii) the fair-basis hypothesis fails on `Vec^omega_{Z/3}` (kappa there is a
primitive cube root of unity, not real), so Bartlett's Thm 4.17 as stated does
not cover the tree's still-owed `i* != i` witness -- that needs the complex
`gamma` version of his Thm 5.4 and is out of scope of this comparison.

One *consequence* is recorded at the end, labelled and not part of the
comparison: the twist Bartlett's formula produces is the honest one, and the
(K) table `Prop821CNorm.settledJ` agrees with it on five of the six data sets
but not on Yang-Lee, where the honest (derived) twist is 1 on both tau (x) tau
channels.  That is the WP3 non-goal ("the per-channel identity fails for
Yang-Lee"), not a defect of the closed form.

Run:  python3 FusionCategory/docs/bartlett_check.py [-v]
Exit status 0 iff every comparison check passes.
"""
import math
import sys
from fractions import Fraction


# ---------------------------------------------------------------------------
# Exact arithmetic: p + q*sqrt(D) with p, q in Q; D is 1 (rationals), 2 or 5.
# ---------------------------------------------------------------------------
def _align(x, y):
    """Bring two elements into a common field Q(sqrt D).  The only two cases
    that can occur here are `same D` and `one of them rational`."""
    if isinstance(y, (int, Fraction)):
        y = Surd(y, 0, x.D)
    if isinstance(x, (int, Fraction)):
        x = Surd(x, 0, y.D)
    if x.D == y.D:
        return x, y
    if y.q == 0:
        return x, Surd(y.p, 0, x.D)
    if x.q == 0:
        return Surd(x.p, 0, y.D), y
    raise AssertionError(f"incommensurable: {x} and {y}")


class Surd:
    """p + q*sqrt(D), p and q in Q.  D = 1 is canonicalised to q = 0."""
    __slots__ = ('p', 'q', 'D')

    def __init__(self, p=0, q=0, D=1):
        p, q = Fraction(p), Fraction(q)
        if D == 1:                       # rationals: canonical form q = 0
            p, q = p + q, Fraction(0)
        self.p, self.q, self.D = p, q, D

    def __add__(self, o):
        x, y = _align(self, o)
        return Surd(x.p + y.p, x.q + y.q, x.D)

    __radd__ = __add__

    def __neg__(self):
        return Surd(-self.p, -self.q, self.D)

    def __sub__(self, o):
        return self + (-o if isinstance(o, Surd) else -Surd(o, 0, self.D))

    def __rsub__(self, o):
        return Surd(o, 0, self.D) + (-self)

    def __mul__(self, o):
        x, y = _align(self, o)
        return Surd(x.p * y.p + x.q * y.q * x.D, x.p * y.q + x.q * y.p, x.D)

    __rmul__ = __mul__

    def __truediv__(self, o):
        x, y = _align(self, o)
        den = y.p * y.p - y.q * y.q * y.D          # the conjugate norm
        assert den != 0, "division by zero in Q(sqrt D)"
        return x * Surd(y.p / den, -y.q / den, x.D)

    def is_zero(self):
        return self.p == 0 and self.q == 0

    def __bool__(self):
        return not self.is_zero()

    def __eq__(self, o):
        x, y = _align(self, o)
        return x.p == y.p and x.q == y.q

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.p, self.q, self.D))

    def val(self):
        return float(self.p) + float(self.q) * math.sqrt(self.D)

    def __repr__(self):
        if self.q == 0:
            return str(self.p)
        return f"({self.p} + {self.q}*sqrt({self.D}))"


ZERO = Surd(0, 0, 1)
ONE = Surd(1, 0, 1)


# ---------------------------------------------------------------------------
# The data sets.  Each is the tuple (N, dual, F, Finv, ev, coev) of
# `FusionCategory.System.FusionSystem`, transcribed from the Lean declaration
# named in its comment.  `D` is the quadratic field; the Lean files' `ZP.zval`
# of a pair (p, q) is (p + q sqrt D)/2, which is what `half` computes.
# ---------------------------------------------------------------------------
def supported(N, a, b, c, d, e, f):
    """`FusionSystem.F_support`'s hypothesis."""
    return (N(a, b, e) > 0 and N(e, c, d) > 0
            and N(b, c, f) > 0 and N(a, f, d) > 0)


def half(D, pair):
    return Surd(Fraction(pair[0], 2), Fraction(pair[1], 2), D)


def build(n, D, N, dual, Fblk, Finvblk, evblk, coevblk):
    def F(a, b, c, d, e, f):
        return half(D, Fblk(a, b, c, d, e, f)) if supported(N, a, b, c, d, e, f) else ZERO

    def Finv(a, b, c, d, f, e):
        ok = (N(b, c, f) > 0 and N(a, f, d) > 0
              and N(a, b, e) > 0 and N(e, c, d) > 0)
        return half(D, Finvblk(a, b, c, d, f, e)) if ok else ZERO

    return dict(n=n, D=D, N=N, dual=dual, F=F, Finv=Finv,
                ev=lambda i: half(D, evblk(i)),
                coev=lambda i: half(D, coevblk(i)))


def fib_N(a, b, c):
    """Examples/FibonacciIsing.lean `Fibonacci.N`, reused as `YangLee.N`."""
    if a == 0:
        return 1 if b == c else 0
    if b == 0:
        return 1 if a == c else 0
    return 1


def vecz2_N(a, b, c):
    """System.lean `VecZ2.N` (0 = 1, 1 = g)."""
    if a == 0:
        return 1 if b == c else 0
    if b == 0:
        return 1 if a == c else 0
    return 1 if c == 0 else 0


def gadd(a, b):
    """Examples/Z2SqHonest.lean `Z2SqH.gadd` (label = 2*(high bit) + low bit)."""
    return ((a % 2 + b % 2) % 2) + 2 * ((a // 2 + b // 2) % 2)


def z2sq_N(a, b, c):
    """Examples/Z2SqHonest.lean `Z2SqH.N`."""
    return 1 if c == gadd(a, b) else 0


def ising_N(a, b, c):
    """Examples/FibonacciIsing.lean `Ising.N` (0 = 1, 1 = sigma, 2 = psi)."""
    if a == 0:
        return 1 if b == c else 0
    if b == 0:
        return 1 if a == c else 0
    if a == 1 and b == 1:
        return 1 if c in (0, 2) else 0
    if a == 1 and b == 2:
        return 1 if c == 1 else 0
    if a == 2 and b == 1:
        return 1 if c == 1 else 0
    if a == 2 and b == 2:
        return 1 if c == 0 else 0
    return 0


def IDENT(i):
    return i


def vecz2():
    """System.lean `VecZ2.system`: F = Finv = 1 on support, ev = coev = 1."""
    return build(2, 1, vecz2_N, IDENT,
                 lambda a, b, c, d, e, f: (2, 0),
                 lambda a, b, c, d, f, e: (2, 0),
                 lambda i: (2, 0), lambda i: (2, 0))


def vecz2twisted():
    """System.lean `VecZ2Twisted.system`: F = -1 on the all-g block, kappa g = -1."""
    def Fblk(a, b, c, d, e, f):
        return (-2, 0) if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    def Finvblk(a, b, c, d, f, e):
        return (-2, 0) if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    return build(2, 1, vecz2_N, IDENT, Fblk, Finvblk,
                 lambda i: (2, 0),
                 lambda i: (2, 0) if i == 0 else (-2, 0))


def z2sqh():
    """Examples/Z2SqHonest.lean `Z2SqH.systemH`: omega = (-1)^(a1 b2 c1),
    coev i = omega(i,i,i); kappa = (1,1,1,-1)."""
    def wZ(a, b, c):
        return -1 if (a // 2 == 1 and b % 2 == 1 and c // 2 == 1) else 1

    return build(4, 1, z2sq_N, IDENT,
                 lambda a, b, c, d, e, f: (2 * wZ(a, b, c), 0),
                 lambda a, b, c, d, f, e: (2 * wZ(a, b, c), 0),
                 lambda i: (2, 0),
                 lambda i: (2 * wZ(i, i, i), 0))


def fibonacci():
    """Examples/FibonacciIsing.lean `Fibonacci`: F^(tau tau tau)_tau =
    [[1/phi, 1], [1/phi, -1/phi]] (rows e, columns f); kappa tau = phi."""
    blk = {(0, 0): (-1, 1), (0, 1): (2, 0), (1, 0): (-1, 1), (1, 1): (1, -1)}

    def Fblk(a, b, c, d, e, f):
        return blk[(e, f)] if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    def Finvblk(a, b, c, d, f, e):
        return blk[(f, e)] if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    return build(2, 5, fib_N, IDENT, Fblk, Finvblk,
                 lambda i: (2, 0), lambda i: (2, 0) if i == 0 else (1, 1))


def yanglee():
    """Examples/YangLee.lean `YangLee`: F^(tau tau tau)_tau = [[-phi, 1],
    [-phi, phi]]; coev tau = -1/phi, so kappa tau = -1/phi."""
    blk = {(0, 0): (-1, -1), (0, 1): (2, 0), (1, 0): (-1, -1), (1, 1): (1, 1)}

    def Fblk(a, b, c, d, e, f):
        return blk[(e, f)] if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    def Finvblk(a, b, c, d, f, e):
        return blk[(f, e)] if (a, b, c, d) == (1, 1, 1, 1) else (2, 0)

    return build(2, 5, fib_N, IDENT, Fblk, Finvblk,
                 lambda i: (2, 0), lambda i: (2, 0) if i == 0 else (1, -1))


def ising():
    """Examples/FibonacciIsing.lean `Ising`: F^(sigma sigma sigma)_sigma =
    (1/sqrt 2)[[1,1],[1,-1]] in the channel basis (1, psi); F^(sigma psi
    sigma)_psi = F^(psi sigma psi)_sigma = -1; kappa sigma = sqrt 2."""
    def Fblk(a, b, c, d, e, f):
        if (a, b, c, d) == (1, 1, 1, 1):
            return (0, 1) if (e, f) in ((0, 0), (0, 2), (2, 0)) else (0, -1)
        if (a, b, c, d, e, f) == (1, 2, 1, 2, 1, 1):
            return (-2, 0)
        if (a, b, c, d, e, f) == (2, 1, 2, 1, 1, 1):
            return (-2, 0)
        return (2, 0)

    def Finvblk(a, b, c, d, f, e):
        if (a, b, c, d) == (1, 1, 1, 1):
            return (0, 1) if (f, e) in ((0, 0), (0, 2), (2, 0)) else (0, -1)
        if (a, b, c, d, f, e) == (1, 2, 1, 2, 1, 1):
            return (-2, 0)
        if (a, b, c, d, f, e) == (2, 1, 2, 1, 1, 1):
            return (-2, 0)
        return (2, 0)

    return build(3, 2, ising_N, IDENT, Fblk, Finvblk,
                 lambda i: (2, 0), lambda i: (0, 2) if i == 1 else (2, 0))


# --- control datum, not in the tree ----------------------------------------
def z4_N(a, b, c):
    return 1 if c == (a + b) % 4 else 0


def z4_dual(i):
    return (-i) % 4


def z4_om(a, b, c):
    """(-1)^(a floor((b+c)/4)), the square of the generator
    i^(a floor((b+c)/4)) of H^3(Z/4); real, and nontrivial on the support."""
    return -1 if (a * ((b + c) // 4)) % 2 == 1 else 1


def z4_control():
    """`Vec^omega_{Z/4}` with i* = -i.  Not in the tree; included because all
    six tree data sets have `dual = id`, so none of them exercises the branch
    i* != i of any formula above."""
    return build(4, 1, z4_N, z4_dual,
                 lambda a, b, c, d, e, f: (2 * z4_om(a, b, c), 0),
                 lambda a, b, c, d, f, e: (2 * z4_om(a, b, c), 0),
                 lambda i: (2, 0),
                 lambda i: (2 * z4_om(i, z4_dual(i), i), 0))


TREE = [('VecZ2', vecz2()), ('VecZ2Twisted', vecz2twisted()),
        ('Z2SqH.systemH', z2sqh()), ('YangLee', yanglee()),
        ('Fibonacci', fibonacci()), ('Ising', ising())]
CONTROL = [('control Vec^omega_{Z/4} (i* != i, nontrivial cocycle)', z4_control())]


# ---------------------------------------------------------------------------
# The two sides of the comparison.
# ---------------------------------------------------------------------------
def kappa(S, i):
    """`FusionSystem.kappa`: coev i * ev i."""
    return S['coev'](i) * S['ev'](i)


def comparison_scalar(S, x, y, z):
    """`DerivedJScalar.comparisonScalar`:
    ev z / (F y* x* z 0 z* y * Finv x* x y y z 0 * ev x * ev y)."""
    du = S['dual']
    den = (S['F'](du(y), du(x), z, 0, du(z), y)
           * S['Finv'](du(x), x, y, y, z, 0)
           * S['ev'](x) * S['ev'](y))
    return None if den.is_zero() else S['ev'](z) / den


def derived_j(S, a, b, c):
    """`DerivedJScalar.derivedJGen`: psi_{a,b}|_c / psi_{b*,a*}|_{c*}."""
    du = S['dual']
    n1 = comparison_scalar(S, a, b, c)
    n2 = comparison_scalar(S, du(b), du(a), du(c))
    if n1 is None or n2 is None or n2.is_zero():
        return None
    return n1 / n2


def apex(S, i, j, k):
    """Bartlett's apex associator S_ijk = F i j k 0 k* i* (multiplicity-free)."""
    du = S['dual']
    return S['F'](i, j, k, 0, du(k), du(i))


def monodromy(S, i, j, k):
    """Bartlett's A_ijk = S_jki S_kij S_ijk."""
    return apex(S, j, k, i) * apex(S, k, i, j) * apex(S, i, j, k)


def exact_sqrt(S, x):
    """The positive square root of x in Q(sqrt D).  The candidate comes from a
    float; the *exact* verification is what decides, and a miss is an error."""
    for q in range(0, 17):
        for p in range(-64, 65):
            for qq in ({0, q, -q} if q else {0}):
                cand = Surd(Fraction(p, 2), Fraction(qq, 2), S['D'])
                if cand * cand == x and cand.val() > 0:
                    return cand
    raise AssertionError(f"no exact positive square root of {x}")


def bartlett_data(S):
    """The quantities of Bartlett Def 4.9 / Thm 4.17, from F and the snakes."""
    n = S['n']
    kap = [kappa(S, i) for i in range(n)]
    a = [S['F'](i, S['dual'](i), i, i, 0, 0) for i in range(n)]     # = 1/kappa
    d = [exact_sqrt(S, kap[i] * kap[S['dual'](i)]) for i in range(n)]
    fair = all(a[i] * d[i] == ONE or a[i] * d[i] == -ONE for i in range(n))
    p = [1 if a[i] * d[i] == ONE else -1 for i in range(n)]         # sign(a_i d_i)
    sigma = [d[i] / kap[i] for i in range(n)]
    return kap, a, d, p, sigma, fair


def bartlett_T(S, p, a, b, c):
    """T^c_ab = p_a p_b p_c A_{c* a b}  (Thm 4.17; Y is trivial here)."""
    return Surd(p[a] * p[b] * p[c], 0, S['D']) * monodromy(S, S['dual'](c), a, b)


def settled_j(S, fpdim, a, b, c):
    """`Prop821CNorm.settledJ`: f_c kappa_a kappa_b / (kappa_c f_a f_b)."""
    return (fpdim[c] * kappa(S, a) * kappa(S, b)
            / (kappa(S, c) * fpdim[a] * fpdim[b]))


# ---------------------------------------------------------------------------
# The checks.
# ---------------------------------------------------------------------------
def report(name, S, verbose):
    n, D = S['n'], S['D']
    kap, a, d, p, sigma, fair = bartlett_data(S)
    print(f"--- {name}   (n = {n}, field Q(sqrt {D})) ---")
    print(f"    kappa = {[round(k.val(), 6) for k in kap]}")
    print(f"    a_i = F^(i i* i)_i(0,0) = {[round(x.val(), 6) for x in a]}"
          f"    kappa_i a_i = 1: {all(kap[i] * a[i] == ONE for i in range(n))}")
    print(f"    d_i = {[round(x.val(), 6) for x in d]}   p_i = {p}"
          f"   fair basis: {fair}"
          f"   dual = id: {all(S['dual'](i) == i for i in range(n))}")

    bad = []
    nhit = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if S['N'](x, y, z) == 0:
                    continue
                nhit += 1
                J = derived_j(S, x, y, z)
                if J is None:
                    bad.append(('comparisonScalar vanishes', x, y, z))
                    continue
                A = monodromy(S, S['dual'](z), x, y)
                T = bartlett_T(S, p, x, y, z)
                delta = sigma[z] / (sigma[x] * sigma[y])
                ok_d = (J * T == delta)                       # (D)
                ok_e = (A != ZERO and J * A == ONE)            # (E)
                if not (ok_d and ok_e):
                    bad.append((x, y, z, J, T, delta, A))
                if verbose:
                    print(f"      ({x},{y};{z})  J = {J.val():+.6f}"
                          f"   T = {T.val():+.6f}"
                          f"   1/A = {('undefined' if A == ZERO else format((ONE / A).val(), '+.6f'))}"
                          f"   delta(sigma) = {delta.val():+.6f}")
    print(f"    (D) J = delta(sigma)/T  and  (E) J = 1/A_(c*ab):  "
          f"{nhit - len(bad)}/{nhit} supported channels agree")
    for b in bad:
        print("      MISMATCH:", b)

    # (F): the assembled F-only form, and the tree's omegaCoeff
    fb = ob = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if S['N'](x, y, z) == 0:
                    continue
                du = S['dual']
                hD = (S['F'](du(y), du(x), z, 0, du(z), y)
                      * S['Finv'](du(x), x, y, y, z, 0))
                hN = (S['F'](x, y, du(z), 0, z, du(x))
                      * S['Finv'](y, du(y), du(x), du(x), du(z), 0))
                A = monodromy(S, du(z), x, y)
                if hD.is_zero() or hN * A != hD:
                    fb += 1
                    print("      (F) MISMATCH:", x, y, z)
                J = derived_j(S, x, y, z)
                if hD.is_zero() or J is None or hN / hD != J:
                    ob += 1
                    print("      omegaCoeff MISMATCH:", x, y, z)
    print(f"    (F) F(b*,a*,c;0,c*,b) Finv(a*,a,b;b,c,0) = S_abc* S_bc*a S_c*ab:"
          f"  {nhit - fb}/{nhit}")
    print(f"    omegaCoeff = derivedJGen (the ev factors cancel):  {nhit - ob}/{nhit}")

    # Bartlett's Cor 3.26: the F-free coherence law, where his qualification holds
    tot = ok = skipped = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                for w in range(n):
                    for e in range(n):
                        for f in range(n):
                            if not (S['N'](x, y, e) and S['N'](e, z, w)
                                    and S['N'](y, z, f) and S['N'](x, f, w)):
                                continue
                            tot += 1
                            if S['F'](x, y, z, w, e, f).is_zero():
                                skipped += 1
                                continue
                            lhs = derived_j(S, x, y, e) * derived_j(S, e, z, w)
                            rhs = derived_j(S, y, z, f) * derived_j(S, x, f, w)
                            if lhs is not None and lhs == rhs:
                                ok += 1
                            else:
                                bad.append(('Cor 3.26', x, y, z, w, e, f))
    print(f"    Cor 3.26 (F-free coherence of the derived twist): {ok}/{tot - skipped}"
          f" pentagon instances with F != 0  (supported entries with F = 0: {skipped};"
          f" `J_coherent` keeps the F factor and needs no qualification)")
    return bad


def check_published():
    """Bartlett's published Yang-Lee numbers, read off the tree's datum."""
    S = yanglee()
    _, _, d, p, _, _ = bartlett_data(S)
    got = [('p(tau)', p[1], -1),
           ('S_ttt', apex(S, 1, 1, 1), ONE),
           ('d_tau', d[1], Surd(Fraction(-1, 2), Fraction(1, 2), 5)),
           ('T^tau_tt', bartlett_T(S, p, 1, 1, 1), Surd(-1, 0, 5)),
           ('J^tau_tt', derived_j(S, 1, 1, 1), ONE)]
    print("--- Yang-Lee: Bartlett's published values (Ex 3.4, 4.10, 4.13, 4.19),"
          " read off `YangLee.F`/`yangLee.coev` ---")
    ok = True
    for nm, g, w in got:
        same = (g == w)
        ok = ok and same
        gs = round(g.val(), 6) if isinstance(g, Surd) else g
        ws = round(w.val(), 6) if isinstance(w, Surd) else w
        print(f"    {nm:9s} = {gs}   expected {ws}   {'ok' if same else 'MISMATCH'}")
    return ok


def check_K():
    """Consequence, not part of the comparison (see the docstring)."""
    print("--- consequence: the (K) table `settledJ` against the honest (derived) twist ---")
    phi = Surd(Fraction(1, 2), Fraction(1, 2), 5)
    sets = [('Fibonacci', fibonacci(), [ONE, phi]),
            ('Ising', ising(), [ONE, Surd(0, 1, 2), ONE]),
            ('YangLee', yanglee(), [ONE, phi]),
            ('Z2SqH.systemH', z2sqh(), [ONE] * 4)]
    fails = {}
    for name, S, f in sets:
        n = S['n']
        fl = []
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    if S['N'](x, y, z) == 0:
                        continue
                    st = settled_j(S, f, x, y, z)
                    J = derived_j(S, x, y, z)
                    if st != J:
                        fl.append((x, y, z, st, J))
        fails[name] = fl
        if fl:
            for (x, y, z, st, J) in fl:
                print(f"    {name}: ({x},{y};{z})  settledJ = {st.val():+.6f}"
                      f"  derivedJ = {J.val():+.6f}   <- (K) fails")
        else:
            print(f"    {name}: derived twist = settledJ on every channel")
    return fails


def derived_j_no_finv(S, a, b, c):
    """A deliberately WRONG closed form: `comparisonScalar` with the `Finv`
    factor dropped.  Only the negative controls use it."""
    du = S['dual']

    def cs(x, y, z):
        den = S['F'](du(y), du(x), z, 0, du(z), y) * S['ev'](x) * S['ev'](y)
        return None if den.is_zero() else S['ev'](z) / den
    n1, n2 = cs(a, b, c), cs(du(b), du(a), du(c))
    if n1 is None or n2 is None or n2.is_zero():
        return None
    return n1 / n2


def monodromy_short(S, i, j, k):
    """A deliberately WRONG Bartlett side: the monodromy with the third apex
    factor dropped.  Only the negative controls use it."""
    return apex(S, j, k, i) * apex(S, k, i, j)


def count_mismatches(S, closed_form=None, mono=None):
    """How many supported channels fail (E) `J = 1/A_{c*ab}`."""
    n = S['n']
    cf = closed_form or derived_j
    mf = mono or monodromy
    bad = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if S['N'](x, y, z) == 0:
                    continue
                J = cf(S, x, y, z)
                A = mf(S, S['dual'](z), x, y)
                if J is None or A == ZERO or J * A != ONE:
                    bad += 1
    return bad


def check_negative_controls():
    """A comparison that cannot fail is worth nothing, so: the check must
    DETECT two perturbed closed forms and a perturbed datum.  Note that the
    datum mutation must hit a *composite-0* F entry: only those enter
    `comparisonScalar` and the apex associator, so a perturbation elsewhere in
    the associator is invisible to this comparison (a fact worth knowing)."""
    base = sum(count_mismatches(S) for _, S in TREE)
    f1 = sum(count_mismatches(S, derived_j_no_finv) for _, S in TREE)
    f2 = sum(count_mismatches(S, mono=monodromy_short) for _, S in TREE)

    mut = z2sqh()
    orig = mut['F']

    def Fmut(a, b, c, d, e, f):
        v = orig(a, b, c, d, e, f)
        return -v if (a, b, c, d, e, f) == (2, 1, 3, 0, 3, 2) else v
    mut['F'] = Fmut
    f3 = count_mismatches(mut)

    ok = (base == 0 and f1 > 0 and f2 > 0 and f3 > 0)
    print("--- negative controls (the comparison must be able to fail) ---")
    print(f"    correct closed form, all tree data: {base} mismatches (expected 0)")
    print(f"    `comparisonScalar` without the Finv factor: {f1} (expected > 0)")
    print(f"    monodromy with two factors instead of three: {f2} (expected > 0)")
    print(f"    `Z2SqH`, one composite-0 F entry negated: {f3} (expected > 0)")
    print(f"    {'ok' if ok else 'THE CHECK IS VACUOUS -- investigate'}")
    return ok


def check_control_axioms():
    """The control datum really is one: the pointed pentagon is the 3-cocycle
    identity, plus the unit laws and the two snakes."""
    S = z4_control()
    n = 4
    bad = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                for w in range(n):
                    yz, xy = (y + z) % 4, (x + y) % 4
                    lhs = (z4_om(x, y, z) * z4_om(x, yz, w) * z4_om(y, z, w))
                    rhs = (z4_om(xy, z, w) * z4_om(x, y, (z + w) % 4))
                    if lhs != rhs:
                        bad += 1
    for z in range(n):
        if z4_om(0, z, z) != 1 or z4_om(z, 0, z) != 1 or z4_om(z, z, 0) != 1:
            bad += 1
    snakes = all(kappa(S, i) * S['F'](i, z4_dual(i), i, i, 0, 0) == ONE
                 and kappa(S, i) * S['Finv'](z4_dual(i), i, z4_dual(i),
                                             z4_dual(i), 0, 0) == ONE
                 for i in range(n))
    print(f"--- control datum: cocycle/unit violations {bad}, snakes hold {snakes},"
          f" kappa = {[kappa(S, i).val() for i in range(n)]} ---")
    return bad == 0 and snakes


def main(argv):
    verbose = ('-v' in argv) or ('--verbose' in argv)
    print("Bartlett comparison (WP3 Task 3.5): exact arithmetic, no floats in any"
          " equality.")
    print()
    failures = 0
    for name, S in TREE:
        failures += len(report(name, S, verbose))
    if not check_control_axioms():
        failures += 1
    for name, S in CONTROL:
        failures += len(report(name, S, verbose))
    print()
    if not check_published():
        failures += 1
    print()
    if not check_negative_controls():
        failures += 1
    print()
    fails = check_K()
    print()
    print('=' * 72)
    if failures:
        print(f"FAILED: {failures} mismatch(es).  Per WP3 Task 3.5 a mismatch is a"
              f" defect in the derivation, not in the check.")
        return 1
    print("PASSED: Bartlett's Theorem 4.17 agrees with `derivedJGen` on every")
    print("supported channel of every data set above (D, E, F, omegaCoeff), and")
    print("his Corollary 3.26 F-free law holds on every pentagon instance with F != 0.")
    broken = ', '.join(k for k, v in fails.items() if v) or 'no data set'
    print(f"Recorded separately, not a check failure: the (K) table fails on {broken}.")
    print("There the honest twist is the one Bartlett's formula gives (all 1 on the")
    print("tau (x) tau channels), so this is the WP3 non-goal, not a defect.")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
