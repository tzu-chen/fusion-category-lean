"""
battery.py -- WP2 Round 3, member m8, direction D8: the numerical battery on the
CANONICAL scaffold.

WHAT THIS IS.  Every frozen WP2 statement is an equation between morphisms of
`FusionCategory.FusionMat n k`, i.e. between block matrices.  `ReconAssocIso`,
`ReconSnake` and (open) D2/D3 prove them by the "composite engine".  This script
is the independent check: it re-implements the canonical definitions *literally*
and evaluates both sides of every frozen equation on honest data.

The transliteration is line by line against the definitions; the projection-heavy
ones are pinned to kernel-checked lemmas of the scaffold:

  assocEntry / assocInvEntry <- ReconAssoc.lean, with the proved entry forms
      `assocEntry_apply_matched` / `assocInvEntry_apply_matched` and the zero
      lemmas `assocEntry_zero_{a,b,c}`: the entry is `F a b c d e f` iff the six
      leaf data agree, else 0.
  blockDiag / tensorHom       <- Recon.lean / ReconTensor.lean, with
      `blockDiag_mk`, `tensorHom_apply`, `tensorHom_apply_ne`.
  ev / coev                   <- ReconRigid.lean (`ev_apply`, `coev_apply`).
  unitors                     <- ReconRigid.FusionMat.leftUnitor/rightUnitor
      (the ones the FROZEN SnakeLeft/SnakeRight use) plus the ReconUnitors
      (Units.*) copies for the triangle and the dedupe check.
  trace                       <- ReconTraceCorrespondence.trSimple_eq.

Index types are nested exactly as Lean's: the `c`-block of `X (x) Y` is
`Sigma p : Fin n x Fin n, Fin (N p.1 p.2 c) x X.blk p.1 x Y.blk p.2`, represented
here as the tuple `((p1,p2), (nu, (x, y)))`.  `Prod` is right associative in
Lean, so `r.2.2.1` is `r[1][1][0]` here, and `X.blk` is defined by *recursion on
the object* (`Obj.idx`), exactly as `tensorObj` defines it -- which is what makes
a doubly tensored object's indices the same nested type as in Lean.

DATA.  Not hand-transcribed: `bridge.out` (from `Bridge.lean`) holds `#eval`
dumps of the *computable* definitions of each datum, and `Bridge.lean` proves by
`rfl` that those are the `FusionSystem` fields of the instances.  This script
refuses to run on a dataset whose tables are absent.

Scalars are exact: `Sc` is `Q(sqrt d)` as pairs `(p + q sqrt d)` -- the repo's own
`ZP` encoding -- so a Fibonacci or Ising check is exact arithmetic, not floating
point.

USAGE.  python3 battery.py [bridge.out]
EXIT.   0 iff every check passes on every dataset.
"""
import itertools
import random
import sys
from fractions import Fraction as Fr


# ---------------------------------------------------------------- exact scalars
class Sc:
    """p + q*sqrt(d), exactly; `Sc.d` is set per dataset."""
    d = 1
    __slots__ = ('p', 'q')

    def __init__(self, p, q=0):
        self.p = Fr(p)
        self.q = Fr(q)

    def __add__(self, o):
        return Sc(self.p + o.p, self.q + o.q)

    def __sub__(self, o):
        return Sc(self.p - o.p, self.q - o.q)

    def __neg__(self):
        return Sc(-self.p, -self.q)

    def __mul__(self, o):
        return Sc(self.p * o.p + Sc.d * self.q * o.q, self.p * o.q + self.q * o.p)

    def __eq__(self, o):
        return self.p == o.p and self.q == o.q

    def __hash__(self):
        return hash((self.p, self.q))

    def __repr__(self):
        if self.q == 0:
            return str(self.p)
        if self.p == 0:
            return "%s*r%d" % (self.q, Sc.d)
        return "(%s+%s*r%d)" % (self.p, self.q, Sc.d)

    def is_zero(self):
        return self.p == 0 and self.q == 0


ZERO = Sc(0)
ONE = Sc(1)


# ---------------------------------------------------------------- the objects
class Obj:
    """A `FusionMat` object, by the recursion that defines its block types.

    `Obj(m=...)`      -- multiplicities `m` (the `ofM` embedding);
    `Obj(X=A, Y=B)`   -- `ReconTensor.tensorObj S A B`;
    `Obj(dual_of=A)`  -- `ReconRigid.dual S A` (labels dualised, blocks carried).
    """

    def __init__(self, m=None, X=None, Y=None, dual_of=None):
        self.m_ = m
        self.X = X
        self.Y = Y
        self.dual_of = dual_of
        self._m = {}
        self._idx = {}

    def is_base(self):
        return self.m_ is not None

    def __repr__(self):
        if self.is_base():
            return "M%s" % (tuple(self.m_),)
        if self.dual_of is not None:
            return "(%s)*" % (self.dual_of,)
        return "(%s(x)%s)" % (self.X, self.Y)


def base(m):
    return Obj(m=tuple(m))


def tmul(S, X, Y, c):
    """`ReconTensor.tensorMul`."""
    return sum(S.N[a][b][c] * mul(S, X, a) * mul(S, Y, b)
               for a in range(S.n) for b in range(S.n))


def mul(S, X, c):
    """`X.m c`."""
    if c in X._m:
        return X._m[c]
    if X.is_base():
        v = X.m_[c]
    elif X.dual_of is not None:
        v = mul(S, X.dual_of, S.dual[c])
    else:
        v = tmul(S, X.X, X.Y, c)
    X._m[c] = v
    return v


def idx(S, X, c):
    """`X.blk c` as a tuple of nested index elements."""
    if c in X._idx:
        return X._idx[c]
    if X.is_base():
        v = tuple(range(mul(S, X, c)))
    elif X.dual_of is not None:
        v = idx(S, X.dual_of, S.dual[c])
    else:
        v = tuple(((a, b), (nu, (x, y)))
                  for a in range(S.n) for b in range(S.n)
                  for nu in range(S.N[a][b][c])
                  for x in idx(S, X.X, a) for y in idx(S, X.Y, b))
    X._idx[c] = v
    return v


def tobj(S, X, Y):
    return Obj(X=X, Y=Y)


def dobl(S, X):
    return Obj(dual_of=X)


def unitObj(S):
    return base([1] + [0] * (S.n - 1))


# ---------------------------------------------------------------- the morphisms
# A morphism `X --> Y` is `{c: {(r, q): value}}` with `r in X.blk c`, `q in Y.blk c`.

def mor(entries):
    """entries: iterable of `(c, r, q, v)`."""
    f = {}
    for c, r, q, v in entries:
        if v.is_zero():
            continue
        d = f.setdefault(c, {})
        d[(r, q)] = d.get((r, q), ZERO) + v
    return f


def oneM(S, X):
    return mor((c, r, r, ONE) for c in range(S.n) for r in idx(S, X, c))


def blkmap(f):
    """`{c: {(r,q): v}} -> {c: {r: [(q,v)]}}`."""
    out = {}
    for c, d in f.items():
        g = {}
        for (r, q), v in d.items():
            g.setdefault(r, []).append((q, v))
        out[c] = g
    return out


def mat_mul(A, B):
    """Sparse `{((r,m)): v} * {((m,q)): v}`."""
    brows = {}
    for (m, q), v in B.items():
        brows.setdefault(m, []).append((q, v))
    C = {}
    for (r, m), a in A.items():
        for q, b in brows.get(m, ()):
            C[(r, q)] = C.get((r, q), ZERO) + a * b
    return {k: v for k, v in C.items() if not v.is_zero()}


def cmp(*fs):
    """Composition `f1 ; f2 ; ...` (blockwise matrix product)."""
    out = fs[0]
    for g in fs[1:]:
        h = {}
        for c in set(out) | set(g):
            h[c] = mat_mul(out.get(c, {}), g.get(c, {}))
        out = h
    return out


COVER = {'compared': 0, 'nonzero': 0, 'identity': 0, 'blocks': 0}


def mat_eq(A, B):
    """Equality of two sparse blocks, with coverage accounting: a check is only
    evidence if the blocks it compares are not empty (an empty block compares
    equal to anything)."""
    keys = set(A) | set(B)
    COVER['blocks'] += 1
    COVER['compared'] += len(keys)
    COVER['nonzero'] += sum(1 for k in keys if not A.get(k, ZERO).is_zero()
                            or not B.get(k, ZERO).is_zero())
    return all(A.get(k, ZERO) == B.get(k, ZERO) for k in keys)


def mat_eq_id(M, rows):
    """Is the square matrix `M` on `rows` the identity?"""
    rows = list(rows)
    COVER['blocks'] += 1
    COVER['identity'] += len(rows)
    COVER['compared'] += len(rows)
    COVER['nonzero'] += len(M)
    for (r, q), v in M.items():
        if v != (ONE if r == q else ZERO):
            return False
    return all((r, r) in M for r in rows)


# ---------------------------------------------------------------- the scaffold
def tensorHom(S, f, g, X, X1, Y, Y1):
    """`ReconTensor.tensorHom S f g : X (x) Y --> X' (x) Y'`.

    `tensorHom_apply`: at row `((a,b),(nu,(x,y)))` and column `((a,b),(nu,(x',y')))`
    the entry is `f x x' * g y y'`; `tensorHom_apply_ne`: 0 at differing labels.
    """
    fi = blkmap(f)
    gi = blkmap(g)
    out = {}
    for c in range(S.n):
        for r in idx(S, tobj(S, X, Y), c):
            (a, b) = r[0]
            nu = r[1][0]
            x = r[1][1][0]
            y = r[1][1][1]
            for (x2, v1) in fi.get(a, {}).get(x, ()):
                for (y2, v2) in gi.get(b, {}).get(y, ()):
                    q = ((a, b), (nu, (x2, y2)))
                    out[(c, r, q)] = out.get((c, r, q), ZERO) + v1 * v2
    return mor([(c, r, q, v) for (c, r, q), v in out.items()])


def assocEntry(S, X, Y, Z, d):
    """`ReconAssoc.assocEntry S X Y Z d`, by `assocEntry_apply_matched` + zeros."""
    XY = tobj(S, X, Y)
    YZ = tobj(S, Y, Z)
    rowleaf = {}
    for r in idx(S, tobj(S, XY, Z), d):
        (e, c) = r[0]
        u = r[1][1][0]
        z = r[1][1][1]
        (a, b) = u[0]
        rowleaf[r] = (a, b, c, u[1][1][0], u[1][1][1], z, e)
    colleaf = {}
    for q in idx(S, tobj(S, X, YZ), d):
        (a, f) = q[0]
        x = q[1][1][0]
        u = q[1][1][1]
        (b, c) = u[0]
        colleaf[q] = (a, b, c, x, u[1][1][0], u[1][1][1], f)
    out = {}
    for r, lr in rowleaf.items():
        leaf = lr[:6]
        for q, lq in colleaf.items():
            if lq[:6] == leaf:
                v = S.F[leaf[0]][leaf[1]][leaf[2]][d][lr[6]][lq[6]]
                if not v.is_zero():
                    out[(r, q)] = v
    return out


def assocInvEntry(S, X, Y, Z, d):
    """`ReconAssoc.assocInvEntry S X Y Z d` (`assocInvEntry_apply_matched`)."""
    XY = tobj(S, X, Y)
    YZ = tobj(S, Y, Z)
    colleaf = {}
    for r in idx(S, tobj(S, XY, Z), d):
        (e, c) = r[0]
        u = r[1][1][0]
        z = r[1][1][1]
        (a, b) = u[0]
        colleaf[r] = (a, b, c, u[1][1][0], u[1][1][1], z, e)
    rowleaf = {}
    for q in idx(S, tobj(S, X, YZ), d):
        (a, f) = q[0]
        x = q[1][1][0]
        u = q[1][1][1]
        (b, c) = u[0]
        rowleaf[q] = (a, b, c, x, u[1][1][0], u[1][1][1], f)
    out = {}
    for q, lq in rowleaf.items():
        leaf = lq[:6]
        for r, lr in colleaf.items():
            if lr[:6] == leaf:
                v = S.Finv[leaf[0]][leaf[1]][leaf[2]][d][lq[6]][lr[6]]
                if not v.is_zero():
                    out[(q, r)] = v
    return out


def assocMor(S, X, Y, Z):
    """`ReconAssoc.associatorHom S X Y Z`."""
    return {d: assocEntry(S, X, Y, Z, d) for d in range(S.n)}


def assocInvMor(S, X, Y, Z):
    """`ReconAssoc.associatorInv S X Y Z`."""
    return {d: assocInvEntry(S, X, Y, Z, d) for d in range(S.n)}


def ev_mor(S, X):
    """`ReconRigid.ev S hn X : X* (x) X --> 1`."""
    Xd = dobl(S, X)
    U = unitObj(S)
    return mor((c, r, j, S.ev[p2])
               for c in range(S.n)
               for r in idx(S, tobj(S, Xd, X), c)
               for (p1, p2) in [r[0]]
               if p2 == S.dual[p1] and r[1][1][0] == r[1][1][1]
               for j in idx(S, U, c))


def coev_mor(S, X):
    """`ReconRigid.coev S hn X : 1 --> X (x) X*`."""
    Xd = dobl(S, X)
    U = unitObj(S)
    return mor((c, j, q, S.coev[p1])
               for c in range(S.n)
               for q in idx(S, tobj(S, X, Xd), c)
               for (p1, p2) in [q[0]]
               if p1 == S.dual[p2] and q[1][1][0] == q[1][1][1]
               for j in idx(S, U, c))


def unitIdxL(S, X, c, j):
    """`ReconRigid.FusionMat.unitIdxL S hn X c j`."""
    return ((0, c), (0, (0, j)))


def unitIdxR(S, X, c, j):
    """`ReconRigid.FusionMat.unitIdxR S hn X c j`."""
    return ((c, 0), (0, (j, 0)))


def leftUnitor(S, X):
    """`ReconRigid.FusionMat.leftUnitor : 1 (x) X --> X` (a graph matrix)."""
    return mor((c, unitIdxL(S, X, c, j), j, ONE)
               for c in range(S.n) for j in idx(S, X, c))


def rightUnitor(S, X):
    """`ReconRigid.FusionMat.rightUnitor : X (x) 1 --> X`."""
    return mor((c, unitIdxR(S, X, c, j), j, ONE)
               for c in range(S.n) for j in idx(S, X, c))


def units_leftUnitor(S, X):
    """`ReconUnitors.leftUnitor : 1 (x) X --> X`, through `leftIdxEquiv`."""
    U = unitObj(S)
    return mor((c, r, r[1][1][1], ONE)
               for c in range(S.n) for r in idx(S, tobj(S, U, X), c))


def units_rightUnitor(S, X):
    """`ReconUnitors.rightUnitor : X (x) 1 --> X`, through `rightIdxEquiv`."""
    U = unitObj(S)
    return mor((c, r, r[1][1][0], ONE)
               for c in range(S.n) for r in idx(S, tobj(S, X, U), c))


# ---------------------------------------------------------------- the checks
def chk_assoc_iso(S, X, Y, Z):
    """Frozen `AssociatorIso`: `associatorHom ; associatorInv = 1` and back."""
    XY, YZ = tobj(S, X, Y), tobj(S, Y, Z)
    for d in range(S.n):
        A = assocEntry(S, X, Y, Z, d)
        B = assocInvEntry(S, X, Y, Z, d)
        if not mat_eq_id(mat_mul(A, B), idx(S, tobj(S, XY, Z), d)):
            return ("hom;inv", d)
        if not mat_eq_id(mat_mul(B, A), idx(S, tobj(S, X, YZ), d)):
            return ("inv;hom", d)
    return None


def rand_mor(S, X, Y, rng, dens=0.6):
    e = []
    for c in range(S.n):
        for x in idx(S, X, c):
            for y in idx(S, Y, c):
                if rng.random() < dens:
                    e.append((c, x, y, Sc(rng.choice([-2, -1, 1, 2, 3]))))
    return mor(e)


def chk_assoc_natural(S, X, Y, Z, X1, Y1, Z1, rng):
    """Frozen `AssociatorNatural`:
    `(f (x) g) (x) h ; a_{X',Y',Z'} = a_{X,Y,Z} ; f (x) (g (x) h)`."""
    f = rand_mor(S, X, X1, rng)
    g = rand_mor(S, Y, Y1, rng)
    h = rand_mor(S, Z, Z1, rng)
    XY, X1Y1 = tobj(S, X, Y), tobj(S, X1, Y1)
    YZ, Y1Z1 = tobj(S, Y, Z), tobj(S, Y1, Z1)
    lhs = cmp(tensorHom(S, tensorHom(S, f, g, X, X1, Y, Y1), h, XY, X1Y1, Z, Z1),
              assocMor(S, X1, Y1, Z1))
    rhs = cmp(assocMor(S, X, Y, Z),
              tensorHom(S, f, tensorHom(S, g, h, Y, Y1, Z, Z1), X, X1, YZ, Y1Z1))
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), rhs.get(d, {})):
            return ("mismatch", d)
    return None


def chk_pentagon(S, W, X, Y, Z):
    """`PentagonShapeHom` (D3's frozen target):

        (a_{W,X,Y} (x) 1_Z) ; a_{W, X(x)Y, Z} ; (1_W (x) a_{X,Y,Z})
          = a_{W(x)X, Y, Z} ; a_{W, X, Y(x)Z}.

    The two-factor legs are `tensorHom` at the objects the associator maps
    between: `a_{W,X,Y} : (W(x)X)(x)Y --> W(x)(X(x)Y)`, tensored with `1_Z`,
    so the leg runs from `((W(x)X)(x)Y)(x)Z` to `(W(x)(X(x)Y))(x)Z`.
    """
    WX, XY, YZ = tobj(S, W, X), tobj(S, X, Y), tobj(S, Y, Z)
    leg1 = tensorHom(S, assocMor(S, W, X, Y), oneM(S, Z),
                     tobj(S, WX, Y), tobj(S, W, XY), Z, Z)
    leg3 = tensorHom(S, oneM(S, W), assocMor(S, X, Y, Z),
                     W, W, tobj(S, XY, Z), tobj(S, X, YZ))
    lhs = cmp(leg1, assocMor(S, W, XY, Z), leg3)
    rhs = cmp(assocMor(S, WX, Y, Z), assocMor(S, W, X, YZ))
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), rhs.get(d, {})):
            return ("mismatch", d)
    return None


def chk_snake_left(S, X):
    """Frozen `FusionMat.SnakeLeft`:
    `(coev (x) 1) ; a_{X,X*,X} ; (1 (x) ev) ; rho_X = lambda_X`."""
    Xd = dobl(S, X)
    XXd = tobj(S, X, Xd)
    XdX = tobj(S, Xd, X)
    U = unitObj(S)
    lhs = cmp(tensorHom(S, coev_mor(S, X), oneM(S, X), U, XXd, X, X),
              assocMor(S, X, Xd, X),
              tensorHom(S, oneM(S, X), ev_mor(S, X), X, X, XdX, U),
              rightUnitor(S, X))
    want = leftUnitor(S, X)
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), want.get(d, {})):
            return ("mismatch", d)
    return None


def chk_snake_right(S, X):
    """Frozen `FusionMat.SnakeRight`:
    `(1 (x) coev) ; a^-1_{X*,X,X*} ; (ev (x) 1) ; lambda_{X*} = rho_{X*}`."""
    Xd = dobl(S, X)
    XdX = tobj(S, Xd, X)
    XdXd = tobj(S, Xd, Xd)
    U = unitObj(S)
    lhs = cmp(tensorHom(S, oneM(S, Xd), coev_mor(S, X), Xd, Xd, U, XdXd),
              assocInvMor(S, Xd, X, Xd),
              tensorHom(S, ev_mor(S, X), oneM(S, Xd), XdX, U, Xd, Xd),
              leftUnitor(S, Xd))
    want = rightUnitor(S, Xd)
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), want.get(d, {})):
            return ("mismatch", d)
    return None


def chk_triangle(S, X, Y):
    """`ReconUnitors.triangle`: `a_{X,1,Y} ; (X (x) lambda_Y) = rho_X (x) Y`."""
    U = unitObj(S)
    XU, UY = tobj(S, X, U), tobj(S, U, Y)
    lhs = cmp(assocMor(S, X, U, Y), tensorHom(S, oneM(S, X), leftUnitor(S, Y), X, X, UY, Y))
    rhs = tensorHom(S, rightUnitor(S, X), oneM(S, Y), XU, X, Y, Y)
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), rhs.get(d, {})):
            return ("mismatch", d)
    return None


def chk_unitor_natural(S, X, X1, rng):
    """`ReconUnitors.whiskerLeft_leftUnitor` / `whiskerRight_rightUnitor`:
    `(1 (x) f) ; lambda_{X'} = lambda_X ; f` and `(f (x) 1) ; rho_{X'} = rho_X ; f`."""
    f = rand_mor(S, X, X1, rng)
    U = unitObj(S)
    UX = tobj(S, U, X)
    UX1 = tobj(S, U, X1)
    lhs = cmp(tensorHom(S, oneM(S, U), f, U, U, X, X1), leftUnitor(S, X1))
    rhs = cmp(leftUnitor(S, X), f)
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), rhs.get(d, {})):
            return ("left", d)
    lhs = cmp(tensorHom(S, f, oneM(S, U), X, X1, U, U), rightUnitor(S, X1))
    rhs = cmp(rightUnitor(S, X), f)
    for d in range(S.n):
        if not mat_eq(lhs.get(d, {}), rhs.get(d, {})):
            return ("right", d)
    return None


def chk_unitors_agree(S, X):
    """The two unitor developments agree as matrices -- D6's dedupe, numerically."""
    for d in range(S.n):
        if not mat_eq(units_leftUnitor(S, X).get(d, {}), leftUnitor(S, X).get(d, {})):
            return ("left", d)
        if not mat_eq(units_rightUnitor(S, X).get(d, {}), rightUnitor(S, X).get(d, {})):
            return ("right", d)
    return None


def chk_object_assoc(S, X, Y, Z):
    """Frozen `ObjectAssociativity`."""
    l = [mul(S, tobj(S, tobj(S, X, Y), Z), c) for c in range(S.n)]
    r = [mul(S, tobj(S, X, tobj(S, Y, Z)), c) for c in range(S.n)]
    return None if l == r else ("mismatch", l, r)


def chk_trace(S, P):
    """The four frozen trace Props at the datum level (`trSimple_eq`)."""
    bad = []
    for i in range(S.n):
        if S.coev[i] * ONE * S.ev[S.dual[i]] != S.coev[i] * S.ev[S.dual[i]]:
            bad.append(("TraceOfScalar", i))
        if P[i] * S.coev[i] * S.ev[S.dual[i]] != P[i] * (S.coev[i] * S.ev[i]):
            bad.append(("TraceOfPivotalComponent", i))
        d1 = P[i] * (S.coev[i] * S.ev[i])
        d2 = P[S.dual[i]] * (S.coev[S.dual[i]] * S.ev[S.dual[i]])
        want = (S.coev[i] * S.ev[i]) * (S.coev[S.dual[i]] * S.ev[S.dual[i]])
        if d1 * d2 != want:
            bad.append(("TraceProduct_eq_kappa", i))
    return bad


def chk_fpdata(S, fpdim):
    """The `FPData` axioms exactly (this is what `globalDim` reads)."""
    bad = []
    if fpdim[0] != ONE:
        bad.append("FPData.unit_one")
    for i in range(S.n):
        for k in range(S.n):
            s = ZERO
            for j in range(S.n):
                s = s + Sc(S.N[i][j][k]) * fpdim[j]
            if s != fpdim[i] * fpdim[k]:
                bad.append(("FPData.eigenvector", i, k))
        if fpdim[S.dual[i]] != fpdim[i]:
            bad.append(("FPData.dual_eq", i))
    return bad


def chk_pseudounitary(S, fpdim):
    """`IsPseudoUnitaryC`: `sum_i kappa_i kappa_{i*} = sum_i fpdim_i^2`."""
    lhs = ZERO
    rhs = ZERO
    for i in range(S.n):
        lhs = lhs + (S.coev[i] * S.ev[i]) * (S.coev[S.dual[i]] * S.ev[S.dual[i]])
        rhs = rhs + fpdim[i] * fpdim[i]
    return (lhs == rhs), lhs, rhs


# ---------------------------------------------------------------- the datum
class Sys:
    def __init__(self, name, n, N, dual, F, Finv, ev, coev, d):
        self.name = name
        self.n = n
        Sc.d = d
        self.N = N
        self.dual = dual
        self.F = F
        self.Finv = Finv
        self.ev = ev
        self.coev = coev
        self.d = d

    def check_datum(self):
        """The label-level axioms of `FusionSystem` -- a check of the *tables*."""
        bad = []
        n = self.n
        rng = range(n)
        for a, b, c, dd, e, ff in itertools.product(rng, repeat=6):
            sup = (self.N[a][b][e] > 0 and self.N[e][c][dd] > 0
                   and self.N[b][c][ff] > 0 and self.N[a][ff][dd] > 0)
            if not sup and not self.F[a][b][c][dd][e][ff].is_zero():
                bad.append(("F_support", a, b, c, dd, e, ff))
            if not sup and not self.Finv[a][b][c][dd][ff][e].is_zero():
                bad.append(("Finv_support", a, b, c, dd, ff, e))
        for a, b, c, dd, e, i, j, r, x in itertools.product(rng, repeat=9):
            lhs = ZERO
            for k in rng:
                lhs = lhs + (self.F[a][b][c][x][e][k] * self.F[a][k][dd][r][x][j]
                             * self.F[b][c][dd][j][k][i])
            if lhs != self.F[e][c][dd][r][x][i] * self.F[a][b][i][r][e][j]:
                bad.append(("pentagon", a, b, c, dd, e, i, j, r, x))
        for a, b, c, dd in itertools.product(rng, repeat=4):
            for f1, f2 in itertools.product(rng, repeat=2):
                if (self.N[b][c][f1] > 0 and self.N[a][f1][dd] > 0
                        and self.N[b][c][f2] > 0 and self.N[a][f2][dd] > 0):
                    s = ZERO
                    for e in rng:
                        s = s + self.Finv[a][b][c][dd][f1][e] * self.F[a][b][c][dd][e][f2]
                    if s != (ONE if f1 == f2 else ZERO):
                        bad.append(("Finv_comp", a, b, c, dd, f1, f2))
            for e1, e2 in itertools.product(rng, repeat=2):
                if (self.N[a][b][e1] > 0 and self.N[e1][c][dd] > 0
                        and self.N[a][b][e2] > 0 and self.N[e2][c][dd] > 0):
                    s = ZERO
                    for f in rng:
                        s = s + self.Finv[a][b][c][dd][f][e1] * self.F[a][b][c][dd][e2][f]
                    if s != (ONE if e1 == e2 else ZERO):
                        bad.append(("F_comp_inv", a, b, c, dd, e1, e2))
        for b, c, dd, ff in itertools.product(rng, repeat=4):
            if self.N[b][c][ff] > 0:
                if self.F[0][b][c][dd][b][ff] != (ONE if dd == ff else ZERO):
                    bad.append(("F_unit_left", 0, b, c, dd, b, ff))
        for a, b, dd, e in itertools.product(rng, repeat=4):
            if self.N[a][b][e] > 0:
                if self.F[a][b][0][dd][e][b] != (ONE if dd == e else ZERO):
                    bad.append(("F_unit_right", a, b, 0, dd, e, b))
        for i in rng:
            kap = self.coev[i] * self.ev[i]
            if kap * self.F[i][self.dual[i]][i][i][0][0] != ONE:
                bad.append(("snake_left", i))
            if kap * self.Finv[self.dual[i]][i][self.dual[i]][self.dual[i]][0][0] != ONE:
                bad.append(("snake_right", i))
            if self.ev[i].is_zero() or self.coev[i].is_zero():
                bad.append(("ev/coev nonzero", i))
            if self.ev[self.dual[i]] != self.ev[i]:
                bad.append(("ev_dual", i))
        return bad


# ---------------------------------------------------------------- loading
def parse_bridge(path):
    tab = {}
    for line in open(path):
        parts = line.split()
        if parts:
            tab.setdefault(parts[0], []).append(parts[1:])
    return tab


def rat(s):
    return Sc(Fr(s))


def pr(p, q):
    """The repo's `ZP` pair `(p,q)` denotes `(p + q*sqrt d)/2` (`ZP.zval`)."""
    return Sc(Fr(p) / 2, Fr(q) / 2)


def zeros6(n):
    return [[[[[[ZERO for _ in range(n)] for _ in range(n)] for _ in range(n)]
               for _ in range(n)] for _ in range(n)] for _ in range(n)]


def build(tab, name):
    def req(tag):
        if tag not in tab:
            raise SystemExit("battery: bridge.out has no table %r -- re-run Bridge.lean" % tag)
        return tab[tag]

    if name == 'Z2SQ':
        n = 4
        N = [[[0] * n for _ in range(n)] for _ in range(n)]
        for a, b, c, v in req('Z2SQ.N'):
            N[int(a)][int(b)][int(c)] = int(v)
        dual = [0] * n
        for a, v in req('Z2SQ.dual'):
            dual[int(a)] = int(v)
        gadd = [[0] * n for _ in range(n)]
        for a, b, v in req('Z2SQ.gadd'):
            gadd[int(a)][int(b)] = int(v)
        wZ = [[[0] * n for _ in range(n)] for _ in range(n)]
        for a, b, c, v in req('Z2SQ.wZ'):
            wZ[int(a)][int(b)][int(c)] = int(v)
        F = zeros6(n)
        Finv = zeros6(n)

        def Fw(a, b, c, d, e, f):
            if e != gadd[a][b] or d != gadd[gadd[a][b]][c] or f != gadd[b][c]:
                return ZERO
            return Sc(wZ[a][b][c])

        for a, b, c, d, e, f in itertools.product(range(n), repeat=6):
            F[a][b][c][d][e][f] = Fw(a, b, c, d, e, f)
            Finv[a][b][c][d][f][e] = Fw(a, b, c, d, e, f)
        return Sys('(Z/2)^2 with the honest cocycle w(a,b,c) = (-1)^(a1 b2 c1)',
                   n, N, dual, F, Finv, [ONE] * n, [Sc(wZ[i][i][i]) for i in range(n)], 1)
    n = 3 if name == 'ISING' else 2
    N = [[[0] * n for _ in range(n)] for _ in range(n)]
    for row in req(name + '.N'):
        N[int(row[0])][int(row[1])][int(row[2])] = int(row[3])
    dual = [0] * n
    for row in req(name + '.dual'):
        dual[int(row[0])] = int(row[1])
    ispair = name in ('FIB', 'ISING', 'YL')
    conv = (lambda v: pr(v[0], v[1])) if ispair else (lambda v: rat(v[0]))
    F = zeros6(n)
    Finv = zeros6(n)
    for row in req(name + '.F'):
        F[int(row[0])][int(row[1])][int(row[2])][int(row[3])][int(row[4])][int(row[5])] = conv(row[6:])
    for row in req(name + '.Finv'):
        Finv[int(row[0])][int(row[1])][int(row[2])][int(row[3])][int(row[4])][int(row[5])] = conv(row[6:])
    ev = [ZERO] * n
    for row in req(name + '.ev'):
        ev[int(row[0])] = conv(row[1:])
    coev = [ZERO] * n
    for row in req(name + '.coev'):
        coev[int(row[0])] = conv(row[1:])
    d = {'VECZ2': 1, 'VECZ2T': 1, 'FIB': 5, 'ISING': 2, 'YL': 5}[name]
    pretty = {'VECZ2': 'Vec_{Z/2}, trivial cocycle (Q)',
              'VECZ2T': 'Vec^omega_{Z/2}, non-trivial cocycle (Q)',
              'FIB': 'Fibonacci (Q(sqrt 5); Finv has a 2x2 block)',
              'ISING': 'Ising (Q(sqrt 2); Finv has a 2x2 block)',
              'YL': 'Yang-Lee (Q(sqrt 5); non-unitary)'}[name]
    return Sys(pretty, n, N, dual, F, Finv, ev, coev, d)


# ---------------------------------------------------------------- driver
def battery_objects(S):
    U = unitObj(S)
    objs = [U]
    objs += [base([1 if c == i else 0 for c in range(S.n)]) for i in range(S.n)]
    objs += [tobj(S, a, b) for a in objs[1:] for b in objs[1:]]
    for i in range(S.n):
        v = [0] * S.n
        v[i] = 2
        objs.append(base(v))
    objs.append(base([1] * S.n))
    seen = []
    keys = []
    for o in objs:
        key = tuple(mul(S, o, c) for c in range(S.n))
        if key not in keys:
            keys.append(key)
            seen.append(o)
    return seen


EXPECT_PU = {'VECZ2': True, 'VECZ2T': True, 'FIB': True, 'ISING': True,
             'YL': False,      # `YangLee.not_pseudoUnitary` (Examples/YangLee.lean:395)
             'Z2SQ': True}


def run(bridge, seed=11):
    tab = parse_bridge(bridge)
    rng = random.Random(seed)
    phi = Sc(Fr(1, 2), Fr(1, 2))            # (1+sqrt5)/2
    data = [('VECZ2', [ONE, ONE]),
            ('VECZ2T', [ONE, ONE]),
            ('FIB', [ONE, phi]),
            ('ISING', [ONE, Sc(0, 1), ONE]),   # sqrt2, read in Q(sqrt2)
            ('YL', [ONE, phi]),
            ('Z2SQ', [ONE, ONE, ONE, ONE])]
    allok = True
    print("=" * 78)
    print("WP2 round 3 / D8: the numerical battery on the canonical block scaffold")
    print("=" * 78)
    for name, fpdim in data:
        S = build(tab, name)
        print("\n--- %s   [n = %d, scalars in Q(sqrt %d)]" % (S.name, S.n, S.d))
        bad = S.check_datum()
        print("    FusionSystem axioms on the tables                  : %s"
              % ("OK  (pentagon on all %d label tuples, both inverse laws,"
                 " units, snakes)" % (S.n ** 9) if not bad else "FAIL %s" % (bad[:3],)))
        allok &= not bad
        if bad:
            continue
        objs = battery_objects(S)
        print("    objects (%d): %s" % (len(objs), ", ".join(repr(o) for o in objs)))
        for k in COVER:
            COVER[k] = 0
        r = next((z for z in (chk_assoc_iso(S, X, Y, Z)
                              for X, Y, Z in itertools.product(objs, repeat=3)) if z), None)
        print("    AssociatorIso   (hom;inv = 1, inv;hom = 1)        : %s  [%d triples]"
              % ("OK" if r is None else "FAIL %s" % (r,), len(objs) ** 3))
        allok &= r is None
        r = next((z for z in (chk_object_assoc(S, X, Y, Z)
                              for X, Y, Z in itertools.product(objs, repeat=3)) if z), None)
        print("    ObjectAssociativity (frozen)                       : %s"
              % ("OK" if r is None else "FAIL %s" % (r,)))
        allok &= r is None
        sext = list(itertools.product(objs, repeat=6))
        rng.shuffle(sext)
        r = next((z for z in (chk_assoc_natural(S, *t, rng) for t in sext[:16]) if z), None)
        print("    AssociatorNatural (frozen) random morphisms        : %s  [%d sextuples]"
              % ("OK" if r is None else "FAIL %s" % (r,), min(16, len(sext))))
        allok &= r is None
        quads = list(itertools.product(objs, repeat=4))
        rng.shuffle(quads)
        r = next((z for z in (chk_pentagon(S, *q) for q in quads[:14]) if z), None)
        print("    PentagonShape (D3's frozen target)                 : %s  [%d quadruples]"
              % ("OK" if r is None else "FAIL %s" % (r,), min(14, len(quads))))
        allok &= r is None
        r = next((z for z in (chk_snake_left(S, X) for X in objs) if z), None)
        print("    SnakeLeft  (frozen)                                : %s  [%d objects]"
              % ("OK" if r is None else "FAIL %s" % (r,), len(objs)))
        allok &= r is None
        r = next((z for z in (chk_snake_right(S, X) for X in objs) if z), None)
        print("    SnakeRight (frozen)                                : %s  [%d objects]"
              % ("OK" if r is None else "FAIL %s" % (r,), len(objs)))
        allok &= r is None
        r = next((z for z in (chk_triangle(S, X, Y)
                              for X, Y in itertools.product(objs, repeat=2)) if z), None)
        print("    Unitors.triangle                                   : %s"
              % ("OK" if r is None else "FAIL %s" % (r,)))
        allok &= r is None
        r = next((z for z in (chk_unitors_agree(S, X) for X in objs) if z), None)
        print("    ReconUnitors = ReconRigid unitors (D6's dedupe)     : %s"
              % ("OK" if r is None else "FAIL %s" % (r,)))
        allok &= r is None
        r = next((z for z in (chk_unitor_natural(S, X, Y, rng)
                              for X, Y in itertools.product(objs, repeat=2)) if z), None)
        print("    unitor naturality (Units.whiskerLeft_leftUnitor /"
              " whiskerRight_rightUnitor) : %s" % ("OK" if r is None else "FAIL %s" % (r,)))
        allok &= r is None
        P = [ONE] * S.n
        badt = chk_trace(S, P)
        badf = chk_fpdata(S, fpdim)
        okp, lhs, rhs = chk_pseudounitary(S, fpdim)
        want_pu = EXPECT_PU[name]
        okp = (okp == want_pu)
        print("    TraceOfScalar / TraceOfPivotalComponent / TraceProduct_eq_kappa : %s"
              % ("OK" if not badt else "FAIL %s" % (badt,)))
        print("    FPData axioms                                      : %s"
              % ("OK" if not badf else "FAIL %s" % (badf[:3],)))
        print("    IsPseudoUnitaryC: sum kappa kappa* = sum fpdim^2    : %s  [%s = %s;"
              " datum is pseudo-unitary: %s%s]"
              % ("OK" if okp else "FAIL", lhs, rhs, "yes" if (lhs == rhs) else "no",
                 "" if want_pu else " (YangLee.not_pseudoUnitary proved in the repo)"))
        allok &= not badt and not badf and okp
        print("    [coverage] %d blocks compared, %d matrix entries examined,"
              " %d of them nonzero, %d identity entries verified"
              % (COVER['blocks'], COVER['compared'], COVER['nonzero'], COVER['identity']))
    print("\n" + "=" * 78)
    print("BATTERY: %s" % ("ALL CHECKS PASS" if allok else "*** FAILURES -- see above ***"))
    print("=" * 78)
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(run(sys.argv[1] if len(sys.argv) > 1 else 'bridge.out'))
