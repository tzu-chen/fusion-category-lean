"""
Numeric regression for the D6 snake statements (m6, WP2 round 2).

Exact arithmetic in Q(sqrt d), encoded as pairs (p,q) meaning p + q*sqrt(d),
with p,q Fractions.  Implements the reconstruction's block model exactly as
FusionCatgory.Recon/ReconTensor/ReconAssoc/ReconRigid2 define it:

  blk of X         : a finite set (list) of hashable indices per label
  morphism         : f c : rows x cols -> k
  tensorObj X Y c  : indices (p1,p2, nu, x, y) with nu < N p1 p2 c
  ev, coev         : supported on the unit channel nu, delta x2 = x1
  unitors          : delta on the identity channel
  associatorHom    : F a b c d e f on matched four-leaf data

and checks the two snake equations of ReconRigid2.SnakeLeft / SnakeRight.
"""
from fractions import Fraction as Fr
from itertools import product

# ---------------- Q(sqrt d) with pairs ----------------
class K:
    def __init__(self, d): self.d = d
    def zero(self): return (Fr(0), Fr(0))
    def one(self): return (Fr(1), Fr(0))
    def add(self,a,b): return (a[0]+b[0], a[1]+b[1])
    def mul(self,a,b):
        d=self.d; return (a[0]*b[0]+d*a[1]*b[1], a[0]*b[1]+a[1]*b[0])
    def neg(self,a): return (-a[0],-a[1])
    def eq(self,a,b): return a[0]==b[0] and a[1]==b[1]
    def isz(self,a): return a[0]==0 and a[1]==0
    def half(self, p, q):  # (p + q sqrt d)/2   (the Lean pair encoding)
        return (Fr(p,2), Fr(q,2))

# ---------------- fusion data ----------------
class Sys:
    def __init__(self, n, N, dual, F, Finv, ev, coev, Kk):
        self.n=n
        self.N=[[[N(a,b,c) for c in range(n)] for b in range(n)] for a in range(n)]
        self.dual=dual; self.F=F; self.Finv=Finv
        self.ev=[ev(i) for i in range(n)]; self.coev=[coev(i) for i in range(n)]; self.K=Kk
    def kappa(self,i): return self.K.mul(self.coev[i], self.ev[i])

def vecZ2(twisted):
    n=2
    def N(a,b,c):
        if a==0: return 1 if b==c else 0
        if b==0: return 1 if a==c else 0
        return 1 if c==0 else 0
    dual=lambda i:i
    Kk=K(1)  # Q
    def supp(a,b,c,d,e,f):
        return N(a,b,e)>0 and N(e,c,d)>0 and N(b,c,f)>0 and N(a,f,d)>0
    def F(a,b,c,d,e,f):
        if not supp(a,b,c,d,e,f): return Kk.zero()
        if twisted and a==1 and b==1 and c==1 and d==1: return Kk.neg(Kk.one())
        return Kk.one()
    def Finv(a,b,c,d,f,e): return F(a,b,c,d,e,f)
    ev=lambda i: Kk.one()
    coev=(lambda i: (Kk.one() if i==0 else Kk.neg(Kk.one()))) if twisted else (lambda i: Kk.one())
    return Sys(n,N,dual,F,Finv,ev,coev,Kk)

def fibonacci():
    n=2
    def N(a,b,c):
        if a==0: return 1 if b==c else 0
        if b==0: return 1 if a==c else 0
        return 1
    dual=lambda i:i
    Kk=K(5)
    def suppF(a,b,c,d,e,f): return N(a,b,e)>0 and N(e,c,d)>0 and N(b,c,f)>0 and N(a,f,d)>0
    def F(a,b,c,d,e,f):
        if not suppF(a,b,c,d,e,f): return Kk.zero()
        if a==1 and b==1 and c==1 and d==1:
            if e==0 and f==0: return Kk.half(-1,1)
            if e==0 and f==1: return Kk.half(2,0)
            if e==1 and f==0: return Kk.half(-1,1)
            return Kk.half(1,-1)
        return Kk.half(2,0)
    def Finv(a,b,c,d,f,e):
        if not (N(b,c,f)>0 and N(a,f,d)>0 and N(a,b,e)>0 and N(e,c,d)>0): return Kk.zero()
        if a==1 and b==1 and c==1 and d==1:
            if f==0 and e==0: return Kk.half(-1,1)
            if f==0 and e==1: return Kk.half(2,0)
            if f==1 and e==0: return Kk.half(-1,1)
            return Kk.half(1,-1)
        return Kk.half(2,0)
    ev=lambda i: Kk.half(2,0)
    coev=lambda i: Kk.half(2,0) if i==0 else Kk.half(1,1)
    return Sys(n,N,dual,F,Finv,ev,coev,Kk)

# ---------------- objects ----------------
class Obj:
    def __init__(self, m, blk):
        self.m=m; self.blk=blk   # blk: label -> list/tuple of indices

def ofM(m):  # the literal model: blk c = Fin (m c)
    return Obj(m, [tuple(('b',c,i) for i in range(m[c])) for c in range(len(m))])

def dualObj(S,X): 
    return Obj([X.m[S.dual(c)] for c in range(S.n)],
               [X.blk[S.dual(c)] for c in range(S.n)])

def tensorObj(S,X,Y):
    n=S.n
    m=[sum(S.N[a][b][c]*X.m[a]*Y.m[b] for a in range(n) for b in range(n)) for c in range(n)]
    blk=[]
    for c in range(n):
        idx=[]
        for a in range(n):
            for b in range(n):
                for nu in range(S.N[a][b][c]):
                    for x in X.blk[a]:
                        for y in Y.blk[b]:
                            idx.append(((a,b),nu,x,y))
        blk.append(idx)
    o=Obj(m,blk)
    for c in range(n): assert len(o.blk[c])==m[c], (c, len(o.blk[c]), m[c])
    return o

def unitObj(S):
    return Obj([1]+[0]*(S.n-1), [ [('u',0)] ] + [ [] for _ in range(S.n-1)])

# ---------------- morphisms ----------------
class Mor:
    def __init__(self, src, tgt, mat):  # mat: label -> dict (row,col) -> val
        self.src=src; self.tgt=tgt; self.mat=mat
    def get(self,c,i,j):
        return self.mat[c].get((i,j), self.mat[c].get('zero', None) or None)

def call(S, f, c, i, j):
    """f is (label,row,col) -> val, sparse dict."""
    v=f[c].get((i,j))
    return v if v is not None else S.K.zero()

def comp(S, f, g, mid):
    """(f >> g) with middle object `mid` (f.tgt = mid = g.src)."""
    out=[]
    for c in range(S.n):
        d={}
        gcols={}
        for (k,j),v2 in g[c].items(): gcols.setdefault(k,[]).append((j,v2))
        for (i,k1),v1 in f[c].items():
            for (j,v2) in gcols.get(k1,[]):
                w=S.K.mul(v1,v2)
                if not S.K.isz(w): d[(i,j)]=S.K.add(d.get((i,j),S.K.zero()),w)
        out.append(d)
    return out

def compose(S, mats, mids):
    cur=mats[0]
    for g,mid in zip(mats[1:], mids):
        cur=comp(S,cur,g,mid)
    return cur

def tensorHom(S, A,A_, B,B_, f, g):
    n=S.n
    out=[]
    for c in range(n):
        d={}
        for a in range(n):
            for b in range(n):
                for nu1 in range(S.N[a][b][c]):
                    for nu2 in range(S.N[a][b][c]):
                        if nu1!=nu2: continue
                        for x1 in A.blk[a]:
                            for x2 in A_.blk[a]:
                                fx=f[a].get((x1,x2))
                                if fx is None or S.K.isz(fx): continue
                                for y1 in B.blk[b]:
                                    for y2 in B_.blk[b]:
                                        gy=g[b].get((y1,y2))
                                        if gy is None or S.K.isz(gy): continue
                                        w=S.K.mul(fx,gy)
                                        d[(((a,b),nu1,x1,y1),((a,b),nu2,x2,y2))]=w
        out.append(d)
    return out

def identity(S,X):
    return [{(x,x):S.K.one() for x in X.blk[c]} for c in range(S.n)]

def evMor(S,X,hn=0):
    A=dualObj(S,X); D=tensorObj(S,A,X); U=unitObj(S)
    out=[]
    for c in range(S.n):
        d={}
        for (p,nu,s,t) in D.blk[c]:
            if c!=0: continue
            a,b=p
            if b==S.dual(a):
                if s==t:
                    d[((p,nu,s,t),('u',0))]=S.ev[b]
        out.append(d)
    return out

def coevMor(S,X):
    A=dualObj(S,X); D=tensorObj(S,X,A); U=unitObj(S)
    out=[]
    for c in range(S.n):
        d={}
        for (p,nu,s,t) in D.blk[c]:
            if c!=0: continue
            a,b=p
            if a==S.dual(b):
                if s==t:
                    d[(('u',0),(p,nu,s,t))]=S.coev[a]
        out.append(d)
    return out

def leftUnitor(S,X):
    U=unitObj(S); D=tensorObj(S,U,X)
    out=[]
    for c in range(S.n):
        d={}
        for (p,nu,s,t) in D.blk[c]:
            a,b=p
            if b==c:
                d[((p,nu,s,t),t)]=S.K.one()
        out.append(d)
    return out

def rightUnitor(S,X):
    U=unitObj(S); D=tensorObj(S,X,U)
    out=[]
    for c in range(S.n):
        d={}
        for (p,nu,s,t) in D.blk[c]:
            a,b=p
            if a==c:
                d[((p,nu,s,t),s)]=S.K.one()
        out.append(d)
    return out

def assocHom(S,X,Y,Z):
    """(X*Y)*Z -> X*(Y*Z), entry F a b c d e f"""
    L=tensorObj(S,tensorObj(S,X,Y),Z); R=tensorObj(S,X,tensorObj(S,Y,Z))
    out=[]
    for c in range(S.n):
        d={}
        for ((e,c1),nu,u,z) in L.blk[c]:
            ((a1,b1),mu,x,y)=u
            for ((a2,f),nu2,x2,w) in R.blk[c]:
                ((b2,c2),mu2,y2,z2)=w
                if (a1,b1,c1)==(a2,b2,c2) and x==x2 and y==y2 and z==z2:
                    v=S.F(a1,b1,c1,c,e,f)
                    if not S.K.isz(v): d[(((e,c1),nu,u,z),((a2,f),nu2,x2,w))]=v
        out.append(d)
    return out

def assocInv(S,X,Y,Z):
    """X*(Y*Z) -> (X*Y)*Z, entry Finv a b c d f e"""
    L=tensorObj(S,tensorObj(S,X,Y),Z); R=tensorObj(S,X,tensorObj(S,Y,Z))
    out=[]
    for c in range(S.n):
        d={}
        for ((a2,f),nu2,x2,w) in R.blk[c]:
            ((b2,c2),mu2,y2,z2)=w
            for ((e,c1),nu,u,z) in L.blk[c]:
                ((a1,b1),mu,x,y)=u
                if (a1,b1,c1)==(a2,b2,c2) and x==x2 and y==y2 and z==z2:
                    v=S.Finv(a1,b1,c1,c,f,e)
                    if not S.K.isz(v): d[(((a2,f),nu2,x2,w),((e,c1),nu,u,z))]=v
        out.append(d)
    return out

def check(S, label, objects):
    n=S.n
    ok=True
    # axiom sanity
    for i in range(n):
        if not S.K.eq(S.K.mul(S.K.mul(S.coev[i],S.ev[i]),S.F(i,S.dual(i),i,i,0,0)),S.K.one()):
            print(f"  !! snake_left axiom fails at {i}"); ok=False
        if not S.K.eq(S.K.mul(S.K.mul(S.coev[i],S.ev[i]),S.Finv(S.dual(i),i,S.dual(i),S.dual(i),0,0)),S.K.one()):
            print(f"  !! snake_right axiom fails at {i}"); ok=False
    for X in objects:
        # SnakeLeft: (coev (x) id) >> assoc >> (id (x) ev) >> rightUnitor = leftUnitor
        A=dualObj(S,X)
        m1=tensorHom(S, unitObj(S), tensorObj(S,X,A), X, X, coevMor(S,X), identity(S,X))
        m2=assocHom(S,X,A,X)
        m3=tensorHom(S, X, X, tensorObj(S,A,X), unitObj(S), identity(S,X), evMor(S,X))
        m4=rightUnitor(S,X)
        c1=compose(S,[m1,m2,m3,m4],[tensorObj(S,X,A), tensorObj(S,tensorObj(S,X,A),X), tensorObj(S,X,tensorObj(S,A,X))])
        lhs=leftUnitor(S,X)
        same=True
        for c in range(n):
            keys=set(list(c1[c].keys())+list(lhs[c].keys()))
            for (i,j) in keys:
                v1=c1[c].get((i,j),S.K.zero()); v2=lhs[c].get((i,j),S.K.zero())
                if not S.K.eq(v1,v2):
                    same=False; print(f"  !! {label} X.m={X.m} SnakeLeft c={c} ({i},{j}): {v1} vs {v2}")
        print(f"  {label} X.m={X.m}: SnakeLeft {'OK' if same else 'FAIL'}")
        ok = ok and same
        # SnakeRight: (id (x) coev) >> assocInv >> (ev (x) id) >> leftUnitor_X* = rightUnitor_X*
        m1r=tensorHom(S, A,A, unitObj(S), tensorObj(S,X,A), identity(S,A), coevMor(S,X))
        m2r=assocInv(S,A,X,A)
        m3r=tensorHom(S, tensorObj(S,A,X), unitObj(S), A, A, evMor(S,X), identity(S,A))
        m4r=leftUnitor(S,A)
        c2=compose(S,[m1r,m2r,m3r,m4r],[tensorObj(S,A,tensorObj(S,X,A)), tensorObj(S,tensorObj(S,A,X),A), tensorObj(S,tensorObj(S,A,X),unitObj(S))])
        rhs=rightUnitor(S,A)
        same2=True
        for c in range(n):
            keys=set(list(c2[c].keys())+list(rhs[c].keys()))
            for (i,j) in keys:
                v1=c2[c].get((i,j),S.K.zero()); v2=rhs[c].get((i,j),S.K.zero())
                if not S.K.eq(v1,v2):
                    same2=False; print(f"  !! {label} X.m={X.m} SnakeRight c={c} ({i},{j}): {v1} vs {v2}")
        print(f"  {label} X.m={X.m}: SnakeRight {'OK' if same2 else 'FAIL'}")
        ok = ok and same2
    return ok

objs = [ofM([1,0]), ofM([0,1]), ofM([1,1]), ofM([2,1]), ofM([0,3]), ofM([2,2])]
allsame=True
print("VecZ2 (trivial cocycle):")
allsame &= check(vecZ2(False), "vecZ2", objs)
print("VecZ2 (nontrivial cocycle, kappa_g = -1):")
allsame &= check(vecZ2(True), "vecZ2tw", objs)
print("Fibonacci (2x2 associator block, F != Finv order):")
allsame &= check(fibonacci(), "fib", objs)
print("ALL OK" if allsame else "FAILURES PRESENT")
