# A single no-pinch ablation with an exact contour defect

## Result and verification scope

Removing only the first of the four clauses in `K4NoPinch` makes
`GammaK4Contour.corrected_value_independent` false for the **actual constructed
hyperbolic gamma function**. Two admissible, absolutely convergent corrected
contours differ by exactly **−1/2**.

The analytic counterexample below is a mathematical derivation checked against
the source, not yet a Lean certificate for the full integral discrepancy.
[GammaContourAblation.lean](GammaContourAblation.lean) isolates the geometry and
finite-sum accounting; its scope is deliberately smaller than the analytic claim.
It passes `lake env lean docs/ablation/GammaContourAblation.lean`.
The two audited main certificates use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry` or custom axioms. The check recorded
2.401 GiB peak process-group RSS; existing dependency warnings were replayed.
The [dependency paths](gamma_contour_ablation_paths.json) were extracted from the
existing graph after verifying all its project source hashes still match.

## 1. Change one clause and retain the actual gamma

Write `gamma` for `GammaContinuation.gamma a b hb hba` and set

\[
a=\sqrt2,\quad b=1,\quad \Omega=a+b,\qquad
r=0,\quad s=-\Omega/2,\quad x=0,\quad y=1/2.
\]

The kernel parameters are

\[
U=\Omega/4+(r+s)/2=0,\qquad
V=\Omega/4+(r-s)/2=\Omega/2.
\]

The four clauses of [K4NoPinch](../../HaagerupIzumi/Analytic/HypGamma.lean)
exclude `2U`, `2V`, `U+V−x`, and `U+V+x` from the negative pole lattice
\(P=-(a\mathbb N+b\mathbb N)\). Their values here are

\[
0,\quad\Omega,\quad\Omega/2,\quad\Omega/2.
\]

**Only the first clause fails.** The other three quantities are positive.
All gamma identities, residue normalization, positivity and irrationality of
the periods remain available. `K4Conv` holds because
\(1/2<\Omega/2\).

The candidate pole families are

\[
L=\{-ma-nb:m,n\ge0\}\cup
  \{-\Omega/2-ma-nb:m,n\ge0\},\qquad R=-L.
\]

Both vertical lines \(\sigma_-=-1/4\) and \(\sigma_+=1/4\) avoid every
candidate pole. The only pole between them is zero, which belongs to **both**
orientations. No assumption about poles lying on an integration line is dropped.

## 2. Reduce the actual gamma kernel and calculate its residue

The four-gamma integrand is

\[
f(z)=e^{\pi i z/\sqrt2}\gamma(z)\gamma(-z)
     \gamma(\Omega/2+z)\gamma(\Omega/2-z).
\]

On the closed strip \(|\Re z|\le1/4\), excluding zero, the last two gamma
factors multiply to one by reflection. The two shift identities also give

\[
\gamma(\Omega-z)
=-4\sin(\pi z/a)\sin(\pi z/b)\gamma(-z).
\]

Combining this with \(\gamma(z)\gamma(\Omega-z)=1\) yields the exact formula

\[
f(z)=-\frac{e^{\pi i z/\sqrt2}}
              {4\sin(\pi z/\sqrt2)\sin(\pi z)}.
\]

The identities used are in
[GammaIdentities.lean](../../HaagerupIzumi/Analytic/GammaIdentities.lean), and
their domain conditions hold throughout this punctured strip. Values assigned
to the total Lean function at a pole are irrelevant to these limits and to the
two integration lines.

Expansion at zero gives

\[
f(z)=-\frac{\sqrt2}{4\pi^2z^2}-\frac{i}{4\pi z}+O(1),\qquad
\rho:=\operatorname{Res}_{0}f=-\frac{i}{4\pi},\qquad
2\pi i\rho=\frac12.
\]

Thus the pole is exactly double, within the existing `HasResidueGen` interface.
This example does not exploit the arbitrary value of `residueValue` when that
interface fails.

Both line integrals converge absolutely. The sine denominators supply decay
\(e^{-\pi(1+1/\sqrt2)|\Im z|}\); the exponential numerator changes its
rate by at most \(\pi/\sqrt2\). The resulting bound is
\(O(e^{-\pi|\Im z|})\), uniformly across the strip at large height.
The existing `k4_tail_bound` in
[GammaKernelDecay.lean](../../HaagerupIzumi/Analytic/GammaKernelDecay.lean)
also gives rate \(c=\pi\) here and requires no no-pinch hypothesis.

## 3. The strip theorem survives; contour independence fails

Let \(I_\sigma=\int_{\sigma-i\infty}^{\sigma+i\infty}f(z)\,dz\), oriented
upward as in the project. The general `strip_residues_gen` theorem in
[Residue.lean](../../HaagerupIzumi/Analytic/Residue.lean) applies: holomorphy away
from zero, an at-most-double pole, exponential decay, and pole-free boundary
lines all hold. Its orientation gives

\[
I_{1/4}-I_{-1/4}=2\pi i\rho=\frac12.
\]

The unchanged `CorrectedContour.value` definition in
[ResidueAlgebra.lean](../../HaagerupIzumi/Analytic/ResidueAlgebra.lean) is

\[
C_\sigma=I_\sigma+2\pi i\sum_{p\in S_L(\sigma)}\operatorname{Res}_p f
                    -2\pi i\sum_{p\in S_R(\sigma)}\operatorname{Res}_p f.
\]

The actual finite sets are

| Line | Crossed left | Crossed right |
|---|---|---|
| \(-1/4\) | \(\{0\}\) | \(\varnothing\) |
| \(1/4\) | \(\varnothing\) | \(\{0\}\) |

Consequently,

\[
C_{-1/4}=I_{-1/4}+\tfrac12,\qquad
C_{1/4}=I_{1/4}-\tfrac12,
\]

and therefore

\[
\boxed{C_{1/4}-C_{-1/4}=-\tfrac12\ne0.}
\]

The origin crosses the strip once. The correction formula treats it as a left
crossing and a right crossing, changing by twice its residue contribution.
There is no contour separating left and right poles at this common point.

## 4. Exact failure classification and dependency path

| Declaration, with the selected no-pinch clause omitted | Status for this witness |
|---|---|
| `noPinch_disjoint` | False: zero lies in both families. |
| `sum_crossedBetween` | False: it asserts \(\rho=2\rho\) for the actual nonzero residue. |
| `kernel_exists_hasResidueGen` | Its conclusion still holds here: the pole is only double. |
| `kernel_strip_residues` | Its conclusion still holds here by the general strip theorem. |
| `corrected_value_eq_of_lt`, `corrected_value_independent` | False: corrected values differ by −1/2. |
| `K4_line`, universally over admissible lines | False: the two different corrected values cannot both equal the fixed `K4` value. |
| Later Euler/completion results | Existing proof dependencies are affected; their falsity does not follow. |

The first finite-sum failure is exactly the invocation of `Finset.sum_union`
in [GammaK4Line.lean](../../HaagerupIzumi/Analytic/GammaK4Line.lean): the two
sets must be disjoint, as in the
[Mathlib statement](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html#Finset.sum_union).
Here their intersection is the origin. The required
correction to the combinatorial formula is an intersection subtraction,
\(\sum_{A\cup B}\rho=\sum_A\rho+\sum_B\rho-\sum_{A\cap B}\rho\).
That explains the error but does not by itself supply a canonical separating
contour or a regular value at a pinch.

Every consecutive arrow in this path exists in the cached proof graph:

```text
sum_crossedBetween
→ corrected_value_eq_of_lt
→ corrected_value_independent
→ K4_line
→ exists_local_scaledK4_representation
→ differentiableAt_K4_scaled
→ K4_euler
→ GammaContinuation.hypGamma._proof_1
→ GammaContinuation.hypGamma
→ ruijsenaarsHypGamma
→ EGEquations_ruijsenaars
→ exists_EGEquations_odd
```

This ablates an intermediate contour-domain assumption. It does not contradict
the actual odd-order theorem, whose use sites establish their no-pinch conditions.

## 5. A separate analytic test: a genuine singularity in the parameter

Keeping the same periods, put \(v=\Omega/4\), and scale fixed parameters
\(r=s=-v,\ x=y=0\) by \(t\to1^-\). Then
\(U=v(1-t)=\varepsilon>0\) and \(V=v\). At \(t=1\), only the first no-pinch
clause fails again, while the convergence margin stays strictly positive.

`K4_eq_integral_zero` and gamma conjugation give

\[
K_4(-tv,-tv,0,0)=\frac1{\sqrt{ab}}
  \int_{\mathbb R}|\gamma(\varepsilon+i\xi)|^2
                       |\gamma(v+i\xi)|^2\,d\xi.
\]

The integrand is nonnegative. Since
\(z\gamma(z)\to R_0=\sqrt{ab}/(2\pi)>0\) at zero and
\(\gamma(v)>0\), on \(|\xi|\le\varepsilon\) it is bounded below by
\(c/(\varepsilon^2+\xi^2)\), for a fixed \(c>0\) and all sufficiently small
\(\varepsilon\). Integrating gives \(K_4\ge c'/\varepsilon\to+\infty\).
No choice of finite value at the pinched point can make this function continuous.

This independently refutes `differentiableAt_K4_scaled` with just that
no-pinch clause removed. It shows why replacing the contour accounting alone
cannot restore ordinary holomorphy across all pinches. This second analytic
argument is also not yet formalized in Lean.
