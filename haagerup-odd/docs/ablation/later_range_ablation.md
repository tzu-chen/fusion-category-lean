# Late range ablations: exact missing terms in the product transforms

## Scope

These experiments retain the actual constructed hyperbolic gamma and change
one named inequality in a Section 6 product-transform lemma. They refute the
specific residue-sum formulas, not the final Evans–Gannon equations.

The common ordered range is

\[
1\le g,\quad 1\le h,\quad g+h<n,\quad 1\le l\le h.
\]

Use \(n=3\), zero Fourier frequency \(k=v=0\), and write

\[
d=\frac{3+\sqrt{13}}2,\qquad b=\omega_2=1+\frac1d
 =\frac{\sqrt{13}-1}2,\qquad r=\sqrt d.
\]

Here `F` is the existing sampling function, `t_p(a)` is `Concrete.tz`, and
\(B\) is the matrix of the constructed coefficient data. All integer samples
of `F` are nonzero by `F_int_ne_zero`; none of the calculations below uses a
singular gamma sample.

| Retained condition | Left experiment | Right experiment |
|---|---|---|
| Parameters \((n,g,h,l)\) | \((3,1,1,2)\) | \((3,1,4,1)\) |
| \(n\) odd, all labels positive | Holds | Holds |
| \(g+h<n\) | \(2<3\) | **Removed: \(5<3\) is false** |
| \(l\le h\) | **Removed: \(2\le1\) is false** | \(1\le4\) |
| Required frequency congruence | Holds for \(k=v=0\) | Holds for \(k=v=0\) |
| Frequency bounds in the later product formula | Holds | Holds |

## A. Remove only `l ≤ h` from `left_residue_sum`

Target: [LeftProduct.lean](../../HaagerupIzumi/Analytic/LeftProduct.lean),
`Concrete.left_residue_sum`, beginning at line 964. Its proof is part of
Proposition 6.3(1), rather than a standalone elementary sampling result.

Put \(g=h=1,l=2\). The labels are \((p,q,s)=(2,-1,1)\).
After division by the nonzero prefactor
\(C=dF(2)F(-1)=dF(2)^2\), its claimed identity is

\[
T_L:=\sum_{a=0}^{2}t_2(a)t_{-1}(a+1)
\stackrel{?}=\sum_{a\in\mathbb Z/3}B(a,2)B(a+1,2)+bB(0,2)=:P_L.
\]

The positive-label sampling formula gives
\(t_2(a)=B(a,2)+b\mathbf1_{a=2}\). For the negative-label factor, the
unmodified proof assumes \(a+l-h\le n-1\). At \(a=2\), this becomes the
false inequality \(3\le2\). In fact,

\[
t_{-1}(3)=\frac1d,\qquad B(0,-1)=B(0,2)=-1.
\]

There is an extra correction \(b\) at that single sample. The two other
samples satisfy the old replacement rule. Since \(t_2(2)=1/d\),

\[
\boxed{T_L-P_L=\frac bd=4-\sqrt{13}>0.}
\]

This is a one-step violation of the ordering: raising \(l\) from \(h\)
to \(h+1\) lets the last shifted sample leave its valid window.

### Exact defect in the original, unnormalized theorem

With \(f=F(2)\ne0\), the original left and right sides reduce to

\[
\mathrm{LHS}=-\frac{2r}{f}+\frac{f^2}{d},\qquad
\mathrm{RHS}=-\frac{2r}{f}-f^2.
\]

Hence

\[
\boxed{\mathrm{LHS}-\mathrm{RHS}=bf^2\ne0.}
\]

For reproduction, the exact sampling values used are
\(F(-2)=-1/f, F(-1)=f, F(0)=r, F(1)=1/f, F(2)=f,
F(3)=1/r,F(4)=1/f\), and
\(B(\cdot,2)=(-1,1/(rf^3),-1)\).

The first failed proof step is the application of `tz_neg_nonneg` in the local
`htq` proof (near line 1026): its sample upper bound is false. Replacing it
with the correct boundary value yields the displayed error, so this is not
merely an unsuccessful `omega` tactic.

## B. Remove only `g + h < n` from `right_residue_sum`

Target: [RightProduct.lean](../../HaagerupIzumi/Analytic/RightProduct.lean),
`Concrete.right_residue_sum`, beginning at line 1404, in Proposition 6.3(2).

Put \(g=1,h=4,l=1\). Then \((p,q,s)=(-2,1,6)\), and the three integer
window points are \(-6,-5,-4\). Write \(\beta=B(2,1)\).
The exact samples are

| \(j\) | \(j-6\) | \(t_{-2}(j-6)\) | \(t_1(j)\) |
|---|---|---|---|
| 0 | −6 | −1 | −1 |
| 1 | −5 | \(b-1\) | \(b-1\) |
| 2 | −4 | \(\beta\) | \(\beta\) |

In particular, the sample \(-5=-2-3\) is a translate of the negative-label
diagonal. `tz_add_n` and `tz_neg_neg` give
\(t_{-2}(-5)=t_{-2}(-2)=b-1\). It lies exactly at the excluded lower
endpoint of `tz_neg_window`: \(-n-(g+l)=-5\).

The normalized actual residue sum is therefore

\[
T_R=1+(b-1)^2+\beta^2.
\]

The theorem's unchanged main sum and two linear corrections give
\(P_R=2+\beta^2-2b\). Its quadratic correction is
\(b^2\mathbf1_{h=l}\), which is zero because \(4\ne1\).
But \(4\equiv1\pmod3\): the two actual sample corrections occur at the
same index \(j=1\). Their product was omitted. Thus

\[
\boxed{T_R-P_R=b^2=\frac{7-\sqrt{13}}2>0.}
\]

The original raw sum has the nonzero prefactor

\[
P=(-1)^{-2+1+6}dF(-2)F(1)=dF(1)^2\ne0.
\]

Its actual defect is consequently \(Pb^2\ne0\).

The first failed proof step is the local `htp` in `right_residue_sum`
(near line 1461). At \(j=1\), its application of `tz_neg_window` needs
\(-5<-5\). Its claimed sample value is also false: the indicator
`a.val = h` asks whether \(1=4\), so it omits the correction \(b\).
Later, the local `hc1` (near line 1523) fails as well: no representative
`a.val` equals \(4\), so its sum is zero, whereas its stated value is
\(bB(1,1)=-b\). The net defect in the final displayed formula is the
quadratic term above. The literal `hc3` identity, applied to the already
incorrect indicators, is not itself a counterexample.

The range \(g+h<n\) keeps the relevant label representatives below \(n\),
so equality modulo \(n\) and equality of those representatives agree.
Once that range is removed, a test such as `if h = l` can miss a genuine
coincidence of the cyclic indices. The certificate is for this concrete
witness; replacing that one indicator is not asserted to repair the formula
for every unrestricted label.

## Why these failures arise without changing the gamma function

The analytic interpolation samples are indexed by integers, whereas \(B\)
is indexed modulo \(n\). Their matching formula depends on the chosen
integer window. The analytic shift has exceptional points:

\[
F(0)=\sqrt d,\qquad F(n)=1/\sqrt d,
\]

while the usual integer shift rule
\(F(a+n)=(-1)^{a+1}F(a)\) requires \(a\ne0\).
The later range restrictions keep these exceptional corrections in the
positions accounted for by the residue-sum formulas. The examples expose
exactly the terms lost when a shifted sample leaves that range.

## Propagation and limits

Both false weakenings lie on these verified paths:

```text
left_residue_sum  → left_product  ┐
                                 ├→ bracket_zero → restricted_fourier
right_residue_sum → right_product ┘
→ EGEquations_concrete → EGEquations_ruijsenaars → exists_EGEquations_odd
```

The [path data](later_range_ablation_paths.json) comes from the current cached
graph, with its project source hashes verified. Only the residue-sum
weakenings have been refuted here. More general product formulas could require
additional residue terms, and the final theorem still holds on its stated
domain. Some other late restrictions are removable by symmetry or completion;
those belong in a separate redundancy category, not among counterexamples.

## Formal certificates

- [LeftProductRangeAblation.lean](LeftProductRangeAblation.lean)
- [RightProductRangeAblation.lean](RightProductRangeAblation.lean)

The certificates use a general `HypGamma` at the construction's \(n=3\)
periods, so they apply in particular to `ruijsenaarsHypGamma 3`.
Both passed Lean elaboration with exit code 0:

```sh
lake env lean docs/ablation/LeftProductRangeAblation.lean
lake env lean docs/ablation/RightProductRangeAblation.lean
```

The left certificate proves the escaped sample identity, the retained
hypotheses, the exact raw discrepancy, and its nonvanishing. It includes
explicit bridges identifying both expressions with the original theorem's
specialized left and right sides. The right certificate proves the sample-window
endpoint defect, the normalized and raw discrepancies, their nonvanishing,
and `original_right_residue_sum_false`, with bridges to the original statement.

The final axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or additional gamma axiom is used. The radical
expressions in this report simplify the exact symbolic defects proved in Lean.
The downstream paths describe existing proof dependencies; they are not
certificates that every downstream conclusion becomes false.

Sampled peak process-group RSS was 2.429 GiB for the left certificate and
2.438 GiB for the right certificate. Lean reported only linter warnings.
