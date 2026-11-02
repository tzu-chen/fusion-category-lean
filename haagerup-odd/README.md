# HaagerupIzumi — Lean 4 formalization of the odd-order Evans–Gannon theorem

This standalone Lake project contains only the odd-order development. It was
extracted from the `lean/` directory of <https://github.com/tzu-chen/haagerup>
at commit `b4b618f`, and its `HaagerupIzumi` modules are byte-identical to that
commit. Commit hashes below refer to that repository.

Lean `v4.33.1`, Mathlib tag `v4.33.1` (commit `0df444a3`). The odd-order
Evans–Gannon theorem is unconditional: the hyperbolic gamma function and all
required integral identities are constructed and proved.

`ruijsenaarsHypGamma n hn` supplies the complete `HypGamma` interface from
its explicit regularized integral. `EGEquations_ruijsenaars` verifies the
resulting concrete coefficient data, and `exists_EGEquations_odd n hodd`
requires only oddness of `n`. The initial conditional development was
checkpointed in `0daf48c`; see [PLAN.md](PLAN.md) for the completed proof plan.

## Layout

| Path | Content |
|---|---|
| `HaagerupIzumi.lean` | Umbrella module and default Lake target |
| `HaagerupIzumi/*.lean`, `HaagerupIzumi/Analytic/` | The development: 115 modules, about 24,000 lines |
| `AxiomAudit.lean` | Prints the axioms of the main results |
| [`PLAN.md`](PLAN.md) | The completed proof plan, retained for its order and mathematical choices |
| [`docs/`](docs/README.md) | Declaration dependency graph, proof flowchart, and ablation experiments |

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get              # download prebuilt Mathlib
lake build                      # build the project modules
lake env lean AxiomAudit.lean   # print the axioms of the main results
```

`lean-toolchain` pins Lean and `lake-manifest.json` pins Mathlib and its
dependencies. Without the first step, Lake builds Mathlib from source.

The build gives linter warnings only. The final axiom audit for the constructor
and both main theorems reports exactly `[propext, Classical.choice, Quot.sound]`;
there are no `sorry`s or added axioms.

## Main statement

`HaagerupIzumi.exists_EGEquations_odd` (in
`Analytic/GammaConstruction.lean`) proves that every odd natural number has
complex coefficient data satisfying all Evans–Gannon equations. Its only
mathematical premise is `Odd n`; the necessary nonzero instance follows
from oddness.

`HaagerupIzumi.EGEquations_ruijsenaars` proves those equations for the actual
`ruijsenaarsCoeffData n hn hodd`, constructed from the samples
`W a = -sgn(a) F(a)/√d` of the proved gamma function. The general theorem
`Concrete.EGEquations_concrete` in `Analytic/Cubics.lean` remains available
for any object satisfying the `HypGamma` interface; `GammaConstruction`
supplies that object without assuming special-function properties.

The proof follows the expanded manuscript `hi_infinitude_expanded.tex`, which is
not included here, through Chapter 9 and stops there: the reconstruction theorem
of Chapter 10 and the categorical conclusions are not formalized. Section, lemma,
and chapter numbers in this README and in the Lean comments refer to that
manuscript.

## The algebraic half (`CoeffData`)

The structure `CoeffData n K` packages the abstract data used by the
algebraic parts of the proof: a field `K`, `δ` with `δ^2 = n δ + 1`, and
coefficients `W : ZMod n → K` with `W 0 = -1`, `W a ≠ 0`, and
`W a * W (-a) = δ` for `a ≠ 0`. Everything below is proved for arbitrary
`n ≠ 0` and, where stated, `CharZero K` or `K = ℂ`.

| Module | Content (section of the expanded proof) |
|---|---|
| `Coefficients` | `B`, `A = B/τ`, uniform formula, order-three and transpose-like symmetries, axis values, linear identities (3.4–3.8), column symmetries |
| `Residuals` | residuals `Q`, `C`, `𝒞 = τ³ C`, swap symmetry, two-product lemma (5.1) |
| `Quartic` | the quartic residual is a contraction of cubic and quadratic residuals (10.1) |
| `Factorization` | balanced triples, `S`, `P`, their permutation/translation invariance, factorization of `𝒞` with and without corrections (5.7, 5.8) |
| `Boundary` | the boundary cubics `g = 0`, `h = 0`, `h = -g`, `g = h = 0` (Lemma 5.4, Part B) |
| `Balanced` | full match and collision values of `δ²S − τP` (Lemma 5.4, Steps A3–A4) |
| `Degenerate` | every degenerate cubic vanishes (Lemma 5.4) |
| `Interpolation` | vanishing Fourier block lemma on `ZMod N` over `ℂ` (Lemma 2.7), via `ZMod.dft` |
| `Reflection` | reflection by matrix inversion (Lemma 9.3), with explicit inverses of both sides |
| `FourierReduction` | Lemma 6.1: the Fourier transform of `𝒞_{g,h}(·,l)` through `û_{-g}` and the two product transforms |
| `Completion` | descent maps, induction in the ordered range (Prop. 9.1), the normal-form combinatorics (Lemma 9.2), all cubics (Prop. 9.4), and `EGEquations_of` |

`CoeffData.EGEquations_of` says: if all quadratic residuals vanish (`Q = 0`)
and the restricted Fourier vanishing `RestrictedFourier` holds, then the
matrix `A` satisfies all four families of Evans–Gannon equations.

## The analytic half (`Concrete`)

| Module | Content |
|---|---|
| `Analytic/Residue` | residue calculus on rectangles from Mathlib's Cauchy–Goursat theorem: `HasResidue`, generalized residues `HasResidueGen` (poles of order ≤ 2), the rectangle residue theorem, and the strip version `strip_residues(_gen)` with exponential decay |
| `Analytic/HypGamma` | the interface `HypGamma ω₁ ω₂` (see below) and elementary consequences |
| `Analytic/Periods` | `d`, `δ`, `ω₁`, `ω₂` and their arithmetic (`ω₁ω₂ = ω₁ + ω₂`, `ω₁ − ω₂ = n`, rational independence used for pole bookkeeping) |
| `Analytic/Sampling` | `F(z) = 1/γ(ω₂ + z)`, Lemma 3.2, the samples `W`, and `toCoeffData` |
| `Analytic/Contour` | Proposition 4.1: sample rule (Lemma 3.9 for positive labels), the kernel `K_h`, the difference identity, residues, decay, the strip and two-gamma applications, `column_fourier_sum` |
| `Analytic/ColumnFourier` | Lemma 4.3 and `Q = 0` (Proposition 4.4) |
| `Analytic/Windows` | Lemma 3.9 in all cases: `tz_pos`, `tz_neg_nonneg`, `tz_neg_neg`, periodicity `tz_add_n` |
| `Analytic/Products` | the two-ratio kernel `K2'`, Lemma 6.2, its residues and decay, `ε`-choice for the lines, residues `ρJ1`, `ρJ2`, translation lemmas for line integrals |
| `Analytic/LeftProduct` | Proposition 6.3 (1) with (8.4): `left_product` |
| `Analytic/RightProduct` | Proposition 6.3 (2) with (8.10): `right_product` (crossed families, double poles when `h = l`, window sample corrections, the two surviving residues) |
| `Analytic/NegColumn` | Lemma 8.1: `neg_column` |
| `Analytic/Restricted` | no-pinch conditions, Euler/shift/evenness chain for the left kernels, the Γ-factor bookkeeping and the four coefficient identities (`term1`–`term4`), and Proposition 8.2 `bracket_zero` |
| `Analytic/Cubics` | the restricted frequency set (`exists_freq`), `restricted_fourier`, and `EGEquations_concrete` |

### The proved interface `HypGamma`

The generic analytic development is organized around `HypGamma ω₁ ω₂`.
Its `HypGammaCore` parent contains the local properties and growth estimate;
`HypGamma` adds the integral identities. The concrete constructor proves
every field:

* position of poles and zeros (`poleSet`, `zeroSet`), holomorphy off the
  poles, nonvanishing off the zeros, the two shift identities, reflection;
* simple poles with residues `residue w`, and the residue
  `√(ω₁ω₂)/(2π)` at the origin (equal to `√Ω/(2π)` for the specialized
  periods);
* positivity on `(0, Ω)` and reality on the real axis;
* the growth of ratios `γ(z + c)/γ(z)` along vertical lines (Lemma 2.4);
* the two-gamma integral formula (2.17) along a vertical line, with the
  crossed left poles added back (`two_gamma`);
* the four-gamma kernel `K₄(r, s, x, y)` of Chapter 7 with: its value
  through a vertical line with crossed poles added back (`K4_line`),
  evenness `K₄(r,s,x,y) = K₄(r,s,−x,−y)`, the shift identity (7.7), the
  Euler transformation (Lemma 7.3), and the four-term identity (Lemma 7.4)
  at the parameters `R = g/2`, `X = (n+g)/2 + l`, `Y = (n+g)/2 + h`.

The four-term field explicitly requires both `ω₁−ω₂ = n` and
`ω₁ω₂ = ω₁+ω₂`. The simple-pole property is intended for irrational period
ratios, as in the specialized construction.

The concrete contour definition proves the line, evenness, swap, and
four-term fields directly. The two-gamma formula holds on its full
residue-corrected domain. Fourier insertion and parameter continuation prove
the full Euler transformation, including coincident poles of the same
orientation.

### Construction modules

The following results concern the explicit BSS-normalized integral and do
not assume a `HypGamma` object:

| Modules | Checked results |
|---|---|
| `GammaIntegral`, `GammaHolomorphic` | Absolute convergence, removable endpoint regularization, differentiation under the integral, and holomorphy on `0 < Re z < ω₁+ω₂` |
| `GammaStrip` | Reflection, midpoint normalization, period symmetry, conjugation, and positivity on the real strip |
| `GammaElementary`, `GammaNormalization`, `GammaShift` | Cotangent integral, Frullani normalization integral, and both shift identities on their strip overlaps |
| `GammaModulus`, `GammaCosine`, `GammaModulusUniform`, `GammaGrowth` | Exact cosine-defect integral, uniform logarithmic modulus estimate, and exact-rate ratio bounds within compact substrips |
| `GammaContinuation`, `GammaIdentities` | Explicit finite-product continuation, global holomorphy, both shifts, reflection, exact zeros, and reality |
| `GammaResidueZero`, `GammaPoleResidues` | Values at both periods, residue normalization at zero, and nonzero simple residues at every pole for irrational period ratios |
| `GammaSineGrowth`, `GammaGlobalGrowth` | Exact-rate ratio bounds on arbitrary bounded vertical strips |
| `GammaConcrete`, `GammaCore` | The actual specialized gamma function and the complete `ruijsenaarsCore` constructor |
| `ResidueAlgebra` | Unique intrinsic residues, linearity, and corrected-contour additivity for poles of order at most two |
| `GammaLocalFactors`, `GammaKernelRegularity` | Regularity of translated and reflected gamma factors; measurability and parameter regularity of the concrete kernel |
| `GammaKernelBounds`, `GammaKernelDecay`, `GammaK4UniformBounds`, `GammaTwoDecay` | Uniform exponential bounds for the two- and four-gamma kernels |
| `GammaK4Contour`, `GammaK4Residues`, `GammaK4Line`, `GammaK4Even`, `GammaK4Swap`, `GammaK4Interface` | Concrete corrected four-gamma contour and the exact line/symmetry identities |
| `ContourAffine`, `ContourLinearity`, `GammaFourTerm*`, `GammaK4LinearRelations`, `GammaK4FourTerm*` | Affine transport, finite contour linearity, and the complete four-term identity |
| `DominatedHolomorphic`, `GammaFourier*`, `GammaPeriodUniqueness`, `GammaStripPeriodicity`, `GammaSech` | Parameter holomorphy, dual Fourier shifts, uniqueness from local incommensurable periods, and the normalized symmetric two-gamma evaluation |
| `GammaTwoFourier`, `GammaTwoFourierShifts`, `GammaTwoCenter`, `GammaTwoContour*` | Asymmetric transform, corrected contours and residues, line independence, and reduction to the symmetric integral for positive parameter sum |
| `GammaTwoFourierCandidate`, `GammaTwoShiftUniqueness`, `GammaTwoEvaluation`, `GammaTwoGammaInterface` | Finite backward-shift extension and the full corrected two-gamma interface |
| `FourierInsertion`, `GammaFourierInsertion`, `GammaFourierDuality`, `GammaK4StraightLine`, `GammaK4Duality`, `GammaK4EulerSmall` | Absolutely integrable Fourier insertion, Fubini, the straight separating contour, duality, and the initial Euler identity |
| `Parametric*`, `MovingPole*`, `GammaMovingPole*`, `GammaK4MovingGeometry`, `GammaK4LocalCorrection`, `GammaK4Parameter*` | Holomorphic parameter integrals and fixed contours around moving, possibly merged, pole clusters |
| `ConvexMinusCountable`, `GammaK4ScalingDomain`, `GammaK4Euler`, `GammaK4EulerInterface` | Connected scaling domain, analytic continuation, and the full Euler identity |
| `GammaFull`, `GammaOdd`, `GammaConstruction` | Assembly of the complete interface and the unconditional odd-order Evans–Gannon theorem |

`GammaTwoDecay` is proved and imported by the umbrella module, but the main
theorem does not depend on it.

## What is not formalized

* The Evans–Gannon reconstruction theorem (Chapter 10) and the categorical
  conclusions.
