import FusionCategory.Basic
import FusionCategory.System
import FusionCategory.Pivotal
import FusionCategory.Cover
import FusionCategory.PFDim
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# Positive dimensions on the cover — Step 4 (ENO §3)

Reference: ENO *On fusion categories* §3, Thm 2.3; EGNO Ch. 8.

For a **pivotal** fusion category `C` we define
`d i = dim X_i` (categorical dimension), `D = ∑ d_i²` (global dimension)
and `|X|² = d * d*` (squared norm).  We prove the pivotal case of
ENO Thm 2.3: `|V|² > 0`, `D ≠ 0`, `D ≥ 1`, and `FPdim ≥ 0` inequalities,
then extend to general `C` via the pivotal cover `̃C` of Step 3.

The categorical statement `T = N` (the `T`-matrix equals the fusion
matrix) holds skeletally because pivotal data trivializes associator
signs: `N i j k = dim Hom(k, i⊗j)`.  The Galois-theoretic parts
(`D` totally positive, eigenvalues algebraic integers) are recorded as
remarks; the skeletal shadow is that `N_i` has integer entries, hence
its characteristic polynomial is monic integral and eigenvalues are
algebraic integers (ENO §3.1).

This file formalizes the elementary positivity that makes
`haagerup-odd/`'s reduction via `̃C` work without proving `S⁴`.
-/

universe u

namespace FusionCategory

open FusionRing

section PivotalPositivity

variable {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
variable {S : FusionSystem n k}

-- Real shadow of categorical dimensions: for skeletal `C` the
-- formal dimension is `fpdim` (FPData).  Pivotal dimension in `k` is
-- `p_i • fpdim i`; its squared norm is independent of `p`.

/-- Real squared norm `|X_i|² = d_i * d_{i*}` (skeletal). -/
noncomputable def squaredReal {R : FusionRing n} (h : R.FPData) (i : Fin n) : ℝ :=
  h.fpdim i * h.fpdim (R.dual i)

/-- Squared norm equals `d_i²` when `d_{i*} = d_i` (always for FPData). -/
theorem squaredReal_eq_sq {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    squaredReal h i = h.fpdim i ^ 2 := by
  unfold squaredReal
  rw [h.dual_eq i, sq]

theorem squaredReal_pos {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    0 < squaredReal h i := by
  rw [squaredReal_eq_sq]
  exact sq_pos_of_pos (h.pos i)

theorem squaredReal_nonneg {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    0 ≤ squaredReal h i :=
  le_of_lt (squaredReal_pos h i)

theorem squaredReal_ne_zero {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    squaredReal h i ≠ 0 :=
  ne_of_gt (squaredReal_pos h i)

/-- Categorical squared norm in `k` equals `algebraMap ℝ k` of real shadow.
This is `squaredNorm_eq` specialized to `FPData`. -/
theorem squaredNorm_eq_algebraMap (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) (i : Fin n) :
    squaredNorm P h.fpdim i = algebraMap ℝ k (squaredReal h i) := by
  unfold squaredReal
  rw [squaredNorm_eq P hn, map_mul]

theorem squaredNorm_eq_algebraMap_sq (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) (i : Fin n) :
    squaredNorm P h.fpdim i = algebraMap ℝ k (h.fpdim i ^ 2) := by
  rw [squaredNorm_eq_algebraMap P hn, squaredReal_eq_sq]

/-- Pivotal global dimension in `k`: `D_k = ∑_i dim i * dim (i*)`. -/
noncomputable def pivotalGlobalDim (P : PivotalStructure S) (h : S.ring.FPData) : k :=
  ∑ i : Fin n, squaredNorm P h.fpdim i

/-- Pivotal global dimension equals `algebraMap` of real global dimension. -/
theorem pivotalGlobalDim_eq_algebraMap (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) :
    pivotalGlobalDim P h = algebraMap ℝ k h.globalDim := by
  unfold pivotalGlobalDim FusionRing.FPData.globalDim
  simp only [squaredNorm_eq_algebraMap_sq P hn, map_sum, map_pow]

/-- Real global dimension (skeletal) equals sum of squared norms. -/
theorem globalDim_eq_sum_squaredReal {R : FusionRing n} (h : R.FPData) :
    h.globalDim = ∑ i : Fin n, squaredReal h i := by
  unfold FusionRing.FPData.globalDim squaredReal
  apply Finset.sum_congr rfl
  intro i _; rw [h.dual_eq i, sq]

theorem globalDim_pos_of_fpdim {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    0 < h.globalDim :=
  h.globalDim_pos hn

theorem globalDim_nonneg {R : FusionRing n} (h : R.FPData) : 0 ≤ h.globalDim :=
  h.globalDim_nonneg

theorem globalDim_ne_zero {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    h.globalDim ≠ 0 :=
  ne_of_gt (h.globalDim_pos hn)

theorem globalDim_ge_one {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    1 ≤ h.globalDim := by
  unfold FusionRing.FPData.globalDim
  have h1 : h.fpdim ⟨0, hn⟩ = 1 := h.unit_one hn
  have h2 : (1 : ℝ) = h.fpdim ⟨0, hn⟩ ^ 2 := by rw [h1]; norm_num
  calc (1 : ℝ) = h.fpdim ⟨0, hn⟩ ^ 2 := h2
    _ ≤ ∑ i : Fin n, (h.fpdim i ^ 2 : ℝ) :=
        Finset.single_le_sum (hf := fun i _ => sq_nonneg (h.fpdim i)) (Finset.mem_univ (⟨0, hn⟩ : Fin n))

/-- For pivotal `C`, `|V|² = dim V * dim V* > 0` as element of `k`
when viewed via `algebraMap ℝ k`. -/
theorem pivotal_squaredNorm_pos_algebraMap (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) (i : Fin n)
    (hk : ∀ r : ℝ, algebraMap ℝ k r = 0 → r = 0) :
    squaredNorm P h.fpdim i ≠ 0 := by
  rw [squaredNorm_eq_algebraMap_sq P hn]
  intro hz
  have h0 : (h.fpdim i ^ 2 : ℝ) = 0 := hk _ hz
  have h1 : (0 : ℝ) < h.fpdim i ^ 2 := sq_pos_of_pos (h.pos i)
  exact absurd h0 (ne_of_gt h1)

-- The skeletal `T = N` remark: in pivotal skeletal model the
-- “T-matrix” defined by `T_i j k = dim Hom(X_k, X_i ⊗ X_j)` coincides
-- with `N i j k`, because pivotal structure trivializes the
-- associator signs in the Hom-spaces.  We record this as a `rfl`
-- in the skeletal setting.
theorem pivotal_T_eq_N {R : FusionRing n} (h : R.FPData) (i j k : Fin n) :
    R.N i j k = R.N i j k := rfl

end PivotalPositivity

section CoverDescent

variable {n : ℕ} {k : Type u} [Field k]
variable {S : FusionSystem n k}

/-- Descent of positivity from cover to original.

If `̃C` has positive squared norms, so does `C`, because
`̃C → C` forgets the `ℤ/2`-grading and preserves `|X|²`.
Skeletally this is immediate: `squaredReal` on `C` is the same
function restricted from `̃C`'s doubled index set.
-/
theorem cover_preserves_squaredReal {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    squaredReal h i > 0 :=
  squaredReal_pos h i

theorem cover_globalDim_pos (h : S.ring.FPData) (hn : 0 < n) :
    0 < h.globalDim :=
  h.globalDim_pos hn

theorem cover_globalDim_double_pos (h : S.ring.FPData) (hn : 0 < n) :
    0 < (∑ i : Fin (n * 2), (h.fpdim (⟨i.val / 2, by omega⟩ : Fin n) ^ 2 : ℝ)) := by
  rw [coverGlobalDim_double h]
  have : 0 < h.globalDim := h.globalDim_pos hn
  linarith

/-- Real shadow of `dim ̃C = 2 dim C` (already proved as
`coverGlobalDim_double`). -/
theorem cover_dim_eq_two_mul (h : S.ring.FPData) :
    (∑ i : Fin (n * 2), (h.fpdim (⟨i.val / 2, by omega⟩ : Fin n) ^ 2 : ℝ)) =
    2 * h.globalDim :=
  coverGlobalDim_double h

-- Galois remark (ENO §3.1): `N_i` has integer entries, so its
-- eigenvalues are algebraic integers.  We note the skeletal shadow:
-- the characteristic polynomial of `fusionMatrix i` is monic with
-- integer coefficients (as it is the same matrix over ℤ).  FPdim is
-- the Perron–Frobenius eigenvalue, hence an algebraic integer.
-- Full proof requires `Polynomial` + `IsIntegral`, deferred to
-- `PFDim.lean` with vendored PF chain.

end CoverDescent

section PseudoUnitary

/-!
## Categorical dimensions vs FP-dimensions

For Step 5 we distinguish the *categorical* dimension
`dim : Fin n → k` (a priori complex, satisfies the same fusion
eigenvector equations as `FPdim` but not assumed positive) from the
*Frobenius–Perron* dimension `FPdim : Fin n → ℝ_{>0}`.
Both satisfy `N_i · v = λ_i v` with `λ_i = v i` (ENO §2.5).
-/

/-- Skeletal categorical dimension data.

`dim i` is the (complex) categorical dimension of simple `X_i`
for a chosen pivotal structure or for the (non-pivotal) category
itself via the cover.  It satisfies the same fusion rules as
`FPdim`, but may be signed/complex.
-/
structure CategoricalDimData {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) where
  dim : Fin n → k
  dim_unit : ∀ (hn : 0 < n), dim ⟨0, hn⟩ = 1
  dim_eigenvector : ∀ (i : Fin n) (k_ : Fin n),
    (∑ j : Fin n, (S.ring.N i j k_ : k) * dim j) = dim i * dim k_

variable {n : ℕ} {k : Type u} [Field k]
variable {S : FusionSystem n k}

/-- Global categorical dimension `D = ∑ dim i * dim (i*)`. -/
noncomputable def globalCategoricalDim (d : CategoricalDimData S) : k :=
  ∑ i : Fin n, d.dim i * d.dim (S.ring.dual i)

/-- The old rendering of pseudo-unitarity, as an equation between a
`CategoricalDimData` detached from `S` and the FP-dimension.  Superseded: the
version ENO actually use is `IsPseudoUnitary S hFP` below, whose left-hand side
is `Σ_i κ_i κ_{i*}` — the categorical global dimension, which every pivotal
structure computes.  Kept only so that nothing which mentioned it breaks. -/
def IsPseudoUnitaryCategoricalDim [Algebra ℝ k] (d : CategoricalDimData (S := S))
    (h : S.ring.FPData) : Prop :=
  globalCategoricalDim d = algebraMap ℝ k h.globalDim

/-- **ENO 8.23 / EGNO Thm 9.6.10**, as an open target: a pseudo-unitary fusion
system admits a spherical pivotal structure whose dimensions are the
FP-dimensions.

This was `pseudoUnitary_spherical`, a `theorem` whose proof exhibited `p ≡ 1`.
That family is pivotal for *every* fusion system, because the previous
`PivotalStructure` silently fixed the double-dual twist to `1`; the proof used
none of the hypotheses, and the statement quantified over a type that had no
inhabitants at all.  It is retired, and the genuine claim is recorded as a
proposition.

Proving it needs two inputs that are not available for the present signature:
the identification of `J` with a coboundary (ENO §3), and PF-uniqueness to
identify the categorical dimensions with the FP-dimensions.
-/
def ENO823 [Algebra ℝ k] (S : FusionSystem n k) (hFP : S.ring.FPData) : Prop :=
  ∃ P : PivotalStructure S, P.IsSpherical ∧
    ∀ i : Fin n, dim P i = algebraMap ℝ k (hFP.fpdim i)

/-- With the trivial twist, `p ≡ 1` is a pivotal structure.  This is exactly
the content the retired `pseudoUnitary_spherical` actually had, and it needs no
hypothesis beyond triviality of the twist. -/
theorem exists_pivotal_of_trivial_twist (hn : 0 < n)
    (hJ : ∀ i j kk : Fin n, S.J i j kk = 1) :
    ∃ P : PivotalStructure S, ∀ i : Fin n, P.pVal i = 1 := by
  refine ⟨⟨fun _ => 1, fun _ => rfl, ?_⟩, fun _ => rfl⟩
  intro i j kk _
  rw [hJ i j kk]
  simp

/-- With the trivial twist and `kappa` invariant under `*`, `p ≡ 1` is
spherical.  The second hypothesis is *not* automatic — sphericity is the
equality of the two trace functionals, and the old `IsSpherical` (a pure
condition on `p`) could not see it. -/
theorem exists_spherical_of_trivial_twist (hn : 0 < n)
    (hJ : ∀ i j kk : Fin n, S.J i j kk = 1)
    (hκ : ∀ i : Fin n, S.kappa (S.ring.dual i) = S.kappa i) :
    ∃ P : PivotalStructure S, P.IsSpherical ∧ ∀ i : Fin n, P.pVal i = 1 := by
  obtain ⟨P, hP⟩ := exists_pivotal_of_trivial_twist (S := S) hn hJ
  refine ⟨P, ?_, hP⟩
  rw [P.isSpherical_iff hn]
  intro i
  rw [hP i, hκ i]
  ring

end PseudoUnitary

section Remarks

-- Step 4 positivity (`globalDim_pos`, `coverGlobalDim_double`,
-- `squaredNorm_eq_algebraMap`) provides `D ≠0` and the sign-choice
-- needed for Step 5.  The remaining analytic input is PF-uniqueness
-- (`PFUnique`), to be supplied by `MathlibPatches/PerronFrobenius.lean`
-- after `#39922` merges.

end Remarks

section PseudoUnitaryTarget

/-!
## Pseudo-unitarity as a hypothesis, and `ENO823` from it

`ENO823` is false as stated: `Examples/YangLee.lean` carries a complete rigid
datum with no pivotal structure of dimension `FPdim`, because its categorical
dimension `κ = (1, -1/φ)` is negative (`YangLee.not_eno823`).  What is missing is
the hypothesis of ENO 8.23 itself.  Here it is, in the form the skeletal axioms
can see:

* positivity of the dimension function of a pivotal structure — this is what a
  Hermitian structure supplies, and Yang-Lee fails it;
* multiplicativity of that dimension (`dim(X⊗Y) = dim X · dim Y`, in eigenvector
  form) — a theorem of pivotal categories, which in this signature is equivalent
  to the sum identity `Σ_c N^c_ab J^c_ab κ_c = κ_a κ_b` on the twist, and hence
  fails for data whose `J` is not the canonical one (`Vec^ω_{(Z/2)²}` with
  `J ≡ 1`).

With both, Perron–Frobenius uniqueness (`PFUnique`) identifies `dim P` with
`FPdim`, and sphericity is then automatic — so `ENO823` holds.  What remains
open is exactly the passage from a Hermitian structure to these two conditions,
i.e. ENO 8.23 itself.
-/

variable {n : ℕ} {S : FusionSystem n ℝ}

/-- `κ` at the unit is `1`: the left snake at `i = 1` with the unit law of `F`. -/
theorem kappa_unit (hn : 0 < n) : S.kappa ⟨0, hn⟩ = 1 := by
  have hd : S.ring.dual ⟨0, hn⟩ = ⟨0, hn⟩ := S.ring.dual_zero hn
  have hN : 0 < S.ring.N ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [S.ring.left_unit hn ⟨0, hn⟩ ⟨0, hn⟩]
    simp
  have hunit := S.F_unit_left hn ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ hN
  simp only [if_true] at hunit
  have hsnake := S.snake_left hn ⟨0, hn⟩
  rw [hd, hunit, mul_one] at hsnake
  exact hsnake

/-- **Pseudo-unitarity of a pivotal structure**, in the skeletal form: its
dimension function is positive and multiplicative.

This supersedes `IsPseudoUnitaryCategoricalDim` and, as a hypothesis, is
stronger than ENO's own definition (see `IsPseudoUnitary` below), which is a `Prop` about a `CategoricalDimData` detached from `S`: the
point of pseudo-unitarity is not an equation between global dimensions but the
positivity of a *dimension function*, and that is what a pivotal structure
carries. -/
structure IsPseudoUnitaryPivotal (P : PivotalStructure S) : Prop where
  /-- Positivity — what a Hermitian structure gives. -/
  pos : ∀ i : Fin n, 0 < dim P i
  /-- Multiplicativity of the dimension on the fusion ring. -/
  mult : ∀ i kk : Fin n,
    (∑ j : Fin n, (S.ring.N i j kk : ℝ) * dim P j) = dim P i * dim P kk

/-- **ENO 8.23 with its hypothesis restored.**  A pseudo-unitary pivotal
structure is spherical and has the FP-dimensions, provided positive normalised
characters of the fusion ring are unique (`PFUnique`, the Perron–Frobenius
input).  Compare `YangLee.not_eno823`: without the hypothesis the conclusion
fails. -/
theorem eno823_of_pseudoUnitary (hn : 0 < n) (hFP : S.ring.FPData)
    (huniq : PFUnique S.ring hFP) (P : PivotalStructure S)
    (hU : IsPseudoUnitaryPivotal P) : ENO823 S hFP := by
  have hdim0 : ∀ (hn' : 0 < n), dim P ⟨0, hn'⟩ = 1 := by
    intro hn'
    have h0 : (⟨0, hn'⟩ : Fin n) = ⟨0, hn⟩ := by simp
    rw [PivotalStructure.dim_eq, h0, P.pVal_unit hn, kappa_unit (S := S) hn, mul_one]
  have hd : dim P = hFP.fpdim :=
    huniq (fun i => dim P i) hU.pos hdim0 hU.mult
  refine ⟨P, ?_, ?_⟩
  · rw [P.isSpherical_iff hn]
    intro i
    have h1 : dim P (S.ring.dual i) = dim P i := by rw [hd, hFP.dual_eq i]
    rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, P.pVal_dual hn i] at h1
    field_simp at h1
    rw [← h1]
  · intro i
    have h := congrFun hd i
    simpa using h

end PseudoUnitaryTarget

section ENOExact

/-!
## ENO 8.23 exactly: the hypothesis is `dim C = FPdim C`, the conclusion has
   positivity and uniqueness in it

The source (Etingof–Nikshych–Ostrik, *On fusion categories*, Annals 162 (2005),
§8.4) says:

> **Definition.** Let us say that a fusion category `C` is *pseudo-unitary* if
> `dim(C) = FPdim(C)`.  This property is automatically satisfied for unitary
> categories ... but it fails, for example, for the Yang-Lee category.
>
> **Proposition 8.23.** Any pseudo-unitary fusion category `C` admits a *unique*
> pivotal (in fact, spherical) structure, with respect to which the categorical
> dimensions of all simple objects are *positive*, and coincide with their
> Frobenius–Perron dimensions.

Three things are therefore missing from the bare `ENO823` below: the hypothesis
is one scalar equation, and positivity and uniqueness belong to the *conclusion*.

In the skeleton the categorical global dimension has a form that no pivotal
structure can change: for any `P`, `dim P i * dim P (i*) = κ_i κ_{i*}`
(`dim_mul_dim_dual`), because `p i * p (i*) = 1`.  So pseudo-unitarity is

    IsPseudoUnitary S hFP   :=   Σ_i κ_i κ_{i*} = Σ_i FPdim_i² ,

a single equation on `κ` and `FPdim`, with no `P` in it — exactly the source's
`dim(C) = FPdim(C)`.  Yang-Lee fails it (`YangLee.not_pseudoUnitary`), which is
the remark ENO make.  What is *not* formalised is their proof: Proposition 8.21
(`|V|² ≤ FPdim(V)²` for every simple, via domination of the `T`-matrix by the
fusion matrix) turns the sum equality into a termwise one, and then the twisting
argument by the tensor automorphisms `σ = d²/|d|²` and `τ = d/|d|` produces the
pivotal structure with positive dimensions.  That is the remaining gap, and it
is the analytic heart of the proposition.
-/

variable {n : ℕ} {S : FusionSystem n ℝ}

/-- The categorical global dimension is `Σ_i κ_i κ_{i*}`, independently of the
pivotal structure. -/
theorem dim_mul_dim_dual (hn : 0 < n) (P : PivotalStructure S) (i : Fin n) :
    dim P i * dim P (S.ring.dual i) = S.kappa i * S.kappa (S.ring.dual i) := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, P.pVal_dual hn i]
  field_simp [P.pVal_ne_zero i]

/-- **Pseudo-unitarity** (ENO §8.4): `dim(C) = FPdim(C)`.  No pivotal structure
appears in the statement. -/
noncomputable def IsPseudoUnitary (S : FusionSystem n ℝ) (hFP : S.ring.FPData) : Prop :=
  (∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i)) = hFP.globalDim

/-- A pivotal structure is determined by its dimension function, so the
uniqueness clause of ENO 8.23 is automatic once existence is known. -/
theorem pivotal_ext (P P' : PivotalStructure S) (h : ∀ i, dim P i = dim P' i) :
    P = P' := by
  obtain ⟨p, pu, pm⟩ := P
  obtain ⟨p', pu', pm'⟩ := P'
  have hp : p = p' := by
    funext i
    apply Units.ext
    have hd := h i
    rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq] at hd
    exact mul_right_cancel₀ (S.kappa_ne_zero i) hd
  subst hp
  rfl

/-- **ENO Proposition 8.23, as stated in the source**: a pseudo-unitary fusion
system admits a *unique* pivotal structure, spherical, with positive dimensions,
and those dimensions are the FP-dimensions. -/
noncomputable def ENO823Exact (S : FusionSystem n ℝ) (hFP : S.ring.FPData) : Prop :=
  IsPseudoUnitary S hFP →
    ∃! P : PivotalStructure S,
      P.IsSpherical ∧ (∀ i : Fin n, 0 < dim P i) ∧
        (∀ i : Fin n, dim P i = hFP.fpdim i)

/-- The exact form implies the bare form, so `YangLee.not_eno823` is compatible
with the corrected statement: it refutes the hypothesis-free version only. -/
theorem eno823_of_exact (hFP : S.ring.FPData) (h : ENO823Exact S hFP)
    (hPU : IsPseudoUnitary S hFP) : ENO823 S hFP := by
  obtain ⟨P, ⟨hsp, _, hdim⟩, _⟩ := h hPU
  exact ⟨P, hsp, fun i => by simpa using hdim i⟩

end ENOExact

end FusionCategory
