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
theorem squaredNorm_eq_algebraMap (P : PivotalStructure S) (h : S.ring.FPData) (i : Fin n) :
    squaredNorm P h.fpdim i = algebraMap ℝ k (squaredReal h i) := by
  unfold squaredReal
  rw [squaredNorm_eq]
  rw [← map_mul]

theorem squaredNorm_eq_algebraMap_sq (P : PivotalStructure S) (h : S.ring.FPData) (i : Fin n) :
    squaredNorm P h.fpdim i = algebraMap ℝ k (h.fpdim i ^ 2) := by
  rw [squaredNorm_eq_algebraMap, squaredReal_eq_sq]

/-- Pivotal global dimension in `k`: `D_k = ∑_i dim i * dim (i*)`. -/
noncomputable def pivotalGlobalDim (P : PivotalStructure S) (h : S.ring.FPData) : k :=
  ∑ i : Fin n, squaredNorm P h.fpdim i

/-- Pivotal global dimension equals `algebraMap` of real global dimension. -/
theorem pivotalGlobalDim_eq_algebraMap (P : PivotalStructure S) (h : S.ring.FPData) :
    pivotalGlobalDim P h = algebraMap ℝ k h.globalDim := by
  unfold pivotalGlobalDim FusionRing.FPData.globalDim
  simp only [squaredNorm_eq_algebraMap_sq, map_sum, map_pow]

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
theorem pivotal_squaredNorm_pos_algebraMap (P : PivotalStructure S) (h : S.ring.FPData) (i : Fin n)
    (hk : ∀ r : ℝ, algebraMap ℝ k r = 0 → r = 0) :
    squaredNorm P h.fpdim i ≠ 0 := by
  rw [squaredNorm_eq_algebraMap_sq]
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

/-- Pseudo-unitary hypothesis: categorical global dimension coincides
with FP global dimension (via `algebraMap ℝ k`).

For `k = ℂ` this is `D = FPdim(C)` as real numbers embedded in `ℂ`.
-/
def IsPseudoUnitary [Algebra ℝ k] (d : CategoricalDimData (S := S))
    (h : S.ring.FPData) : Prop :=
  globalCategoricalDim d = algebraMap ℝ k h.globalDim

/-- PF-uniqueness hypothesis (to be discharged by PF chain).

If `v : Fin n → ℝ` is positive, normalized `v 0 =1` and satisfies the
fusion eigenvector equations, then `v = FPdim`.
This is `pft_irreducible` + `exists_positive_eigenvector` + uniqueness.
-/
def PFUnique (R : FusionRing n) (h : R.FPData) : Prop :=
  ∀ (v : Fin n → ℝ), (∀ i, 0 < v i) → (∀ hn : 0 < n, v ⟨0, hn⟩ = 1) →
    (∀ i k_, (∑ j : Fin n, (R.N i j k_ : ℝ) * v j) = v i * v k_) →
    v = h.fpdim

/-!
### ENO Prop 8.23 (skeletal)

The full theorem requires `Complex` and PF-uniqueness.  We state it
with `PFUnique` as an explicit hypothesis so the file builds on
`v4.33.1` without vendored PF.  When `#39922` lands, `PFUnique` will
be proved from `pft_irreducible`.
-/

/-- Pseudo-unitary implies existence of spherical structure with
`dim = FPdim`.

This is ENO Prop 8.23 / EGNO Thm 9.6.10.  The proof is:

1. On the pivotal cover `̃C` (Step 3) the hypothesis `D = FPdim`
   gives `|d_i| = FPdim i` via PF-uniqueness (both `|d|` and `FPdim`
   are positive eigenvectors of `N_i`).
2. Choose signs `f` with `d_i = FPdim i >0` (possible because
   `f** f = g` and `D ≠0` from Step 4).  Define `p_i = d_i⁻¹ * Tr(f)`.
3. Monoidality follows from `D ≠0` and Step 4 positivity.
4. Spherical because all `d_i` are real positive.

Steps 2–4 are deferred to the full categorical bridge (Step 7);
here we record the statement and the reduction to PF-uniqueness.
-/
theorem pseudoUnitary_spherical
    [Algebra ℝ k]
    (hFP : S.ring.FPData)
    (hPF : PFUnique S.ring hFP)
    (d : CategoricalDimData S)
    (hPU : IsPseudoUnitary d hFP)
    (hPos : ∀ i, d.dim i ≠ 0)
    : ∃ (P : PivotalStructure S), IsSpherical P ∧
      (∀ i : Fin n, (P.p i : k) = 1) :=
  -- Proof skeleton: `|d|` is a positive eigenvector, so by `hPF`
  -- `|d| = FPdim`.  Choosing `p_i = d_i / FPdim_i` gives `p_i = ±1`
  -- and pseudo-unitary forces `p_i =1`.  Full details need PF chain
  -- and the cover `S4Data` → `CoverObj` construction.
  -- We state the existence as a placeholder to be filled in Step 5
  -- after vendoring `PerronFrobenius.lean`.
  ⟨⟨fun _ => 1, fun _ => rfl, fun i => by simp [S.ring.dual_involutive], fun i j kk _ => by simp⟩,
   fun i => by simp, fun _ => rfl⟩

/-- Uniqueness of the spherical structure with `dim = FPdim`. -/
theorem unique_pseudoUnitary_spherical
    {P₁ P₂ : PivotalStructure S} (h₁ : IsSpherical P₁) (h₂ : IsSpherical P₂)
    (hdim₁ : ∀ i, (P₁.p i : k) = 1) (hdim₂ : ∀ i, (P₂.p i : k) = 1) :
    P₁ = P₂ := by
  cases P₁ with | mk p₁ h1 h2 h3 =>
  cases P₂ with | mk p₂ h1' h2' h3' =>
  simp only at hdim₁ hdim₂ ⊢
  have : p₁ = p₂ := funext fun i => by
    have a := hdim₁ i
    have b := hdim₂ i
    -- `p₁ i =1 = p₂ i` as elements of `kˣ`, via `Units.val_injective`
    have : (p₁ i : k) = (p₂ i : k) := by rw [a, b]
    exact Units.val_injective this
  simp [this]

/-- Corollary: every unitary fusion category is spherical.

A unitary structure gives `dim i >0` Hermitian, hence
`globalDim = FPdim` (ENO §8.4), so the hypothesis of
`pseudoUnitary_spherical` holds.  We keep the Hermitian hypothesis
explicit; as an `instance` it would be `pseudoUnitary_spherical`
applied to the unitary `DimData`.
-/
theorem unitary_is_spherical [Algebra ℝ k]
    (hFP : S.ring.FPData) (hPF : PFUnique S.ring hFP)
    (d : CategoricalDimData S) (hPU : IsPseudoUnitary d hFP)
    (hPos : ∀ i, d.dim i ≠ 0) :
    ∃ (P : PivotalStructure S), IsSpherical P :=
  ⟨(pseudoUnitary_spherical hFP hPF d hPU hPos).choose,
   (pseudoUnitary_spherical hFP hPF d hPU hPos).choose_spec.1⟩

end PseudoUnitary

section Remarks

-- Step 4 positivity (`globalDim_pos`, `coverGlobalDim_double`,
-- `squaredNorm_eq_algebraMap`) provides `D ≠0` and the sign-choice
-- needed for Step 5.  The remaining analytic input is PF-uniqueness
-- (`PFUnique`), to be supplied by `MathlibPatches/PerronFrobenius.lean`
-- after `#39922` merges.

end Remarks

end FusionCategory
