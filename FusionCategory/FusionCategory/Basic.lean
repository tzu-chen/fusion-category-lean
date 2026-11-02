
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.ConnectedComponent


/-!
# Fusion rings — skeletal fusion data (Step 1)

Reference: Etingof-Nikshych-Ostrik, *On fusion categories*, Annals 162 (2005),
§2-3; EGNO *Tensor Categories* Ch. 3-4; ENO §8.4.

A fusion ring is the Grothendieck ring of a fusion category, viewed
skeletally: a finite Z≥0-basis with unit `0`, involutive dual `*`, and
associative fusion coefficients `N_{i,j}^k ∈ N`.

This file is pure combinatorics — no analysis, no categories.  PF dimension
theory (the subject of `PFDim.lean`) builds on top of the matrix
`N_i` defined here.

Axiom budget: `[propext, Classical.choice, Quot.sound]` — matching
`haagerup-odd/`.
-/

open Matrix Finset BigOperators

/-! ## Fusion ring -/

/-- Skeletal fusion ring with `n` simple objects.

Conventions mirror `haagerup-odd/Coefficients.lean` and AnyonWiki:

* `0 : Fin n` is the unit object `1`.
* `dual i = i*` is the dual label.
* `N i j k = dim Hom(k, i ⊗ j)` — equivalently the structure constant of
  `i * j = ∑_k N i j k • k` in the Grothendieck ring.

The axioms below are the standard ones; see EGNO Def. 3.3.5 / ENO §2.2.
-/
structure FusionRing (n : ℕ) where
  N : Fin n → Fin n → Fin n → ℕ
  dual : Fin n → Fin n
  dual_involutive : ∀ i, dual (dual i) = i
  dual_zero : ∀ (hn : 0 < n), dual ⟨0, hn⟩ = ⟨0, hn⟩
  left_unit : ∀ (hn : 0 < n) (i j : Fin n), N ⟨0, hn⟩ i j = if i = j then 1 else 0
  right_unit : ∀ (hn : 0 < n) (i j : Fin n), N i ⟨0, hn⟩ j = if i = j then 1 else 0
  dual_coeff : ∀ (hn : 0 < n) (i j : Fin n),
    N i j ⟨0, hn⟩ = if j = dual i then 1 else 0
  associativity : ∀ (i j k l : Fin n),
    (∑ p : Fin n, (N i j p : ℕ) * N p k l) =
    (∑ q : Fin n, (N j k q : ℕ) * N i q l)
  dual_symm : ∀ i j k, N i j k = N (dual j) (dual i) (dual k)

namespace FusionRing

variable {n : ℕ} (R : FusionRing n)

/-! ### Fusion matrices -/

/-- The fusion matrix `N_i` with entries `(N_i)_{j,k} = N i j k` (as R).

Convention: row = `j`, column = `k`. -/
noncomputable def fusionMatrix (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => (R.N i j k : ℝ)

/-- Alias for `fusionMatrix`, matching the name in `PLAN.md`. -/
noncomputable abbrev FPdimMatrix (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  R.fusionMatrix i

@[simp]
theorem fusionMatrix_apply (i j k : Fin n) :
    R.fusionMatrix i j k = (R.N i j k : ℝ) := by
  simp [fusionMatrix, Matrix.of_apply]

theorem fusionMatrix_nonneg (i j k : Fin n) : 0 ≤ R.fusionMatrix i j k := by
  simp

theorem fusionMatrix_nonneg_entrywise (i : Fin n) :
    ∀ j k, 0 ≤ R.fusionMatrix i j k := fun _ _ => by simp

/-- The total fusion matrix `M = ∑_i N_i` controls connectivity of the
fusion ring: `R` is a fusion ring (in the usual sense) iff `M` is
irreducible, i.e. every simple appears in some tensor power. -/
noncomputable def totalMatrix : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin n, R.fusionMatrix i

theorem totalMatrix_nonneg (j k : Fin n) : 0 ≤ R.totalMatrix j k := by
  have h : R.totalMatrix j k = ∑ i : Fin n, R.fusionMatrix i j k := by
    simp only [totalMatrix, Matrix.sum_apply]
  rw [h]
  apply Finset.sum_nonneg
  intro i _
  exact R.fusionMatrix_nonneg i j k

theorem totalMatrix_nonneg_entrywise :
    ∀ j k, 0 ≤ R.totalMatrix j k := fun j k => R.totalMatrix_nonneg j k

/-! ### Duality helpers -/

theorem dual_dual (i : Fin n) : R.dual (R.dual i) = i :=
  R.dual_involutive i

theorem dual_injective : Function.Injective R.dual :=
  fun _ _ h => by
    have := congrArg R.dual h
    rwa [R.dual_involutive, R.dual_involutive] at this

theorem dual_surjective : Function.Surjective R.dual :=
  fun i => ⟨R.dual i, R.dual_involutive i⟩

theorem dual_bijective : Function.Bijective R.dual :=
  ⟨R.dual_injective, R.dual_surjective⟩

theorem dual_zero_eq (hn : 0 < n) :
    R.dual ⟨0, hn⟩ = ⟨0, hn⟩ :=
  R.dual_zero hn

/-! ### FP-dimension data

We do not assume the Perron-Frobenius theorem in this file (it is the
content of the Mathlib PRs `#39914`-`#39922` vendored in
`MathlibPatches/`).  Instead we define the *predicate* that a vector
is a PF eigenvector and package the existence as `FPData`.  Existence
for irreducible non-negative matrices will be proved in `PFDim.lean`
once the PF chain is available; for now the examples in
`Examples/` construct `FPData` by hand (`norm_num`).

This keeps `Basic.lean` buildable on `v4.33.1` (`0df444a3`) with no
vendored patches.
-/

/-- Predicate: `v` is a Perron-Frobenius eigenvector for the whole
family `N_i` with eigenvalues `d i`. -/
def IsPFEigenvector (d : Fin n → ℝ) (v : Fin n → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧
  (∀ i, 0 < v i) ∧
  (∀ (hn : 0 < n), v ⟨0, hn⟩ = 1) ∧
  (∀ i : Fin n, ∀ k : Fin n,
    (∑ j : Fin n, (R.N i j k : ℝ) * v j) = d i * v k)

/-- Equivalent `mulVec` form using transposed matrix orientation.

We use `Mᵀ` because `mulVec` sums over the column index: `(M *ᵥ v) k =
∑ j M k j * v j`.  Our `fusionMatrix` has `(j,k) = N i j k`, so
`(fusionMatrix i)ᵀ` has `(k,j) = N i j k` and satisfies `Mᵀ *ᵥ v = d·v`. -/
theorem isPFEigenvector_iff_mulVec (d : Fin n → ℝ) (v : Fin n → ℝ) :
    R.IsPFEigenvector d v ↔
      (∀ i, 0 < d i) ∧ (∀ i, 0 < v i) ∧ (∀ hn : 0 < n, v ⟨0, hn⟩ = 1) ∧
      (∀ i, (R.fusionMatrix i)ᵀ *ᵥ v = d i • v) := by
  constructor
  · intro ⟨hd, hv, h1, heig⟩
    refine ⟨hd, hv, h1, fun i => ?_⟩
    ext k
    simp only [mulVec, dotProduct, transpose_apply, fusionMatrix_apply, Pi.smul_apply, smul_eq_mul]
    exact heig i k
  · intro ⟨hd, hv, h1, heig⟩
    refine ⟨hd, hv, h1, fun i k => ?_⟩
    have h := congrFun (heig i) k
    simp only [mulVec, dotProduct, transpose_apply, fusionMatrix_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h

/-- Data witnessing existence of FP-dimensions.  In the presence of the
full PF theorem this is inhabited for every connected fusion ring; we
keep it as data so that `Basic.lean` needs no analysis. -/
structure FPData (R : FusionRing n) where
  fpdim : Fin n → ℝ
  pos : ∀ i, 0 < fpdim i
  unit_one : ∀ (hn : 0 < n), fpdim ⟨0, hn⟩ = 1
  eigenvector : ∀ (i : Fin n) (k : Fin n),
    (∑ j : Fin n, (R.N i j k : ℝ) * fpdim j) = fpdim i * fpdim k
  dual_eq : ∀ i, fpdim (R.dual i) = fpdim i

namespace FPData

variable {R : FusionRing n} (h : R.FPData)

/-- Global FP dimension `D = ∑_i d_i²`. -/
noncomputable def globalDim : ℝ :=
  ∑ i : Fin n, (h.fpdim i) ^ 2

theorem globalDim_pos (hn : 0 < n) : 0 < h.globalDim := by
  unfold globalDim
  apply Finset.sum_pos
  · intro i _; exact sq_pos_of_pos (h.pos i)
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem globalDim_nonneg : 0 ≤ h.globalDim := by
  unfold globalDim
  apply Finset.sum_nonneg
  intro i _; exact sq_nonneg _

theorem fpdim_dual (i : Fin n) : h.fpdim (R.dual i) = h.fpdim i :=
  h.dual_eq i

end FPData

/-! ### Simple sanity lemmas (no PF needed) -/

theorem left_unit_eq (hn : 0 < n) (i j : Fin n) :
    R.N ⟨0, hn⟩ i j = if i = j then 1 else 0 :=
  R.left_unit hn i j

theorem right_unit_eq (hn : 0 < n) (i j : Fin n) :
    R.N i ⟨0, hn⟩ j = if i = j then 1 else 0 :=
  R.right_unit hn i j

theorem dual_coeff_eq (hn : 0 < n) (i j : Fin n) :
    R.N i j ⟨0, hn⟩ = if j = R.dual i then 1 else 0 :=
  R.dual_coeff hn i j

theorem assoc_eq (i j k l : Fin n) :
    (∑ p : Fin n, (R.N i j p : ℕ) * R.N p k l) =
    (∑ q : Fin n, (R.N j k q : ℕ) * R.N i q l) :=
  R.associativity i j k l

/-- `fusionMatrix 0` is the identity when `n > 0`. -/
theorem fusionMatrix_zero (hn : 0 < n) :
    R.fusionMatrix ⟨0, hn⟩ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext j k
  simp only [fusionMatrix_apply, Matrix.one_apply]
  rw [R.left_unit hn j k]
  split
  · simp_all
  · simp_all

end FusionRing
