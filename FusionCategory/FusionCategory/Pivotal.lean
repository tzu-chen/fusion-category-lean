import FusionCategory.System

/-!
# Pivotal structures on skeletal fusion systems — Step 2

Reference: ENO §2.2, Bartlett 2009 Prop 5.7, EGNO Ch. 9.

A pivotal structure is `p : 𝟙 ≅ **` monoidal, equivalently a family
`p_i ∈ kˣ` with `p_{i*} = p_i⁻¹` and monoidality
`p_k • F = F • (p i * p j)` on each multiplicity factor.

We give the skeletal formulation: a pivotal structure is a collection
of invertible scalars twisting the F-symbols.
-/

universe u

namespace FusionCategory

/-- Pivotal structure on a skeletal fusion system.

In the skeletal model a pivotal structure is a monoidal natural
isomorphism `p : Id ≅ **` given by scalars `p_i ∈ kˣ` on simples.
The axioms are:

* `p_0 = 1`  (unit)
* `p_{i*} = p_i⁻¹`  (compatibility with duals)
* Monoidality: for all `i,j,k` with `N i j k >0`,
  `p_k = p_i * p_j` up to F-symbol twist.  In the multiplicity-free
  case this reduces to `p_k = p_i * p_j` when F is trivial; in
  general the F-twist is `F^{i j k*}…` (see Vercleyen §3).  We state
  the simplified grading-compatibility form, which is sufficient for
  the pseudo-unitary → spherical theorem and is equivalent to
  monoidality when the universal grading is considered (Step 3).
-/
structure PivotalStructure {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) where
  p : Fin n → kˣ
  p_unit : ∀ (hn : 0 < n), p ⟨0, hn⟩ = 1
  p_dual : ∀ (i : Fin n), p (S.ring.dual i) = (p i)⁻¹
  -- Grading-compatibility / monoidality (skeletal form).
  -- For all admissible fusions `N i j k > 0`, the pivotal scalars
  -- multiply: `p_k = p_i * p_j` in `k`.  The general F-twisted form
  -- is `F * p = p * F` and reduces to this when F is normalized.
  p_fusion : ∀ (i j k : Fin n), S.ring.N i j k > 0 → (p k : k) = (p i : k) * (p j : k)

namespace PivotalStructure

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
variable (P : PivotalStructure S)

/-- Underlying scalar at `i`. -/
def pVal (i : Fin n) : k := (P.p i : k)

theorem pVal_unit (hn : 0 < n) : P.pVal ⟨0, hn⟩ = 1 := by
  simp [pVal, P.p_unit hn]

theorem pVal_dual (i : Fin n) : P.pVal (S.ring.dual i) = (P.pVal i)⁻¹ := by
  unfold pVal
  have h := P.p_dual i
  have : ((P.p (S.ring.dual i) : kˣ) : k) = ((P.p i)⁻¹ : kˣ) := by rw [h]
  simpa using congrArg Units.val this

theorem pVal_inv (i : Fin n) : P.pVal i * (P.pVal (S.ring.dual i)) = 1 := by
  rw [P.pVal_dual i]
  exact mul_inv_cancel₀ (Units.ne_zero _)

end PivotalStructure

/-! ### Dimensions -/

/-- Categorical dimension associated to a pivotal structure.

Given a fusion ring with FP-dimension data `h : FPData`, the pivotal
dimension is `dim_p(i) = p_i * fpdim(i)` (embedded into `k` via the
canonical map `ℝ → k` when `k = ℂ`).  For `k = ℂ` we use the coercion
`ℝ → ℂ`.  In general we parametrize by a chosen formal dimension
vector `d : Fin n → k` (e.g. `h.fpdim` embedded).

When `d` is the FP-dimension, `dim_p(i)` is the usual quantum
dimension; it satisfies `dim_p(0)=1` and
`dim_p(i*) = dim_p(i)⁻¹ * |dim_p(i)|²` etc.  See ENO §2.2.
-/
noncomputable def pivotalDim {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) : k :=
  (P.p i : k) * algebraMap ℝ k (d i)

/-- Simplified dimension when the base is trivial (just `p_i`). -/
def pivotalDimSimple {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (i : Fin n) : k :=
  (P.p i : k)

theorem pivotalDimSimple_unit {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n) :
    pivotalDimSimple P (⟨0, hn⟩ : Fin n) = 1 := by
  simp [pivotalDimSimple, P.p_unit hn]

theorem pivotalDimSimple_dual {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (i : Fin n) :
    pivotalDimSimple P (S.ring.dual i) = (pivotalDimSimple P i)⁻¹ := by
  simp [pivotalDimSimple, P.pVal_dual]

/-- Squared norm `|V|² = dim(V) * dim(V*)` (ENO §2.2). -/
noncomputable def squaredNorm {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) : k :=
  pivotalDim P d i * pivotalDim P d (S.ring.dual i)

theorem squaredNorm_eq {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) :
    squaredNorm P d i = algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i)) := by
  unfold squaredNorm pivotalDim
  have h : (P.p (S.ring.dual i) : k) = ((P.p i)⁻¹ : k) := by
    have := P.p_dual i
    simpa [Units.val_inv_eq_inv_val] using congrArg Units.val this
  rw [h, mul_inv_cancel₀]
  · ring
  · exact Units.ne_zero _

/-! ### Spherical -/

/-- A pivotal structure is spherical when categorical dimensions are
invariant under duals: `dim_p(i) = dim_p(i*)` for all `i`.

In the skeletal model with `dim_p(i) = p_i * d_i` and `d_{i*}=d_i`
(FPdim duality), this is equivalent to `p_i = p_i⁻¹`, i.e.
`p_i² = 1`, i.e. `p_i = ±1` when `k = ℂ` and dimensions are real.
See ENO §2.2, EGNO Def. 4.7.1.

We give the `p`-form as definition and prove equivalence with the
dimension form when `d` is dual-invariant.
-/
def IsSpherical {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) : Prop :=
  ∀ i : Fin n, (P.p i : k) = (P.p (S.ring.dual i) : k)

theorem IsSpherical_iff_inv {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) :
    IsSpherical P ↔ ∀ i : Fin n, (P.p i : kˣ) = (P.p i)⁻¹ := by
  constructor
  · intro h i
    have hi := h i
    have hd := P.p_dual i
    rw [hd] at hi
    have hval : ((P.p i : kˣ) : k) = (((P.p i)⁻¹ : kˣ) : k) := hi
    exact Units.val_injective hval
  · intro h i
    have hi := h i
    have hd := P.p_dual i
    rw [hd]
    exact congrArg Units.val hi

theorem IsSpherical.p_sq_one {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} {P : PivotalStructure S} (h : IsSpherical P) (i : Fin n) :
    (P.p i : k) * (P.p i : k) = 1 := by
  have hi := (IsSpherical_iff_inv P).mp h i
  have : (P.p i : kˣ) * (P.p i : kˣ) = 1 := by rw [hi, inv_mul_cancel]
  exact congrArg Units.val this

theorem IsSpherical_of_p_sq_one {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S)
    (h : ∀ i, (P.p i : k) * (P.p i : k) = 1) : IsSpherical P := by
  rw [IsSpherical_iff_inv]
  intro i
  have hi := h i
  have inv_eq : (P.p i : kˣ)⁻¹ = P.p i := by
    apply Units.val_injective
    simp [Units.val_inv_eq_inv_val]
    have hpow : (P.p i : k) * (P.p i : k) = 1 := hi
    have hinv : (P.p i : k)⁻¹ = (P.p i : k) := by
      rw [eq_comm, inv_eq_of_mul_eq_one_right hpow]
    simpa [Units.val_inv_eq_inv_val] using hinv.symm
  exact inv_eq.symm

/-- Spherical ↔ dimensions equal when FPdim is dual-invariant and
non-vanishing. -/
theorem isSpherical_iff_dim_eq {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ)
    (hd : ∀ i, d (S.ring.dual i) = d i)
    (hd_ne : ∀ i, algebraMap ℝ k (d i) ≠ 0) :
    IsSpherical P ↔ ∀ i, pivotalDim P d i = pivotalDim P d (S.ring.dual i) := by
  constructor
  · intro h i
    unfold pivotalDim
    have hs := h i
    have hd_i := hd i
    rw [hd_i, hs]
  · intro h i
    have hi := h i
    unfold pivotalDim at hi
    have hd_i := hd i
    rw [hd_i] at hi
    have hmul : (P.p i : k) * algebraMap ℝ k (d i) = (P.p (S.ring.dual i) : k) * algebraMap ℝ k (d i) := hi
    have hcancel : (P.p i : k) = (P.p (S.ring.dual i) : k) := mul_right_cancel₀ (hd_ne i) hmul
    exact hcancel

end FusionCategory
