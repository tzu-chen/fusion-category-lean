import FusionCategory.System

/-!
# Pivotal structures on skeletal fusion systems — Step 2
-/

universe u

namespace FusionCategory

structure PivotalStructure {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) where
  p : Fin n → kˣ
  p_unit : ∀ (hn : 0 < n), p ⟨0, hn⟩ = 1
  p_dual : ∀ (i : Fin n), p (S.ring.dual i) = (p i)⁻¹
  p_fusion : ∀ (i j kk : Fin n), S.ring.N i j kk > 0 → (p kk : k) = (p i : k) * (p j : k)

def pVal {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : k := (P.p i : k)

theorem pVal_unit {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (hn : 0 < n) : pVal P ⟨0, hn⟩ = 1 := by
  simp [pVal, P.p_unit hn]

theorem pVal_dual {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : pVal P (S.ring.dual i) = (pVal P i)⁻¹ := by
  simp only [pVal, P.p_dual i, Units.val_inv_eq_inv_val]

theorem pVal_inv {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : pVal P i * (pVal P (S.ring.dual i)) = 1 := by
  rw [pVal_dual P i]
  exact mul_inv_cancel₀ (Units.ne_zero _)

noncomputable def pivotalDim {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) : k :=
  (P.p i : k) * algebraMap ℝ k (d i)

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
  simp only [pivotalDimSimple, P.p_dual i, Units.val_inv_eq_inv_val]

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
  rw [h]
  have h2 : (P.p i : k) * ((P.p i : k)⁻¹ : k) = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  calc (P.p i : k) * algebraMap ℝ k (d i) * (((P.p i : k)⁻¹ : k) * algebraMap ℝ k (d (S.ring.dual i)))
      = ((P.p i : k) * ((P.p i : k)⁻¹ : k)) * (algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i))) := by ring
    _ = 1 * (algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i))) := by rw [h2]
    _ = algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i)) := by ring

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

theorem IsSpherical_p_sq_one {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} {P : PivotalStructure S} (h : IsSpherical P) (i : Fin n) :
    (P.p i : k) * (P.p i : k) = 1 := by
  have hi : (P.p i : kˣ) = (P.p i : kˣ)⁻¹ := (IsSpherical_iff_inv P).mp h i
  have h1 : (P.p i : kˣ) * (P.p i : kˣ)⁻¹ = 1 := mul_inv_cancel _
  rw [←hi] at h1
  exact congrArg Units.val h1

end FusionCategory
