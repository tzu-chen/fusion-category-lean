import FusionCategory.Basic
import FusionCategory.PFDim
import FusionCategory.PseudoUnitary

/-!
# Example: Ostrik test — rank 3 fusion ring K(1,0,1)

X² = 1 ⊕ X ⊕ Y,  X⊗Y = X,  Y² = 1  — valid fusion ring with FPdim (1,2,1),
globalDim 6, cover 12.  See PLAN §6.
-/

namespace FusionCategory.Examples

open FusionRing
open FusionCategory

def k2210Dual : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2

def k2210N (i j k : Fin 3) : ℕ :=
  match i.val, j.val, k.val with
  | 0, 0, 0 => 1
  | 0, 1, 1 => 1
  | 0, 2, 2 => 1
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 1, 2, 1 => 1
  | 2, 0, 2 => 1
  | 2, 1, 1 => 1
  | 2, 2, 0 => 1
  | _, _, _ => 0

theorem k2210Dual_involutive : ∀ i : Fin 3, k2210Dual (k2210Dual i) = i := by
  intro i; fin_cases i <;> rfl

theorem k2210Dual_zero : ∀ hn : 0 < 3, k2210Dual ⟨0, hn⟩ = ⟨0, hn⟩ := by
  intro hn; rfl

theorem k2210LeftUnit : ∀ hn : 0 < 3, ∀ i j : Fin 3, k2210N ⟨0, hn⟩ i j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [k2210N]

theorem k2210RightUnit : ∀ hn : 0 < 3, ∀ i j : Fin 3, k2210N i ⟨0, hn⟩ j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [k2210N]

theorem k2210DualCoeff : ∀ hn : 0 < 3, ∀ i j : Fin 3, k2210N i j ⟨0, hn⟩ = if j = k2210Dual i then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [k2210N, k2210Dual]

theorem k2210DualSymm : ∀ i j k : Fin 3, k2210N i j k = k2210N (k2210Dual j) (k2210Dual i) (k2210Dual k) := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [k2210N, k2210Dual]

theorem k2210Associativity : ∀ i j k l : Fin 3,
    (∑ p : Fin 3, (k2210N i j p : ℕ) * k2210N p k l) =
    (∑ q : Fin 3, (k2210N j k q : ℕ) * k2210N i q l) := by
  intro i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

def K2210Ring : FusionRing 3 where
  N := k2210N
  dual := k2210Dual
  dual_involutive := k2210Dual_involutive
  dual_zero := k2210Dual_zero
  left_unit := k2210LeftUnit
  right_unit := k2210RightUnit
  dual_coeff := k2210DualCoeff
  associativity := k2210Associativity
  dual_symm := k2210DualSymm

def k2210FPdim : Fin 3 → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 1

theorem k2210FPdim_pos : ∀ i, 0 < k2210FPdim i := by
  intro i; fin_cases i <;> simp [k2210FPdim]

theorem k2210FPdim_unit_one : ∀ hn : 0 < 3, k2210FPdim ⟨0, hn⟩ = 1 := by
  intro hn; simp [k2210FPdim]

theorem k2210FPdim_dual_eq : ∀ i, k2210FPdim (k2210Dual i) = k2210FPdim i := by
  intro i; fin_cases i <;> simp [k2210FPdim, k2210Dual]

theorem k2210FPdim_eigenvector : ∀ i k : Fin 3,
    (∑ j : Fin 3, (k2210N i j k : ℝ) * k2210FPdim j) = k2210FPdim i * k2210FPdim k := by
  intro i k; fin_cases i <;> fin_cases k <;> simp [k2210N, k2210FPdim, Fin.sum_univ_three] <;> ring

def K2210FPData : K2210Ring.FPData where
  fpdim := k2210FPdim
  pos := k2210FPdim_pos
  unit_one := k2210FPdim_unit_one
  eigenvector := k2210FPdim_eigenvector
  dual_eq := k2210FPdim_dual_eq

theorem K2210_has_FPData : Nonempty K2210Ring.FPData := ⟨K2210FPData⟩

theorem K2210_globalDim : K2210FPData.globalDim = 6 := by
  unfold FusionRing.FPData.globalDim
  simp only [K2210FPData, k2210FPdim, Fin.sum_univ_three]
  norm_num

theorem K2210_globalDim_pos : 0 < K2210FPData.globalDim := by
  rw [K2210_globalDim]; norm_num

theorem K2210_cover_globalDim :
    (∑ i : Fin (3 * 2), (K2210FPData.fpdim (⟨i.val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ)) = 12 := by
  -- Fin (3*2) = Fin 6 definitionally, but simp needs explicit Fin 6 form
  change (∑ i : Fin 6, (K2210FPData.fpdim (⟨i.val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ)) = 12
  simp only [K2210FPData, k2210FPdim, Fin.sum_univ_six]
  norm_num
-- PF-uniqueness for K2210: positive normalized eigenvector forced to (1,2,1)
theorem K2210PFUnique : ∀ (v : Fin 3 → ℝ), (∀ i, 0 < v i) → (∀ hn : 0 < 3, v ⟨0, hn⟩ = 1) → (∀ i k_, (∑ j : Fin 3, (K2210Ring.N i j k_ : ℝ) * v j) = v i * v k_) → v = K2210FPData.fpdim := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 3) = 1 := by
    have h := hv_one (by omega)
    have : (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 3) (1 : Fin 3)
  simp only [Fin.sum_univ_three] at h11
  have hN101 : (K2210Ring.N 1 0 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN111 : (K2210Ring.N 1 1 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN121 : (K2210Ring.N 1 2 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have h12 := heig (1 : Fin 3) (2 : Fin 3)
  simp only [Fin.sum_univ_three] at h12
  have hN102 : (K2210Ring.N 1 0 2 : ℕ) = 0 := by simp [K2210Ring, k2210N]
  have hN112 : (K2210Ring.N 1 1 2 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN122 : (K2210Ring.N 1 2 2 : ℕ) = 0 := by simp [K2210Ring, k2210N]
  have hv2_eq : v (2 : Fin 3) = 1 := by
    have h12' := h12
    rw [hN102, hN112, hN122] at h12'
    simp at h12'
    have hmul : v 1 * (v 2 - 1) = 0 := by nlinarith
    have hor : v 1 = 0 ∨ v 2 - 1 = 0 := mul_eq_zero.mp hmul
    cases hor with
    | inl h => exact absurd h (ne_of_gt (hv_pos 1))
    | inr h => linarith
  have hv1_eq : v (1 : Fin 3) = 2 := by
    have h11' := h11
    rw [hN101, hN111, hN121] at h11'
    simp at h11'
    rw [hv0, hv2_eq] at h11'
    have h_eq : v 1 * v 1 - v 1 - 2 = 0 := by linarith
    have h_factor : (v 1 - 2) * (v 1 + 1) = 0 := by nlinarith [sq_nonneg (v 1)]
    have hor : v 1 - 2 = 0 ∨ v 1 + 1 = 0 := mul_eq_zero.mp h_factor
    cases hor with
    | inl h => linarith
    | inr h => linarith [hv_pos 1]
  ext i; fin_cases i
  · simp [hv0, K2210FPData, k2210FPdim]
  · simp [hv1_eq, K2210FPData, k2210FPdim]
  · simp [hv2_eq, K2210FPData, k2210FPdim]

end FusionCategory.Examples
