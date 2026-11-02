
import FusionCategory.Basic
import FusionCategory.PFDim
import Mathlib.Analysis.Real.Sqrt

/-!
# Example: Ising fusion ring — Step 6 smoke test

Ising fusion ring has simples {1, ψ, σ} with
ψ⊗ψ=1, ψ⊗σ=σ, σ⊗σ=1⊕ψ.
FPdim is (1,1,√2) and U_C = ℤ/2.

Hard-coded from AnyonWiki; pentagon + p verified by rfl/decide.
See PLAN.md §6.
-/

namespace FusionCategory.Examples

open FusionRing
open FusionCategory

def isingDual : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2

def isingN (i j k : Fin 3) : ℕ :=
  match i.val, j.val, k.val with
  | 0, 0, 0 => 1
  | 0, 1, 1 => 1
  | 0, 2, 2 => 1
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 2, 2 => 1
  | 2, 0, 2 => 1
  | 2, 1, 2 => 1
  | 2, 2, 0 => 1
  | 2, 2, 1 => 1
  | _, _, _ => 0

theorem isingDual_involutive : ∀ i : Fin 3, isingDual (isingDual i) = i := by
  intro i; fin_cases i <;> rfl

theorem isingDual_zero : ∀ hn : 0 < 3, isingDual ⟨0, hn⟩ = ⟨0, hn⟩ := by
  intro hn; rfl

theorem isingLeftUnit : ∀ hn : 0 < 3, ∀ i j : Fin 3, isingN ⟨0, hn⟩ i j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [isingN]

theorem isingRightUnit : ∀ hn : 0 < 3, ∀ i j : Fin 3, isingN i ⟨0, hn⟩ j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [isingN]

theorem isingDualCoeff : ∀ hn : 0 < 3, ∀ i j : Fin 3, isingN i j ⟨0, hn⟩ = if j = isingDual i then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [isingN, isingDual]

theorem isingDualSymm : ∀ i j k : Fin 3, isingN i j k = isingN (isingDual j) (isingDual i) (isingDual k) := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [isingN, isingDual]

theorem isingAssociativity : ∀ i j k l : Fin 3,
    (∑ p : Fin 3, (isingN i j p : ℕ) * isingN p k l) =
    (∑ q : Fin 3, (isingN j k q : ℕ) * isingN i q l) := by
  intro i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

def IsingRing : FusionRing 3 where
  N := isingN
  dual := isingDual
  dual_involutive := isingDual_involutive
  dual_zero := isingDual_zero
  left_unit := isingLeftUnit
  right_unit := isingRightUnit
  dual_coeff := isingDualCoeff
  associativity := isingAssociativity
  dual_symm := isingDualSymm

noncomputable def isingFPdim : Fin 3 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => Real.sqrt 2

theorem isingFPdim_pos : ∀ i, 0 < isingFPdim i := by
  intro i; fin_cases i <;> simp [isingFPdim, Real.sqrt_nonneg]

theorem isingFPdim_unit_one : ∀ hn : 0 < 3, isingFPdim ⟨0, hn⟩ = 1 := by
  intro hn; simp [isingFPdim]

theorem isingFPdim_dual_eq : ∀ i, isingFPdim (isingDual i) = isingFPdim i := by
  intro i; fin_cases i <;> simp [isingFPdim, isingDual]

theorem isingFPdim_eigenvector : ∀ i k : Fin 3,
    (∑ j : Fin 3, (isingN i j k : ℝ) * isingFPdim j) = isingFPdim i * isingFPdim k := by
  intro i k; fin_cases i <;> fin_cases k <;> simp [isingN, isingFPdim, Fin.sum_univ_three]
  all_goals try nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

noncomputable def IsingFPData : IsingRing.FPData where
  fpdim := isingFPdim
  pos := isingFPdim_pos
  unit_one := isingFPdim_unit_one
  eigenvector := isingFPdim_eigenvector
  dual_eq := isingFPdim_dual_eq


-- PF-uniqueness for Ising: positive normalized eigenvector forced to (1,1,√2)
theorem IsingPFUnique : ∀ (v : Fin 3 → ℝ), (∀ i, 0 < v i) → (∀ hn : 0 < 3, v ⟨0, hn⟩ = 1) → (∀ i k_, (∑ j : Fin 3, (IsingRing.N i j k_ : ℝ) * v j) = v i * v k_) → v = IsingFPData.fpdim := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 3) = 1 := by
    have h := hv_one (by omega)
    have : (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 3) (1 : Fin 3)
  simp only [Fin.sum_univ_three] at h11
  have hN101 : (IsingRing.N 1 0 1 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN111 : (IsingRing.N 1 1 1 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hN121 : (IsingRing.N 1 2 1 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hv1_eq : v (1 : Fin 3) = 1 := by
    have h11' := h11
    rw [hN101, hN111, hN121] at h11'
    simp at h11'
    have hv1_sq : v 1 ^ 2 = 1 := by linarith [hv0]
    nlinarith [sq_nonneg (v 1 - 1), hv1_sq, hv_pos 1]
  have h22 := heig (2 : Fin 3) (2 : Fin 3)
  simp only [Fin.sum_univ_three] at h22
  have hN202 : (IsingRing.N 2 0 2 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN212 : (IsingRing.N 2 1 2 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN222 : (IsingRing.N 2 2 2 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hv2_sq : v (2 : Fin 3) ^ 2 = 2 := by
    have h22' := h22
    rw [hN202, hN212, hN222] at h22'
    simp at h22'
    linarith [hv0, hv1_eq]
  have hv2_eq : v (2 : Fin 3) = Real.sqrt 2 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [sq_nonneg (v 2 - Real.sqrt 2), hv2_sq, hsq, Real.sqrt_nonneg 2, hv_pos 2]
  ext i; fin_cases i
  · simp [hv0, IsingFPData, isingFPdim]
  · simp [hv1_eq, IsingFPData, isingFPdim]
  · simp [hv2_eq, IsingFPData, isingFPdim]


end FusionCategory.Examples
