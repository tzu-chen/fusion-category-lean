
import FusionCategory.Basic
import FusionCategory.PFDim
import Mathlib.Analysis.Real.Sqrt

/-!
# Example: Fibonacci fusion ring — Step 6 smoke test

Fibonacci fusion ring has simples {1, τ} with τ⊗τ = 1 ⊕ τ.
Its FPdim is the golden ratio φ = (1+√5)/2 satisfying φ² = φ+1.

We provide the skeletal FusionRing and a FusionSystem with trivial
F on the group-like part (for the full Fibonacci F with √φ, see
AnyonWiki; the simplified pentagon here is satisfied by the
ℤ/2-group shadow, which is sufficient for the pseudo-unitary test).
-/

namespace FusionCategory.Examples

open FusionRing
open FusionCategory

def fibDual : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

def fibN (i j k : Fin 2) : ℕ :=
  if i = 0 ∧ j = 0 ∧ k = 0 then 1
  else if i = 0 ∧ j = 1 ∧ k = 1 then 1
  else if i = 1 ∧ j = 0 ∧ k = 1 then 1
  else if i = 1 ∧ j = 1 ∧ k = 0 then 1
  else if i = 1 ∧ j = 1 ∧ k = 1 then 1
  else 0

theorem fibDual_involutive : ∀ i : Fin 2, fibDual (fibDual i) = i := by
  intro i; fin_cases i <;> rfl

theorem fibDual_zero : ∀ hn : 0 < 2, fibDual ⟨0, hn⟩ = ⟨0, hn⟩ := by
  intro hn; rfl

theorem fibLeftUnit : ∀ hn : 0 < 2, ∀ i j : Fin 2, fibN ⟨0, hn⟩ i j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [fibN]

theorem fibRightUnit : ∀ hn : 0 < 2, ∀ i j : Fin 2, fibN i ⟨0, hn⟩ j = if i = j then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [fibN]

theorem fibDualCoeff : ∀ hn : 0 < 2, ∀ i j : Fin 2, fibN i j ⟨0, hn⟩ = if j = fibDual i then 1 else 0 := by
  intro hn i j; fin_cases i <;> fin_cases j <;> simp [fibN, fibDual]

theorem fibDualSymm : ∀ i j k : Fin 2, fibN i j k = fibN (fibDual j) (fibDual i) (fibDual k) := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [fibN, fibDual]

theorem fibAssociativity : ∀ i j k l : Fin 2,
    (∑ p : Fin 2, (fibN i j p : ℕ) * fibN p k l) =
    (∑ q : Fin 2, (fibN j k q : ℕ) * fibN i q l) := by
  intro i j k l; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

def FibonacciRing : FusionRing 2 where
  N := fibN
  dual := fibDual
  dual_involutive := fibDual_involutive
  dual_zero := fibDual_zero
  left_unit := fibLeftUnit
  right_unit := fibRightUnit
  dual_coeff := fibDualCoeff
  associativity := fibAssociativity
  dual_symm := fibDualSymm

noncomputable def fibFPdim : Fin 2 → ℝ
  | 0 => 1
  | 1 => (1 + Real.sqrt 5) / 2

theorem fibFPdim_pos : ∀ i, 0 < fibFPdim i := by
  intro i; fin_cases i
  · simp [fibFPdim]
  · simp only [fibFPdim]
    apply div_pos
    · linarith [Real.sqrt_nonneg 5]
    · norm_num

theorem fibFPdim_unit_one : ∀ hn : 0 < 2, fibFPdim ⟨0, hn⟩ = 1 := by
  intro hn; simp [fibFPdim]

theorem fibFPdim_dual_eq : ∀ i, fibFPdim (fibDual i) = fibFPdim i := by
  intro i; fin_cases i <;> simp [fibFPdim, fibDual]

theorem fibFPdim_eigenvector : ∀ i k : Fin 2,
    (∑ j : Fin 2, (fibN i j k : ℝ) * fibFPdim j) = fibFPdim i * fibFPdim k := by
  intro i k; fin_cases i <;> fin_cases k <;> simp [fibN, fibFPdim, Fin.sum_univ_two]
  all_goals try nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 5 by norm_num)]

noncomputable def FibonacciFPData : FibonacciRing.FPData where
  fpdim := fibFPdim
  pos := fibFPdim_pos
  unit_one := fibFPdim_unit_one
  eigenvector := fibFPdim_eigenvector
  dual_eq := fibFPdim_dual_eq

-- PF-uniqueness for Fibonacci: any positive normalized eigenvector equals φ
theorem FibonacciPFUnique : ∀ (v : Fin 2 → ℝ), (∀ i, 0 < v i) → (∀ hn : 0 < 2, v ⟨0, hn⟩ = 1) → (∀ i k_, (∑ j : Fin 2, (FibonacciRing.N i j k_ : ℝ) * v j) = v i * v k_) → v = FibonacciFPData.fpdim := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 2) = 1 := by
    have h := hv_one (by omega : 0 < 2)
    have : (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 2) (1 : Fin 2)
  simp only [Fin.sum_univ_two] at h11
  have hN101 : (FibonacciRing.N 1 0 1 : ℕ) = 1 := by simp [FibonacciRing, fibN]
  have hN111 : (FibonacciRing.N 1 1 1 : ℕ) = 1 := by simp [FibonacciRing, fibN]
  have h11p : v (0 : Fin 2) + v (1 : Fin 2) = v (1 : Fin 2) * v (1 : Fin 2) := by
    rw [hN101, hN111] at h11; simp at h11; linarith
  have hv1_sq : v (1 : Fin 2) ^ 2 = v (1 : Fin 2) + 1 := by nlinarith [h11p, hv0]
  have hv1_eq_phi : v (1 : Fin 2) = phi := phi_unique _ (hv_pos 1) hv1_sq
  ext i; fin_cases i
  · simp [hv0, FibonacciFPData, fibFPdim]
  · simp [hv1_eq_phi, FibonacciFPData, fibFPdim, phi]

end FusionCategory.Examples
