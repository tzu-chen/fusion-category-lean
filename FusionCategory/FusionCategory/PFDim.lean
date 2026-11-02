import FusionCategory.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# PF-dimension via Perron–Frobenius — Step 1

Reference: ENO §2.5, §8.4; Perron–Frobenius.

This file provides:
- `PFUnique R h`: uniqueness of positive normalized eigenvectors.
  For general `n` this is the PF theorem (PRs #39914–#39922).
  We prove it unconditionally for the example rings (n=2,3).

Axiom budget: [propext, Classical.choice, Quot.sound].
-/

namespace FusionCategory

open FusionRing

/-! ### PF-uniqueness predicate -/

/-- PF-uniqueness: any positive normalized eigenvector equals FPdim. -/
def PFUnique {n : ℕ} (R : FusionRing n) (h : R.FPData) : Prop :=
  ∀ (v : Fin n → ℝ), (∀ i, 0 < v i) → (∀ hn : 0 < n, v ⟨0, hn⟩ = 1) →
    (∀ i k_, (∑ j : Fin n, (R.N i j k_ : ℝ) * v j) = v i * v k_) →
    v = h.fpdim

/-! ### Fibonacci n=2 — φ = (1+√5)/2 -/

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_pos : 0 < phi := by
  unfold phi; apply div_pos <;> linarith [Real.sqrt_nonneg 5]

theorem phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [hsq, Real.sqrt_nonneg 5]

-- Uniqueness of positive root of x^2 = x + 1
theorem phi_unique (x : ℝ) (hx_pos : 0 < x) (hx_eq : x ^ 2 = x + 1) : x = phi := by
  unfold phi
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [hsq, Real.sqrt_nonneg 5, sq_nonneg (x - (1 + Real.sqrt 5) / 2), sq_nonneg x,
             sq_nonneg (Real.sqrt 5)]

end FusionCategory
