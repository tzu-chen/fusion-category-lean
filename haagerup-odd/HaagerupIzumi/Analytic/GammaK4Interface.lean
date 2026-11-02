module

public import HaagerupIzumi.Analytic.GammaK4Even
public import HaagerupIzumi.Analytic.GammaK4Swap
import all Mathlib.Data.Complex.Basic

/-! # The concrete four-gamma contour in the interface's explicit pole notation -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma leftPoles_mem_explicit (a b : ℝ) (r s x z : ℂ) :
    z ∈ leftPoles a b r s x ↔
      (∃ m n : ℕ, z = -k4U a b r s - (m : ℂ) * a - (n : ℂ) * b) ∨
      (∃ m n : ℕ, z = -k4V a b r s - x - (m : ℂ) * a - (n : ℂ) * b) := by
  simp only [leftPoles, Set.mem_union, leftFamily_mem_iff, neg_add, sub_eq_add_neg, add_assoc]

lemma rightPoles_mem_explicit (a b : ℝ) (r s x z : ℂ) :
    z ∈ rightPoles a b r s x ↔
      (∃ m n : ℕ, z = k4U a b r s + (m : ℂ) * a + (n : ℂ) * b) ∨
      (∃ m n : ℕ, z = k4V a b r s - x + (m : ℂ) * a + (n : ℂ) * b) := by
  simp only [rightPoles, Set.mem_union, rightFamily_mem_iff]

/-- The concrete K4 satisfies the precise line-characterization field of the
hyperbolic-gamma interface, including arbitrary supplied residue functions
and finite sets specified by their candidate-pole membership. -/
theorem K4_line_explicit (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ) (σ : ℝ)
    (SL SR : Finset ℂ) (ρL ρR : ℂ → ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (hL₁ : ∀ m n : ℕ, (-k4U a b r s - m * a - n * b).re ≠ σ)
    (hL₂ : ∀ m n : ℕ, (-k4V a b r s - x - m * a - n * b).re ≠ σ)
    (hR₁ : ∀ m n : ℕ, (k4U a b r s + m * a + n * b).re ≠ σ)
    (hR₂ : ∀ m n : ℕ, (k4V a b r s - x + m * a + n * b).re ≠ σ)
    (hSL : ∀ w, w ∈ SL ↔
      ((∃ m n : ℕ, w = -k4U a b r s - m * a - n * b) ∨
       (∃ m n : ℕ, w = -k4V a b r s - x - m * a - n * b)) ∧ σ < w.re)
    (hSR : ∀ w, w ∈ SR ↔
      ((∃ m n : ℕ, w = k4U a b r s + m * a + n * b) ∨
       (∃ m n : ℕ, w = k4V a b r s - x + m * a + n * b)) ∧ w.re < σ)
    (hρL : ∀ w ∈ SL, HasResidueGen (k4Integrand (gamma a b hb hba) a b r s x y) w (ρL w))
    (hρR : ∀ w ∈ SR, HasResidueGen (k4Integrand (gamma a b hb hba) a b r s x y) w (ρR w)) :
    Integrable (fun t : ℝ => k4Integrand (gamma a b hb hba) a b r s x y (σ + t * I)) ∧
    lineIntegral (k4Integrand (gamma a b hb hba) a b r s x y) σ +
      2 * Real.pi * I * ∑ w ∈ SL, ρL w - 2 * Real.pi * I * ∑ w ∈ SR, ρR w =
        I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba r s x y := by
  have hσ : AvoidsPoles a b r s x σ := by
    intro w hw
    rcases hw with hw | hw
    · rcases (leftPoles_mem_explicit a b r s x w).mp hw with
        ⟨m, n, rfl⟩ | ⟨m, n, rfl⟩
      · exact hL₁ m n
      · exact hL₂ m n
    · rcases (rightPoles_mem_explicit a b r s x w).mp hw with
        ⟨m, n, rfl⟩ | ⟨m, n, rfl⟩
      · exact hR₁ m n
      · exact hR₂ m n
  have hSL' : crossedLeft a b hb hba r s x σ = SL := by
    ext w
    rw [mem_crossedLeft, hSL, leftPoles_mem_explicit]
  have hSR' : crossedRight a b hb hba r s x σ = SR := by
    ext w
    rw [mem_crossedRight, hSR, rightPoles_mem_explicit]
  have h := K4_line a b hb hba hirr r s x y hconv hnp σ hσ
  rw [hSL', hSR'] at h
  refine ⟨h.1, ?_⟩
  have hLsum : (∑ w ∈ SL, residueValue (kernel a b hb hba r s x y) w) =
      ∑ w ∈ SL, ρL w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_eq (hρL w hw)
  have hRsum : (∑ w ∈ SR, residueValue (kernel a b hb hba r s x y) w) =
      ∑ w ∈ SR, ρR w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_eq (hρR w hw)
  have hv := h.2
  unfold CorrectedContour.value at hv
  rw [hLsum, hRsum] at hv
  exact hv

end HaagerupIzumi.GammaK4Contour
