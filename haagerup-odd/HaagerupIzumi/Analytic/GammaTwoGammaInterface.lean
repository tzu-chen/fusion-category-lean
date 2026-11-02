module

public import HaagerupIzumi.Analytic.GammaTwoEvaluation
import all Mathlib.Data.Complex.Basic

/-! # The concrete two-gamma evaluation in the hyperbolic-gamma interface -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaTwoFourier

def bssParameter (a b : ℝ) (f h α : ℂ) : ℂ :=
  I * (2 * α + h + f - a - b) / 2

lemma bssParameter_convergence (a b : ℝ) (f h α : ℂ)
    (hα : 0 < α.re) (hα' : α.re < ((a : ℂ) + b - h - f).re) :
    |(bssParameter a b f h α).im| < (a + b - f.re - h.re) / 2 := by
  simp only [bssParameter, div_ofNat_im, I_mul_im, sub_re, add_re, mul_re,
    re_ofNat, im_ofNat, ofReal_re, zero_mul, sub_zero] at *
  apply abs_lt.mpr
  constructor <;> linarith

lemma kernel_bssParameter (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h α : ℂ) :
    kernel a b hb hba f h (bssParameter a b f h α) =
      fun z => Complex.exp (Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
        gamma a b hb hba (f + z) * gamma a b hb hba (h - z) := by
  funext z
  unfold kernel bssParameter
  rw [show 2 * (Real.pi : ℂ) * (I * (2 * α + h + f - a - b) / 2) * z / ((a : ℂ) * b) =
    Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b) by ring]

lemma closedCandidate_bssParameter (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h α : ℂ) :
    I * closedCandidate a b hb hba f h (bssParameter a b f h α) =
      I * (Real.sqrt (a * b) : ℂ) *
        Complex.exp (Real.pi * I / (2 * a * b) * (h - f) * (2 * α + h + f - a - b)) *
        gamma a b hb hba α * gamma a b hb hba ((a : ℂ) + b - h - f - α) *
        gamma a b hb hba (f + h) := by
  have hI : I * bssParameter a b f h α = -(2 * α + h + f - a - b) / 2 := by
    unfold bssParameter
    rw [← mul_div_assoc, ← mul_assoc, I_mul_I]
    ring
  have hplus : ((a : ℂ) + b) / 2 - (f + h) / 2 + I * bssParameter a b f h α =
      (a : ℂ) + b - h - f - α := by rw [hI]; ring
  have hminus : ((a : ℂ) + b) / 2 - (f + h) / 2 - I * bssParameter a b f h α = α := by
    rw [hI]
    ring
  have hexp : (Real.pi : ℂ) * (h - f) * bssParameter a b f h α / ((a : ℂ) * b) =
      Real.pi * I / (2 * a * b) * (h - f) * (2 * α + h + f - a - b) := by
    unfold bssParameter
    ring
  unfold closedCandidate fourierCandidate fourierCandidateOf
  rw [hplus, hminus, hexp]
  ring

/-- The actual gamma satisfies the precise `HypGamma.two_gamma` field,
including arbitrary supplied simple residues and the finite crossed-pole set. -/
theorem two_gamma_explicit (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h α : ℂ) (σ : ℝ) (S : Finset ℂ) (ρ : ℂ → ℂ)
    (hα : 0 < α.re) (hα' : α.re < ((a : ℂ) + b - h - f).re) (hσh : σ < h.re)
    (hnp : ∀ r s r' s' : ℕ, -f - r * a - s * b ≠ h + r' * a + s' * b)
    (havoid : ∀ r s : ℕ, (-f - r * a - s * b).re ≠ σ)
    (hS : ∀ w, w ∈ S ↔ (∃ r s : ℕ, w = -f - r * a - s * b) ∧ σ < w.re)
    (hρ : ∀ w ∈ S, HasResidue
      (fun z => Complex.exp (Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
        gamma a b hb hba (f + z) * gamma a b hb hba (h - z)) w (ρ w)) :
    Integrable (fun t : ℝ =>
      Complex.exp (Real.pi * I * (σ + t * I) * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
        gamma a b hb hba (f + (σ + t * I)) * gamma a b hb hba (h - (σ + t * I))) ∧
      lineIntegral (fun z =>
        Complex.exp (Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
          gamma a b hb hba (f + z) * gamma a b hb hba (h - z)) σ +
        2 * Real.pi * I * ∑ w ∈ S, ρ w =
          I * (Real.sqrt (a * b) : ℂ) *
            Complex.exp (Real.pi * I / (2 * a * b) * (h - f) * (2 * α + h + f - a - b)) *
            gamma a b hb hba α * gamma a b hb hba ((a : ℂ) + b - h - f - α) *
            gamma a b hb hba (f + h) := by
  have hnp' : f + h ∉ poleLattice a b := by
    rintro ⟨r, s, hp⟩
    apply hnp r s 0 0
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linear_combination -hp
  have hσ : AvoidsPoles a b f h σ := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨r, s, rfl⟩ := (GammaK4Contour.leftFamily_mem_iff a b f z).mp hz
      exact havoid r s
    · exact ne_of_gt (hσh.trans_le
        (GammaK4Contour.rightFamily_re_ge (hb.trans_le hba) hb hz))
  have hSL : crossedLeft a b hb hba f σ = S := by
    ext w
    rw [mem_crossedLeft, hS, GammaK4Contour.leftFamily_mem_iff]
  have hSR : crossedRight a b hb hba h σ = ∅ :=
    crossedRight_eq_empty_of_separating a b hb hba h σ hσh
  have hc := bssParameter_convergence a b f h α hα hα'
  have ht := correctedTransform_line a b hb hba hirr f h (bssParameter a b f h α)
    hc hnp' σ hσ
  rw [correctedTransform_evaluation a b hb hba hirr f h _ hnp' hc,
    closedCandidate_bssParameter, hSL, hSR, kernel_bssParameter] at ht
  refine ⟨ht.1, ?_⟩
  have hsum : (∑ w ∈ S, residueValue
      (fun z => Complex.exp (Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
        gamma a b hb hba (f + z) * gamma a b hb hba (h - z)) w) = ∑ w ∈ S, ρ w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_eq (hρ w hw).hasResidueGen
  have he := ht.2
  unfold CorrectedContour.value at he
  simpa only [hsum, Finset.sum_empty, mul_zero, sub_zero] using he

end HaagerupIzumi.GammaTwoFourier
