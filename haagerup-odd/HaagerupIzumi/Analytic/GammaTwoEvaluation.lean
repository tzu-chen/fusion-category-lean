module

public import HaagerupIzumi.Analytic.GammaTwoShiftUniqueness
public import HaagerupIzumi.Analytic.GammaTwoContourCenter
public import HaagerupIzumi.Analytic.GammaTwoFourierCandidate
public import HaagerupIzumi.Analytic.GammaFourierEvaluation
import all Mathlib.Data.Complex.Basic

/-! # The full corrected two-gamma Fourier integral evaluation -/

@[expose] public section
noncomputable section

open Complex
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

lemma correctedTransform_satisfiesTwoShifts (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) :
    SatisfiesTwoShifts a b (correctedTransform a b hb hba) := by
  intro f h y hnp hc
  exact ⟨correctedTransform_shift_first a b hb hba hirr f h y hnp hc,
    correctedTransform_shift_second a b hb hba hirr f h y hnp hc⟩

lemma closedCandidate_satisfiesTwoShifts (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    SatisfiesTwoShifts a b (closedCandidate a b hb hba) := by
  intro f h y hnp hc
  exact ⟨closedCandidate_shift_first hb hba f h y hnp hc,
    closedCandidate_shift_second hb hba f h y hnp hc⟩

theorem correctedTransform_evaluation_positive_sum (a b : ℝ) (hb : 0 < b)
    (hba : b ≤ a) (hirr : Irrational (a / b)) (f h y : ℂ)
    (hsum : 0 < f.re + h.re) (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    correctedTransform a b hb hba f h y = closedCandidate a b hb hba f h y := by
  have hba' := periods_strictly_ordered a b hb hba hirr
  rw [correctedTransform_eq_symmetric a b hb hba hirr f h y hsum hc,
    symmetricTransform_evaluation hb hba' hirr
      (show 0 < (midpoint f h).re by rw [midpoint_re]; linarith)
      (show |y.im| < (a + b) / 2 - (midpoint f h).re by rw [midpoint_re]; linarith)]
  unfold closedCandidate midpoint
  rw [show 2 * ((f + h) / 2) = f + h by ring]
  ring

/-- The constructed hyperbolic gamma satisfies the two-gamma Fourier identity
throughout its full convergence domain, with the residue-corrected contour. -/
theorem correctedTransform_evaluation (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ) (hnp : f + h ∉ poleLattice a b)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    correctedTransform a b hb hba f h y = closedCandidate a b hb hba f h y := by
  exact eq_of_satisfiesTwoShifts hb (periods_strictly_ordered a b hb hba hirr)
    (correctedTransform a b hb hba) (closedCandidate a b hb hba)
    (correctedTransform_satisfiesTwoShifts a b hb hba hirr)
    (closedCandidate_satisfiesTwoShifts a b hb hba)
    (correctedTransform_evaluation_positive_sum a b hb hba hirr) f h y hnp hc

end HaagerupIzumi.GammaTwoFourier
