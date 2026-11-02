module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4Line

/-! # The straight separating contour in the positive parameter tube -/

@[expose] public section
noncomputable section

open Complex Set MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma noPinch_of_straight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re) :
    K4NoPinch a b r s x := by
  obtain ⟨hx₀, hx₁⟩ := abs_lt.mp hV
  have hp : ∀ z : ℂ, 0 < z.re → z ∉ poleSet a b := fun z hz =>
    not_mem_poleLattice_of_re_pos ha hb hz
  refine ⟨hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_⟩ <;>
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, add_re, sub_re] <;>
    linarith

lemma leftPoles_re_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x z : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re)
    (hz : z ∈ leftPoles a b r s x) : z.re < 0 := by
  rcases hz with hz | hz
  · have h := poleLattice_re_nonpos ha hb hz
    simp only [add_re] at h
    linarith
  · have h := poleLattice_re_nonpos ha hb hz
    simp only [add_re] at h
    linarith [(abs_lt.mp hV).1]

lemma rightPoles_re_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x z : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re)
    (hz : z ∈ rightPoles a b r s x) : 0 < z.re := by
  rcases hz with hz | hz
  · exact hU.trans_le (rightFamily_re_ge ha hb hz)
  · have h := rightFamily_re_ge ha hb hz
    simp only [sub_re] at h
    linarith [(abs_lt.mp hV).2]

lemma avoidsPoles_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re) :
    AvoidsPoles a b r s x 0 := by
  intro z hz
  rcases hz with hz | hz
  · exact (leftPoles_re_neg ha hb hU hV hz).ne
  · exact (rightPoles_re_pos ha hb hU hV hz).ne'

lemma crossedLeft_zero_eq_empty {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) {r s x : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re) :
    crossedLeft a b hb hba r s x 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hz₀⟩ := (mem_crossedLeft a b hb hba r s x 0 z).mp hz
  exact (leftPoles_re_neg (hb.trans_le hba) hb hU hV hz).not_gt hz₀

lemma crossedRight_zero_eq_empty {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) {r s x : ℂ}
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re) :
    crossedRight a b hb hba r s x 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hz₀⟩ := (mem_crossedRight a b hb hba r s x 0 z).mp hz
  exact (rightPoles_re_pos (hb.trans_le hba) hb hU hV hz).not_gt hz₀

/-- The usual real integral whenever the imaginary axis separates all
left and right poles. -/
theorem K4_eq_integral_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) {r s x y : ℂ} (hconv : K4Conv a b r y)
    (hU : 0 < (k4U a b r s).re) (hV : |x.re| < (k4V a b r s).re) :
    (Real.sqrt (a * b) : ℂ) * K4 a b hb hba r s x y =
      ∫ t : ℝ, kernel a b hb hba r s x y (t * I) := by
  have ht := (K4_line a b hb hba hirr r s x y hconv
    (noPinch_of_straight (hb.trans_le hba) hb hU hV) 0
    (avoidsPoles_zero (hb.trans_le hba) hb hU hV)).2
  rw [crossedLeft_zero_eq_empty hb hba hU hV,
    crossedRight_zero_eq_empty hb hba hU hV] at ht
  simp only [CorrectedContour.value, Finset.sum_empty, mul_zero, add_zero,
    sub_zero, lineIntegral, ofReal_zero, zero_add, integral_mul_const] at ht
  apply mul_left_cancel₀ I_ne_zero
  linear_combination -ht

end HaagerupIzumi.GammaK4Contour
