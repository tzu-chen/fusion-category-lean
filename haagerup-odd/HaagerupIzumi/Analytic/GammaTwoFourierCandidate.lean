module

public import HaagerupIzumi.Analytic.GammaFourierCandidateQShift
import all Mathlib.Data.Complex.Basic

/-!
# The closed candidate for an asymmetric two-gamma transform

The candidate satisfies both gamma-parameter shift equations even when the
parameter sum has negative real part, provided that sum is not a pole.
-/

@[expose] public section
noncomputable section

open Complex
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

def closedCandidate (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) : ℂ :=
  Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) * (Real.sqrt (a * b) : ℂ) *
    gamma a b hb hba (f + h) * fourierCandidate a b hb hba ((f + h) / 2) y

lemma fourierCandidate_neg (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) :
    fourierCandidate a b hb hba q (-y) = fourierCandidate a b hb hba q y := by
  simp only [fourierCandidate, fourierCandidateOf, mul_neg,
    sub_neg_eq_add, mul_comm, ← sub_eq_add_neg]

lemma closedCandidate_swap_neg (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) :
    closedCandidate a b hb hba h f (-y) = closedCandidate a b hb hba f h y := by
  have he : (Real.pi : ℂ) * (f - h) * (-y) / ((a : ℂ) * b) =
      Real.pi * (h - f) * y / ((a : ℂ) * b) := by ring
  simp only [closedCandidate, he, fourierCandidate_neg, add_comm h f]

private lemma weight_shift_first {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (f h y : ℂ) :
    Complex.exp (Real.pi * (h - (f + b)) * y / ((a : ℂ) * b)) =
      Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        Complex.exp (-(Real.pi * y / a)) := by
  rw [← Complex.exp_add]
  congr 1
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp
  ring

private lemma coefficient_weight_plus {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (f h y : ℂ) :
    Complex.exp (Real.pi * I * f / a) *
        Complex.exp (Real.pi * (h - f) * (y + b * I / 2) / ((a : ℂ) * b)) =
      Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        Complex.exp (Real.pi * I * ((f + h) / 2) / a) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp
  ring

private lemma coefficient_weight_minus {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (f h y : ℂ) :
    Complex.exp (-(Real.pi * I * f / a)) *
        Complex.exp (Real.pi * (h - f) * (y - b * I / 2) / ((a : ℂ) * b)) =
      Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        Complex.exp (-(Real.pi * I * ((f + h) / 2) / a)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp
  ring

theorem closedCandidate_shift_first {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (f h y : ℂ) (hp : f + h ∉ poleLattice a b)
    (hconv : |y.im| < (a + b - f.re - h.re - b) / 2) :
    I * closedCandidate a b hb hba (f + b) h y =
      Complex.exp (Real.pi * I * f / a) * closedCandidate a b hb hba f h (y + b * I / 2) -
      Complex.exp (-(Real.pi * I * f / a)) * closedCandidate a b hb hba f h (y - b * I / 2) := by
  have ha := (hb.trans_le hba).ne'
  have hq : 2 * ((f + h) / 2) = f + h := by ring
  have hq' : (f + b + h) / 2 = (f + h) / 2 + (b : ℂ) / 2 := by ring
  have hq'' : f + b + h = 2 * ((f + h) / 2 + (b : ℂ) / 2) := by ring
  have heq := normalizedCandidate_q_shift_second_of_not_mem hb hba ((f + h) / 2) y
    (by simpa only [hq] using hp)
    (by simp only [div_ofNat_re, add_re]; linarith)
  rw [hq] at heq
  unfold closedCandidate
  rw [weight_shift_first ha hb.ne', hq', hq'']
  calc
    _ = Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) * (Real.sqrt (a * b) : ℂ) *
        (I * Complex.exp (-(Real.pi * y / a)) *
          (gamma a b hb hba (2 * ((f + h) / 2 + (b : ℂ) / 2)) *
            fourierCandidate a b hb hba ((f + h) / 2 + (b : ℂ) / 2) y)) := by ring
    _ = Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) * (Real.sqrt (a * b) : ℂ) *
        (Complex.exp (Real.pi * I * ((f + h) / 2) / a) *
          (gamma a b hb hba (f + h) * fourierCandidate a b hb hba ((f + h) / 2) (y + b * I / 2)) -
          Complex.exp (-(Real.pi * I * ((f + h) / 2) / a)) *
          (gamma a b hb hba (f + h) * fourierCandidate a b hb hba ((f + h) / 2) (y - b * I / 2))) := by
      rw [heq]
    _ = _ := by
      have hplus := coefficient_weight_plus ha hb.ne' f h y
      have hminus := coefficient_weight_minus ha hb.ne' f h y
      linear_combination
        -hplus * (Real.sqrt (a * b) : ℂ) * gamma a b hb hba (f + h) *
          fourierCandidate a b hb hba ((f + h) / 2) (y + b * I / 2) +
        hminus * (Real.sqrt (a * b) : ℂ) * gamma a b hb hba (f + h) *
          fourierCandidate a b hb hba ((f + h) / 2) (y - b * I / 2)

theorem closedCandidate_shift_second {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (f h y : ℂ) (hp : f + h ∉ poleLattice a b)
    (hconv : |y.im| < (a + b - f.re - h.re - b) / 2) :
    I * closedCandidate a b hb hba f (h + b) y =
      Complex.exp (Real.pi * I * h / a) * closedCandidate a b hb hba f h (y - b * I / 2) -
      Complex.exp (-(Real.pi * I * h / a)) * closedCandidate a b hb hba f h (y + b * I / 2) := by
  have heq := closedCandidate_shift_first hb hba h f (-y)
    (by simpa only [add_comm h f] using hp)
    (by simpa only [neg_im, abs_neg] using (show |y.im| < (a + b - h.re - f.re - b) / 2 by linarith))
  have hplus : -y + (b : ℂ) * I / 2 = -(y - b * I / 2) := by ring
  have hminus : -y - (b : ℂ) * I / 2 = -(y + b * I / 2) := by ring
  rw [hplus, hminus, closedCandidate_swap_neg, closedCandidate_swap_neg,
    closedCandidate_swap_neg] at heq
  exact heq

end HaagerupIzumi.GammaTwoFourier
