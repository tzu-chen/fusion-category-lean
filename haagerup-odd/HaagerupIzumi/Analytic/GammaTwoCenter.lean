module

public import HaagerupIzumi.Analytic.GammaTwoFourier
import all Mathlib.Data.Complex.Basic

/-! # Reduction of the asymmetric Fourier integral to its symmetric form -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

def midpoint (f h : ℂ) : ℂ := (f + h) / 2

def centerShift (f h : ℂ) : ℂ := (h - f) / 2

lemma midpoint_re (f h : ℂ) : (midpoint f h).re = (f.re + h.re) / 2 := by
  simp [midpoint]

lemma centerShift_re (f h : ℂ) : (centerShift f h).re = (h.re - f.re) / 2 := by
  simp [centerShift]

lemma midpoint_re_pos {f h : ℂ} (hf : 0 < f.re) (hh : 0 < h.re) :
    0 < (midpoint f h).re := by
  rw [midpoint_re]
  positivity

lemma midpoint_conv {a b : ℝ} {f h y : ℂ}
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    |y.im| < (a + b) / 2 - (midpoint f h).re := by
  rw [midpoint_re]
  linarith

lemma kernel_comp_center (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) :
    (fun z => kernel a b hb hba f h y (centerShift f h + z)) =
      fun z => Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        kernel a b hb hba (midpoint f h) (midpoint f h) y z := by
  funext z
  unfold kernel
  have h₁ : f + (centerShift f h + z) = midpoint f h + z := by
    unfold centerShift midpoint
    ring
  have h₂ : h - (centerShift f h + z) = midpoint f h - z := by
    unfold centerShift midpoint
    ring
  have he : 2 * (Real.pi : ℂ) * y * (centerShift f h + z) / ((a : ℂ) * b) =
      Real.pi * (h - f) * y / ((a : ℂ) * b) + 2 * Real.pi * y * z / ((a : ℂ) * b) := by
    unfold centerShift
    ring
  rw [h₁, h₂, he, Complex.exp_add]
  ring

lemma kernel_center_lines (a b : ℝ) (hb : 0 < b) (hba : b < a) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    lineIntegral (kernel a b hb hba.le f h y) (centerShift f h).re =
      lineIntegral (kernel a b hb hba.le f h y) 0 := by
  rcases lt_trichotomy 0 (centerShift f h).re with hpos | heq | hneg
  · exact (kernel_strip_integrals a b hb hba f h y hc 0 (centerShift f h).re hpos
      (by simpa using hf) (by rw [centerShift_re]; linarith)).2.2
  · rw [← heq]
  · exact (kernel_strip_integrals a b hb hba f h y hc (centerShift f h).re 0 hneg
      (by rw [centerShift_re]; linarith) hh).2.2.symm

/-- Complex translation of the contour gives the asymmetric transform from
its symmetric instance; the imaginary part of the translation causes no
additional pole crossings. -/
theorem transform_eq_symmetric (a b : ℝ) (hb : 0 < b) (hba : b < a) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    transform a b hb hba.le f h y =
      Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        symmetricTransform a b hb hba.le (midpoint f h) y := by
  have ht := CorrectedContour.lineIntegral_comp_const_add
    (kernel a b hb hba.le f h y) (centerShift f h) 0
  simp only [zero_add] at ht
  rw [kernel_comp_center, CorrectedContour.lineIntegral_const_mul,
    kernel_center_lines a b hb hba f h y hf hh hc,
    lineIntegral_zero, lineIntegral_zero, transform_diag_eq_symmetricTransform] at ht
  apply mul_right_cancel₀ I_ne_zero
  simpa only [mul_assoc] using ht.symm

end HaagerupIzumi.GammaTwoFourier
