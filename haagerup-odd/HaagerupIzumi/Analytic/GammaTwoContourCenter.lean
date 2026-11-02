module

public import HaagerupIzumi.Analytic.GammaTwoContourLine
import all Mathlib.Data.Complex.Basic

/-!
# The separating-contour base case for the corrected two-gamma transform

A positive real part of `f+h` permits a separating line even when the
individual real parts of `f` and `h` are not positive. Complex centering of
that line reduces the corrected transform directly to the symmetric integral.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaTwoFourier

lemma separating_avoidsPoles (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h : ℂ)
    (σ : ℝ) (hf : 0 < f.re + σ) (hh : σ < h.re) : AvoidsPoles a b f h σ := by
  intro z hz heq
  rcases hz with hz | hz
  · have hp := GammaK4Contour.poleLattice_re_nonpos (lt_of_lt_of_le hb hba) hb hz
    change (f + z).re ≤ 0 at hp
    simp only [add_re, heq] at hp
    linarith
  · have hp := GammaK4Contour.rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
    rw [heq] at hp
    linarith

lemma crossedLeft_eq_empty_of_separating (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f : ℂ) (σ : ℝ) (hf : 0 < f.re + σ) : crossedLeft a b hb hba f σ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hσ⟩ := (mem_crossedLeft a b hb hba f σ z).mp hz
  have hp := GammaK4Contour.poleLattice_re_nonpos (lt_of_lt_of_le hb hba) hb hz
  change (f + z).re ≤ 0 at hp
  simp only [add_re] at hp
  linarith

lemma crossedRight_eq_empty_of_separating (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (h : ℂ) (σ : ℝ) (hh : σ < h.re) : crossedRight a b hb hba h σ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hσ⟩ := (mem_crossedRight a b hb hba h σ z).mp hz
  have hp := GammaK4Contour.rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
  linarith

/-- Base case of the continuation argument, requiring only positivity of the
sum of the real gamma parameters. -/
theorem correctedTransform_eq_symmetric (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ) (hsum : 0 < f.re + h.re)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    correctedTransform a b hb hba f h y =
      Complex.exp (Real.pi * (h - f) * y / ((a : ℂ) * b)) *
        symmetricTransform a b hb hba (midpoint f h) y := by
  let σ := (centerShift f h).re
  have hf : 0 < f.re + σ := by dsimp [σ]; rw [centerShift_re]; linarith
  have hh : σ < h.re := by dsimp [σ]; rw [centerShift_re]; linarith
  have hnp : f + h ∉ poleLattice a b :=
    not_mem_poleLattice_of_re_pos (lt_of_lt_of_le hb hba) hb (by simpa only [add_re] using hsum)
  have hline := (correctedTransform_line a b hb hba hirr f h y hc hnp σ
    (separating_avoidsPoles a b hb hba f h σ hf hh)).2
  rw [crossedLeft_eq_empty_of_separating a b hb hba f σ hf,
    crossedRight_eq_empty_of_separating a b hb hba h σ hh] at hline
  simp only [CorrectedContour.value, Finset.sum_empty, mul_zero, add_zero, sub_zero] at hline
  have ht := CorrectedContour.lineIntegral_comp_const_add (kernel a b hb hba f h y)
    (centerShift f h) 0
  simp only [zero_add] at ht
  rw [kernel_comp_center, CorrectedContour.lineIntegral_const_mul,
    lineIntegral_zero, transform_diag_eq_symmetricTransform] at ht
  apply mul_left_cancel₀ I_ne_zero
  calc
    _ = lineIntegral (kernel a b hb hba f h y) σ := hline.symm
    _ = _ := ht.symm
    _ = _ := by ring

lemma correctedTransform_eq_transform (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) (f h y : ℂ) (hf : 0 < f.re) (hh : 0 < h.re)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) :
    correctedTransform a b hb hba.le f h y = transform a b hb hba.le f h y := by
  rw [correctedTransform_eq_symmetric a b hb hba.le hirr f h y (by linarith) hc,
    transform_eq_symmetric a b hb hba f h y hf hh hc]

end HaagerupIzumi.GammaTwoFourier
