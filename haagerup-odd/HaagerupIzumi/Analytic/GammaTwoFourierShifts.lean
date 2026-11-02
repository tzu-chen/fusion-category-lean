module

public import HaagerupIzumi.Analytic.GammaTwoFourier
public import HaagerupIzumi.Analytic.GammaFourierShiftKernel
import all Mathlib.Data.Complex.Basic

/-!
# The two Fourier shift equations

The gamma shifts give two linear equations between half-period translates
of the Fourier integral. Contour transport then eliminates the shifted
gamma parameters.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

variable {a b A B : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hA : A ≠ 0) (hB : B ≠ 0) (hab : a * b = A * B)
    (hshift : ∀ v : ℂ, v ∉ poleLattice a b →
      gamma a b hb hba (v + A) = factor B v * gamma a b hb hba v)

include hA hB hab hshift

lemma kernel_shift_first (f h y z : ℂ) (hf : f + z ∉ poleLattice a b) :
    I * kernel a b hb hba (f + A) h y z =
      Complex.exp (Real.pi * I * f / B) * kernel a b hb hba f h (y + A * I / 2) z -
      Complex.exp (-(Real.pi * I * f / B)) * kernel a b hb hba f h (y - A * I / 2) z := by
  unfold kernel
  rw [show f + (A : ℂ) + z = (f + z) + A by ring, hshift _ hf]
  have hw := fourierWeight_factor_add hA hB hab f y z
  unfold fourierWeight at hw
  linear_combination hw * gamma a b hb hba (f + z) * gamma a b hb hba (h - z)

lemma kernel_shift_second (f h y z : ℂ) (hh : h - z ∉ poleLattice a b) :
    I * kernel a b hb hba f (h + A) y z =
      Complex.exp (Real.pi * I * h / B) * kernel a b hb hba f h (y - A * I / 2) z -
      Complex.exp (-(Real.pi * I * h / B)) * kernel a b hb hba f h (y + A * I / 2) z := by
  unfold kernel
  rw [show h + (A : ℂ) - z = (h - z) + A by ring, hshift _ hh]
  have hw := fourierWeight_factor_sub hA hB hab h y z
  unfold fourierWeight at hw
  linear_combination hw * gamma a b hb hba (f + z) * gamma a b hb hba (h - z)

omit hb hba hA hB hab hshift in
lemma half_shift_convergence (hApos : 0 < A) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re - A) / 2) :
    |(y + (A : ℂ) * I / 2).im| < (a + b - f.re - h.re) / 2 ∧
    |(y - (A : ℂ) * I / 2).im| < (a + b - f.re - h.re) / 2 := by
  simp only [add_im, sub_im, div_ofNat_im, mul_im, ofReal_re, I_im, mul_one,
    ofReal_im, I_re, mul_zero, add_zero]
  have hp := abs_add_le y.im (A / 2)
  have hm := abs_sub y.im (A / 2)
  rw [abs_of_pos (half_pos hApos)] at hp hm
  constructor <;> linarith

omit hA in
lemma transform_shift_first (hba' : b < a) (hApos : 0 < A) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hconv : |y.im| < (a + b - f.re - h.re - A) / 2) :
    I * transform a b hb hba (f + A) h y =
      Complex.exp (Real.pi * I * f / B) * transform a b hb hba f h (y + A * I / 2) -
      Complex.exp (-(Real.pi * I * f / B)) * transform a b hb hba f h (y - A * I / 2) := by
  have hconv' := half_shift_convergence hApos f h y hconv
  have hp := integrable_zero_line a b hb hba' f h _ hf hh hconv'.1
  have hm := integrable_zero_line a b hb hba' f h _ hf hh hconv'.2
  unfold transform
  rw [← integral_const_mul]
  calc
    _ = ∫ t : ℝ, Complex.exp (Real.pi * I * f / B) *
        kernel a b hb hba f h (y + A * I / 2) (t * I) -
        Complex.exp (-(Real.pi * I * f / B)) *
        kernel a b hb hba f h (y - A * I / 2) (t * I) := by
      apply integral_congr_ae
      filter_upwards with t
      exact kernel_shift_first hb hba hApos.ne' hB hab hshift f h y (t * I)
        (not_mem_poleLattice_of_re_pos (hb.trans hba') hb (by simpa using hf))
    _ = _ := by rw [integral_sub (hp.const_mul _) (hm.const_mul _),
      integral_const_mul, integral_const_mul]

omit hA in
lemma transform_shift_second (hba' : b < a) (hApos : 0 < A) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hconv : |y.im| < (a + b - f.re - h.re - A) / 2) :
    I * transform a b hb hba f (h + A) y =
      Complex.exp (Real.pi * I * h / B) * transform a b hb hba f h (y - A * I / 2) -
      Complex.exp (-(Real.pi * I * h / B)) * transform a b hb hba f h (y + A * I / 2) := by
  have hconv' := half_shift_convergence hApos f h y hconv
  have hp := integrable_zero_line a b hb hba' f h _ hf hh hconv'.1
  have hm := integrable_zero_line a b hb hba' f h _ hf hh hconv'.2
  unfold transform
  rw [← integral_const_mul]
  calc
    _ = ∫ t : ℝ, Complex.exp (Real.pi * I * h / B) *
        kernel a b hb hba f h (y - A * I / 2) (t * I) -
        Complex.exp (-(Real.pi * I * h / B)) *
        kernel a b hb hba f h (y + A * I / 2) (t * I) := by
      apply integral_congr_ae
      filter_upwards with t
      exact kernel_shift_second hb hba hApos.ne' hB hab hshift f h y (t * I)
        (not_mem_poleLattice_of_re_pos (hb.trans hba') hb (by simpa using hh))
    _ = _ := by rw [integral_sub (hm.const_mul _) (hp.const_mul _),
      integral_const_mul, integral_const_mul]

omit hA in
theorem transform_dual_shift (hba' : b < a) (hApos : 0 < A) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hconv : |y.im| < (a + b - f.re - h.re - A) / 2) :
    (Complex.exp (Real.pi * I * f / B) + Complex.exp (-2 * Real.pi * y / B) *
        Complex.exp (-(Real.pi * I * h / B))) *
        transform a b hb hba f h (y + A * I / 2) =
      (Complex.exp (-(Real.pi * I * f / B)) + Complex.exp (-2 * Real.pi * y / B) *
        Complex.exp (Real.pi * I * h / B)) *
        transform a b hb hba f h (y - A * I / 2) := by
  have h₁ := transform_shift_first hb hba hB hab hshift hba' hApos f h y hf hh hconv
  have h₂ := transform_shift_second hb hba hB hab hshift hba' hApos f h y hf hh hconv
  have ht := transform_shift_real a b hb hba' f h y A hApos hf hh hconv
  have hexp : -2 * (Real.pi : ℂ) * A * y / ((a : ℂ) * b) = -2 * Real.pi * y / B := by
    have hAC : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hApos.ne'
    have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
    rw [← Complex.ofReal_mul, hab, Complex.ofReal_mul]
    field_simp
  rw [hexp] at ht
  linear_combination -h₁ + Complex.exp (-2 * Real.pi * y / B) * h₂ + I * ht

end HaagerupIzumi.GammaTwoFourier
