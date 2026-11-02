module

public import HaagerupIzumi.Analytic.GammaIdentities
import all Mathlib.Data.Complex.Basic

/-!
# Exponential algebra for the Fourier shift equations

Multiplication by a sine factor becomes a difference of the two half-period
shifts of the Fourier variable. These are pointwise identities, prior to
integration.
-/

@[expose] public section
noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

def fourierWeight (a b : ℝ) (y z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * y * z / ((a : ℂ) * b))

lemma fourierWeight_add_half {a b A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hab : a * b = A * B) (y z : ℂ) :
    fourierWeight a b (y + (A : ℂ) * I / 2) z =
      Complex.exp (Real.pi * I * z / B) * fourierWeight a b y z := by
  unfold fourierWeight
  rw [← Complex.exp_add]
  congr 1
  have hAC : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  rw [← Complex.ofReal_mul, hab, Complex.ofReal_mul]
  field_simp
  ring

lemma fourierWeight_sub_half {a b A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hab : a * b = A * B) (y z : ℂ) :
    fourierWeight a b (y - (A : ℂ) * I / 2) z =
      Complex.exp (-(Real.pi * I * z / B)) * fourierWeight a b y z := by
  unfold fourierWeight
  rw [← Complex.exp_add]
  congr 1
  have hAC : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  rw [← Complex.ofReal_mul, hab, Complex.ofReal_mul]
  field_simp
  ring

lemma I_mul_factor (B : ℝ) (z : ℂ) :
    I * factor B z = Complex.exp (Real.pi * I * z / B) -
      Complex.exp (-(Real.pi * I * z / B)) := by
  unfold factor
  rw [Complex.two_sin]
  have hp : (Real.pi * z / B) * I = Real.pi * I * z / B := by ring
  have hn : -(Real.pi * z / B) * I = -(Real.pi * I * z / B) := by ring
  rw [hp, hn, mul_left_comm I, I_mul_I]
  ring

lemma fourierWeight_factor_add {a b A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hab : a * b = A * B) (f y z : ℂ) :
    I * fourierWeight a b y z * factor B (f + z) =
      Complex.exp (Real.pi * I * f / B) * fourierWeight a b (y + (A : ℂ) * I / 2) z -
      Complex.exp (-(Real.pi * I * f / B)) * fourierWeight a b (y - (A : ℂ) * I / 2) z := by
  rw [mul_right_comm I, I_mul_factor, fourierWeight_add_half hA hB hab,
    fourierWeight_sub_half hA hB hab]
  rw [show Real.pi * I * (f + z) / B = Real.pi * I * f / B + Real.pi * I * z / B by ring,
    Complex.exp_add, neg_add, Complex.exp_add]
  ring

lemma fourierWeight_factor_sub {a b A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hab : a * b = A * B) (h y z : ℂ) :
    I * fourierWeight a b y z * factor B (h - z) =
      Complex.exp (Real.pi * I * h / B) * fourierWeight a b (y - (A : ℂ) * I / 2) z -
      Complex.exp (-(Real.pi * I * h / B)) * fourierWeight a b (y + (A : ℂ) * I / 2) z := by
  rw [mul_right_comm I, I_mul_factor, fourierWeight_add_half hA hB hab,
    fourierWeight_sub_half hA hB hab]
  rw [show Real.pi * I * (h - z) / B = Real.pi * I * h / B + -(Real.pi * I * z / B) by ring,
    Complex.exp_add, neg_add, neg_neg, Complex.exp_add]
  ring

end HaagerupIzumi.GammaContinuation
