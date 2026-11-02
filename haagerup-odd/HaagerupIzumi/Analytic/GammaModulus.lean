module

public import HaagerupIzumi.Analytic.GammaStrip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import all Mathlib.Data.Complex.Basic

/-!
# The real part of the gamma integral

The oscillatory remainder is the cosine transform of the already integrable
real-axis kernel. This isolates the universal cosine-defect integral needed
for the exact vertical growth rate, without requiring phase asymptotics.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace HaagerupIzumi.GammaIntegral

/-- The universal, nonnegative cosine defect. Its value at the endpoint is
irrelevant to the integral. -/
def cosineDefect (y t : ℝ) : ℝ := (1 - Real.cos (2 * y * t)) / t ^ 2

def cosineMass (y : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), cosineDefect y t

def modulusSlope (ω₁ ω₂ x : ℝ) : ℝ := (2 * x - (ω₁ + ω₂)) / (2 * ω₁ * ω₂)

def cosineRemainder (ω₁ ω₂ x y : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.cos (2 * y * t) * realIntegrand ω₁ ω₂ x t

/-- A finite error constant, independent of the imaginary coordinate. -/
def modulusError (ω₁ ω₂ x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), |realIntegrand ω₁ ω₂ x t|

lemma cosineDefect_nonneg (y t : ℝ) : 0 ≤ cosineDefect y t := by
  unfold cosineDefect
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)

lemma cosineDefect_eq_sinc {t : ℝ} (ht : t ≠ 0) (y : ℝ) :
    cosineDefect y t = 2 * y ^ 2 * Real.sinc (y * t) ^ 2 := by
  by_cases hy : y = 0
  · simp [cosineDefect, hy]
  · rw [cosineDefect, show 2 * y * t = 2 * (y * t) by ring,
      Real.cos_two_mul_eq_one_sub, Real.sinc_of_ne_zero (mul_ne_zero hy ht)]
    field_simp
    ring

lemma cosineDefect_le_inv_sq (y t : ℝ) : cosineDefect y t ≤ 2 * (t ^ 2)⁻¹ := by
  unfold cosineDefect
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg _))
  linarith [Real.neg_one_le_cos (2 * y * t)]

lemma integrableOn_cosineDefect (y : ℝ) : IntegrableOn (cosineDefect y) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => 2 * y ^ 2 * Real.sinc (y * t) ^ 2) := by
    fun_prop
  have hnear : IntegrableOn (cosineDefect y) (Ioc 0 1) := by
    have hi : IntegrableOn (fun t : ℝ => 2 * y ^ 2 * Real.sinc (y * t) ^ 2)
        (Icc 0 1) volume := hc.continuousOn.integrableOn_Icc
    apply (hi.mono_set Ioc_subset_Icc_self).congr_fun
    · intro t ht
      exact (cosineDefect_eq_sinc ht.1.ne' y).symm
    · exact measurableSet_Ioc
  have hpow : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi 1) := by
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat] using
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)
  have htail : IntegrableOn (cosineDefect y) (Ioi 1) := by
    apply (hpow.const_mul 2).mono'
    · apply Measurable.aestronglyMeasurable
      unfold cosineDefect
      fun_prop
    · filter_upwards [] with t
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cosineDefect_nonneg y t)] using
        cosineDefect_le_inv_sq y t
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hnear.union htail

lemma cosineMass_nonneg (y : ℝ) : 0 ≤ cosineMass y :=
  integral_nonneg (fun t => cosineDefect_nonneg y t)

@[simp] lemma cosineMass_zero : cosineMass 0 = 0 := by
  simp [cosineMass, cosineDefect]

lemma cosineMass_neg (y : ℝ) : cosineMass (-y) = cosineMass y := by
  unfold cosineMass
  congr 1
  funext t
  simp [cosineDefect]

lemma integrableOn_realIntegrand {ω₁ ω₂ x : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hx₁ : 0 < x) (hx₂ : x < ω₁ + ω₂) :
    IntegrableOn (realIntegrand ω₁ ω₂ x) (Ioi 0) := by
  have hi := (integrableOn_integrand hω₁ hω₂ (z := (x : ℂ))
    (by simpa using hx₁) (by simpa using hx₂)).re
  change Integrable (realIntegrand ω₁ ω₂ x) (volume.restrict (Ioi (0 : ℝ)))
  convert! hi using 1
  ext t
  simp only [RCLike.re_eq_complex_re, integrand_ofReal, Complex.ofReal_re]

lemma integrableOn_cosineRemainder {ω₁ ω₂ x : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hx₁ : 0 < x) (hx₂ : x < ω₁ + ω₂) (y : ℝ) :
    IntegrableOn (fun t => Real.cos (2 * y * t) * realIntegrand ω₁ ω₂ x t) (Ioi 0) := by
  exact (integrableOn_realIntegrand hω₁ hω₂ hx₁ hx₂).bdd_mul
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (ae_of_all _ (fun t => by simpa using Real.abs_cos_le_one (2 * y * t)))

lemma cosineRemainder_bound {ω₁ ω₂ x : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hx₁ : 0 < x) (hx₂ : x < ω₁ + ω₂) (y : ℝ) :
    |cosineRemainder ω₁ ω₂ x y| ≤ modulusError ω₁ ω₂ x := by
  have hi := integrableOn_realIntegrand hω₁ hω₂ hx₁ hx₂
  have hj := integrableOn_cosineRemainder hω₁ hω₂ hx₁ hx₂ y
  calc
    |cosineRemainder ω₁ ω₂ x y| ≤
        ∫ t in Ioi (0 : ℝ), ‖Real.cos (2 * y * t) * realIntegrand ω₁ ω₂ x t‖ := by
      simpa only [cosineRemainder, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun t => Real.cos (2 * y * t) * realIntegrand ω₁ ω₂ x t)
    _ ≤ modulusError ω₁ ω₂ x := by
      apply integral_mono hj.norm hi.norm
      intro t
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

lemma integrand_re_vertical (ω₁ ω₂ x y t : ℝ) :
    (integrand ω₁ ω₂ ((x : ℂ) + y * I) t).re =
      Real.cos (2 * y * t) * realIntegrand ω₁ ω₂ x t -
        modulusSlope ω₁ ω₂ x * cosineDefect y t := by
  have harg : center ω₁ ω₂ ((x : ℂ) + y * I) * t =
      (((2 * x - (ω₁ + ω₂)) * t : ℝ) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I := by
    simp only [center, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_ofNat]
    ring
  have hs : (Complex.sinh (center ω₁ ω₂ ((x : ℂ) + y * I) * t)).re =
      Real.sinh ((2 * x - (ω₁ + ω₂)) * t) * Real.cos (2 * y * t) := by
    rw [harg, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    ring
  have hden : 2 * Complex.sinh ((ω₁ : ℂ) * t) * Complex.sinh ((ω₂ : ℂ) * t) =
      ((2 * Real.sinh (ω₁ * t) * Real.sinh (ω₂ * t) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hden' : (2 * (ω₁ : ℂ) * ω₂ * t) = ((2 * ω₁ * ω₂ * t : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [integrand, hden, Complex.div_ofReal_re, Complex.sub_re,
    Complex.div_ofReal_re, hs, hden', Complex.div_ofReal_re]
  norm_num only [center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, zero_add,
    mul_one]
  simp only [realIntegrand, modulusSlope, cosineDefect, div_eq_mul_inv, mul_inv, pow_two]
  ring

/-- The logarithmic modulus is an explicit universal leading term plus a
cosine transform with an error bounded independently of the height. -/
theorem log_norm_gamma_vertical {ω₁ ω₂ x : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hx₁ : 0 < x) (hx₂ : x < ω₁ + ω₂) (y : ℝ) :
    Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ =
      modulusSlope ω₁ ω₂ x * cosineMass y - cosineRemainder ω₁ ω₂ x y := by
  have hi := integrableOn_integrand hω₁ hω₂
    (z := (x : ℂ) + y * I) (by simpa using hx₁) (by simpa using hx₂)
  have hj := integrableOn_cosineRemainder hω₁ hω₂ hx₁ hx₂ y
  have hk := (integrableOn_cosineDefect y).const_mul (modulusSlope ω₁ ω₂ x)
  have hre : (∫ t in Ioi (0 : ℝ), integrand ω₁ ω₂ ((x : ℂ) + y * I) t).re =
      ∫ t in Ioi (0 : ℝ), (integrand ω₁ ω₂ ((x : ℂ) + y * I) t).re := by
    exact (Complex.reCLM.integral_comp_comm hi).symm
  rw [gamma, Complex.norm_exp, Real.log_exp, logGamma, Complex.neg_re,
    hre]
  simp only [integrand_re_vertical]
  rw [integral_sub hj hk, integral_const_mul]
  simp only [cosineMass, cosineRemainder]
  ring

theorem log_norm_gamma_vertical_bound {ω₁ ω₂ x : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hx₁ : 0 < x) (hx₂ : x < ω₁ + ω₂) (y : ℝ) :
    |Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ -
      modulusSlope ω₁ ω₂ x * cosineMass y| ≤ modulusError ω₁ ω₂ x := by
  rw [log_norm_gamma_vertical hω₁ hω₂ hx₁ hx₂ y]
  simpa only [sub_sub_cancel_left, abs_neg] using
    cosineRemainder_bound hω₁ hω₂ hx₁ hx₂ y

end HaagerupIzumi.GammaIntegral
