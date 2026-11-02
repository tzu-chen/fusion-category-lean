module

public import HaagerupIzumi.Analytic.Residue
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The elementary normalization integral

The two-gamma Fourier transform at its normalization parameter reduces to
the mass of `1 / cosh`. Its primitive is `2 * arctan (exp x)`.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory

namespace HaagerupIzumi.GammaSech

lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * arctan (exp t)) (cosh x)⁻¹ x := by
  convert! ((hasDerivAt_arctan (exp x)).comp x (hasDerivAt_exp x)).const_mul 2 using 1
  rw [cosh_eq, exp_neg]
  have he := exp_ne_zero x
  field_simp
  ring

lemma inv_cosh_le (x : ℝ) : (cosh x)⁻¹ ≤ 2 * exp (-|x|) := by
  have hc : cosh x = cosh |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, cosh_neg]
  rw [hc, cosh_eq, exp_neg]
  have he := exp_pos |x|
  have hn := exp_pos (-|x|)
  apply (inv_le_iff_one_le_mul₀ (by positivity)).2
  rw [exp_neg] at hn
  field_simp
  nlinarith [sq_nonneg (exp |x|)]

lemma integrable_inv_cosh : Integrable (fun x : ℝ => (cosh x)⁻¹) := by
  apply (integrable_const_mul_exp_neg_mul_abs 2 1 (by norm_num)).mono'
    (by fun_prop)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cosh_pos x)), neg_one_mul]
    using inv_cosh_le x

theorem integral_inv_cosh : (∫ x : ℝ, (cosh x)⁻¹) = π := by
  have hbot : Tendsto (fun x : ℝ => 2 * arctan (exp x)) atBot (𝓝 0) := by
    have h := (continuous_arctan.tendsto 0).comp tendsto_exp_atBot
    simpa using h.const_mul 2
  have htop : Tendsto (fun x : ℝ => 2 * arctan (exp x)) atTop (𝓝 π) := by
    have h := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp tendsto_exp_atTop
    simpa only [Function.comp_def, show (2 : ℝ) * (π / 2) = π by ring] using h.const_mul 2
  simpa using integral_of_hasDerivAt_of_tendsto hasDerivAt_primitive
    integrable_inv_cosh hbot htop

theorem integral_scaled {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, 1 / (2 * cosh (π * t / a))) = a / 2 := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (cosh x)⁻¹) (π / a)
  rw [integral_inv_cosh, abs_of_pos (inv_pos.mpr (div_pos pi_pos ha))] at h
  have hfun : (fun t : ℝ => 1 / (2 * cosh (π * t / a))) =
      fun t => (1 / 2 : ℝ) * (cosh ((π / a) * t))⁻¹ := by
    funext t
    rw [show π * t / a = (π / a) * t by ring]
    simp only [one_div, mul_inv_rev]
    ring
  rw [hfun, integral_const_mul, h, smul_eq_mul]
  field_simp

end HaagerupIzumi.GammaSech
