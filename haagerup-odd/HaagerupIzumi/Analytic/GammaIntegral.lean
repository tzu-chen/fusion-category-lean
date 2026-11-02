module

import all Mathlib.Data.Complex.Basic

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# The regularized integral defining the hyperbolic gamma function

The convention is the uncentered BSS convention: the defining strip is
`0 < re z < ω₁ + ω₂`. The regularization at the integration endpoint is kept
inside one integrand; its two summands are not separately integrable there.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace HaagerupIzumi.GammaIntegral

/-- Twice the displacement from the center of the defining strip. -/
def center (ω₁ ω₂ : ℝ) (z : ℂ) : ℂ := 2 * z - (ω₁ + ω₂)

/-- The regularized BSS integrand, including the factor `dt/t`. -/
def integrand (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.sinh (center ω₁ ω₂ z * t) /
      (2 * Complex.sinh ((ω₁ : ℂ) * t) * Complex.sinh ((ω₂ : ℂ) * t)) -
    center ω₁ ω₂ z / (2 * ω₁ * ω₂ * t)) / t

/-- The strip logarithm; convergence is established below. -/
def logGamma (ω₁ ω₂ : ℝ) (z : ℂ) : ℂ :=
  -(∫ t in Ioi (0 : ℝ), integrand ω₁ ω₂ z t)

/-- Hyperbolic gamma on its defining strip, in the BSS normalization. -/
def gamma (ω₁ ω₂ : ℝ) (z : ℂ) : ℂ := Complex.exp (logGamma ω₁ ω₂ z)

/-- The entire function `sinh z / z`, with its removable value at zero. -/
def sinhc : ℂ → ℂ := dslope Complex.sinh 0

@[simp] lemma sinhc_zero : sinhc 0 = 1 := by
  simp [sinhc, Complex.deriv_sinh]

lemma sinhc_of_ne_zero {z : ℂ} (hz : z ≠ 0) : sinhc z = Complex.sinh z / z := by
  simp [sinhc, dslope_of_ne _ hz, slope, div_eq_mul_inv, mul_comm]

@[simp] lemma sinhc_neg (z : ℂ) : sinhc (-z) = sinhc z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [sinhc_of_ne_zero hz, sinhc_of_ne_zero (neg_ne_zero.mpr hz)]

lemma differentiable_sinhc : Differentiable ℂ sinhc := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 0)).mpr
    Complex.differentiable_sinh.differentiableOn

lemma continuous_sinhc : Continuous sinhc := differentiable_sinhc.continuous

lemma hasDerivAt_sinhc_zero : HasDerivAt sinhc 0 0 := by
  have hd : HasDerivAt sinhc (deriv sinhc 0) (0 : ℂ) :=
    (differentiable_sinhc 0).hasDerivAt
  have hdneg : HasDerivAt sinhc (deriv sinhc 0) (-(0 : ℂ)) := by simpa using hd
  have hn := hdneg.comp (0 : ℂ) (hasDerivAt_id (0 : ℂ)).neg
  have hn' : HasDerivAt sinhc (-(deriv sinhc 0)) 0 := by
    simpa [Function.comp_def] using hn
  have he := hd.unique hn'
  have he' : deriv sinhc 0 = 0 := by linear_combination (1 / 2 : ℂ) * he
  simpa [he'] using hd

lemma sinhc_ofReal_ne_zero (x : ℝ) : sinhc (x : ℂ) ≠ 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sinhc_of_ne_zero (by exact_mod_cast hx)]
    apply div_ne_zero
    · rw [← Complex.ofReal_sinh]
      exact_mod_cast (Real.sinh_eq_zero.not.mpr hx)
    · exact_mod_cast hx

/-- A normalized analytic quotient whose constant term is one and whose
linear term vanishes. -/
def normalized (ω₁ ω₂ : ℝ) (z t : ℂ) : ℂ :=
  sinhc (center ω₁ ω₂ z * t) /
    (sinhc ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t))

@[simp] lemma normalized_zero (ω₁ ω₂ : ℝ) (z : ℂ) : normalized ω₁ ω₂ z 0 = 1 := by
  simp [normalized]

lemma hasDerivAt_normalized_zero (ω₁ ω₂ : ℝ) (z : ℂ) :
    HasDerivAt (normalized ω₁ ω₂ z) 0 0 := by
  have hc (c : ℂ) : HasDerivAt (fun t : ℂ => sinhc (c * t)) 0 0 := by
    have h0 : HasDerivAt sinhc 0 (c * (0 : ℂ)) := by
      simpa using hasDerivAt_sinhc_zero
    simpa [Function.comp_def] using h0.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul c)
  convert! (hc (center ω₁ ω₂ z)).div ((hc ω₁).mul (hc ω₂)) (by simp) using 1
  simp

/-- The removable extension of the integral kernel at the endpoint. -/
def regularized (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  center ω₁ ω₂ z / (2 * ω₁ * ω₂) *
    dslope (dslope (normalized ω₁ ω₂ z) 0) 0 (t : ℂ)

lemma continuous_regularized (ω₁ ω₂ : ℝ) (z : ℂ) :
    Continuous (regularized ω₁ ω₂ z) := by
  let U : Set ℂ := {t | sinhc ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t) ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_ne_fun
    · exact (continuous_sinhc.comp (continuous_const.mul continuous_id)).mul
        (continuous_sinhc.comp (continuous_const.mul continuous_id))
    · exact continuous_const
  have hzero : (0 : ℂ) ∈ U := by simp [U]
  have hnorm : DifferentiableOn ℂ (normalized ω₁ ω₂ z) U := by
    intro t ht
    exact ((differentiable_sinhc _).comp t ((differentiableAt_const _).mul
      differentiableAt_id)).differentiableWithinAt.div
      (((differentiable_sinhc _).comp t ((differentiableAt_const _).mul
        differentiableAt_id)).differentiableWithinAt.mul
      ((differentiable_sinhc _).comp t ((differentiableAt_const _).mul
        differentiableAt_id)).differentiableWithinAt) ht
  have hfirst := (Complex.differentiableOn_dslope (hU.mem_nhds hzero)).mpr hnorm
  have hsecond := (Complex.differentiableOn_dslope (hU.mem_nhds hzero)).mpr hfirst
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : (t : ℂ) ∈ U := by
    dsimp [U]
    apply mul_ne_zero
    · simpa only [← Complex.ofReal_mul] using sinhc_ofReal_ne_zero (ω₁ * t)
    · simpa only [← Complex.ofReal_mul] using sinhc_ofReal_ne_zero (ω₂ * t)
  exact continuousAt_const.mul
    ((hsecond.differentiableAt (hU.mem_nhds ht)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)

lemma regularized_eq_integrand (ω₁ ω₂ : ℝ) (z : ℂ)
    (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    regularized ω₁ ω₂ z t = integrand ω₁ ω₂ z t := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hω₁' : (ω₁ : ℂ) ≠ 0 := by exact_mod_cast hω₁
  have hω₂' : (ω₂ : ℂ) ≠ 0 := by exact_mod_cast hω₂
  have hs₁ : Complex.sinh ((ω₁ : ℂ) * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast (Real.sinh_eq_zero.not.mpr (mul_ne_zero hω₁ ht))
  have hs₂ : Complex.sinh ((ω₂ : ℂ) * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast (Real.sinh_eq_zero.not.mpr (mul_ne_zero hω₂ ht))
  have hn' : deriv (normalized ω₁ ω₂ z) 0 = 0 :=
    (hasDerivAt_normalized_zero ω₁ ω₂ z).deriv
  by_cases hc : center ω₁ ω₂ z = 0
  · simp [regularized, integrand, hc]
  · simp only [regularized, dslope_of_ne _ ht', slope, vsub_eq_sub, sub_zero, smul_eq_mul,
      dslope_same, hn', normalized, mul_zero, sinhc_zero,
      sinhc_of_ne_zero (mul_ne_zero hc ht'),
      sinhc_of_ne_zero (mul_ne_zero hω₁' ht'),
      sinhc_of_ne_zero (mul_ne_zero hω₂' ht'), integrand]
    field_simp

/-- The endpoint cancellation gives absolute integrability on every finite
positive interval, without requiring the strip restriction. -/
lemma integrableOn_Ioc_integrand (ω₁ ω₂ : ℝ) (z : ℂ)
    (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) (b : ℝ) :
    IntegrableOn (integrand ω₁ ω₂ z) (Ioc 0 b) := by
  have hi : IntegrableOn (regularized ω₁ ω₂ z) (Icc (0 : ℝ) b) volume :=
    (continuous_regularized ω₁ ω₂ z).continuousOn.integrableOn_Icc
  apply (hi.mono_set Ioc_subset_Icc_self).congr_fun
  · intro t ht
    exact regularized_eq_integrand ω₁ ω₂ z hω₁ hω₂ (ne_of_gt ht.1)
  · exact measurableSet_Ioc

/-- The bounded scalar factor in the exponential form of the kernel. -/
def tailWeight (ω₁ ω₂ t : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * ω₁ * t)) * (1 - Real.exp (-2 * ω₂ * t)) * t)⁻¹

lemma tailWeight_bound {ω₁ ω₂ t : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (ht : 1 ≤ t) :
    |tailWeight ω₁ ω₂ t| ≤
      ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹ := by
  have hd (a : ℝ) (ha : 0 < a) : 0 < 1 - Real.exp (-2 * a) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * a < 0 by linarith)
    linarith
  have hm (a : ℝ) (ha : 0 < a) :
      1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * a * t) := by
    have hh : -2 * a * t ≤ -2 * a := by nlinarith
    exact sub_le_sub_left (Real.exp_le_exp.mpr hh) 1
  have hp := mul_pos (hd ω₁ hω₁) (hd ω₂ hω₂)
  have hp' : (1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)) ≤
      (1 - Real.exp (-2 * ω₁ * t)) * (1 - Real.exp (-2 * ω₂ * t)) :=
    mul_le_mul (hm ω₁ hω₁) (hm ω₂ hω₂) (hd ω₂ hω₂).le
      ((hd ω₁ hω₁).le.trans (hm ω₁ hω₁))
  have hp'' : (1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)) ≤
      (1 - Real.exp (-2 * ω₁ * t)) * (1 - Real.exp (-2 * ω₂ * t)) * t :=
    hp'.trans (le_mul_of_one_le_right (hp.le.trans hp') ht)
  rw [tailWeight, abs_of_pos (inv_pos.mpr (hp.trans_le hp''))]
  exact inv_anti₀ hp hp''

/-- The extra factor `t` from differentiating in the gamma argument also
leaves a uniformly bounded tail weight. -/
lemma mul_tailWeight_bound {ω₁ ω₂ t : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (ht : 1 ≤ t) :
    |t * tailWeight ω₁ ω₂ t| ≤
      ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹ := by
  have hd (a : ℝ) (ha : 0 < a) : 0 < 1 - Real.exp (-2 * a) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * a < 0 by linarith)
    linarith
  have hm (a : ℝ) (ha : 0 < a) :
      1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * a * t) := by
    have hh : -2 * a * t ≤ -2 * a := by nlinarith
    exact sub_le_sub_left (Real.exp_le_exp.mpr hh) 1
  have hp := mul_pos (hd ω₁ hω₁) (hd ω₂ hω₂)
  have hp' : (1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)) ≤
      (1 - Real.exp (-2 * ω₁ * t)) * (1 - Real.exp (-2 * ω₂ * t)) :=
    mul_le_mul (hm ω₁ hω₁) (hm ω₂ hω₂) (hd ω₂ hω₂).le
      ((hd ω₁ hω₁).le.trans (hm ω₁ hω₁))
  have htne : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
  have he : t * tailWeight ω₁ ω₂ t =
      ((1 - Real.exp (-2 * ω₁ * t)) * (1 - Real.exp (-2 * ω₂ * t)))⁻¹ := by
    simp only [tailWeight, mul_inv]
    rw [mul_comm t, mul_assoc, inv_mul_cancel₀ htne, mul_one]
  rw [he, abs_of_pos (inv_pos.mpr (hp.trans_le hp'))]
  exact inv_anti₀ hp hp'

lemma sinh_factor (u : ℂ) :
    Complex.sinh u = Complex.exp u * (1 - Complex.exp (-2 * u)) / 2 := by
  rw [show -2 * u = -(u + u) by ring, Complex.exp_neg, Complex.exp_add,
    Complex.sinh, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]

lemma integrand_eq_exponential {ω₁ ω₂ t : ℝ} (z : ℂ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ht : 0 < t) :
    integrand ω₁ ω₂ z t =
      (Complex.exp ((2 * (z - (ω₁ + ω₂))) * t) -
        Complex.exp ((-2 * z) * t)) * (tailWeight ω₁ ω₂ t : ℂ) -
      center ω₁ ω₂ z / (2 * ω₁ * ω₂) * ((t : ℂ) ^ 2)⁻¹ := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hω₁' : (ω₁ : ℂ) ≠ 0 := by exact_mod_cast hω₁.ne'
  have hω₂' : (ω₂ : ℂ) ≠ 0 := by exact_mod_cast hω₂.ne'
  have hd (a : ℝ) (ha : 0 < a) : (1 : ℂ) - Complex.exp (-2 * a * t) ≠ 0 := by
    have hh : 1 - Real.exp (-2 * a * t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (show -2 * a * t < 0 by nlinarith)
      linarith
    exact_mod_cast hh
  have he₁ : 2 * (z - ((ω₁ : ℂ) + ω₂)) * t =
      center ω₁ ω₂ z * t - (ω₁ : ℂ) * t - (ω₂ : ℂ) * t := by
    dsimp [center]
    ring
  have he₂ : -2 * z * t =
      -(center ω₁ ω₂ z * t) - (ω₁ : ℂ) * t - (ω₂ : ℂ) * t := by
    dsimp [center]
    ring
  rw [integrand, sinh_factor ((ω₁ : ℂ) * t), sinh_factor ((ω₂ : ℂ) * t),
    Complex.sinh, he₁, he₂]
  simp only [tailWeight, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.exp_sub, Complex.exp_neg]
  have hd₁ := hd ω₁ hω₁
  have hd₂ := hd ω₂ hω₂
  simp only [mul_assoc] at hd₁ hd₂ ⊢
  field_simp [Complex.exp_ne_zero]

/-- Absolute convergence at infinity under the exact defining-strip conditions. -/
lemma integrableOn_Ioi_one_integrand {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    {z : ℂ} (hz₁ : 0 < z.re) (hz₂ : z.re < ω₁ + ω₂) :
    IntegrableOn (integrand ω₁ ω₂ z) (Ioi 1) := by
  have hexp₁ : IntegrableOn
      (fun t : ℝ => Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t)) (Ioi 1) :=
    integrableOn_exp_mul_complex_Ioi (by norm_num [Complex.mul_re]; linarith) 1
  have hexp₂ : IntegrableOn
      (fun t : ℝ => Complex.exp ((-2 * z) * t)) (Ioi 1) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 1
  have hweight : AEStronglyMeasurable (fun t : ℝ => (tailWeight ω₁ ω₂ t : ℂ))
      (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold tailWeight
    fun_prop
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1),
      ‖(tailWeight ω₁ ω₂ t : ℂ)‖ ≤
        ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa using tailWeight_bound hω₁ hω₂ ht.le
  have hi₁ := (hexp₁.sub hexp₂).mul_bdd hweight hbound
  have hpow : IntegrableOn (fun t : ℝ => ((t : ℂ) ^ 2)⁻¹) (Ioi 1) := by
    have hr : IntegrableOn (fun t : ℝ => ((t ^ (-2 : ℝ) : ℝ) : ℂ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).ofReal
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, Complex.ofReal_inv,
      Complex.ofReal_pow] using hr
  apply (hi₁.sub (hpow.const_mul (center ω₁ ω₂ z / (2 * ω₁ * ω₂)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (integrand_eq_exponential z hω₁ hω₂ (lt_trans zero_lt_one ht)).symm

/-- An exponential-plus-inverse-square majorant uniform on every closed
substrip. The remaining parameter dependence is only the explicit linear
factor `‖center ω₁ ω₂ z‖`. -/
lemma norm_integrand_le_tail {ω₁ ω₂ δ t : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    {z : ℂ} (hz₁ : δ ≤ z.re) (hz₂ : z.re ≤ ω₁ + ω₂ - δ) (ht : 1 ≤ t) :
    ‖integrand ω₁ ω₂ z t‖ ≤
      2 * ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹ *
        Real.exp (-2 * δ * t) +
      ‖center ω₁ ω₂ z‖ / (2 * ω₁ * ω₂) * (t ^ 2)⁻¹ := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  let C := ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹
  have hC : 0 ≤ C := (abs_nonneg _).trans (tailWeight_bound hω₁ hω₂ ht)
  have hfirst : ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t)‖ ≤
      Real.exp (-2 * δ * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re]
    nlinarith
  have hsecond : ‖Complex.exp ((-2 * z) * t)‖ ≤ Real.exp (-2 * δ * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re]
    nlinarith
  have hnum : ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) -
      Complex.exp ((-2 * z) * t)‖ ≤ 2 * Real.exp (-2 * δ * t) :=
    (norm_sub_le _ _).trans (by linarith)
  have hweight : ‖(tailWeight ω₁ ω₂ t : ℂ)‖ ≤ C := by
    simpa [C] using tailWeight_bound hω₁ hω₂ ht
  have hrem : ‖center ω₁ ω₂ z / (2 * ω₁ * ω₂) * ((t : ℂ) ^ 2)⁻¹‖ =
      ‖center ω₁ ω₂ z‖ / (2 * ω₁ * ω₂) * (t ^ 2)⁻¹ := by
    simp [norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hω₁, abs_of_pos hω₂, abs_of_pos htpos]
  rw [integrand_eq_exponential z hω₁ hω₂ htpos]
  calc
    _ ≤ ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) -
          Complex.exp ((-2 * z) * t)‖ * ‖(tailWeight ω₁ ω₂ t : ℂ)‖ +
        ‖center ω₁ ω₂ z / (2 * ω₁ * ω₂) * ((t : ℂ) ^ 2)⁻¹‖ := by
      simpa only [norm_mul] using norm_sub_le
        ((Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) -
          Complex.exp ((-2 * z) * t)) * (tailWeight ω₁ ω₂ t : ℂ))
        (center ω₁ ω₂ z / (2 * ω₁ * ω₂) * ((t : ℂ) ^ 2)⁻¹)
    _ ≤ (2 * Real.exp (-2 * δ * t)) * C +
        ‖center ω₁ ω₂ z‖ / (2 * ω₁ * ω₂) * (t ^ 2)⁻¹ := by
      rw [hrem]
      exact add_le_add (mul_le_mul hnum hweight (norm_nonneg _) (by positivity)) le_rfl
    _ = _ := by dsimp [C]; ring

/-- The defining hyperbolic-gamma integral is absolutely convergent on its strip. -/
theorem integrableOn_integrand {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    {z : ℂ} (hz₁ : 0 < z.re) (hz₂ : z.re < ω₁ + ω₂) :
    IntegrableOn (integrand ω₁ ω₂ z) (Ioi 0) := by
  have hnear := integrableOn_Ioc_integrand ω₁ ω₂ z hω₁.ne' hω₂.ne' 1
  have htail := integrableOn_Ioi_one_integrand hω₁ hω₂ hz₁ hz₂
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans zero_lt_one h
    · intro h
      by_cases ht : t ≤ 1
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr (lt_of_not_ge ht)
  rw [← hu]
  exact hnear.union htail

end HaagerupIzumi.GammaIntegral
