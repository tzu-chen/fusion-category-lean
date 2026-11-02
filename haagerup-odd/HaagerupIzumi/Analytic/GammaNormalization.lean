module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaIntegral
public import HaagerupIzumi.Analytic.GammaElementary
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-!
# The logarithmic normalization of the hyperbolic-gamma shift

The constant in the shift integral is `log 2`. Frullani's integral evaluates
it using the regularized hyperbolic cotangent, whose endpoint limits are
zero and one.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace HaagerupIzumi.GammaNormalization

def regularizedCoth (t : ℝ) : ℂ :=
  Complex.cosh t / Complex.sinh t - (t : ℂ)⁻¹

def normalizationIntegrand (t : ℝ) : ℂ :=
  (1 / (t : ℂ) - 1 / Complex.sinh t) / t

lemma sinh_ofReal_ne_zero {t : ℝ} (ht : t ≠ 0) : Complex.sinh t ≠ 0 := by
  rw [← Complex.ofReal_sinh, Complex.ofReal_ne_zero]
  exact Real.sinh_ne_zero.mpr ht

lemma continuousOn_regularizedCoth : ContinuousOn regularizedCoth (Ioi 0) := by
  apply ContinuousOn.sub
  · exact (Complex.continuous_cosh.comp Complex.continuous_ofReal).continuousOn.div
      (Complex.continuous_sinh.comp Complex.continuous_ofReal).continuousOn
      (fun t ht => sinh_ofReal_ne_zero (ne_of_gt ht))
  · exact Complex.continuous_ofReal.continuousOn.inv₀
      (fun t ht => Complex.ofReal_ne_zero.mpr (ne_of_gt ht))

/-- The singular-looking cotangent remainder has an analytic expression
in terms of the entire function `sinh z / z`. -/
lemma regularizedCoth_eq_dslope (t : ℝ) (ht : t ≠ 0) :
    regularizedCoth t =
      dslope (fun z : ℂ => Complex.cosh z - GammaIntegral.sinhc z) 0 (t : ℂ) /
        GammaIntegral.sinhc (t : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hs := sinh_ofReal_ne_zero ht
  rw [dslope_of_ne _ htC]
  simp only [slope, vsub_eq_sub, Complex.cosh_zero, GammaIntegral.sinhc_zero,
    sub_self, sub_zero, smul_eq_mul]
  rw [GammaIntegral.sinhc_of_ne_zero htC]
  unfold regularizedCoth
  field_simp

lemma tendsto_regularizedCoth_zero :
    Tendsto regularizedCoth (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  let F : ℂ → ℂ := fun z => Complex.cosh z - GammaIntegral.sinhc z
  have hF : HasDerivAt F 0 0 := by
    convert! (Complex.hasDerivAt_cosh 0).sub GammaIntegral.hasDerivAt_sinhc_zero using 1
    simp
  have hdiff : Differentiable ℂ F :=
    Complex.differentiable_cosh.sub GammaIntegral.differentiable_sinhc
  have hds : Continuous (dslope F 0) := by
    apply Differentiable.continuous (𝕜 := ℂ)
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 0)).mpr
      hdiff.differentiableOn
  have hn : Tendsto (fun t : ℝ => dslope F 0 (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, dslope_same, hF.deriv] using
      (hds.tendsto 0).comp Complex.continuous_ofReal.continuousAt.tendsto
  have hd : Tendsto (fun t : ℝ => GammaIntegral.sinhc (t : ℂ)) (𝓝 0) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, GammaIntegral.sinhc_zero] using
      (GammaIntegral.continuous_sinhc.tendsto 0).comp
        Complex.continuous_ofReal.continuousAt.tendsto
  have hlim := (hn.div hd one_ne_zero).mono_left
    (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
  have hlim' : Tendsto (fun t : ℝ => dslope F 0 (t : ℂ) /
      GammaIntegral.sinhc (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [zero_div, Pi.div_def] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (regularizedCoth_eq_dslope t (ne_of_gt ht)).symm

lemma cosh_div_sinh_eq_exp (t : ℝ) (ht : 0 < t) :
    Complex.cosh t / Complex.sinh t =
      (1 + Complex.exp (-2 * (t : ℂ))) / (1 - Complex.exp (-2 * (t : ℂ))) := by
  have he : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hs : Complex.exp (t : ℂ) - (Complex.exp (t : ℂ))⁻¹ ≠ 0 := by
    intro h
    apply sinh_ofReal_ne_zero (ne_of_gt ht)
    simp only [Complex.sinh, Complex.exp_neg, h, zero_div]
  have hq : Complex.exp (-2 * (t : ℂ)) =
      (Complex.exp (t : ℂ))⁻¹ * (Complex.exp (t : ℂ))⁻¹ := by
    rw [show -2 * (t : ℂ) = -(t : ℂ) + -(t : ℂ) by ring,
      Complex.exp_add, Complex.exp_neg]
  have hd : 1 - Complex.exp (-2 * (t : ℂ)) ≠ 0 := by
    have hp : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have heq : (Real.exp (-2 * t) : ℂ) = Complex.exp (-2 * (t : ℂ)) := by
      rw [Complex.ofReal_exp]
      push_cast
      rfl
    rw [← heq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact sub_ne_zero.mpr (ne_of_gt hp)
  rw [hq] at hd ⊢
  rw [Complex.cosh, Complex.sinh, Complex.exp_neg]
  field_simp

lemma tendsto_regularizedCoth_atTop :
    Tendsto regularizedCoth atTop (𝓝 (1 : ℂ)) := by
  have hq : Tendsto (fun t : ℝ => Complex.exp (-2 * (t : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    simpa only [id_eq, mul_re, neg_re, neg_im, re_ofNat, im_ofNat, ofReal_re,
      ofReal_im, mul_zero, zero_mul, neg_zero, sub_zero] using
      (tendsto_id.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num))
  have hi : Tendsto (fun t : ℝ => (t : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hlim := ((hq.const_add 1).div (hq.const_sub 1) (by norm_num)).sub hi
  have hlim' : Tendsto (fun t : ℝ =>
      (Complex.exp (-2 * (t : ℂ)) + 1) / (1 - Complex.exp (-2 * (t : ℂ))) -
        (t : ℂ)⁻¹) atTop (𝓝 (1 : ℂ)) := by
    simpa only [zero_add, add_zero, sub_zero, div_one, Pi.div_apply, add_comm] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [regularizedCoth, cosh_div_sinh_eq_exp t ht, add_comm]

/-- The normalization integrand is itself a special case of the
absolutely convergent BSS integral. -/
lemma normalizationIntegrand_eq_gammaIntegrand (t : ℝ) (ht : 0 < t) :
    normalizationIntegrand t = 2 * GammaIntegral.integrand 1 1 (1 / 2) t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hs := sinh_ofReal_ne_zero (ne_of_gt ht)
  have hc : GammaIntegral.center 1 1 (1 / 2) = -1 := by
    unfold GammaIntegral.center
    norm_num
  unfold normalizationIntegrand GammaIntegral.integrand
  rw [hc]
  simp only [Complex.ofReal_one, one_mul, neg_one_mul, Complex.sinh_neg]
  field_simp
  ring

lemma integrableOn_normalizationIntegrand : IntegrableOn normalizationIntegrand (Ioi 0) := by
  have hg := (GammaIntegral.integrableOn_integrand
    (ω₁ := 1) (ω₂ := 1) (z := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).const_mul (2 : ℂ)
  apply hg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (normalizationIntegrand_eq_gammaIntegrand t ht).symm

lemma regularizedCoth_difference (t : ℝ) (ht : 0 < t) :
    (t⁻¹ : ℝ) • (regularizedCoth t - regularizedCoth ((1 / 2 : ℝ) * t)) =
      normalizationIntegrand t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hs := sinh_ofReal_ne_zero (ne_of_gt ht)
  have hhalf : (1 / 2 : ℝ) * t ≠ 0 := ne_of_gt (by positivity : 0 < (1 / 2 : ℝ) * t)
  have hsh := sinh_ofReal_ne_zero hhalf
  have hdouble : (t : ℂ) = 2 * ((t : ℂ) / 2) := by ring
  have hc : Complex.cosh t = 2 * Complex.cosh ((t : ℂ) / 2) ^ 2 - 1 := by
    nth_rw 1 [hdouble]
    rw [Complex.cosh_two_mul, Complex.sinh_sq]
    ring
  have hsi : Complex.sinh t =
      2 * Complex.sinh ((t : ℂ) / 2) * Complex.cosh ((t : ℂ) / 2) := by
    nth_rw 1 [hdouble]
    rw [Complex.sinh_two_mul]
  have hsh' : Complex.sinh ((t : ℂ) / 2) ≠ 0 := by
    have heq : (((1 / 2 : ℝ) * t : ℝ) : ℂ) = (t : ℂ) / 2 := by push_cast; ring
    rwa [heq] at hsh
  unfold regularizedCoth normalizationIntegrand
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show (1 / 2 : ℂ) * t = (t : ℂ) / 2 by ring]
  field_simp
  rw [hc, hsi]
  ring

/-- The logarithmic normalization constant in the gamma shift formula. -/
theorem integral_normalizationIntegrand :
    (∫ t : ℝ in Ioi 0, normalizationIntegrand t) = (Real.log 2 : ℂ) := by
  have hloc : LocallyIntegrableOn regularizedCoth (Ioi 0) :=
    continuousOn_regularizedCoth.locallyIntegrableOn measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ =>
      t⁻¹ • (regularizedCoth (1 * t) - regularizedCoth ((1 / 2 : ℝ) * t))) (Ioi 0) := by
    apply integrableOn_normalizationIntegrand.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [one_mul] using (regularizedCoth_difference t ht).symm
  have heval := Frullani.integral_Ioi_eq hloc (a := 1) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) tendsto_regularizedCoth_zero tendsto_regularizedCoth_atTop hint
  calc
    (∫ t : ℝ in Ioi 0, normalizationIntegrand t) =
        ∫ t : ℝ in Ioi 0, t⁻¹ •
          (regularizedCoth (1 * t) - regularizedCoth ((1 / 2 : ℝ) * t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [one_mul] using (regularizedCoth_difference t ht).symm
    _ = (Real.log 2 : ℂ) := by
      rw [heval]
      simp [Complex.real_smul]

end HaagerupIzumi.GammaNormalization
