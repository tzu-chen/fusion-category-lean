module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaHolomorphic
public import HaagerupIzumi.Analytic.GammaNormalization
public import HaagerupIzumi.Analytic.GammaStrip
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Convex

/-!
# Reduction of the gamma shift to elementary integrals

The overlap strip for a shift by `a` is `0 < re z < b`. On that
strip the two logarithmic integrals differ by a one-period kernel.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace HaagerupIzumi.GammaIntegral

def shiftIntegrand (b : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (1 / ((b : ℂ) * t) - Complex.cosh ((2 * z - b) * t) /
    Complex.sinh ((b : ℂ) * t)) / t

lemma center_shift_add (a b : ℝ) (z : ℂ) (t : ℝ) :
    center a b (z + a) * t = (2 * z - b) * t + (a : ℂ) * t := by
  unfold center
  ring

lemma center_shift_sub (a b : ℝ) (z : ℂ) (t : ℝ) :
    center a b z * t = (2 * z - b) * t - (a : ℂ) * t := by
  unfold center
  ring

/-- Cancellation of the two regularized BSS kernels on the overlap
strip. The identity itself only uses positive periods and `t > 0`. -/
lemma integrand_shift_sub (a b : ℝ) (z : ℂ) (t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    integrand a b (z + a) t - integrand a b z t = -shiftIntegrand b z t := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsa : Complex.sinh ((a : ℂ) * t) ≠ 0 := by
    simpa only [← Complex.ofReal_mul] using
      GammaNormalization.sinh_ofReal_ne_zero (ne_of_gt (mul_pos ha ht))
  have hsb : Complex.sinh ((b : ℂ) * t) ≠ 0 := by
    simpa only [← Complex.ofReal_mul] using
      GammaNormalization.sinh_ofReal_ne_zero (ne_of_gt (mul_pos hb ht))
  unfold integrand shiftIntegrand
  rw [center_shift_add, center_shift_sub, Complex.sinh_add, Complex.sinh_sub]
  unfold center
  generalize Complex.sinh ((a : ℂ) * t) = A at *
  generalize Complex.sinh ((b : ℂ) * t) = B at *
  field_simp
  ring

/-- The difference of the differentiated kernels is the elementary
hyperbolic quotient evaluated by the paired cotangent expansion. -/
lemma integrandDeriv_shift_sub (a b : ℝ) (z : ℂ) (t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    integrandDeriv a b (z + a) t - integrandDeriv a b z t =
      2 * (Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t)) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsa : Complex.sinh ((a : ℂ) * t) ≠ 0 := by
    simpa only [← Complex.ofReal_mul] using
      GammaNormalization.sinh_ofReal_ne_zero (ne_of_gt (mul_pos ha ht))
  have hsb : Complex.sinh ((b : ℂ) * t) ≠ 0 := by
    simpa only [← Complex.ofReal_mul] using
      GammaNormalization.sinh_ofReal_ne_zero (ne_of_gt (mul_pos hb ht))
  unfold integrandDeriv
  rw [center_shift_add, center_shift_sub, Complex.cosh_add, Complex.cosh_sub]
  generalize Complex.sinh ((a : ℂ) * t) = A at *
  generalize Complex.sinh ((b : ℂ) * t) = B at *
  field_simp
  ring

lemma integrableOn_shiftIntegrand (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    IntegrableOn (shiftIntegrand b z) (Ioi 0) := by
  have hz₀' : 0 < (z + a).re := by simp only [add_re, ofReal_re]; linarith
  have hz₁' : (z + a).re < a + b := by simp only [add_re, ofReal_re]; linarith
  have hbase := integrableOn_integrand ha hb hz₀ (by linarith : z.re < a + b)
  have hshift := integrableOn_integrand ha hb hz₀' hz₁'
  apply (hbase.sub hshift).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.sub_apply]
  have heq := integrand_shift_sub a b z t ha hb ht
  linear_combination -heq

lemma logGamma_shift_sub (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    logGamma a b (z + a) - logGamma a b z =
      ∫ t : ℝ in Ioi 0, shiftIntegrand b z t := by
  have hz₀' : 0 < (z + a).re := by simp only [add_re, ofReal_re]; linarith
  have hz₁' : (z + a).re < a + b := by simp only [add_re, ofReal_re]; linarith
  have hbase := integrableOn_integrand ha hb hz₀ (by linarith : z.re < a + b)
  have hshift := integrableOn_integrand ha hb hz₀' hz₁'
  unfold logGamma
  calc
    _ = ∫ t : ℝ in Ioi 0, integrand a b z t - integrand a b (z + a) t := by
      rw [integral_sub hbase hshift]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have heq := integrand_shift_sub a b z t ha hb ht
      linear_combination -heq

lemma shiftIntegrand_midpoint (b : ℝ) (t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    shiftIntegrand b ((b : ℂ) / 2) t =
      (b : ℂ) * GammaNormalization.normalizationIntegrand (b * t) := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold shiftIntegrand GammaNormalization.normalizationIntegrand
  rw [show 2 * ((b : ℂ) / 2) - b = 0 by ring]
  simp only [zero_mul, Complex.cosh_zero, Complex.ofReal_mul]
  field_simp

lemma integral_shiftIntegrand_midpoint (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, shiftIntegrand b ((b : ℂ) / 2) t) = (Real.log 2 : ℂ) := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  calc
    _ = ∫ t : ℝ in Ioi 0,
        (b : ℂ) * GammaNormalization.normalizationIntegrand (b * t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact shiftIntegrand_midpoint b t hb ht
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hb]
      simp only [mul_zero, Complex.real_smul, Complex.ofReal_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hbC, one_mul,
        GammaNormalization.integral_normalizationIntegrand]

lemma logGamma_shift_sub_midpoint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    logGamma a b ((b : ℂ) / 2 + a) - logGamma a b ((b : ℂ) / 2) =
      (Real.log 2 : ℂ) := by
  rw [logGamma_shift_sub a b ((b : ℂ) / 2) ha hb]
  · exact integral_shiftIntegrand_midpoint b hb
  · simp only [div_ofNat_re, ofReal_re]
    positivity
  · simp only [div_ofNat_re, ofReal_re]
    linarith

/-- Convergence of the one-period hyperbolic quotient follows directly
from the already established derivative-kernel convergence. -/
lemma integrableOn_shift_sinh_quotient (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    IntegrableOn (fun t : ℝ => Complex.sinh ((2 * z - b) * t) /
      Complex.sinh ((b : ℂ) * t)) (Ioi 0) := by
  have hz₀' : 0 < (z + a).re := by simp only [add_re, ofReal_re]; linarith
  have hz₁' : (z + a).re < a + b := by simp only [add_re, ofReal_re]; linarith
  have hbase := integrableOn_integrandDeriv ha hb hz₀ (by linarith : z.re < a + b)
  have hshift := integrableOn_integrandDeriv ha hb hz₀' hz₁'
  apply ((hshift.sub hbase).const_mul (1 / 2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.sub_apply]
  rw [integrandDeriv_shift_sub a b z t ha hb ht]
  ring

lemma hasDerivAt_logGamma_shift_sub (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    HasDerivAt (fun w => logGamma a b (w + a) - logGamma a b w)
      ((Real.pi : ℂ) / b * Complex.cot (Real.pi * (z / b))) z := by
  have hz₀' : 0 < (z + a).re := by simp only [add_re, ofReal_re]; linarith
  have hz₁' : (z + a).re < a + b := by simp only [add_re, ofReal_re]; linarith
  have hbase := integrableOn_integrandDeriv ha hb hz₀ (by linarith : z.re < a + b)
  have hshift := integrableOn_integrandDeriv ha hb hz₀' hz₁'
  have hI : (∫ t : ℝ in Ioi 0, integrandDeriv a b (z + a) t) -
      (∫ t : ℝ in Ioi 0, integrandDeriv a b z t) =
      2 * ∫ t : ℝ in Ioi 0, Complex.sinh ((2 * z - b) * t) /
        Complex.sinh ((b : ℂ) * t) := by
    rw [← integral_sub hshift hbase, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrandDeriv_shift_sub a b z t ha hb ht
  have hval : -(∫ t : ℝ in Ioi 0, integrandDeriv a b (z + a) t) -
      (-(∫ t : ℝ in Ioi 0, integrandDeriv a b z t)) =
        (Real.pi : ℂ) / b * Complex.cot (Real.pi * (z / b)) := by
    rw [show -(∫ t : ℝ in Ioi 0, integrandDeriv a b (z + a) t) -
        (-(∫ t : ℝ in Ioi 0, integrandDeriv a b z t)) =
        -((∫ t : ℝ in Ioi 0, integrandDeriv a b (z + a) t) -
          (∫ t : ℝ in Ioi 0, integrandDeriv a b z t)) by ring]
    rw [hI, GammaElementary.integral_sinh_div_sinh b z hb hz₀ hz₁
      (integrableOn_shift_sinh_quotient a b z ha hb hz₀ hz₁)]
    ring
  have hp := (hasDerivAt_logGamma ha hb hz₀' hz₁').comp z
    ((hasDerivAt_id z).add_const (a : ℂ))
  have hd := hp.sub (hasDerivAt_logGamma ha hb hz₀ (by linarith : z.re < a + b))
  convert! hd using 1
  simp [hval]

lemma sin_shift_ne_zero (b : ℝ) (z : ℂ) (hb : 0 < b)
    (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    Complex.sin (Real.pi * (z / b)) ≠ 0 := by
  apply sin_pi_mul_ne_zero
  apply GammaElementary.mem_integerComplement_of_re_between
  · rw [Complex.div_ofReal_re]
    exact div_pos hz₀ hb
  · rw [Complex.div_ofReal_re]
    exact (div_lt_one hb).mpr hz₁

def shiftRatio (a b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (logGamma a b (z + a) - logGamma a b z) /
    Complex.sin (Real.pi * (z / b))

lemma hasDerivAt_shiftRatio (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    HasDerivAt (shiftRatio a b) 0 z := by
  have hf := hasDerivAt_logGamma_shift_sub a b z ha hb hz₀ hz₁
  have hs := (((hasDerivAt_id z).div_const (b : ℂ)).const_mul (Real.pi : ℂ)).csin
  have hsin := sin_shift_ne_zero b z hb hz₀ hz₁
  have hd := hf.cexp.div hs hsin
  simp only [Pi.div_def, id_eq] at hd
  unfold shiftRatio
  convert! hd using 1
  simp only [Complex.cot]
  generalize Complex.sin (Real.pi * (z / b)) = S at *
  field_simp
  ring

lemma shiftRatio_midpoint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    shiftRatio a b ((b : ℂ) / 2) = 2 := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  unfold shiftRatio
  rw [logGamma_shift_sub_midpoint a b ha hb]
  have harg : (Real.pi : ℂ) * (((b : ℂ) / 2) / b) = Real.pi / 2 := by
    field_simp
  rw [harg, Complex.sin_pi_div_two, div_one, ← Complex.ofReal_exp,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The first hyperbolic-gamma shift is now proved for the explicit
integral on the overlap of its two defining strips. -/
theorem gamma_shift₁_strip (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    gamma a b (z + a) = 2 * Complex.sin (Real.pi * (z / b)) * gamma a b z := by
  let S : Set ℂ := {w | 0 < w.re ∧ w.re < b}
  have hs : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hc : Convex ℝ S := by
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt b)
  have hmid : (b : ℂ) / 2 ∈ S := by
    change 0 < ((b : ℂ) / 2).re ∧ ((b : ℂ) / 2).re < b
    simp only [Complex.div_ofNat_re, Complex.ofReal_re]
    constructor <;> linarith
  have hconstant := hs.is_const_of_deriv_eq_zero hc.isPreconnected
    (fun w hw => (hasDerivAt_shiftRatio a b w ha hb hw.1 hw.2).differentiableAt.differentiableWithinAt)
    (fun w hw => (hasDerivAt_shiftRatio a b w ha hb hw.1 hw.2).deriv)
    (show z ∈ S from ⟨hz₀, hz₁⟩) hmid
  rw [shiftRatio_midpoint a b ha hb] at hconstant
  have he : Complex.exp (logGamma a b (z + a) - logGamma a b z) =
      2 * Complex.sin (Real.pi * (z / b)) :=
    (div_eq_iff (sin_shift_ne_zero b z hb hz₀ hz₁)).mp hconstant
  calc
    gamma a b (z + a) =
        Complex.exp (logGamma a b (z + a) - logGamma a b z) * gamma a b z := by
      unfold gamma
      rw [← Complex.exp_add, sub_add_cancel]
    _ = _ := by rw [he]

/-- The second shift follows by exchanging the two periods in the
defining integral. -/
theorem gamma_shift₂_strip (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < a) :
    gamma a b (z + b) = 2 * Complex.sin (Real.pi * (z / a)) * gamma a b z := by
  rw [← gamma_swap a b (z + b), gamma_shift₁_strip b a z hb ha hz₀ hz₁,
    gamma_swap a b z]

end HaagerupIzumi.GammaIntegral
