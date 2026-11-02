module

public import HaagerupIzumi.Analytic.GammaModulus
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import all Mathlib.Data.Complex.Basic

/-!
# The universal cosine integral

A nonnegative Laplace kernel permits an absolutely integrable Fubini argument.
This avoids a conditionally convergent integral of `sin t / t`.
-/

@[expose] public section

noncomputable section

open Filter Topology Set MeasureTheory

namespace HaagerupIzumi.GammaIntegral

lemma integral_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-(t * s))) = (t ^ 2)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ht
  have hgamma : Real.Gamma 2 = 1 := by
    norm_num [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [hgamma, Real.rpow_two, one_div, inv_pow] at h
  exact h

lemma integrableOn_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(t * s))) (Ioi 0) := by
  by_contra hn
  have he := integral_mul_exp_neg_mul ht
  rw [integral_undef hn] at he
  exact (inv_ne_zero (pow_ne_zero 2 ht.ne')) he.symm

lemma laplace_cos_integrable {s : ℝ} (hs : 0 < s) (u : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * Real.cos (u * t)) (Ioi 0) := by
  have he := integrableOn_exp_mul_complex_Ioi
    (a := -(s : ℂ) + (u : ℂ) * Complex.I) (by simpa using neg_neg_of_pos hs) 0
  change Integrable _ (volume.restrict (Ioi 0))
  convert! he.re using 1
  ext t
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

lemma integral_laplace_cos {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * Real.cos (u * t)) =
      s / (s ^ 2 + u ^ 2) := by
  have hs' : (-(s : ℂ) + (u : ℂ) * Complex.I).re < 0 := by
    simpa using neg_neg_of_pos hs
  have he := integrableOn_exp_mul_complex_Ioi hs' 0
  have hr := (Complex.reCLM.integral_comp_comm he).trans
    (congrArg Complex.re (integral_exp_mul_complex_Ioi hs' 0))
  simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.normSq_apply, add_comm, pow_two] using hr

def laplaceDefect (y s t : ℝ) : ℝ :=
  s * Real.exp (-(s * t)) * (1 - Real.cos (2 * y * t))

lemma laplaceDefect_nonneg (y : ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    0 ≤ laplaceDefect y s t := by
  unfold laplaceDefect
  exact mul_nonneg (mul_nonneg hs (Real.exp_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one _))

lemma integrableOn_laplaceDefect_left (y : ℝ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s => laplaceDefect y s t) (Ioi 0) := by
  change Integrable _ (volume.restrict (Ioi 0))
  convert! (integrableOn_mul_exp_neg_mul ht).mul_const (1 - Real.cos (2 * y * t)) using 1
  ext s
  simp only [laplaceDefect, mul_comm t s]

lemma integral_laplaceDefect_left (y : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), laplaceDefect y s t) = cosineDefect y t := by
  have hfun : (fun s => laplaceDefect y s t) =
      fun s => (s * Real.exp (-(t * s))) * (1 - Real.cos (2 * y * t)) := by
    ext s
    simp only [laplaceDefect, mul_comm s t]
  rw [hfun]
  simp only [integral_mul_const,
    integral_mul_exp_neg_mul ht, cosineDefect, div_eq_mul_inv]
  ring

lemma integrable_laplaceDefect (y : ℝ) :
    Integrable (fun p : ℝ × ℝ => laplaceDefect y p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff' (show AEStronglyMeasurable
    (fun p : ℝ × ℝ => laplaceDefect y p.1 p.2) _ from by
      apply Continuous.aestronglyMeasurable
      unfold laplaceDefect
      fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrableOn_laplaceDefect_left y ht
  · apply (integrableOn_cosineDefect y).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← integral_laplaceDefect_left y ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (Real.norm_eq_abs _).trans (abs_of_nonneg (laplaceDefect_nonneg y hs.le)) |>.symm

lemma integral_laplaceDefect_right (y : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), laplaceDefect y s t) =
      (2 * y) ^ 2 / (s ^ 2 + (2 * y) ^ 2) := by
  have he := integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0
  have hc := laplace_cos_integrable hs (2 * y)
  have hfun : (fun t => laplaceDefect y s t) =
      fun t => s * (Real.exp (-s * t) - Real.exp (-s * t) * Real.cos ((2 * y) * t)) := by
    ext t
    simp only [laplaceDefect, neg_mul]
    ring
  rw [hfun, integral_const_mul, integral_sub he hc, integral_laplace_cos hs,
    integral_exp_mul_Ioi (neg_neg_of_pos hs)]
  have hden : s ^ 2 + (2 * y) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

lemma cosineMass_eq_rational_integral (y : ℝ) :
    cosineMass y = ∫ s in Ioi (0 : ℝ), (2 * y) ^ 2 / (s ^ 2 + (2 * y) ^ 2) := by
  calc
    cosineMass y = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), laplaceDefect y s t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (integral_laplaceDefect_left y ht).symm
    _ = ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), laplaceDefect y s t :=
      (integral_integral_swap (integrable_laplaceDefect y)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact integral_laplaceDefect_right y hs

lemma integral_scaled_cauchy {v : ℝ} (hv : 0 < v) :
    (∫ s in Ioi (0 : ℝ), v ^ 2 / (s ^ 2 + v ^ 2)) = v * (Real.pi / 2) := by
  have hfun : (fun s : ℝ => v ^ 2 / (s ^ 2 + v ^ 2)) =
      fun s => (1 + (v⁻¹ * s) ^ 2)⁻¹ := by
    ext s
    field_simp
    ring
  rw [hfun, integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 (inv_pos.mpr hv)]
  simp

lemma cosineMass_eq (y : ℝ) : cosineMass y = Real.pi * |y| := by
  by_cases hy : y = 0
  · simp [hy]
  have habs : (2 * y) ^ 2 = (2 * |y|) ^ 2 := by simp [mul_pow]
  rw [cosineMass_eq_rational_integral, habs,
    integral_scaled_cauchy (mul_pos (by norm_num) (abs_pos.mpr hy))]
  ring

end HaagerupIzumi.GammaIntegral
