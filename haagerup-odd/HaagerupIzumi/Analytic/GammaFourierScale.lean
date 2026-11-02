module

public import HaagerupIzumi.Analytic.GammaFourierProportional
public import HaagerupIzumi.Analytic.GammaFourierCandidateQShift
public import HaagerupIzumi.Analytic.GammaTwoCenter
import all Mathlib.Data.Complex.Basic

/-!
# Constancy of the normalized Fourier factor

Dividing the remaining factor by `gamma (2*q)` gives a holomorphic function
with the two half-periods. The same local-period uniqueness theorem removes
this last parameter dependence.
-/

@[expose] public section
noncomputable section

open Complex Set
open HaagerupIzumi.GammaPeriodUniqueness

namespace HaagerupIzumi.GammaContinuation

def normalizedFourierScale (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q : ℂ) : ℂ :=
  fourierScale a b hb hba q / gamma a b hb hba (2 * q)

lemma differentiableAt_normalizedFourierScale {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q : ℂ} (hq : 0 < q.re) (hqΩ : q.re < (a + b) / 2) :
    DifferentiableAt ℂ (normalizedFourierScale a b hb hba.le) q := by
  have hp : 0 < (2 * q).re := by simp; linarith
  have hd := (analyticAt_gamma_of_re_pos hb hba.le hp).differentiableAt.comp q
    (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) q by fun_prop)
  exact (differentiableAt_fourierScale hb hba hq hqΩ).div hd
    (gamma_two_mul_ne_zero hb hba.le hq hqΩ)

lemma normalizedFourierScale_period_of_shift {a b A B : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) (hA : 0 < A) (hB : 0 < B)
    (hprod : a * b = A * B) (_hsum : a + b = A + B)
    (hshift : ∀ z : ℂ, z ∉ poleLattice a b →
      gamma a b hb hba.le (z + A) = factor B z * gamma a b hb hba.le z)
    (q : ℂ) (hq : 0 < q.re) (hqA : (q + (A : ℂ) / 2).re < (a + b) / 2)
    (hC : Complex.exp (Real.pi * I * q / B) * fourierCandidate a b hb hba.le q (A * I / 2) -
        Complex.exp (-(Real.pi * I * q / B)) * fourierCandidate a b hb hba.le q (-(A * I / 2)) =
      I * factor B (2 * q) * fourierCandidate a b hb hba.le (q + A / 2) 0) :
    normalizedFourierScale a b hb hba.le (q + A / 2) = normalizedFourierScale a b hb hba.le q := by
  have hqaRe : (q + (A : ℂ) / 2).re = q.re + A / 2 := by simp
  have hqΩ : q.re < (a + b) / 2 := by rw [hqaRe] at hqA; linarith
  have hqAp : 0 < (q + (A : ℂ) / 2).re := by rw [hqaRe]; positivity
  have hconv : |(0 : ℂ).im| < (a + b - q.re - q.re - A) / 2 := by
    rw [hqaRe] at hqA
    simp
    linarith
  have hyP : |((A : ℂ) * I / 2).im| < (a + b) / 2 - q.re := by
    rw [hqaRe] at hqA
    simpa only [div_ofNat_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero, abs_of_pos (half_pos hA)] using (by linarith : A / 2 < (a + b) / 2 - q.re)
  have hyM : |(-(A : ℂ) * I / 2).im| < (a + b) / 2 - q.re := by
    simpa only [neg_mul, neg_div, neg_im, abs_neg] using hyP
  have hzero : |(0 : ℂ).im| < (a + b) / 2 - (q + (A : ℂ) / 2).re := by simp; linarith
  have ht := GammaTwoFourier.transform_shift_first hb hba.le hB.ne' hprod hshift hba hA q q 0
    hq hq hconv
  have hc := GammaTwoFourier.transform_eq_symmetric a b hb hba (q + A) q 0
    (by simp; linarith) hq (by
      simp only [zero_im, abs_zero, add_re, ofReal_re]
      rw [hqaRe] at hqA
      linarith)
  have hmid : GammaTwoFourier.midpoint (q + A) q = q + (A : ℂ) / 2 := by
    unfold GammaTwoFourier.midpoint
    ring
  simp only [mul_zero, zero_div, Complex.exp_zero, one_mul, hmid] at hc
  rw [hc, GammaTwoFourier.transform_diag_eq_symmetricTransform,
    GammaTwoFourier.transform_diag_eq_symmetricTransform] at ht
  simp only [zero_add, zero_sub] at ht
  rw [symmetricTransform_eq_scale_mul hb hba hirr hqAp hzero,
    symmetricTransform_eq_scale_mul hb hba hirr hq hyP,
    symmetricTransform_eq_scale_mul hb hba hirr hq (by simpa only [neg_mul, neg_div] using hyM)] at ht
  have hscale : fourierScale a b hb hba.le (q + A / 2) =
      factor B (2 * q) * fourierScale a b hb hba.le q := by
    apply mul_left_cancel₀ (mul_ne_zero I_ne_zero (fourierCandidate_ne_zero hb hba.le hqAp hzero))
    linear_combination ht + fourierScale a b hb hba.le q * hC
  unfold normalizedFourierScale
  apply (div_eq_div_iff (gamma_two_mul_ne_zero hb hba.le hqAp hqA)
    (gamma_two_mul_ne_zero hb hba.le hq hqΩ)).2
  rw [hscale, show 2 * (q + (A : ℂ) / 2) = 2 * q + A by ring,
    hshift _ (not_mem_poleLattice_of_re_pos (hb.trans hba) hb (by simp; linarith))]
  ring

lemma normalizedFourierScale_period_first {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q : ℂ} (hq : 0 < q.re)
    (hqA : (q + (a : ℂ) / 2).re < (a + b) / 2) :
    normalizedFourierScale a b hb hba.le (q + a / 2) = normalizedFourierScale a b hb hba.le q := by
  apply normalizedFourierScale_period_of_shift hb hba hirr (hb.trans hba) hb rfl rfl
    (fun z hz => gamma_shift₁ a b hb hba.le z hz) q hq hqA
  have hc : |(0 : ℂ).im| < b / 2 - q.re := by
    simp only [add_re, div_ofNat_re, ofReal_re] at hqA
    simp
    linarith
  simpa only [zero_add, zero_sub, mul_zero, zero_div, neg_zero, Complex.exp_zero, mul_one]
    using fourierCandidate_q_shift_first hb hba.le q 0 hc

lemma normalizedFourierScale_period_second {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q : ℂ} (hq : 0 < q.re)
    (hqB : (q + (b : ℂ) / 2).re < (a + b) / 2) :
    normalizedFourierScale a b hb hba.le (q + b / 2) = normalizedFourierScale a b hb hba.le q := by
  apply normalizedFourierScale_period_of_shift hb hba hirr hb (hb.trans hba) (mul_comm a b) (add_comm a b)
    (fun z hz => gamma_shift₂ a b hb hba.le z hz) q hq hqB
  have hc : |(0 : ℂ).im| < a / 2 - q.re := by
    simp only [add_re, div_ofNat_re, ofReal_re] at hqB
    simp
    linarith
  simpa only [zero_add, zero_sub, mul_zero, zero_div, neg_zero, Complex.exp_zero, mul_one]
    using fourierCandidate_q_shift_second hb hba.le q 0 hc

theorem normalizedFourierScale_eq {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q w : ℂ}
    (hq : q ∈ strip ((a + b) / 2)) (hw : w ∈ strip ((a + b) / 2)) :
    normalizedFourierScale a b hb hba.le q = normalizedFourierScale a b hb hba.le w := by
  have hirr' : Irrational ((a / 2) / (b / 2)) := by
    rw [show (a / 2) / (b / 2) = a / b by ring]
    exact hirr
  apply eq_of_local_periods (half_pos (hb.trans hba)) (half_pos hb)
    (by linarith) (by linarith) hirr' ?_ ?_ ?_ hq hw
  · intro z hz
    exact (differentiableAt_normalizedFourierScale hb hba hz.1 hz.2).differentiableWithinAt
  · intro z hz hza
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      normalizedFourierScale_period_first hb hba hirr hz.1
        (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hza.2)
  · intro z hz hzb
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      normalizedFourierScale_period_second hb hba hirr hz.1
        (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hzb.2)

end HaagerupIzumi.GammaContinuation
