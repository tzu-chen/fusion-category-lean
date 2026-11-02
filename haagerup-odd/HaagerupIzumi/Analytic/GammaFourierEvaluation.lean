module

public import HaagerupIzumi.Analytic.GammaFourierScale
public import HaagerupIzumi.Analytic.GammaFourierNormalization
import all Mathlib.Data.Complex.Basic

/-!
# The symmetric two-gamma Fourier evaluation

The normalized factor is constant by its half-periods. The elementary
sech integral at the half first period fixes that constant to `sqrt (a*b)`.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory
open HaagerupIzumi.GammaPeriodUniqueness

namespace HaagerupIzumi.GammaContinuation

lemma symmetricTransform_at_half_first (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    symmetricTransform a b hb hba ((a : ℂ) / 2) 0 = (a : ℂ) / 2 := by
  unfold symmetricTransform symmetricIntegrand
  simp only [mul_zero, zero_mul, zero_div, Complex.exp_zero, one_mul]
  exact integral_gamma_half_period_pair a b hb hba

lemma fourierCandidate_at_half_first (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    fourierCandidate a b hb hba ((a : ℂ) / 2) 0 = (1 : ℂ) / 2 := by
  unfold fourierCandidate fourierCandidateOf
  simp only [mul_zero, add_zero, sub_zero]
  rw [show ((a : ℂ) + b) / 2 - a / 2 = (b : ℂ) / 2 by ring, ← pow_two]
  exact gamma_half_second_period_sq a b hb hba

lemma normalizedFourierScale_at_half_first (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    normalizedFourierScale a b hb hba ((a : ℂ) / 2) = (Real.sqrt (a * b) : ℂ) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hsqrt : a / Real.sqrt (a / b) = Real.sqrt (a * b) := by
    rw [Real.sqrt_div ha.le, div_div_eq_mul_div]
    calc
      a * Real.sqrt b / Real.sqrt a = (a / Real.sqrt a) * Real.sqrt b := by ring
      _ = Real.sqrt a * Real.sqrt b := by rw [Real.div_sqrt]
      _ = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm
  unfold normalizedFourierScale fourierScale fourierQuotient
  rw [symmetricTransform_at_half_first, fourierCandidate_at_half_first,
    show 2 * ((a : ℂ) / 2) = a by ring, gamma_at_first_period_global]
  have hdiv : ((a : ℂ) / 2 / (1 / 2)) = a := by ring
  rw [hdiv, ← Complex.ofReal_div, hsqrt]

/-- The symmetric hyperbolic beta/Fourier integral, with its exact constant,
constructed from the regularized hyperbolic-gamma integral. -/
theorem symmetricTransform_evaluation {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q y : ℂ} (hq : 0 < q.re)
    (hy : |y.im| < (a + b) / 2 - q.re) :
    symmetricTransform a b hb hba.le q y =
      (Real.sqrt (a * b) : ℂ) * gamma a b hb hba.le (2 * q) *
        fourierCandidate a b hb hba.le q y := by
  have hqΩ : q.re < (a + b) / 2 := by linarith [abs_nonneg y.im]
  have hhalf : ((a : ℂ) / 2) ∈ strip ((a + b) / 2) := by
    constructor <;> simp only [div_ofNat_re, ofReal_re] <;> linarith
  have hE := normalizedFourierScale_eq hb hba hirr ⟨hq, hqΩ⟩ hhalf
  rw [normalizedFourierScale_at_half_first] at hE
  have hD := (div_eq_iff (gamma_two_mul_ne_zero hb hba.le hq hqΩ)).mp hE
  rw [symmetricTransform_eq_scale_mul hb hba hirr hq hy, hD]

end HaagerupIzumi.GammaContinuation
