module

public import HaagerupIzumi.Analytic.GammaFourierHolomorphic
import all Mathlib.Data.Complex.Basic

/-!
# The product candidate for the symmetric Fourier transform

In the convergence domain both gamma arguments remain strictly inside the
fundamental strip. The candidate is therefore nonzero and separately
holomorphic in its two complex parameters.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

def fourierCandidateOf (g : ℂ → ℂ) (a b : ℝ) (q y : ℂ) : ℂ :=
  g (((a : ℂ) + b) / 2 - q + I * y) * g (((a : ℂ) + b) / 2 - q - I * y)

def fourierCandidate (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) : ℂ :=
  fourierCandidateOf (gamma a b hb hba) a b q y

lemma candidate_args_in_strip {a b : ℝ} {q y : ℂ} (hq : 0 < q.re)
    (hconv : |y.im| < (a + b) / 2 - q.re) :
    (0 < (((a : ℂ) + b) / 2 - q + I * y).re ∧
      (((a : ℂ) + b) / 2 - q + I * y).re < a + b) ∧
    (0 < (((a : ℂ) + b) / 2 - q - I * y).re ∧
      (((a : ℂ) + b) / 2 - q - I * y).re < a + b) := by
  simp only [add_re, sub_re, div_ofNat_re, ofReal_re, I_mul_re]
  have hh := abs_lt.mp hconv
  constructor <;> constructor <;> linarith

theorem fourierCandidate_ne_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    fourierCandidate a b hb hba q y ≠ 0 := by
  have hh := candidate_args_in_strip hq hconv
  unfold fourierCandidate fourierCandidateOf
  rw [gamma_eq_on_strip a b hb hba _ hh.1.1 hh.1.2,
    gamma_eq_on_strip a b hb hba _ hh.2.1 hh.2.2]
  exact mul_ne_zero (GammaIntegral.gamma_ne_zero a b _) (GammaIntegral.gamma_ne_zero a b _)

theorem differentiableAt_fourierCandidate_q {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    DifferentiableAt ℂ (fun w => fourierCandidate a b hb hba w y) q := by
  have hh := candidate_args_in_strip hq hconv
  have h₁ := (analyticAt_gamma_of_re_pos hb hba hh.1.1).differentiableAt.comp q
    (show DifferentiableAt ℂ (fun w : ℂ => ((a : ℂ) + b) / 2 - w + I * y) q by fun_prop)
  have h₂ := (analyticAt_gamma_of_re_pos hb hba hh.2.1).differentiableAt.comp q
    (show DifferentiableAt ℂ (fun w : ℂ => ((a : ℂ) + b) / 2 - w - I * y) q by fun_prop)
  convert! h₁.mul h₂ using 1

theorem differentiableAt_fourierCandidate_y {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    DifferentiableAt ℂ (fun v => fourierCandidate a b hb hba q v) y := by
  have hh := candidate_args_in_strip hq hconv
  have h₁ := (analyticAt_gamma_of_re_pos hb hba hh.1.1).differentiableAt.comp y
    (show DifferentiableAt ℂ (fun v : ℂ => ((a : ℂ) + b) / 2 - q + I * v) y by fun_prop)
  have h₂ := (analyticAt_gamma_of_re_pos hb hba hh.2.1).differentiableAt.comp y
    (show DifferentiableAt ℂ (fun v : ℂ => ((a : ℂ) + b) / 2 - q - I * v) y by fun_prop)
  convert! h₁.mul h₂ using 1

end HaagerupIzumi.GammaContinuation
