module

public import HaagerupIzumi.Analytic.GammaIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Symmetries and normalization of the defining gamma integral

These are identities of the explicit integral, independently of the convergence
proof. Their special-function interpretation is on `0 < re z < ω₁ + ω₂`;
extension outside that strip will be defined separately by recurrence.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace HaagerupIzumi.GammaIntegral

lemma center_reflection (ω₁ ω₂ : ℝ) (z : ℂ) :
    center ω₁ ω₂ ((ω₁ : ℂ) + ω₂ - z) = -center ω₁ ω₂ z := by
  unfold center
  ring

lemma integrand_reflection (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) :
    integrand ω₁ ω₂ ((ω₁ : ℂ) + ω₂ - z) t = -integrand ω₁ ω₂ z t := by
  simp only [integrand, center_reflection, neg_mul, Complex.sinh_neg, neg_div]
  ring

lemma logGamma_reflection (ω₁ ω₂ : ℝ) (z : ℂ) :
    logGamma ω₁ ω₂ ((ω₁ : ℂ) + ω₂ - z) = -logGamma ω₁ ω₂ z := by
  simp only [logGamma, integrand_reflection, integral_neg]

lemma gamma_reflection (ω₁ ω₂ : ℝ) (z : ℂ) :
    gamma ω₁ ω₂ z * gamma ω₁ ω₂ ((ω₁ : ℂ) + ω₂ - z) = 1 := by
  simp only [gamma, logGamma_reflection, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero]

lemma gamma_ne_zero (ω₁ ω₂ : ℝ) (z : ℂ) : gamma ω₁ ω₂ z ≠ 0 :=
  Complex.exp_ne_zero _

lemma integrand_midpoint (ω₁ ω₂ : ℝ) (t : ℝ) :
    integrand ω₁ ω₂ (((ω₁ : ℂ) + ω₂) / 2) t = 0 := by
  have hc : center ω₁ ω₂ (((ω₁ : ℂ) + ω₂) / 2) = 0 := by
    unfold center
    ring
  simp [integrand, hc]

lemma logGamma_midpoint (ω₁ ω₂ : ℝ) :
    logGamma ω₁ ω₂ (((ω₁ : ℂ) + ω₂) / 2) = 0 := by
  simp [logGamma, integrand_midpoint]

lemma gamma_midpoint (ω₁ ω₂ : ℝ) :
    gamma ω₁ ω₂ (((ω₁ : ℂ) + ω₂) / 2) = 1 := by
  simp [gamma, logGamma_midpoint]

lemma integrand_swap (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) :
    integrand ω₂ ω₁ z t = integrand ω₁ ω₂ z t := by
  have hc : center ω₂ ω₁ z = center ω₁ ω₂ z := by unfold center; ring
  simp only [integrand, hc]
  congr 2 <;> ring

lemma logGamma_swap (ω₁ ω₂ : ℝ) (z : ℂ) :
    logGamma ω₂ ω₁ z = logGamma ω₁ ω₂ z := by
  simp only [logGamma, integrand_swap]

lemma gamma_swap (ω₁ ω₂ : ℝ) (z : ℂ) : gamma ω₂ ω₁ z = gamma ω₁ ω₂ z := by
  simp only [gamma, logGamma_swap]

/-- The real kernel whose complexification is the defining kernel on the
real axis. Keeping the subtraction inside the kernel preserves regularization. -/
def realIntegrand (ω₁ ω₂ x t : ℝ) : ℝ :=
  (Real.sinh ((2 * x - (ω₁ + ω₂)) * t) /
      (2 * Real.sinh (ω₁ * t) * Real.sinh (ω₂ * t)) -
    (2 * x - (ω₁ + ω₂)) / (2 * ω₁ * ω₂ * t)) / t

lemma integrand_ofReal (ω₁ ω₂ x t : ℝ) :
    integrand ω₁ ω₂ x t = (realIntegrand ω₁ ω₂ x t : ℂ) := by
  simp [integrand, center, realIntegrand, Complex.ofReal_sinh]

lemma logGamma_ofReal (ω₁ ω₂ x : ℝ) :
    logGamma ω₁ ω₂ x = (-(∫ t in Ioi (0 : ℝ), realIntegrand ω₁ ω₂ x t) : ℝ) := by
  simp only [logGamma, integrand_ofReal, Complex.ofReal_neg]
  congr 1
  exact integral_complex_ofReal

lemma gamma_ofReal (ω₁ ω₂ x : ℝ) :
    gamma ω₁ ω₂ x =
      (Real.exp (-(∫ t in Ioi (0 : ℝ), realIntegrand ω₁ ω₂ x t)) : ℂ) := by
  rw [gamma, logGamma_ofReal, ← Complex.ofReal_exp]

lemma gamma_real_pos (ω₁ ω₂ x : ℝ) :
    0 < (gamma ω₁ ω₂ x).re ∧ (gamma ω₁ ω₂ x).im = 0 := by
  rw [gamma_ofReal]
  exact ⟨Real.exp_pos _, rfl⟩

lemma integrand_conj (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) :
    integrand ω₁ ω₂ (conj z) t = conj (integrand ω₁ ω₂ z t) := by
  norm_num [integrand, center, map_div₀, ← Complex.sinh_conj, Complex.conj_ofNat]

lemma logGamma_conj (ω₁ ω₂ : ℝ) (z : ℂ) :
    logGamma ω₁ ω₂ (conj z) = conj (logGamma ω₁ ω₂ z) := by
  simp only [logGamma, integrand_conj, integral_conj, map_neg]

lemma gamma_conj (ω₁ ω₂ : ℝ) (z : ℂ) :
    gamma ω₁ ω₂ (conj z) = conj (gamma ω₁ ω₂ z) := by
  simp only [gamma, logGamma_conj, Complex.exp_conj]

end HaagerupIzumi.GammaIntegral
