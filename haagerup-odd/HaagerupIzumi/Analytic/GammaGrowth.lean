module

public import HaagerupIzumi.Analytic.GammaModulusUniform
public import HaagerupIzumi.Analytic.GammaCosine
import all Mathlib.Data.Complex.Basic

/-!
# Exact vertical growth inside the defining strip

Only the modulus is estimated. The universal cosine integral fixes its exact
linear exponent, and the uniform remainder controls the multiplicative error.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaIntegral

def verticalExponent (ω₁ ω₂ x y : ℝ) : ℝ :=
  Real.pi * (x - (ω₁ + ω₂) / 2) * |y| / (ω₁ * ω₂)

lemma modulusSlope_mul_cosineMass (ω₁ ω₂ x y : ℝ) :
    modulusSlope ω₁ ω₂ x * cosineMass y = verticalExponent ω₁ ω₂ x y := by
  rw [cosineMass_eq]
  simp only [modulusSlope, verticalExponent, div_eq_mul_inv, mul_inv]
  ring

theorem log_norm_gamma_vertical_uniform_exact {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ,
      |Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ - verticalExponent ω₁ ω₂ x y| ≤ C := by
  obtain ⟨C, hC⟩ := log_norm_gamma_vertical_uniform hω₁ hω₂ ha hb
  refine ⟨C, fun x hx y => ?_⟩
  simpa only [modulusSlope_mul_cosineMass] using hC x hx y

theorem norm_gamma_vertical_bounds {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ y : ℝ,
      Real.exp (-C) * Real.exp (verticalExponent ω₁ ω₂ x y) ≤
        ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ ∧
      ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ ≤
        Real.exp C * Real.exp (verticalExponent ω₁ ω₂ x y) := by
  obtain ⟨C, hC⟩ := log_norm_gamma_vertical_uniform_exact hω₁ hω₂ ha hb
  refine ⟨|C|, abs_nonneg C, fun x hx y => ?_⟩
  have he := (hC x hx y).trans (le_abs_self C)
  have hpos : 0 < ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ :=
    norm_pos_iff.mpr (gamma_ne_zero ω₁ ω₂ _)
  constructor
  · calc
      Real.exp (-|C|) * Real.exp (verticalExponent ω₁ ω₂ x y) =
          Real.exp (-|C| + verticalExponent ω₁ ω₂ x y) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).1])
      _ = _ := Real.exp_log hpos
  · calc
      ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ =
          Real.exp (Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (|C| + verticalExponent ω₁ ω₂ x y) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).2])
      _ = _ := Real.exp_add _ _

lemma verticalExponent_add_sub (ω₁ ω₂ x c y : ℝ) :
    verticalExponent ω₁ ω₂ (x + c) y - verticalExponent ω₁ ω₂ x y =
      Real.pi * c * |y| / (ω₁ * ω₂) := by
  unfold verticalExponent
  ring

/-- Exact-rate ratio control whenever both arguments remain in a fixed
compact substrip. This holds for every height, with no asymptotic threshold. -/
theorem ratio_bound_in_strip {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ x c y : ℝ, x ∈ Icc a b → x + c ∈ Icc a b →
      ‖gamma ω₁ ω₂ (((x + c : ℝ) : ℂ) + y * I)‖ ≤
        C * Real.exp (Real.pi * c * |y| / (ω₁ * ω₂)) *
          ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ := by
  obtain ⟨B, hB⟩ := log_norm_gamma_vertical_uniform_exact hω₁ hω₂ ha hb
  refine ⟨Real.exp (2 * B), Real.exp_pos _, fun x c y hx hxc => ?_⟩
  have h₀ := hB x hx y
  have h₁ := hB (x + c) hxc y
  have hdiff := verticalExponent_add_sub ω₁ ω₂ x c y
  have hlog : Real.log ‖gamma ω₁ ω₂ (((x + c : ℝ) : ℂ) + y * I)‖ ≤
      Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ +
        Real.pi * c * |y| / (ω₁ * ω₂) + 2 * B := by
    linarith [(abs_le.mp h₀).1, (abs_le.mp h₁).2]
  have hp₀ : 0 < ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ :=
    norm_pos_iff.mpr (gamma_ne_zero ω₁ ω₂ _)
  have hp₁ : 0 < ‖gamma ω₁ ω₂ (((x + c : ℝ) : ℂ) + y * I)‖ :=
    norm_pos_iff.mpr (gamma_ne_zero ω₁ ω₂ _)
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp₁, Real.exp_add, Real.exp_add, Real.exp_log hp₀] at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

end HaagerupIzumi.GammaIntegral
