module

import all Mathlib.Data.Complex.Basic

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-! # Absolutely convergent Fourier insertion

The mixed oscillatory exponential has modulus one. Thus two integrable
one-variable factors suffice for Fubini, with no Fourier inversion theorem.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory

namespace HaagerupIzumi.FourierInsertion

def phase (c t u : ℝ) : ℂ := Complex.exp (I * (c * t * u : ℝ))

lemma norm_phase (c t u : ℝ) : ‖phase c t u‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma continuous_phase (c : ℝ) : Continuous (fun p : ℝ × ℝ => phase c p.1 p.2) := by
  unfold phase
  fun_prop

lemma integrable_joint {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 * (phase c p.1 p.2 * g p.2))
      (volume.prod volume) := by
  apply (hf.mul_prod hg).mono
    (hf.aestronglyMeasurable.comp_fst.mul
      ((continuous_phase c).aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd))
  filter_upwards [] with p
  simp only [Pi.mul_apply, norm_mul, norm_phase, one_mul, le_refl]

/-- Interchanging an inserted inverse Fourier integral is justified by the
product of the two one-dimensional absolute integrals. -/
theorem integral_mul_integral_phase {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (c : ℝ) :
    (∫ t : ℝ, f t * (∫ u : ℝ, phase c t u * g u)) =
      ∫ u : ℝ, g u * (∫ t : ℝ, phase c t u * f t) := by
  calc
    _ = ∫ t : ℝ, ∫ u : ℝ, f t * (phase c t u * g u) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_const_mul]
    _ = ∫ u : ℝ, ∫ t : ℝ, f t * (phase c t u * g u) :=
      integral_integral_swap (integrable_joint hf hg c)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring

end HaagerupIzumi.FourierInsertion
