module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
import all Mathlib.Data.Complex.Basic

/-!
# Uniform growth of the sine factors in the gamma shifts

All estimates are independent of the real part. A positive distance from the
real axis gives a two-sided exponential bound and a bounded logarithmic error.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaIntegral

lemma norm_two_sin_bounds (w : ℂ) :
    Real.exp |w.im| - Real.exp (-|w.im|) ≤ ‖2 * Complex.sin w‖ ∧
    ‖2 * Complex.sin w‖ ≤ Real.exp |w.im| + Real.exp (-|w.im|) := by
  have hn : ‖2 * Complex.sin w‖ =
      ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  have hlo := abs_norm_sub_norm_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  have hhi := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  simp only [Complex.norm_exp] at hlo hhi
  have hre₁ : (-w * I).re = w.im := by simp
  have hre₂ : (w * I).re = -w.im := by simp
  rw [hre₁, hre₂] at hlo hhi
  rw [hn]
  rcases le_total 0 w.im with hw | hw
  · have he : Real.exp (-w.im) ≤ Real.exp w.im := Real.exp_le_exp.mpr (by linarith)
    simpa only [abs_of_nonneg hw, abs_of_nonneg (sub_nonneg.mpr he)] using And.intro hlo hhi
  · have he : Real.exp w.im ≤ Real.exp (-w.im) := Real.exp_le_exp.mpr (by linarith)
    constructor
    · simpa only [abs_of_nonpos hw, neg_neg, abs_of_nonpos (sub_nonpos.mpr he),
        neg_sub] using hlo
    · simpa only [abs_of_nonpos hw, neg_neg, add_comm] using hhi

lemma norm_two_sin_ge_exp {ε : ℝ} {w : ℂ} (hw : ε ≤ |w.im|) :
    (1 - Real.exp (-2 * ε)) * Real.exp |w.im| ≤ ‖2 * Complex.sin w‖ := by
  have he : Real.exp (-2 * |w.im|) ≤ Real.exp (-2 * ε) :=
    Real.exp_le_exp.mpr (by linarith)
  have hidentity : Real.exp (-|w.im|) = Real.exp |w.im| * Real.exp (-2 * |w.im|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlo := (norm_two_sin_bounds w).1
  rw [hidentity] at hlo
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos |w.im|).le
  nlinarith

lemma norm_two_sin_le_exp (w : ℂ) : ‖2 * Complex.sin w‖ ≤ 2 * Real.exp |w.im| := by
  have he : Real.exp (-|w.im|) ≤ Real.exp |w.im| :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg w.im])
  have hh := (norm_two_sin_bounds w).2
  linarith

lemma exists_log_two_sin_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ε ≤ |w.im| →
      |Real.log ‖2 * Complex.sin w‖ - (|w.im|)| ≤ C := by
  let d := 1 - Real.exp (-2 * ε)
  have hd : 0 < d := by
    have := Real.exp_lt_one_iff.mpr (show -2 * ε < 0 by linarith)
    dsimp [d]
    linarith
  refine ⟨|Real.log d| + |Real.log 2|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro w hw
  have hl := norm_two_sin_ge_exp hw
  have hu := norm_two_sin_le_exp w
  have hnorm : 0 < ‖2 * Complex.sin w‖ := (mul_pos hd (Real.exp_pos _)).trans_le hl
  have hlogl := Real.log_le_log (mul_pos hd (Real.exp_pos _)) hl
  have hlogu := Real.log_le_log hnorm hu
  rw [Real.log_mul hd.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlogu
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log d), abs_nonneg (Real.log 2)]
  · linarith [le_abs_self (Real.log 2), abs_nonneg (Real.log d)]

/-- Uniform logarithmic control of the sine factor in a hyperbolic-gamma
shift, at all heights at least one. -/
theorem exists_log_sine_bound {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ |z.im| →
      |Real.log ‖2 * Complex.sin (Real.pi * z / a)‖ - Real.pi * |z.im| / a| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_log_two_sin_bound (div_pos Real.pi_pos ha)
  refine ⟨C, hC, fun z hz => ?_⟩
  have him : |((Real.pi : ℂ) * z / a).im| = Real.pi * |z.im| / a := by
    simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, abs_div, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos ha]
  have hheight : Real.pi / a ≤ |((Real.pi : ℂ) * z / a).im| := by
    rw [him]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith [Real.pi_pos]
  simpa only [him] using hb ((Real.pi : ℂ) * z / a) hheight

end HaagerupIzumi.GammaIntegral
