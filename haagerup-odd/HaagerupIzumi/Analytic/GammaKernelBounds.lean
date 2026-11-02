module

public import HaagerupIzumi.Analytic.GammaGlobalGrowth
public import HaagerupIzumi.Analytic.HypGamma
import all Mathlib.Data.Complex.Basic

/-!
# Decay of gamma integral kernels

The bounded logarithmic error remains uniform under bounded imaginary shifts.
This yields exact exponential decay for the two- and four-gamma kernels without
requiring a complex phase asymptotic expansion.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaContinuation

lemma abs_verticalExponent_shift_sub_le {a b L U M x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : L ≤ x) (hU : x ≤ U) (hy : |y| ≤ M)
    (t : ℝ) :
    |GammaIntegral.verticalExponent a b x (t + y) -
      GammaIntegral.verticalExponent a b x t| ≤
      Real.pi * (|L| + |U| + |(a + b) / 2|) * M / (a * b) := by
  have hx : |x| ≤ |L| + |U| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le L, le_abs_self U, abs_nonneg L, abs_nonneg U]
  have hcoef : |x - (a + b) / 2| ≤ |L| + |U| + |(a + b) / 2| :=
    (abs_sub _ _).trans (add_le_add hx le_rfl)
  have hdiff : |(|t + y|) - (|t|)| ≤ M := by
    have hh : |(|t + y|) - (|t|)| ≤ |y| := by
      simpa using abs_abs_sub_abs_le_abs_sub (t + y) t
    exact hh.trans hy
  have heq : GammaIntegral.verticalExponent a b x (t + y) -
      GammaIntegral.verticalExponent a b x t =
      Real.pi * (x - (a + b) / 2) * (|t + y| - |t|) / (a * b) := by
    unfold GammaIntegral.verticalExponent
    ring
  rw [heq, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (mul_pos ha hb)]
  apply div_le_div_of_nonneg_right _ (mul_pos ha hb).le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hcoef Real.pi_pos.le) hdiff
    (abs_nonneg _) (mul_nonneg Real.pi_pos.le (by positivity))

/-- Uniform growth on a bounded vertical strip, allowing any imaginary shift
of size at most `M`. The constant is independent of all three real variables. -/
theorem norm_gamma_vertical_shift_uniform {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (L U M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y t : ℝ, L ≤ x → x ≤ U → |y| ≤ M →
      M + 1 ≤ |t| →
      ‖gamma a b hb hba.le ((x : ℂ) + (t + y) * I)‖ ≤
        C * Real.exp (GammaIntegral.verticalExponent a b x t) := by
  obtain ⟨B, hB⟩ := log_norm_gamma_uniform hb hba L U
  let E := Real.pi * (|L| + |U| + |(a + b) / 2|) * M / (a * b)
  refine ⟨Real.exp (B + E), Real.exp_pos _, fun x y t hxL hxU hy ht => ?_⟩
  have hheight : 1 ≤ |t + y| := by
    have hh : |t| ≤ |t + y| + |y| := by simpa using abs_sub (t + y) y
    linarith
  have hh := hB ((x : ℂ) + (t + y) * I) (by simpa using hxL)
    (by simpa using hxU) (by simpa using hheight)
  have hd := abs_verticalExponent_shift_sub_le (hb.trans hba) hb hxL hxU hy t
  have hlog : Real.log ‖gamma a b hb hba.le ((x : ℂ) + (t + y) * I)‖ ≤
      B + E + GammaIntegral.verticalExponent a b x t := by
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add] at hh
    linarith [(abs_le.mp hh).2, (abs_le.mp hd).2]
  have hpos : 0 < ‖gamma a b hb hba.le ((x : ℂ) + (t + y) * I)‖ := by
    apply norm_pos_iff.mpr
    apply gamma_ne_zero_of_im_ne_zero a b hb hba.le
    have : t + y ≠ 0 := by intro h; norm_num [h] at hheight
    simpa using this
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos, Real.exp_add] at hexp
  exact hexp

lemma abs_re_le_of_norm_le {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : |z.re| ≤ R :=
  (Complex.abs_re_le_norm z).trans hz

lemma abs_im_le_of_norm_le {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : |z.im| ≤ R :=
  (Complex.abs_im_le_norm z).trans hz

/-- A pair of oppositely shifted gamma factors has a uniform bound for bounded
parameters and bounded real parts of the integration variable. -/
theorem norm_gamma_pair_uniform {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (R L U : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f h z : ℂ, ‖f‖ ≤ R → ‖h‖ ≤ R →
      L ≤ z.re → z.re ≤ U → R + 1 ≤ |z.im| →
      ‖gamma a b hb hba.le (f + z) * gamma a b hb hba.le (h - z)‖ ≤
        C * Real.exp (Real.pi * (f.re + h.re - (a + b)) * |z.im| / (a * b)) := by
  obtain ⟨B, hBpos, hB⟩ := norm_gamma_vertical_shift_uniform hb hba
    (min (L - R) (-U - R)) (max (U + R) (-L + R)) R
  refine ⟨B * B, mul_pos hBpos hBpos, fun f h z hf hh hL hU hz => ?_⟩
  have hfr := abs_le.mp (abs_re_le_of_norm_le hf)
  have hhr := abs_le.mp (abs_re_le_of_norm_le hh)
  have hfbound := hB (f.re + z.re) f.im z.im
    ((min_le_left _ _).trans (by linarith))
    ((show f.re + z.re ≤ U + R by linarith).trans (le_max_left _ _))
    (abs_im_le_of_norm_le hf) hz
  have hhbound := hB (h.re - z.re) h.im (-z.im)
    ((min_le_right _ _).trans (by linarith))
    ((show h.re - z.re ≤ -L + R by linarith).trans (le_max_right _ _))
    (abs_im_le_of_norm_le hh) (by simpa only [abs_neg] using hz)
  have hfarg : ((f.re + z.re : ℝ) : ℂ) + (z.im + f.im) * I = f + z := by
    apply Complex.ext <;> simp
    ring
  have hharg : ((h.re - z.re : ℝ) : ℂ) + (-z.im + h.im) * I = h - z := by
    apply Complex.ext <;> simp
    ring
  rw [hfarg] at hfbound
  simp only [Complex.ofReal_neg] at hhbound
  rw [hharg] at hhbound
  have hprod := mul_le_mul hfbound hhbound (norm_nonneg _)
    (mul_nonneg hBpos.le (Real.exp_pos _).le)
  rw [norm_mul]
  refine hprod.trans_eq ?_
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  unfold GammaIntegral.verticalExponent
  rw [abs_neg]
  ring

end HaagerupIzumi.GammaContinuation
