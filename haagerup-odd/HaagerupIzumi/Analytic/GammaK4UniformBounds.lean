module

public import HaagerupIzumi.Analytic.GammaKernelDecay
import all Mathlib.Data.Complex.Basic

/-!
# A parameter-uniform tail bound for the four-gamma kernel

Bounded gamma parameters and a common convergence margin give one
exponential majorant on every bounded vertical strip.
-/

@[expose] public section
noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaContinuation

theorem k4_norm_tail_uniform {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (R Q Y L U : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s x y : ℂ,
      ‖k4U a b r s‖ ≤ R → ‖k4V a b r s + x‖ ≤ R → ‖k4V a b r s - x‖ ≤ R →
      |y.im| ≤ Y → r.re + |y.re| ≤ Q → ∀ z : ℂ,
      L ≤ z.re → z.re ≤ U → R + 1 ≤ |z.im| →
      ‖k4Integrand (gamma a b hb hba.le) a b r s x y z‖ ≤
        C * Real.exp (-(2 * Real.pi * ((a + b) / 2 - Q) / (a * b)) * |z.im|) := by
  have hab : 0 < a * b := mul_pos (hb.trans hba) hb
  obtain ⟨B, hBpos, hB⟩ := norm_gamma_pair_uniform hb hba R L U
  let E := Real.exp ((2 * Real.pi * Y / (a * b)) * (|L| + |U|))
  refine ⟨E * (B * B), mul_pos (Real.exp_pos _) (mul_pos hBpos hBpos),
    fun r s x y hu hvp hvm hY hQ z hL hU hz => ?_⟩
  let u := k4U a b r s
  let v := k4V a b r s
  let lam : ℂ := 2 * Real.pi * I * y / ((a : ℂ) * b)
  have hlam_re : |lam.re| = 2 * Real.pi * |y.im| / (a * b) := by
    dsimp [lam]
    simp only [← ofReal_mul, div_ofReal_re, mul_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub,
      add_zero, zero_add, abs_div, abs_of_pos hab]
    norm_num [abs_mul, abs_of_pos Real.pi_pos]
  have hlam_im : |lam.im| = 2 * Real.pi * |y.re| / (a * b) := by
    dsimp [lam]
    simp only [← ofReal_mul, div_ofReal_im, mul_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub,
      add_zero, zero_add, abs_div, abs_of_pos hab]
    norm_num [abs_mul, abs_of_pos Real.pi_pos]
  have hlam_bound : |lam.re| ≤ 2 * Real.pi * Y / (a * b) := by
    rw [hlam_re]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hY (mul_nonneg (by norm_num) Real.pi_pos.le)) hab.le
  have hexp : ‖Complex.exp (lam * z)‖ ≤ E * Real.exp (|lam.im| * |z.im|) := by
    refine (norm_exp_mul_le lam z hL hU).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hlam_bound (add_nonneg (abs_nonneg L) (abs_nonneg U))
  have hp₁ := hB u u z hu hu hL hU hz
  have hp₂ := hB (v + x) (v - x) z hvp hvm hL hU hz
  have hpp := mul_le_mul hp₁ hp₂ (norm_nonneg _)
    (mul_nonneg hBpos.le (Real.exp_pos _).le)
  have htotal := mul_le_mul hexp hpp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have harg : k4Integrand (gamma a b hb hba.le) a b r s x y z =
      Complex.exp (lam * z) *
        (gamma a b hb hba.le (u + z) * gamma a b hb hba.le (u - z)) *
        (gamma a b hb hba.le ((v + x) + z) * gamma a b hb hba.le ((v - x) - z)) := by
    have hexparg : 2 * (Real.pi : ℂ) * I * y * z / ((a : ℂ) * b) = lam * z := by
      dsimp [lam]
      ring
    have hplus : v + z + x = (v + x) + z := by ring
    have hminus : v - z - x = (v - x) - z := by ring
    unfold k4Integrand
    change Complex.exp (2 * Real.pi * I * y * z / ((a : ℂ) * b)) *
      gamma a b hb hba.le (u + z) * gamma a b hb hba.le (u - z) *
      gamma a b hb hba.le (v + z + x) * gamma a b hb hba.le (v - z - x) = _
    rw [hexparg, hplus, hminus]
    ring
  rw [harg, norm_mul, norm_mul, mul_assoc]
  refine htotal.trans ?_
  have huvre : u.re + v.re = (a + b) / 2 + r.re := by
    dsimp [u, v, k4U, k4V]
    simp only [add_re, div_ofNat_re, ofReal_re, sub_re]
    ring
  calc
    _ = (E * (B * B)) * Real.exp (|lam.im| * |z.im| +
        Real.pi * (u.re + u.re - (a + b)) * |z.im| / (a * b) +
        Real.pi * ((v + x).re + (v - x).re - (a + b)) * |z.im| / (a * b)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = (E * (B * B)) * Real.exp
        (2 * Real.pi * (r.re + |y.re| - (a + b) / 2) * |z.im| / (a * b)) := by
      congr 2
      rw [hlam_im, add_re, sub_re]
      linear_combination (2 * Real.pi * |z.im| / (a * b)) * huvre
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le (mul_self_nonneg B))
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hQ ((a + b) / 2))
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)) (abs_nonneg z.im)
      exact (div_le_div_of_nonneg_right hh hab.le).trans_eq (by ring)

end HaagerupIzumi.GammaContinuation
