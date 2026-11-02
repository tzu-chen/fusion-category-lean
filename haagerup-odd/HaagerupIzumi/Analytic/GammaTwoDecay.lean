module

public import HaagerupIzumi.Analytic.GammaKernelDecay
import all Mathlib.Data.Complex.Basic

/-!
# The convergence range of the two-gamma Fourier transform

Both strict inequalities on the Fourier parameter yield exponential decay at
the two ends of every bounded vertical strip.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

theorem two_gamma_tail_bound {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (f h α : ℂ) (hα₀ : 0 < α.re) (hα₁ : α.re < ((a : ℂ) + b - h - f).re)
    (L U : ℝ) :
    ∃ M c T : ℝ, 0 < M ∧ 0 < c ∧ 0 < T ∧ ∀ z : ℂ,
      L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖Complex.exp (Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b)) *
        gamma a b hb hba.le (f + z) * gamma a b hb hba.le (h - z)‖ ≤
          M * Real.exp (-c * |z.im|) := by
  let lam : ℂ := Real.pi * I * (2 * α + h + f - a - b) / ((a : ℂ) * b)
  let q := |lam.im| + Real.pi * (f.re + h.re - (a + b)) / (a * b)
  have hab : 0 < a * b := mul_pos (hb.trans hba) hb
  have hlam : lam.im = Real.pi * (2 * α.re + h.re + f.re - a - b) / (a * b) := by
    dsimp [lam]
    simp only [← ofReal_mul, div_ofReal_im, mul_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, zero_mul, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, add_re, sub_re]
    norm_num
  have hα₁' : α.re < a + b - h.re - f.re := by simpa using hα₁
  have hmiddle : |2 * α.re + h.re + f.re - a - b| < a + b - h.re - f.re := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hq : q < 0 := by
    dsimp [q]
    rw [hlam, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hab]
    have hn : Real.pi * |2 * α.re + h.re + f.re - a - b| +
        Real.pi * (f.re + h.re - (a + b)) < 0 := by
      nlinarith [Real.pi_pos]
    rw [← add_div]
    exact div_neg_of_neg_of_pos hn hab
  obtain ⟨M, T, hM, hT, hbound⟩ := two_gamma_kernel_bound hb hba f h lam L U
  refine ⟨M, -q, T, hM, neg_pos.mpr hq, hT, fun z hL hU hz => ?_⟩
  have harg : Real.pi * I * z * (2 * α + h + f - a - b) / ((a : ℂ) * b) = lam * z := by
    dsimp [lam]
    ring
  rw [harg, neg_neg]
  exact hbound z hL hU hz

end HaagerupIzumi.GammaContinuation
