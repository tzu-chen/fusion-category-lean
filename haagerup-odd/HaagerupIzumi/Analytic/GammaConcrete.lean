module

public import HaagerupIzumi.Analytic.GammaGlobalGrowth
public import HaagerupIzumi.Analytic.Periods

/-!
# The gamma function for the odd-order construction

The prescribed periods have an irrational ratio and a strict ordering.
Thus the explicit finite-product continuation and its global growth bound
apply to them, without an assumed hyperbolic-gamma object.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi

namespace Periods

lemma ω₂_lt_ω₁ (n : ℕ) (hn : 1 ≤ n) : ω₂ n < ω₁ n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  linarith [ω₁_sub_ω₂ n]

lemma ω₁_div_ω₂ (n : ℕ) : ω₁ n / ω₂ n = d n := by
  apply (div_eq_iff (ω₂_pos n).ne').mpr
  unfold ω₁ ω₂
  have hd := d_ne_zero n
  field_simp

lemma irrational_period_ratio (n : ℕ) (hn : 1 ≤ n) : Irrational (ω₁ n / ω₂ n) := by
  rw [ω₁_div_ω₂]
  exact irrational_d n hn

end Periods

open Periods

/-- The actual gamma function used by the odd-order construction. -/
def ruijsenaarsGamma (n : ℕ) (hn : 1 ≤ n) : ℂ → ℂ :=
  GammaContinuation.gamma (ω₁ n) (ω₂ n) (ω₂_pos n) (ω₂_lt_ω₁ n hn).le

lemma ruijsenaarsGamma_eq_integral (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz₀ : 0 < z.re) (hz₁ : z.re < ω₁ n + ω₂ n) :
    ruijsenaarsGamma n hn z = GammaIntegral.gamma (ω₁ n) (ω₂ n) z :=
  GammaContinuation.gamma_eq_on_strip _ _ _ _ z hz₀ hz₁

lemma ruijsenaarsGamma_differentiableOn (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableOn ℂ (ruijsenaarsGamma n hn) (poleSet (ω₁ n) (ω₂ n))ᶜ := by
  intro z hz
  exact (GammaContinuation.gamma_differentiableAt _ _ _ _ z hz).differentiableWithinAt

lemma ruijsenaarsGamma_real_pos (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx₀ : 0 < x) (hx₁ : x < ω₁ n + ω₂ n) :
    0 < (ruijsenaarsGamma n hn x).re ∧ (ruijsenaarsGamma n hn x).im = 0 :=
  GammaContinuation.gamma_real_pos _ _ _ _ x hx₀ hx₁

lemma ruijsenaarsGamma_real_axis (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (ruijsenaarsGamma n hn x).im = 0 :=
  GammaContinuation.gamma_real_axis _ _ _ _ x

lemma ruijsenaarsGamma_ratio_bound (n : ℕ) (hn : 1 ≤ n) (c L U : ℝ) :
    ∃ C T : ℝ, 0 < T ∧ ∀ z : ℂ, L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖ruijsenaarsGamma n hn (z + c)‖ ≤
        C * Real.exp (Real.pi * c * |z.im| / (ω₁ n * ω₂ n)) * ‖ruijsenaarsGamma n hn z‖ :=
  GammaContinuation.ratio_bound (ω₂_pos n) (ω₂_lt_ω₁ n hn) c L U

end HaagerupIzumi
