module

public import HaagerupIzumi.Analytic.GammaKernelBounds
import all Mathlib.Data.Complex.Basic

/-!
# Exact decay of the two- and four-gamma kernels

The convergence margins in the Fourier identities give positive exponential
decay rates uniformly on every bounded vertical strip.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaContinuation

lemma norm_exp_mul_le (lam z : ℂ) {L U : ℝ} (hL : L ≤ z.re) (hU : z.re ≤ U) :
    ‖Complex.exp (lam * z)‖ ≤
      Real.exp (|lam.re| * (|L| + |U|)) * Real.exp (|lam.im| * |z.im|) := by
  have hz : |z.re| ≤ |L| + |U| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le L, le_abs_self U, abs_nonneg L, abs_nonneg U]
  have hr : lam.re * z.re ≤ |lam.re| * (|L| + |U|) := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hi : -(lam.im * z.im) ≤ |lam.im| * |z.im| := by
    simpa only [abs_mul] using neg_le_abs (lam.im * z.im)
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Complex.mul_re]
  linarith

/-- General exponential multiplier times a pair of gamma factors. The real
coefficient in the last exponential is exact. -/
theorem two_gamma_kernel_bound {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (f h lam : ℂ) (L U : ℝ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ,
      L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖Complex.exp (lam * z) * gamma a b hb hba.le (f + z) * gamma a b hb hba.le (h - z)‖ ≤
        C * Real.exp ((|lam.im| + Real.pi * (f.re + h.re - (a + b)) / (a * b)) * |z.im|) := by
  let R := ‖f‖ + ‖h‖ + 1
  obtain ⟨B, hBpos, hB⟩ := norm_gamma_pair_uniform hb hba R L U
  let E := Real.exp (|lam.re| * (|L| + |U|))
  refine ⟨E * B, R + 1, mul_pos (Real.exp_pos _) hBpos, by dsimp [R]; positivity,
    fun z hL hU hz => ?_⟩
  have hpair := hB f h z (by dsimp [R]; linarith [norm_nonneg h])
    (by dsimp [R]; linarith [norm_nonneg f]) hL hU hz
  have hexp := norm_exp_mul_le lam z hL hU
  have hprod := mul_le_mul hexp hpair (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  rw [mul_assoc, norm_mul]
  refine hprod.trans_eq ?_
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

/-- Exponential decay on any bounded vertical strip for the centered
four-gamma kernel. The rate is the exact positive convergence margin. -/
theorem k4_tail_bound {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (r s x y : ℂ) (hconv : K4Conv a b r y) (L U : ℝ) :
    ∃ M c T : ℝ, 0 < M ∧ 0 < c ∧ 0 < T ∧ ∀ z : ℂ,
      L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖k4Integrand (gamma a b hb hba.le) a b r s x y z‖ ≤ M * Real.exp (-c * |z.im|) := by
  let u := k4U a b r s
  let v := k4V a b r s
  let lam : ℂ := 2 * Real.pi * I * y / ((a : ℂ) * b)
  let R := ‖u‖ + ‖v + x‖ + ‖v - x‖ + 1
  let c := 2 * Real.pi * ((a + b) / 2 - r.re - |y.re|) / (a * b)
  have hc : 0 < c := by
    apply div_pos _ (mul_pos (hb.trans hba) hb)
    apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
    exact sub_pos.mpr hconv
  obtain ⟨B, hBpos, hB⟩ := norm_gamma_pair_uniform hb hba R L U
  let E := Real.exp (|lam.re| * (|L| + |U|))
  refine ⟨E * (B * B), c, R + 1,
    mul_pos (Real.exp_pos _) (mul_pos hBpos hBpos), hc,
    by dsimp [R]; positivity, fun z hL hU hz => ?_⟩
  have hu : ‖u‖ ≤ R := by dsimp [R]; linarith [norm_nonneg (v + x), norm_nonneg (v - x)]
  have hvx : ‖v + x‖ ≤ R := by dsimp [R]; linarith [norm_nonneg u, norm_nonneg (v - x)]
  have hvx' : ‖v - x‖ ≤ R := by dsimp [R]; linarith [norm_nonneg u, norm_nonneg (v + x)]
  have hp₁ := hB u u z hu hu hL hU hz
  have hp₂ := hB (v + x) (v - x) z hvx hvx' hL hU hz
  have hpp := mul_le_mul hp₁ hp₂ (norm_nonneg _)
    (mul_nonneg hBpos.le (Real.exp_pos _).le)
  have hexp := norm_exp_mul_le lam z hL hU
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
  refine htotal.trans_eq ?_
  have hlam : |lam.im| = 2 * Real.pi * |y.re| / (a * b) := by
    dsimp [lam]
    simp only [← ofReal_mul, div_ofReal_im, mul_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub,
      add_zero, zero_add, abs_div,
      abs_of_pos (mul_pos (hb.trans hba) hb)]
    norm_num [abs_mul, abs_of_pos Real.pi_pos]
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
    _ = _ := by
      congr 2
      rw [hlam, add_re, sub_re]
      dsimp [c]
      linear_combination (2 * Real.pi * |z.im| / (a * b)) * huvre

end HaagerupIzumi.GammaContinuation
