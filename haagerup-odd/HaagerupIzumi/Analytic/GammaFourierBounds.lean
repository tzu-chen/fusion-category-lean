module

public import HaagerupIzumi.Analytic.GammaKernelDecay
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import all Mathlib.Data.Complex.Basic

/-!
# The symmetric two-gamma Fourier integral

This module defines the actual integral and supplies an integrable bound that
is uniform over compact parameter sets inside its convergence domain.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace HaagerupIzumi.GammaContinuation

def symmetricIntegrand (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * y * t / ((a : ℂ) * b)) *
    gamma a b hb hba (q + t * I) * gamma a b hb hba (q - t * I)

def symmetricTransform (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) : ℂ :=
  ∫ t : ℝ, symmetricIntegrand a b hb hba q y t

lemma analyticAt_gamma_of_re_pos {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ (gamma a b hb hba) z := by
  have hd : DifferentiableOn ℂ (gamma a b hb hba) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (gamma_differentiableAt a b hb hba w
      (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hw)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) z hz

lemma continuousAt_symmetricIntegrand {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {p : ℂ × ℂ × ℝ} (hp : 0 < p.1.re) :
    ContinuousAt (fun v : ℂ × ℂ × ℝ => symmetricIntegrand a b hb hba v.1 v.2.1 v.2.2) p := by
  have hplus : ContinuousAt (fun v : ℂ × ℂ × ℝ => v.1 + v.2.2 * I) p := by fun_prop
  have hminus : ContinuousAt (fun v : ℂ × ℂ × ℝ => v.1 - v.2.2 * I) p := by fun_prop
  have hg₁ := (analyticAt_gamma_of_re_pos hb hba
    (z := p.1 + p.2.2 * I) (by simpa using hp)).continuousAt.comp
      (f := fun v : ℂ × ℂ × ℝ => v.1 + v.2.2 * I) (x := p) hplus
  have hg₂ := (analyticAt_gamma_of_re_pos hb hba
    (z := p.1 - p.2.2 * I) (by simpa using hp)).continuousAt.comp
      (f := fun v : ℂ × ℂ × ℝ => v.1 - v.2.2 * I) (x := p) hminus
  unfold symmetricIntegrand
  exact (ContinuousAt.mul (by fun_prop) hg₁).mul hg₂

lemma continuous_symmetricIntegrand {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (y : ℂ) : Continuous (symmetricIntegrand a b hb hba q y) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (continuousAt_symmetricIntegrand hb hba (p := (q, y, t)) hq).comp
    (f := fun t : ℝ => (q, y, t)) (x := t) (by fun_prop)

/-- A single tail constant for bounded `q` and fixed upper bounds on `Re q`
and `|Im y|`. No bound on `Re y` is needed. -/
theorem symmetric_norm_tail_uniform {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (R Q Y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q y : ℂ, ‖q‖ ≤ R → q.re ≤ Q → |y.im| ≤ Y →
      ∀ t : ℝ, R + 1 ≤ |t| →
      ‖symmetricIntegrand a b hb hba.le q y t‖ ≤
        C * Real.exp (-(2 * Real.pi * ((a + b) / 2 - Q - Y) / (a * b)) * |t|) := by
  obtain ⟨C, hC, hpair⟩ := norm_gamma_pair_uniform hb hba R 0 0
  refine ⟨C, hC, fun q y hq hQ hY t ht => ?_⟩
  have hp := hpair q q ((t : ℂ) * I) hq hq (by simp) (by simp) (by simpa using ht)
  simp only [mul_I_im, ofReal_re] at hp
  have hab : 0 < a * b := mul_pos (hb.trans hba) hb
  have hexpre : (2 * (Real.pi : ℂ) * I * y * t / ((a : ℂ) * b)).re =
      -2 * Real.pi * y.im * t / (a * b) := by
    simp only [← ofReal_mul, div_ofReal_re, mul_re, mul_im, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero,
      zero_add, zero_sub]
    norm_num
  have hexp : ‖Complex.exp (2 * Real.pi * I * y * t / ((a : ℂ) * b))‖ ≤
      Real.exp (2 * Real.pi * Y * |t| / (a * b)) := by
    rw [Complex.norm_exp, hexpre]
    apply Real.exp_le_exp.mpr
    have hm : -(y.im * t) ≤ Y * |t| := by
      apply (neg_le_abs _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hY (abs_nonneg _)
    apply div_le_div_of_nonneg_right _ hab.le
    nlinarith [Real.pi_pos]
  unfold symmetricIntegrand
  rw [mul_assoc, norm_mul]
  apply (mul_le_mul hexp hp (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  rw [← add_div]
  have hm := mul_le_mul_of_nonneg_right hQ (abs_nonneg t)
  have hm' := mul_le_mul_of_nonneg_left hm Real.pi_pos.le
  apply (div_le_div_of_nonneg_right (show
    2 * Real.pi * Y * |t| + Real.pi * (q.re + q.re - (a + b)) * |t| ≤
      2 * Real.pi * Y * |t| + Real.pi * (Q + Q - (a + b)) * |t| by nlinarith) hab.le).trans_eq
  ring

/-- An integrable majorant valid on prescribed compact sets of Fourier
parameters, with a strictly positive common convergence margin. -/
theorem exists_symmetric_majorant {a b Q Y : ℝ} (hb : 0 < b) (hba : b < a)
    {Kq Ky : Set ℂ} (hqcompact : IsCompact Kq) (hycompact : IsCompact Ky)
    (hqpos : ∀ q ∈ Kq, 0 < q.re) (hqbound : ∀ q ∈ Kq, q.re ≤ Q)
    (hybound : ∀ y ∈ Ky, |y.im| ≤ Y) (hmargin : Q + Y < (a + b) / 2) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ q ∈ Kq, ∀ y ∈ Ky, ∀ t : ℝ, ‖symmetricIntegrand a b hb hba.le q y t‖ ≤ bound t := by
  obtain ⟨R₀, hR₀⟩ := hqcompact.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := |R₀| + 1
  let T := R + 1
  let c := 2 * Real.pi * ((a + b) / 2 - Q - Y) / (a * b)
  have hc : 0 < c := by
    apply div_pos _ (mul_pos (hb.trans hba) hb)
    apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
    linarith
  obtain ⟨C, hC, htail⟩ := symmetric_norm_tail_uniform hb hba R Q Y
  have hcont : ContinuousOn
      (fun p : ℂ × ℂ × ℝ => symmetricIntegrand a b hb hba.le p.1 p.2.1 p.2.2)
      (Kq ×ˢ (Ky ×ˢ Icc (-T) T)) := by
    intro p hp
    exact (continuousAt_symmetricIntegrand hb hba.le (hqpos p.1 hp.1)).continuousWithinAt
  obtain ⟨B, hB⟩ := (hqcompact.prod (hycompact.prod isCompact_Icc)).exists_bound_of_continuousOn hcont
  let bound : ℝ → ℝ := fun t => (Icc (-T) T).indicator (fun _ => B) t + C * Real.exp (-c * |t|)
  refine ⟨bound, ?_, fun q hq y hy t => ?_⟩
  · have hi : IntegrableOn (fun _ : ℝ => B) (Icc (-T) T) :=
      continuous_const.integrableOn_Icc
    exact (hi.integrable_indicator measurableSet_Icc).add (integrable_const_mul_exp_neg_mul_abs C c hc)
  · by_cases ht : t ∈ Icc (-T) T
    · have hh := hB (q, y, t) ⟨hq, hy, ht⟩
      have he : 0 ≤ C * Real.exp (-c * |t|) := mul_nonneg hC.le (Real.exp_pos _).le
      simpa only [bound, indicator_of_mem ht] using hh.trans (le_add_of_nonneg_right he)
    · have hheight : R + 1 ≤ |t| := by
        have ht' : ¬ |t| ≤ T := by simpa only [abs_le, mem_Icc] using ht
        exact (lt_of_not_ge ht').le
      have hqnorm : ‖q‖ ≤ R := (hR₀ q hq).trans (by dsimp [R]; linarith [le_abs_self R₀])
      simpa only [bound, indicator_of_notMem ht, zero_add] using
        htail q y hqnorm (hqbound q hq) (hybound y hy) t hheight

end HaagerupIzumi.GammaContinuation
