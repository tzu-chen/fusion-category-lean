module

public import HaagerupIzumi.Analytic.GammaKernelRegularity
public import HaagerupIzumi.Analytic.GammaK4UniformBounds
import all Mathlib.Data.Complex.Basic

/-! # Holomorphy of a fixed vertical line in the Euler scaling parameter -/

@[expose] public section
noncomputable section

open Complex Set Metric Filter MeasureTheory
open scoped Topology
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

theorem exists_scaledKernel_line_majorant {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (r s x y : ℂ) (σ Q : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hQ : Q < (a + b) / 2)
    (hmargin : ∀ w ∈ K, (w * r).re + |(w * y).re| ≤ Q)
    (havoid : ∀ w ∈ K, AvoidsPoles a b (w * r) (w * s) (w * x) σ) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ w ∈ K, ∀ t : ℝ,
      ‖scaledKernel a b hb hba.le r s x y w (σ + t * I)‖ ≤ bound t := by
  obtain ⟨Ru, hRu⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun w : ℂ => k4U a b (w * r) (w * s)) K by
      unfold k4U; fun_prop)
  obtain ⟨Rp, hRp⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun w : ℂ => k4V a b (w * r) (w * s) + w * x) K by
      unfold k4V; fun_prop)
  obtain ⟨Rm, hRm⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun w : ℂ => k4V a b (w * r) (w * s) - w * x) K by
      unfold k4V; fun_prop)
  obtain ⟨Y, hY⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun w : ℂ => (w * y).im) K by fun_prop)
  let R := |Ru| + |Rp| + |Rm| + 1
  let T := R + 1
  let c := 2 * Real.pi * ((a + b) / 2 - Q) / (a * b)
  have hc : 0 < c := div_pos
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hQ))
    (mul_pos (hb.trans hba) hb)
  obtain ⟨C, hC, htail⟩ := k4_norm_tail_uniform hb hba R Q Y σ σ
  have hp (w : ℂ) (hw : w ∈ K) (t : ℝ) :
      (σ : ℂ) + t * I ∉ leftPoles a b (w * r) (w * s) (w * x) ∪
        rightPoles a b (w * r) (w * s) (w * x) := by
    intro hz
    exact havoid w hw _ hz (by simp)
  have hcont : ContinuousOn
      (fun p : ℂ × ℝ => scaledKernel a b hb hba.le r s x y p.1 (σ + p.2 * I))
      (K ×ˢ Icc (-T) T) := by
    intro p hp'
    exact ((continuousAt_scaledKernel a b hb hba.le r s x y
      (p.1, σ + p.2 * I) (hp p.1 hp'.1 p.2)).comp
      (f := fun p : ℂ × ℝ => (p.1, (σ : ℂ) + p.2 * I)) (by fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  let bound : ℝ → ℝ := fun t => (Icc (-T) T).indicator (fun _ => B) t +
    C * Real.exp (-c * |t|)
  refine ⟨bound, ?_, fun w hw t => ?_⟩
  · have hi : IntegrableOn (fun _ : ℝ => B) (Icc (-T) T) :=
      continuous_const.integrableOn_Icc
    exact (hi.integrable_indicator measurableSet_Icc).add
      (integrable_const_mul_exp_neg_mul_abs C c hc)
  · by_cases ht : t ∈ Icc (-T) T
    · have hh := hB (w, t) ⟨hw, ht⟩
      have he : 0 ≤ C * Real.exp (-c * |t|) := mul_nonneg hC.le (Real.exp_pos _).le
      simpa only [bound, indicator_of_mem ht] using hh.trans (le_add_of_nonneg_right he)
    · have hheight : R + 1 ≤ |t| := by
        have ht' : ¬ |t| ≤ T := by simpa only [abs_le, mem_Icc] using ht
        exact (lt_of_not_ge ht').le
      have hu : ‖k4U a b (w * r) (w * s)‖ ≤ R := by
        have := hRu w hw
        dsimp [R]; linarith [le_abs_self Ru, abs_nonneg Rp, abs_nonneg Rm]
      have hvp : ‖k4V a b (w * r) (w * s) + w * x‖ ≤ R := by
        have := hRp w hw
        dsimp [R]; linarith [le_abs_self Rp, abs_nonneg Ru, abs_nonneg Rm]
      have hvm : ‖k4V a b (w * r) (w * s) - w * x‖ ≤ R := by
        have := hRm w hw
        dsimp [R]; linarith [le_abs_self Rm, abs_nonneg Ru, abs_nonneg Rp]
      have hy : |(w * y).im| ≤ Y := by simpa only [Real.norm_eq_abs] using hY w hw
      have hh := htail (w * r) (w * s) (w * x) (w * y) hu hvp hvm hy
        (hmargin w hw) ((σ : ℂ) + t * I) (by simp) (by simp) (by simpa using hheight)
      simpa only [bound, indicator_of_notMem ht, zero_add, scaledKernel, kernel,
        add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
        zero_add, c] using hh

theorem differentiableAt_scaledKernel_line_integral {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (r s x y t₀ : ℂ) (σ : ℝ)
    (hc : K4Conv a b (t₀ * r) (t₀ * y))
    (havoid : ∀ᶠ w in 𝓝 t₀, AvoidsPoles a b (w * r) (w * s) (w * x) σ) :
    DifferentiableAt ℂ
      (fun w => ∫ t : ℝ, scaledKernel a b hb hba.le r s x y w (σ + t * I)) t₀ := by
  let Q := ((t₀ * r).re + |(t₀ * y).re| + (a + b) / 2) / 2
  have hQ : Q < (a + b) / 2 := by dsimp [Q, K4Conv] at *; linarith
  have hQ₀ : (t₀ * r).re + |(t₀ * y).re| < Q := by
    dsimp [Q, K4Conv] at *; linarith
  have hev : ∀ᶠ w in 𝓝 t₀, (w * r).re + |(w * y).re| < Q :=
    (show ContinuousAt (fun w : ℂ => (w * r).re + |(w * y).re|) t₀ by
      fun_prop).eventually (gt_mem_nhds hQ₀)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and havoid)
  let ε := δ / 4
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hmem (w : ℂ) (hw : w ∈ closedBall t₀ (2 * ε)) :
      (w * r).re + |(w * y).re| < Q ∧
        AvoidsPoles a b (w * r) (w * s) (w * x) σ := by
    apply hball
    have hd := mem_closedBall.mp hw
    dsimp [ε] at hd
    linarith
  obtain ⟨bound, hint, hbound⟩ := exists_scaledKernel_line_majorant hb hba r s x y σ Q
    (isCompact_closedBall t₀ (2 * ε)) hQ (fun w hw => (hmem w hw).1.le)
    (fun w hw => (hmem w hw).2)
  apply differentiableAt_integral_of_holomorphic_bound_measure volume hε
    (fun w => ((measurable_scaledKernel a b hb hba.le r s x y).comp
      (show Measurable (fun t : ℝ => (w, (σ : ℂ) + t * I)) by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ (fun t w hw => ?_)) (ae_of_all _ (fun t w hw => hbound w hw t)) hint
  apply differentiableAt_scaledKernel_parameter
  intro hz
  exact (hmem w hw).2 _ hz (by simp)

end HaagerupIzumi.GammaK4Contour
