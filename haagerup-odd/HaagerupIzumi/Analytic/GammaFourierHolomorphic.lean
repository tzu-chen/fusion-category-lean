module

public import HaagerupIzumi.Analytic.GammaFourierBounds
public import HaagerupIzumi.Analytic.DominatedHolomorphic
import all Mathlib.Data.Complex.Basic

/-!
# Separate holomorphy of the symmetric gamma transform

Both complex parameters may be differentiated under the actual integral in
the domain `0 < Re q` and `|Im y| < (a+b)/2 - Re q`.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace HaagerupIzumi.GammaContinuation

def symmetricDerivQ (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * y * t / ((a : ℂ) * b)) *
    (deriv (gamma a b hb hba) (q + t * I) * gamma a b hb hba (q - t * I) +
      gamma a b hb hba (q + t * I) * deriv (gamma a b hb hba) (q - t * I))

def symmetricDerivY (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) (t : ℝ) : ℂ :=
  (2 * Real.pi * I * t / ((a : ℂ) * b)) * symmetricIntegrand a b hb hba q y t

lemma hasDerivAt_symmetricIntegrand_q {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (y : ℂ) (t : ℝ) :
    HasDerivAt (fun w => symmetricIntegrand a b hb hba w y t)
      (symmetricDerivQ a b hb hba q y t) q := by
  have h₁ := ((analyticAt_gamma_of_re_pos hb hba (z := q + t * I)
    (by simpa using hq)).differentiableAt.hasDerivAt).comp q ((hasDerivAt_id q).add_const (t * I))
  have h₂ := ((analyticAt_gamma_of_re_pos hb hba (z := q - t * I)
    (by simpa using hq)).differentiableAt.hasDerivAt).comp q ((hasDerivAt_id q).sub_const (t * I))
  have hd := (h₁.mul h₂).const_mul (Complex.exp (2 * Real.pi * I * y * t / ((a : ℂ) * b)))
  convert! hd using 1 <;> simp [symmetricIntegrand, symmetricDerivQ, Function.comp_def, mul_assoc]

lemma hasDerivAt_symmetricIntegrand_y (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (t : ℝ) :
    HasDerivAt (fun w => symmetricIntegrand a b hb hba q w t)
      (symmetricDerivY a b hb hba q y t) y := by
  have hlin := (((hasDerivAt_id y).const_mul (2 * (Real.pi : ℂ) * I)).mul_const (t : ℂ)).div_const
    ((a : ℂ) * b)
  have hd := (hlin.cexp.mul_const (gamma a b hb hba (q + t * I))).mul_const
    (gamma a b hb hba (q - t * I))
  convert! hd using 1
  simp [symmetricIntegrand, symmetricDerivY, mul_assoc, mul_left_comm]

lemma continuous_symmetricDerivQ {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (y : ℂ) : Continuous (symmetricDerivQ a b hb hba q y) := by
  have hg₁ : Continuous (fun t : ℝ => gamma a b hb hba (q + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_gamma_of_re_pos hb hba (z := q + t * I)
      (by simpa using hq)).continuousAt.comp (f := fun t : ℝ => q + t * I) (x := t) (by fun_prop)
  have hg₂ : Continuous (fun t : ℝ => gamma a b hb hba (q - t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_gamma_of_re_pos hb hba (z := q - t * I)
      (by simpa using hq)).continuousAt.comp (f := fun t : ℝ => q - t * I) (x := t) (by fun_prop)
  have hd₁ : Continuous (fun t : ℝ => deriv (gamma a b hb hba) (q + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_gamma_of_re_pos hb hba (z := q + t * I)
      (by simpa using hq)).deriv.continuousAt.comp (f := fun t : ℝ => q + t * I) (x := t) (by fun_prop)
  have hd₂ : Continuous (fun t : ℝ => deriv (gamma a b hb hba) (q - t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_gamma_of_re_pos hb hba (z := q - t * I)
      (by simpa using hq)).deriv.continuousAt.comp (f := fun t : ℝ => q - t * I) (x := t) (by fun_prop)
  unfold symmetricDerivQ
  exact Continuous.mul (by fun_prop) ((hd₁.mul hg₂).add (hg₁.mul hd₂))

lemma continuous_symmetricDerivY {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (y : ℂ) : Continuous (symmetricDerivY a b hb hba q y) := by
  exact Continuous.mul (by fun_prop) (continuous_symmetricIntegrand hb hba hq y)

lemma exists_symmetric_local_majorant {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    ∃ r : ℝ, 0 < r ∧ ∃ bound : ℝ → ℝ, Integrable bound ∧
      (∀ w ∈ closedBall q (2 * r), 0 < w.re) ∧
      ∀ w ∈ closedBall q (2 * r), ∀ v ∈ closedBall y (2 * r), ∀ t : ℝ,
        ‖symmetricIntegrand a b hb hba.le w v t‖ ≤ bound t := by
  let gap := (a + b) / 2 - q.re - |y.im|
  let r := min q.re gap / 8
  have hgap : 0 < gap := sub_pos.mpr hconv
  have hr : 0 < r := div_pos (lt_min hq hgap) (by norm_num)
  have hrq : 8 * r ≤ q.re := by dsimp [r]; linarith [min_le_left q.re gap]
  have hrg : 8 * r ≤ gap := by dsimp [r]; linarith [min_le_right q.re gap]
  have hqball {w : ℂ} (hw : w ∈ closedBall q (2 * r)) : |w.re - q.re| ≤ 2 * r := by
    have hh : ‖w - q‖ ≤ 2 * r := by simpa only [dist_eq_norm] using mem_closedBall.mp hw
    simpa only [sub_re] using (Complex.abs_re_le_norm (w - q)).trans hh
  have hyball {v : ℂ} (hv : v ∈ closedBall y (2 * r)) : |v.im| ≤ |y.im| + 2 * r := by
    have hh : |v.im - y.im| ≤ 2 * r := by
      have ht : ‖v - y‖ ≤ 2 * r := by simpa only [dist_eq_norm] using mem_closedBall.mp hv
      simpa only [sub_im] using (Complex.abs_im_le_norm (v - y)).trans ht
    have ht := abs_add_le (v.im - y.im) y.im
    simp only [sub_add_cancel] at ht
    linarith
  have hpos : ∀ w ∈ closedBall q (2 * r), 0 < w.re := by
    intro w hw
    have hh := (abs_le.mp (hqball hw)).1
    linarith
  have hup : ∀ w ∈ closedBall q (2 * r), w.re ≤ q.re + 2 * r := by
    intro w hw
    linarith [(abs_le.mp (hqball hw)).2]
  obtain ⟨bound, hint, hbound⟩ := exists_symmetric_majorant hb hba
    (isCompact_closedBall q (2 * r)) (isCompact_closedBall y (2 * r)) hpos hup
    (fun v hv => hyball hv) (by dsimp [gap] at hrg; linarith)
  exact ⟨r, hr, bound, hint, hpos, hbound⟩

theorem integrable_symmetricIntegrand {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    Integrable (symmetricIntegrand a b hb hba.le q y) := by
  obtain ⟨r, hr, bound, hint, _, hbound⟩ := exists_symmetric_local_majorant hb hba hq hconv
  have hqc : q ∈ closedBall q (2 * r) := mem_closedBall_self (by positivity)
  have hyc : y ∈ closedBall y (2 * r) := mem_closedBall_self (by positivity)
  exact hint.mono' (continuous_symmetricIntegrand hb hba.le hq y).aestronglyMeasurable
    (ae_of_all _ (fun t => hbound q hqc y hyc t))

/-- The derivative in the gamma parameter is the integral of the two gamma
derivatives. -/
theorem hasDerivAt_symmetricTransform_q {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    HasDerivAt (fun w => symmetricTransform a b hb hba.le w y)
      (∫ t : ℝ, symmetricDerivQ a b hb hba.le q y t) q := by
  obtain ⟨r, hr, bound, hint, hpos, hbound⟩ := exists_symmetric_local_majorant hb hba hq hconv
  have hy : y ∈ closedBall y (2 * r) := mem_closedBall_self (by positivity)
  exact (hasDerivAt_integral_of_holomorphic_bound
    (F := fun w t => symmetricIntegrand a b hb hba.le w y t)
    (F' := fun w t => symmetricDerivQ a b hb hba.le w y t) hr
    (fun w hw => continuous_symmetricIntegrand hb hba.le (hpos w hw) y)
    (continuous_symmetricDerivQ hb hba.le hq y)
    (fun t w hw => hasDerivAt_symmetricIntegrand_q hb hba.le (hpos w hw) y t)
    (fun t w hw => hbound w hw y hy t) hint).2

/-- Differentiation in the Fourier parameter introduces its elementary
linear multiplier. -/
theorem hasDerivAt_symmetricTransform_y {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    HasDerivAt (fun v => symmetricTransform a b hb hba.le q v)
      (∫ t : ℝ, symmetricDerivY a b hb hba.le q y t) y := by
  obtain ⟨r, hr, bound, hint, hpos, hbound⟩ := exists_symmetric_local_majorant hb hba hq hconv
  have hqc : q ∈ closedBall q (2 * r) := mem_closedBall_self (by positivity)
  exact (hasDerivAt_integral_of_holomorphic_bound
    (F := fun v t => symmetricIntegrand a b hb hba.le q v t)
    (F' := fun v t => symmetricDerivY a b hb hba.le q v t) hr
    (fun v _ => continuous_symmetricIntegrand hb hba.le hq v)
    (continuous_symmetricDerivY hb hba.le hq y)
    (fun t v _ => hasDerivAt_symmetricIntegrand_y a b hb hba.le q v t)
    (fun t v hv => hbound q hqc v hv t) hint).2

theorem differentiableAt_symmetricTransform_q {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    DifferentiableAt ℂ (fun w => symmetricTransform a b hb hba.le w y) q :=
  (hasDerivAt_symmetricTransform_q hb hba hq hconv).differentiableAt

theorem differentiableAt_symmetricTransform_y {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    DifferentiableAt ℂ (fun v => symmetricTransform a b hb hba.le q v) y :=
  (hasDerivAt_symmetricTransform_y hb hba hq hconv).differentiableAt

end HaagerupIzumi.GammaContinuation
