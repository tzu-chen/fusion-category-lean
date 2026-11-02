module

public import HaagerupIzumi.Analytic.GammaTwoFourierShifts
public import HaagerupIzumi.Analytic.GammaFourierCandidateShift
public import HaagerupIzumi.Analytic.GammaStripPeriodicity
import all Mathlib.Data.Complex.Basic

/-!
# Evaluation up to a factor depending on the gamma parameter

The transform and its explicit product satisfy the same two shift equations.
Their quotient is constant in the Fourier variable, first on the domain
where both shifts overlap, and then throughout the positive-parameter domain
by the identity theorem.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaPeriodUniqueness

namespace HaagerupIzumi.GammaContinuation

def fourierQuotient (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q y : ℂ) : ℂ :=
  symmetricTransform a b hb hba q y / fourierCandidate a b hb hba q y

def fourierScale (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (q : ℂ) : ℂ :=
  fourierQuotient a b hb hba q 0

lemma differentiableAt_fourierQuotient_y {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q y : ℂ} (hq : 0 < q.re) (hy : |y.im| < (a + b) / 2 - q.re) :
    DifferentiableAt ℂ (fourierQuotient a b hb hba.le q) y :=
  (differentiableAt_symmetricTransform_y hb hba hq hy).div
    (differentiableAt_fourierCandidate_y hb hba.le hq hy)
    (fourierCandidate_ne_zero hb hba.le hq hy)

lemma differentiableAt_fourierScale {a b : ℝ} (hb : 0 < b) (hba : b < a)
    {q : ℂ} (hq : 0 < q.re) (hqΩ : q.re < (a + b) / 2) :
    DifferentiableAt ℂ (fourierScale a b hb hba.le) q := by
  have hy : |(0 : ℂ).im| < (a + b) / 2 - q.re := by simp; linarith
  exact (differentiableAt_symmetricTransform_q hb hba hq hy).div
    (differentiableAt_fourierCandidate_q hb hba.le hq hy)
    (fourierCandidate_ne_zero hb hba.le hq hy)

lemma symmetricTransform_shift_first {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (q y : ℂ) (hq : 0 < q.re) (hy : |y.im| < b / 2 - q.re) :
    fourierCoeffPlus b q y * symmetricTransform a b hb hba.le q (y + a * I / 2) =
      fourierCoeffMinus b q y * symmetricTransform a b hb hba.le q (y - a * I / 2) := by
  have h := GammaTwoFourier.transform_dual_shift hb hba.le hb.ne' rfl
    (fun z hz => gamma_shift₁ a b hb hba.le z hz) hba (hb.trans hba) q q y hq hq
    (by linarith : |y.im| < (a + b - q.re - q.re - a) / 2)
  simpa only [fourierCoeffPlus, fourierCoeffMinus,
    GammaTwoFourier.transform_diag_eq_symmetricTransform] using h

lemma symmetricTransform_shift_second {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (q y : ℂ) (hq : 0 < q.re) (hy : |y.im| < a / 2 - q.re) :
    fourierCoeffPlus a q y * symmetricTransform a b hb hba.le q (y + b * I / 2) =
      fourierCoeffMinus a q y * symmetricTransform a b hb hba.le q (y - b * I / 2) := by
  have h := GammaTwoFourier.transform_dual_shift hb hba.le (hb.trans hba).ne' (mul_comm a b)
    (fun z hz => gamma_shift₂ a b hb hba.le z hz) hba hb q q y hq hq
    (by linarith : |y.im| < (a + b - q.re - q.re - b) / 2)
  simpa only [fourierCoeffPlus, fourierCoeffMinus,
    GammaTwoFourier.transform_diag_eq_symmetricTransform] using h

lemma fourierQuotient_local_period {a b A B : ℝ} (hb : 0 < b) (hba : b < a)
    (_hA : 0 < A) (hB : 0 < B) (hsum : a + b = A + B) (q : ℂ) (hq : 0 < q.re)
    (hJ : ∀ y : ℂ, |y.im| < B / 2 - q.re →
      fourierCoeffPlus B q y * symmetricTransform a b hb hba.le q (y + A * I / 2) =
        fourierCoeffMinus B q y * symmetricTransform a b hb hba.le q (y - A * I / 2))
    (hC : ∀ y : ℂ, |y.im| < B / 2 - q.re →
      fourierCoeffPlus B q y * fourierCandidate a b hb hba.le q (y + A * I / 2) =
        fourierCoeffMinus B q y * fourierCandidate a b hb hba.le q (y - A * I / 2))
    (z : ℂ) (hz : |z.im| < (a + b) / 2 - q.re)
    (hzA : |(z + A * I).im| < (a + b) / 2 - q.re) :
    fourierQuotient a b hb hba.le q (z + A * I) = fourierQuotient a b hb hba.le q z := by
  let m : ℂ := z + A * I / 2
  have hmid : |m.im| < B / 2 - q.re := by
    have h₁ := (abs_lt.mp hz).1
    have h₂ := (abs_lt.mp hzA).2
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero] at h₂
    dsimp [m]
    simp only [div_ofNat_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
      I_re, mul_zero, add_zero]
    apply abs_lt.mpr
    constructor <;> linarith
  have hplus : m + A * I / 2 = z + A * I := by dsimp [m]; ring
  have hminus : m - A * I / 2 = z := by dsimp [m]; ring
  have hj := hJ m hmid
  have hc := hC m hmid
  rw [hplus, hminus] at hj hc
  unfold fourierQuotient
  apply (div_eq_div_iff (fourierCandidate_ne_zero hb hba.le hq hzA)
    (fourierCandidate_ne_zero hb hba.le hq hz)).2
  apply mul_left_cancel₀ (fourierCoeffPlus_ne_zero hB hq hmid)
  linear_combination fourierCandidate a b hb hba.le q z * hj -
    symmetricTransform a b hb hba.le q z * hc

lemma symmetricTransform_eq_scale_mul_small {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q y : ℂ} (hq : 0 < q.re) (hqsmall : q.re < b / 2)
    (hy : |y.im| < (a + b) / 2 - q.re) :
    symmetricTransform a b hb hba.le q y =
      fourierScale a b hb hba.le q * fourierCandidate a b hb hba.le q y := by
  have hS : 0 < (a + b) / 2 - q.re := by linarith
  have hdiff : DifferentiableOn ℂ (fourierQuotient a b hb hba.le q)
      (horizontalStrip ((a + b) / 2 - q.re)) := by
    intro z hz
    exact (differentiableAt_fourierQuotient_y hb hba hq hz).differentiableWithinAt
  have hpA := fourierQuotient_local_period hb hba (hb.trans hba) hb rfl q hq
    (fun z hz => symmetricTransform_shift_first hb hba q z hq hz)
    (fourierCandidate_shift_first hb hba.le q)
  have hpB := fourierQuotient_local_period hb hba hb (hb.trans hba) (add_comm a b) q hq
    (fun z hz => symmetricTransform_shift_second hb hba q z hq hz)
    (fourierCandidate_shift_second hb hba.le q)
  have heq := eq_of_local_imaginary_periods (hb.trans hba) hb (by linarith) (by linarith)
    hirr hdiff hpA hpB hy (show (0 : ℂ) ∈ horizontalStrip ((a + b) / 2 - q.re) by
      change |(0 : ℂ).im| < _; simpa using hS)
  exact (div_eq_iff (fourierCandidate_ne_zero hb hba.le hq hy)).mp heq

/-- The proportionality in the Fourier variable holds on the full domain of
positive gamma parameters. -/
theorem symmetricTransform_eq_scale_mul {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q y : ℂ} (hq : 0 < q.re)
    (hy : |y.im| < (a + b) / 2 - q.re) :
    symmetricTransform a b hb hba.le q y =
      fourierScale a b hb hba.le q * fourierCandidate a b hb hba.le q y := by
  let W : ℝ := (a + b) / 2 - |y.im|
  have hW : 0 < W := by dsimp [W]; linarith
  have hqW : q ∈ strip W := ⟨hq, by dsimp [W]; linarith⟩
  have hc (u : ℂ) (hu : u ∈ strip W) : |y.im| < (a + b) / 2 - u.re := by
    dsimp [strip, W] at hu
    linarith [hu.2]
  have hleft : DifferentiableOn ℂ (fun u => symmetricTransform a b hb hba.le u y) (strip W) := by
    intro u hu
    exact (differentiableAt_symmetricTransform_q hb hba hu.1 (hc u hu)).differentiableWithinAt
  have hright : DifferentiableOn ℂ
      (fun u => fourierScale a b hb hba.le u * fourierCandidate a b hb hba.le u y) (strip W) := by
    intro u hu
    exact ((differentiableAt_fourierScale hb hba hu.1 (by
      have := hc u hu; linarith [abs_nonneg y.im])).mul
      (differentiableAt_fourierCandidate_q hb hba.le hu.1 (hc u hu))).differentiableWithinAt
  let d : ℝ := min (b / 2) W
  have hd : 0 < d := lt_min (half_pos hb) hW
  have hmid : ((d / 2 : ℝ) : ℂ) ∈ strip W := by
    have hle := min_le_right (b / 2) W
    constructor <;> simp only [ofReal_re] <;> dsimp [d] at * <;> linarith
  apply (hleft.analyticOnNhd (isOpen_strip W)).eqOn_of_preconnected_of_eventuallyEq
    (hright.analyticOnNhd (isOpen_strip W))
    (((convex_halfSpace_re_gt (0 : ℝ)).inter (convex_halfSpace_re_lt W)).isPreconnected)
    hmid ?_ hqW
  have hmidd : ((d / 2 : ℝ) : ℂ) ∈ strip d := by
    constructor <;> simp only [ofReal_re] <;> linarith
  filter_upwards [(isOpen_strip d).mem_nhds hmidd] with u hu
  have hub : u.re < b / 2 := lt_of_lt_of_le hu.2 (min_le_left _ _)
  have huW : u ∈ strip W := ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_right _ _)⟩
  exact symmetricTransform_eq_scale_mul_small hb hba hirr hu.1 hub (hc u huW)

end HaagerupIzumi.GammaContinuation
