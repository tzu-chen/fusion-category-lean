module

public import HaagerupIzumi.Analytic.GammaStrip
public import Mathlib.Analysis.Calculus.ParametricIntegral
import all Mathlib.Data.Complex.Basic

/-!
# Parameter estimates for the gamma integral

Fixed entire divided differences make the cancellation at `t = 0` uniform
in the complex gamma argument. This avoids estimating two divergent
summands separately when differentiating the defining integral.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace HaagerupIzumi.GammaIntegral

/-- The second divided difference of an entire function at the origin. -/
def secondRemainder (f : ℂ → ℂ) : ℂ → ℂ := dslope (dslope f 0) 0

lemma differentiable_secondRemainder {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (secondRemainder f) := by
  rw [← differentiableOn_univ]
  apply (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 0)).mpr
  exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 0)).mpr
    hf.differentiableOn

lemma secondRemainder_mul_sq (f : ℂ → ℂ) (hf : deriv f 0 = 0) (w : ℂ) :
    secondRemainder f w * w ^ 2 = f w - f 0 := by
  by_cases hw : w = 0
  · simp [hw]
  · simp only [secondRemainder, dslope_of_ne _ hw, slope, vsub_eq_sub, sub_zero,
      dslope_same, hf, smul_eq_mul]
    field_simp

def sinhRemainder : ℂ → ℂ := secondRemainder sinhc

def coshRemainder : ℂ → ℂ := secondRemainder Complex.cosh

lemma continuous_sinhRemainder : Continuous sinhRemainder :=
  (differentiable_secondRemainder differentiable_sinhc).continuous

lemma continuous_coshRemainder : Continuous coshRemainder :=
  (differentiable_secondRemainder Complex.differentiable_cosh).continuous

lemma sinhRemainder_mul_sq (w : ℂ) : sinhRemainder w * w ^ 2 = sinhc w - 1 := by
  simpa [sinhRemainder] using
    secondRemainder_mul_sq sinhc hasDerivAt_sinhc_zero.deriv w

lemma coshRemainder_mul_sq (w : ℂ) :
    coshRemainder w * w ^ 2 = Complex.cosh w - 1 := by
  simpa [coshRemainder] using
    secondRemainder_mul_sq Complex.cosh (by simp [Complex.deriv_cosh]) w

/-- The explicit derivative of the regularized kernel with respect to its
complex parameter. -/
def integrandDeriv (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.cosh (center ω₁ ω₂ z * t) * (2 * t) /
      (2 * Complex.sinh ((ω₁ : ℂ) * t) * Complex.sinh ((ω₂ : ℂ) * t)) -
    2 / (2 * ω₁ * ω₂ * t)) / t

lemma hasDerivAt_integrand (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => integrand ω₁ ω₂ w t) (integrandDeriv ω₁ ω₂ z t) z := by
  have hc : HasDerivAt (center ω₁ ω₂) 2 z := by
    unfold center
    convert! ((hasDerivAt_id z).const_mul (2 : ℂ)).sub_const
      ((ω₁ : ℂ) + ω₂) using 1
    simp only [mul_one]
  have hs := (Complex.hasDerivAt_sinh (center ω₁ ω₂ z * t)).comp z (hc.mul_const (t : ℂ))
  exact ((hs.div_const (2 * Complex.sinh ((ω₁ : ℂ) * t) *
    Complex.sinh ((ω₂ : ℂ) * t))).sub (hc.div_const (2 * ω₁ * ω₂ * t))).div_const t

lemma integrandDeriv_eq_exponential {ω₁ ω₂ t : ℝ} (hω₁ : 0 < ω₁)
    (hω₂ : 0 < ω₂) (ht : 0 < t) (z : ℂ) :
    integrandDeriv ω₁ ω₂ z t =
      (Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) +
        Complex.exp ((-2 * z) * t)) * (2 * t * tailWeight ω₁ ω₂ t) -
      (1 / ((ω₁ : ℂ) * ω₂)) * ((t : ℂ) ^ 2)⁻¹ := by
  have h₁ := ((((hasDerivAt_id z).sub_const ((ω₁ : ℂ) + ω₂)).const_mul 2).mul_const
    (t : ℂ)).cexp
  have h₂ := (((hasDerivAt_id z).const_mul (-2 : ℂ)).mul_const (t : ℂ)).cexp
  have hc : HasDerivAt (center ω₁ ω₂) 2 z := by
    unfold center
    convert! ((hasDerivAt_id z).const_mul (2 : ℂ)).sub_const
      ((ω₁ : ℂ) + ω₂) using 1
    simp only [mul_one]
  have he := ((h₁.sub h₂).mul_const (tailWeight ω₁ ω₂ t : ℂ)).sub
    ((hc.div_const (2 * ω₁ * ω₂)).mul_const (((t : ℂ) ^ 2)⁻¹))
  have hi := hasDerivAt_integrand ω₁ ω₂ z t
  have hfun : (fun w => integrand ω₁ ω₂ w t) =
      (fun w => (Complex.exp ((2 * (w - ((ω₁ : ℂ) + ω₂))) * t) -
        Complex.exp ((-2 * w) * t)) * (tailWeight ω₁ ω₂ t : ℂ) -
        center ω₁ ω₂ w / (2 * ω₁ * ω₂) * ((t : ℂ) ^ 2)⁻¹) := by
    funext w
    exact integrand_eq_exponential w hω₁ hω₂ ht
  rw [hfun] at hi
  convert hi.unique he using 1
  simp only [id_eq]
  ring

/-- A jointly continuous form of the kernel's derivative, including the
removable endpoint value. -/
def regularizedDeriv (ω₁ ω₂ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (center ω₁ ω₂ z ^ 2 * coshRemainder (center ω₁ ω₂ z * t) -
    (ω₁ : ℂ) ^ 2 * sinhRemainder ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t) -
    (ω₂ : ℂ) ^ 2 * sinhRemainder ((ω₂ : ℂ) * t)) /
      (ω₁ * ω₂ * sinhc ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t))

lemma regularizedDeriv_eq_integrandDeriv {ω₁ ω₂ : ℝ} (hω₁ : ω₁ ≠ 0)
    (hω₂ : ω₂ ≠ 0) (z : ℂ) {t : ℝ} (ht : t ≠ 0) :
    regularizedDeriv ω₁ ω₂ z t = integrandDeriv ω₁ ω₂ z t := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have ha : (ω₁ : ℂ) ≠ 0 := by exact_mod_cast hω₁
  have hb : (ω₂ : ℂ) ≠ 0 := by exact_mod_cast hω₂
  have hsa := sinhc_ofReal_ne_zero (ω₁ * t)
  have hsb := sinhc_ofReal_ne_zero (ω₂ * t)
  simp only [Complex.ofReal_mul] at hsa hsb
  have hA := sinhRemainder_mul_sq ((ω₁ : ℂ) * t)
  have hB := sinhRemainder_mul_sq ((ω₂ : ℂ) * t)
  have hC := coshRemainder_mul_sq (center ω₁ ω₂ z * t)
  have hsA := sinhc_of_ne_zero (mul_ne_zero ha ht')
  have hsB := sinhc_of_ne_zero (mul_ne_zero hb ht')
  have hsinA : Complex.sinh ((ω₁ : ℂ) * t) = sinhc ((ω₁ : ℂ) * t) * (ω₁ * t) :=
    (eq_div_iff (mul_ne_zero ha ht')).mp hsA |>.symm
  have hsinB : Complex.sinh ((ω₂ : ℂ) * t) = sinhc ((ω₂ : ℂ) * t) * (ω₂ * t) :=
    (eq_div_iff (mul_ne_zero hb ht')).mp hsB |>.symm
  have hid :
      (center ω₁ ω₂ z ^ 2 * coshRemainder (center ω₁ ω₂ z * t) -
        (ω₁ : ℂ) ^ 2 * sinhRemainder ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t) -
        (ω₂ : ℂ) ^ 2 * sinhRemainder ((ω₂ : ℂ) * t)) * (t : ℂ) ^ 2 =
      Complex.cosh (center ω₁ ω₂ z * t) -
        sinhc ((ω₁ : ℂ) * t) * sinhc ((ω₂ : ℂ) * t) := by
    linear_combination hC - hA * sinhc ((ω₂ : ℂ) * t) - hB
  dsimp [regularizedDeriv, integrandDeriv]
  rw [hsinA, hsinB]
  generalize sinhc ((ω₁ : ℂ) * t) = A at *
  generalize sinhc ((ω₂ : ℂ) * t) = B at *
  generalize sinhRemainder ((ω₁ : ℂ) * t) = RA at *
  generalize sinhRemainder ((ω₂ : ℂ) * t) = RB at *
  field_simp [ha, hb, ht', hsa, hsb]
  linear_combination hid

lemma continuous_regularizedDeriv {ω₁ ω₂ : ℝ} (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    Continuous (fun p : ℂ × ℝ => regularizedDeriv ω₁ ω₂ p.1 p.2) := by
  have hc : Continuous (fun p : ℂ × ℝ => center ω₁ ω₂ p.1) := by
    unfold center
    fun_prop
  have ht : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have ha : Continuous (fun p : ℂ × ℝ => sinhc ((ω₁ : ℂ) * p.2)) :=
    continuous_sinhc.comp (continuous_const.mul ht)
  have hb : Continuous (fun p : ℂ × ℝ => sinhc ((ω₂ : ℂ) * p.2)) :=
    continuous_sinhc.comp (continuous_const.mul ht)
  unfold regularizedDeriv
  apply Continuous.div
  · exact (((hc.pow 2).mul (continuous_coshRemainder.comp (hc.mul ht))).sub
      ((continuous_const.mul (continuous_sinhRemainder.comp
        (continuous_const.mul ht))).mul hb)).sub
      (continuous_const.mul (continuous_sinhRemainder.comp (continuous_const.mul ht)))
  · exact ((continuous_const.mul ha).mul hb)
  · intro p
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by exact_mod_cast hω₁) (by exact_mod_cast hω₂)
      · simpa only [← Complex.ofReal_mul] using sinhc_ofReal_ne_zero (ω₁ * p.2)
    · simpa only [← Complex.ofReal_mul] using sinhc_ofReal_ne_zero (ω₂ * p.2)

lemma norm_integrandDeriv_le_tail {ω₁ ω₂ δ t : ℝ} (hω₁ : 0 < ω₁)
    (hω₂ : 0 < ω₂) {z : ℂ} (hz₁ : δ ≤ z.re) (hz₂ : z.re ≤ ω₁ + ω₂ - δ)
    (ht : 1 ≤ t) :
    ‖integrandDeriv ω₁ ω₂ z t‖ ≤
      4 * ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹ *
        Real.exp (-2 * δ * t) + (ω₁ * ω₂)⁻¹ * (t ^ 2)⁻¹ := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  let C := ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹
  have hC : 0 ≤ C := (abs_nonneg _).trans (mul_tailWeight_bound hω₁ hω₂ ht)
  have hfirst : ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t)‖ ≤
      Real.exp (-2 * δ * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [mul_re, sub_re, add_re, ofReal_re, ofReal_im]
    nlinarith
  have hsecond : ‖Complex.exp ((-2 * z) * t)‖ ≤ Real.exp (-2 * δ * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [mul_re, neg_re, ofReal_re, ofReal_im]
    nlinarith
  have hnum : ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) +
      Complex.exp ((-2 * z) * t)‖ ≤ 2 * Real.exp (-2 * δ * t) :=
    (norm_add_le _ _).trans (by linarith)
  have hweight : ‖(2 * t * tailWeight ω₁ ω₂ t : ℂ)‖ ≤ 2 * C := by
    have hh := mul_le_mul_of_nonneg_left (mul_tailWeight_bound hω₁ hω₂ ht)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa [C, mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] using hh
  have hrem : ‖(1 / ((ω₁ : ℂ) * ω₂)) * ((t : ℂ) ^ 2)⁻¹‖ =
      (ω₁ * ω₂)⁻¹ * (t ^ 2)⁻¹ := by
    simp [norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hω₁, abs_of_pos hω₂, abs_of_pos htpos]
  rw [integrandDeriv_eq_exponential hω₁ hω₂ htpos z]
  calc
    _ ≤ ‖Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) +
          Complex.exp ((-2 * z) * t)‖ * ‖(2 * t * tailWeight ω₁ ω₂ t : ℂ)‖ +
        ‖(1 / ((ω₁ : ℂ) * ω₂)) * ((t : ℂ) ^ 2)⁻¹‖ := by
      simpa only [norm_mul] using norm_sub_le
        ((Complex.exp ((2 * (z - ((ω₁ : ℂ) + ω₂))) * t) +
          Complex.exp ((-2 * z) * t)) * (2 * t * tailWeight ω₁ ω₂ t))
        ((1 / ((ω₁ : ℂ) * ω₂)) * ((t : ℂ) ^ 2)⁻¹)
    _ ≤ (2 * Real.exp (-2 * δ * t)) * (2 * C) + (ω₁ * ω₂)⁻¹ * (t ^ 2)⁻¹ := by
      rw [hrem]
      exact add_le_add (mul_le_mul hnum hweight (norm_nonneg _) (by positivity)) le_rfl
    _ = _ := by dsimp [C]; ring

lemma exists_bound_integrandDeriv_Ioc {ω₁ ω₂ : ℝ} (hω₁ : ω₁ ≠ 0)
    (hω₂ : ω₂ ≠ 0) (z : ℂ) (r : ℝ) :
    ∃ B : ℝ, ∀ w ∈ Metric.closedBall z r, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖integrandDeriv ω₁ ω₂ w t‖ ≤ B := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z r).prod (isCompact_Icc (a := (0 : ℝ))
    (b := 1))).exists_bound_of_continuousOn
      (continuous_regularizedDeriv hω₁ hω₂).continuousOn
  refine ⟨B, fun w hw t ht => ?_⟩
  rw [← regularizedDeriv_eq_integrandDeriv hω₁ hω₂ w (ne_of_gt ht.1)]
  exact hB (w, t) ⟨hw, ht.1.le, ht.2⟩

lemma measurable_integrand (ω₁ ω₂ : ℝ) (z : ℂ) :
    Measurable (integrand ω₁ ω₂ z) := by
  unfold integrand
  fun_prop

lemma measurable_integrandDeriv (ω₁ ω₂ : ℝ) (z : ℂ) :
    Measurable (integrandDeriv ω₁ ω₂ z) := by
  unfold integrandDeriv
  fun_prop

/-- An integrable majorant for the derivative, uniform on a closed parameter
ball lying inside the defining strip. -/
lemma exists_integrable_derivative_bound {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁)
    (hω₂ : 0 < ω₂) {z : ℂ} (hz₁ : 0 < z.re) (hz₂ : z.re < ω₁ + ω₂) :
    ∃ r : ℝ, 0 < r ∧ ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi 0) ∧
      ∀ t ∈ Ioi (0 : ℝ), ∀ w ∈ Metric.closedBall z r,
        ‖integrandDeriv ω₁ ω₂ w t‖ ≤ bound t := by
  let r := min z.re (ω₁ + ω₂ - z.re) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₁ : 2 * r ≤ z.re := by dsimp [r]; linarith [min_le_left z.re (ω₁ + ω₂ - z.re)]
  have hr₂ : 2 * r ≤ ω₁ + ω₂ - z.re := by
    dsimp [r]; linarith [min_le_right z.re (ω₁ + ω₂ - z.re)]
  have hstrip : ∀ w ∈ Metric.closedBall z r,
      r ≤ w.re ∧ w.re ≤ ω₁ + ω₂ - r := by
    intro w hw
    have hnorm : ‖w - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hre : |w.re - z.re| ≤ r := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (w - z)).trans hnorm
    constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
  obtain ⟨B, hB⟩ := exists_bound_integrandDeriv_Ioc hω₁.ne' hω₂.ne' z r
  let C := 4 * ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹
  let tail : ℝ → ℝ := fun t => C * Real.exp (-2 * r * t) + (ω₁ * ω₂)⁻¹ * (t ^ 2)⁻¹
  let bound : ℝ → ℝ := fun t => if t ≤ 1 then B else tail t
  have hnear : IntegrableOn bound (Ioc (0 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => B) (Icc (0 : ℝ) 1) :=
      continuous_const.continuousOn.integrableOn_Icc
    apply (hconst.mono_set Ioc_subset_Icc_self).congr_fun
    · intro t ht
      simp [bound, ht.2]
    · exact measurableSet_Ioc
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-2 * r * t)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hpow : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi 1) := by
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat] using
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1))
  have htail : IntegrableOn bound (Ioi 1) := by
    have hi : IntegrableOn tail (Ioi 1) := (hexp.const_mul C).add (hpow.const_mul (ω₁ * ω₂)⁻¹)
    apply hi.congr_fun
    · intro t ht
      change (1 : ℝ) < t at ht
      simp [bound, tail, not_le.mpr ht]
    · exact measurableSet_Ioi
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans zero_lt_one h
    · intro h
      by_cases ht : t ≤ 1
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr (lt_of_not_ge ht)
  refine ⟨r, hr, bound, ?_, ?_⟩
  · rw [← hu]
    exact hnear.union htail
  · intro t ht w hw
    by_cases ht₁ : t ≤ 1
    · simpa only [bound, if_pos ht₁] using hB w hw t ⟨ht, ht₁⟩
    · have hs := hstrip w hw
      simpa only [bound, if_neg ht₁, tail, C] using
        norm_integrandDeriv_le_tail hω₁ hω₂ hs.1 hs.2 (le_of_lt (lt_of_not_ge ht₁))

lemma integrableOn_integrandDeriv_and_hasDerivAt_integral {ω₁ ω₂ : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) {z : ℂ} (hz₁ : 0 < z.re)
    (hz₂ : z.re < ω₁ + ω₂) :
    IntegrableOn (integrandDeriv ω₁ ω₂ z) (Ioi 0) ∧
      HasDerivAt (fun w => ∫ t in Ioi (0 : ℝ), integrand ω₁ ω₂ w t)
        (∫ t in Ioi (0 : ℝ), integrandDeriv ω₁ ω₂ z t) z := by
  obtain ⟨r, hr, bound, hb, hbound⟩ := exists_integrable_derivative_bound hω₁ hω₂ hz₁ hz₂
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.closedBall_mem_nhds z hr)
    (Filter.Eventually.of_forall (fun w => (measurable_integrand ω₁ ω₂ w).aestronglyMeasurable))
    (integrableOn_integrand hω₁ hω₂ hz₁ hz₂)
    (measurable_integrandDeriv ω₁ ω₂ z).aestronglyMeasurable
    (bound := bound) ?_ hb
  · exact Filter.Eventually.of_forall (fun t w _ => hasDerivAt_integrand ω₁ ω₂ w t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht

lemma integrableOn_integrandDeriv {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    {z : ℂ} (hz₁ : 0 < z.re) (hz₂ : z.re < ω₁ + ω₂) :
    IntegrableOn (integrandDeriv ω₁ ω₂ z) (Ioi 0) :=
  (integrableOn_integrandDeriv_and_hasDerivAt_integral hω₁ hω₂ hz₁ hz₂).1

theorem hasDerivAt_logGamma {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    {z : ℂ} (hz₁ : 0 < z.re) (hz₂ : z.re < ω₁ + ω₂) :
    HasDerivAt (logGamma ω₁ ω₂) (-(∫ t in Ioi (0 : ℝ), integrandDeriv ω₁ ω₂ z t)) z :=
  (integrableOn_integrandDeriv_and_hasDerivAt_integral hω₁ hω₂ hz₁ hz₂).2.neg

theorem differentiableOn_gamma {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) :
    DifferentiableOn ℂ (gamma ω₁ ω₂) {z | 0 < z.re ∧ z.re < ω₁ + ω₂} := by
  intro z hz
  exact (hasDerivAt_logGamma hω₁ hω₂ hz.1 hz.2).cexp.differentiableAt.differentiableWithinAt

end HaagerupIzumi.GammaIntegral
