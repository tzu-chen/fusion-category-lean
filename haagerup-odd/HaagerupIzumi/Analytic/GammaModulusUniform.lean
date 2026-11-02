module

public import HaagerupIzumi.Analytic.GammaModulus
public import HaagerupIzumi.Analytic.GammaHolomorphic
public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Data.Complex.Basic

/-!
# Uniform control of the gamma modulus on compact substrips

At the midpoint the regularized kernel vanishes. A derivative bound on a
fixed parameter ball therefore gives a uniform endpoint bound by the mean
value theorem. The explicit exponential tail controls the other endpoint.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace HaagerupIzumi.GammaIntegral

lemma exists_bound_realIntegrand_Ioc {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) :
    ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (ω₁ + ω₂), ∀ t ∈ Ioc (0 : ℝ) 1,
      |realIntegrand ω₁ ω₂ x t| ≤ B := by
  let Ω := ω₁ + ω₂
  let m : ℝ := Ω / 2
  have hΩ : 0 < Ω := add_pos hω₁ hω₂
  obtain ⟨B, hB⟩ := exists_bound_integrandDeriv_Ioc hω₁.ne' hω₂.ne' (0 : ℂ) Ω
  have hmem (x : ℝ) (hx : x ∈ Icc (0 : ℝ) Ω) : (x : ℂ) ∈ Metric.closedBall 0 Ω := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hm : m ∈ Icc (0 : ℝ) Ω := by
    constructor <;> dsimp [m] <;> linarith
  refine ⟨|B| * Ω, fun x hx t ht => ?_⟩
  have hmid : integrand ω₁ ω₂ (m : ℂ) t = 0 := by
    simpa [m, Ω, Complex.ofReal_div] using integrand_midpoint ω₁ ω₂ t
  have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w (_ : w ∈ Metric.closedBall (0 : ℂ) Ω) =>
      (hasDerivAt_integrand ω₁ ω₂ w t).hasDerivWithinAt)
    (fun w hw => (hB w hw t ht).trans (le_abs_self B))
    (convex_closedBall (0 : ℂ) Ω) (hmem m hm) (hmem x hx)
  rw [hmid, sub_zero, integrand_ofReal, Complex.norm_real, Real.norm_eq_abs] at hdiff
  have hdist : ‖(x : ℂ) - (m : ℂ)‖ ≤ Ω := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [m]
    constructor <;> linarith [hx.1, hx.2]
  exact hdiff.trans (mul_le_mul_of_nonneg_left hdist (abs_nonneg B))

/-- A single integrable real majorant for all real-axis remainder kernels
whose parameters lie in a prescribed compact substrip. -/
lemma exists_uniform_realIntegrand_majorant {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi 0) ∧
      ∀ x ∈ Icc a b, ∀ t ∈ Ioi (0 : ℝ), |realIntegrand ω₁ ω₂ x t| ≤ bound t := by
  let Ω := ω₁ + ω₂
  let δ := min a (Ω - b)
  have hΩ : 0 < Ω := add_pos hω₁ hω₂
  have hδ : 0 < δ := lt_min ha (by dsimp [Ω]; linarith)
  let C := 2 * ((1 - Real.exp (-2 * ω₁)) * (1 - Real.exp (-2 * ω₂)))⁻¹
  let tail : ℝ → ℝ := fun t => C * Real.exp (-2 * δ * t) +
    Ω / (2 * ω₁ * ω₂) * (t ^ 2)⁻¹
  obtain ⟨B, hB⟩ := exists_bound_realIntegrand_Ioc hω₁ hω₂
  let bound : ℝ → ℝ := fun t => if t ≤ 1 then B else tail t
  have hnear : IntegrableOn bound (Ioc (0 : ℝ) 1) := by
    have hi : IntegrableOn (fun _ : ℝ => B) (Icc (0 : ℝ) 1) :=
      continuous_const.continuousOn.integrableOn_Icc
    apply (hi.mono_set Ioc_subset_Icc_self).congr_fun
    · intro t ht
      simp [bound, ht.2]
    · exact measurableSet_Ioc
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-2 * δ * t)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hpow : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi 1) := by
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat] using
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1))
  have htail : IntegrableOn bound (Ioi 1) := by
    have hi : IntegrableOn tail (Ioi 1) :=
      (hexp.const_mul C).add (hpow.const_mul (Ω / (2 * ω₁ * ω₂)))
    apply hi.congr_fun
    · intro t ht
      change (1 : ℝ) < t at ht
      simp only [bound, if_neg (not_le.mpr ht)]
    · exact measurableSet_Ioi
  refine ⟨bound, ?_, fun x hx t ht => ?_⟩
  · rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hnear.union htail
  · have hxpos : 0 < x := ha.trans_le hx.1
    have hxupper : x < Ω := hx.2.trans_lt hb
    by_cases ht₁ : t ≤ 1
    · simpa only [bound, if_pos ht₁] using hB x ⟨hxpos.le, hxupper.le⟩ t ⟨ht, ht₁⟩
    · have hxδ₁ : δ ≤ (x : ℂ).re := (min_le_left _ _).trans hx.1
      have hxδ₂ : (x : ℂ).re ≤ ω₁ + ω₂ - δ := by
        have := min_le_right a (Ω - b)
        dsimp [δ, Ω] at *
        linarith [hx.2]
      have hc : ‖center ω₁ ω₂ (x : ℂ)‖ ≤ Ω := by
        have he : center ω₁ ω₂ (x : ℂ) = ((2 * x - Ω : ℝ) : ℂ) := by
          simp only [center, Ω, Complex.ofReal_sub, Complex.ofReal_mul,
            Complex.ofReal_add, Complex.ofReal_ofNat]
        rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have hh := norm_integrand_le_tail hω₁ hω₂ hxδ₁ hxδ₂ (le_of_not_ge ht₁)
      rw [integrand_ofReal, Complex.norm_real, Real.norm_eq_abs] at hh
      simp only [bound, if_neg ht₁, tail, C]
      refine hh.trans (add_le_add le_rfl ?_)
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (by positivity)) (inv_nonneg.mpr (sq_nonneg t))

/-- The error constant in the logarithmic modulus estimate is uniformly
bounded on every compact real interval inside the strip. -/
theorem exists_uniform_modulusError_bound {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, modulusError ω₁ ω₂ x ≤ C := by
  obtain ⟨bound, hbint, hbound⟩ := exists_uniform_realIntegrand_majorant hω₁ hω₂ ha hb
  refine ⟨∫ t in Ioi (0 : ℝ), bound t, fun x hx => ?_⟩
  have hi := (integrableOn_realIntegrand hω₁ hω₂ (ha.trans_le hx.1)
    (hx.2.trans_lt hb)).norm
  apply integral_mono_ae hi hbint
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound x hx t ht

/-- The oscillatory error in the vertical logarithmic modulus formula is
uniform in both height and the real coordinate on compact substrips. -/
theorem log_norm_gamma_vertical_uniform {ω₁ ω₂ a b : ℝ}
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : 0 < a) (hb : b < ω₁ + ω₂) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ,
      |Real.log ‖gamma ω₁ ω₂ ((x : ℂ) + y * I)‖ -
        modulusSlope ω₁ ω₂ x * cosineMass y| ≤ C := by
  obtain ⟨C, hC⟩ := exists_uniform_modulusError_bound hω₁ hω₂ ha hb
  refine ⟨C, fun x hx y => ?_⟩
  exact (log_norm_gamma_vertical_bound hω₁ hω₂ (ha.trans_le hx.1)
    (hx.2.trans_lt hb) y).trans (hC x hx)

end HaagerupIzumi.GammaIntegral
