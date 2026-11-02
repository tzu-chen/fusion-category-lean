module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.ParametricHolomorphic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Holomorphic parameter integrals over compact real sets -/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace HaagerupIzumi

/-- Joint continuity on a compact parameter disk times a compact integration
set supplies the constant majorant for holomorphic differentiation. -/
theorem differentiableAt_setIntegral_of_compact
    {F : ℂ → ℝ → ℂ} {z₀ : ℂ} {r : ℝ} {K : Set ℝ}
    (hr : 0 < r) (hK : IsCompact K)
    (hmeas : ∀ w : ℂ, AEStronglyMeasurable (F w))
    (hc : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (closedBall z₀ (2 * r) ×ˢ K))
    (hd : ∀ t ∈ K, ∀ w ∈ closedBall z₀ (2 * r), DifferentiableAt ℂ (fun z => F z t) w) :
    DifferentiableAt ℂ (fun z => ∫ t in K, F z t) z₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z₀ (2 * r)).prod hK).exists_bound_of_continuousOn hc
  apply differentiableAt_integral_of_holomorphic_bound_measure (volume.restrict K)
    (bound := fun _ => B) hr (fun w => (hmeas w).restrict)
  · filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with t ht
    exact hd t ht
  · filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with t ht
    intro w hw
    exact hB (w, t) ⟨hw, ht⟩
  · exact integrableOn_const hK.measure_lt_top.ne

/-- The ordered interval version, including either degenerate endpoint. -/
theorem differentiableAt_intervalIntegral_of_compact
    {F : ℂ → ℝ → ℂ} {z₀ : ℂ} {r α β : ℝ}
    (hr : 0 < r) (hαβ : α ≤ β)
    (hmeas : ∀ w : ℂ, AEStronglyMeasurable (F w))
    (hc : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2)
      (closedBall z₀ (2 * r) ×ˢ Icc α β))
    (hd : ∀ t ∈ Icc α β, ∀ w ∈ closedBall z₀ (2 * r),
      DifferentiableAt ℂ (fun z => F z t) w) :
    DifferentiableAt ℂ (fun z => ∫ t in α..β, F z t) z₀ := by
  have heq : (fun z => ∫ t in α..β, F z t) = (fun z => ∫ t in Icc α β, F z t) := by
    funext z
    rw [intervalIntegral.integral_of_le hαβ, integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact differentiableAt_setIntegral_of_compact hr isCompact_Icc hmeas hc hd

end HaagerupIzumi
