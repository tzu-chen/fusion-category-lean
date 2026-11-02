module

public import HaagerupIzumi.Analytic.DominatedHolomorphic
public import Mathlib.Analysis.Calculus.Deriv.Slope
import all Mathlib.Data.Complex.Basic

/-!
# Holomorphic parameter integrals for arbitrary measures

Difference quotients give measurability of the derivative. Cauchy's estimate
then turns an integrable bound for a holomorphic family into a derivative
bound on a smaller disk. The hypotheses hold almost everywhere, so the
result applies to both complete vertical lines and compact contour edges.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace HaagerupIzumi

lemma aestronglyMeasurable_parameter_deriv {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F : ℂ → X → ℂ} {F' : X → ℂ} {z₀ : ℂ}
    (hF : ∀ w : ℂ, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, HasDerivAt (fun w => F w t) (F' t) z₀) :
    AEStronglyMeasurable F' μ := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun h t => h⁻¹ • (F (z₀ + h) t - F z₀ t))
  · intro h
    exact ((hF (z₀ + h)).sub (hF z₀)).const_smul h⁻¹
  · filter_upwards [hd] with t ht
    exact ht.tendsto_slope_zero

theorem hasDerivAt_integral_of_holomorphic_bound_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {bound : X → ℝ}
    (hr : 0 < r)
    (hmeas : ∀ w : ℂ, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, ∀ w ∈ closedBall z₀ (2 * r), DifferentiableAt ℂ (fun z => F z t) w)
    (hbound : ∀ᵐ t ∂μ, ∀ w ∈ closedBall z₀ (2 * r), ‖F w t‖ ≤ bound t)
    (hint : Integrable bound μ) :
    Integrable (fun t => deriv (fun z => F z t) z₀) μ ∧
      HasDerivAt (fun z => ∫ t, F z t ∂μ) (∫ t, deriv (fun z => F z t) z₀ ∂μ) z₀ := by
  let F' : ℂ → X → ℂ := fun w t => deriv (fun z => F z t) w
  have hcenter : z₀ ∈ closedBall z₀ (2 * r) := mem_closedBall_self (by positivity)
  have hsmall : ball z₀ r ⊆ closedBall z₀ (2 * r) := by
    intro w hw
    rw [mem_closedBall]
    have := mem_ball.mp hw
    linarith
  have hsub {w : ℂ} (hw : w ∈ ball z₀ r) :
      closedBall w r ⊆ closedBall z₀ (2 * r) := by
    intro v hv
    rw [mem_closedBall] at hv ⊢
    have := dist_triangle v w z₀
    have := mem_ball.mp hw
    linarith
  have hderivbound : ∀ᵐ t ∂μ, ∀ w ∈ ball z₀ r, ‖F' w t‖ ≤ bound t / r := by
    filter_upwards [hd, hbound] with t hdt hbt
    intro w hw
    have hdiff : DiffContOnCl ℂ (fun z => F z t) (ball w r) := by
      apply DiffContOnCl.mk_ball
      · intro v hv
        exact (hdt v (hsub hw (ball_subset_closedBall hv))).differentiableWithinAt
      · intro v hv
        exact (hdt v (hsub hw hv)).continuousAt.continuousWithinAt
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff
      (fun v hv => hbt v (hsub hw (sphere_subset_closedBall hv)))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => bound t / r) (ball_mem_nhds z₀ hr)
  · exact Filter.Eventually.of_forall hmeas
  · exact hint.mono' (hmeas z₀) (hbound.mono fun t ht => ht z₀ hcenter)
  · apply aestronglyMeasurable_parameter_deriv μ hmeas
    filter_upwards [hd] with t ht
    exact (ht z₀ hcenter).hasDerivAt
  · exact hderivbound
  · exact hint.div_const r
  · filter_upwards [hd] with t ht
    intro w hw
    exact (ht w (hsmall hw)).hasDerivAt

theorem differentiableAt_integral_of_holomorphic_bound_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {bound : X → ℝ}
    (hr : 0 < r)
    (hmeas : ∀ w : ℂ, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, ∀ w ∈ closedBall z₀ (2 * r), DifferentiableAt ℂ (fun z => F z t) w)
    (hbound : ∀ᵐ t ∂μ, ∀ w ∈ closedBall z₀ (2 * r), ‖F w t‖ ≤ bound t)
    (hint : Integrable bound μ) : DifferentiableAt ℂ (fun z => ∫ t, F z t ∂μ) z₀ :=
  (hasDerivAt_integral_of_holomorphic_bound_measure μ hr hmeas hd hbound hint).2.differentiableAt

end HaagerupIzumi
