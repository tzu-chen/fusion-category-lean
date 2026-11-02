module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ParametricIntegral
import all Mathlib.Data.Complex.Basic

/-!
# Differentiating a dominated holomorphic family

A bound for the functions on a disk gives the needed derivative bound on a
smaller disk by Cauchy's estimate. No asymptotic estimate for derivatives is
required.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace HaagerupIzumi

theorem hasDerivAt_integral_of_holomorphic_bound
    {F F' : ℂ → ℝ → ℂ} {z₀ : ℂ} {r : ℝ} {bound : ℝ → ℝ}
    (hr : 0 < r)
    (hcont : ∀ w ∈ closedBall z₀ (2 * r), Continuous (F w))
    (hcont' : Continuous (F' z₀))
    (hd : ∀ t : ℝ, ∀ w ∈ closedBall z₀ (2 * r),
      HasDerivAt (fun z => F z t) (F' w t) w)
    (hbound : ∀ t : ℝ, ∀ w ∈ closedBall z₀ (2 * r), ‖F w t‖ ≤ bound t)
    (hbound_int : Integrable bound) :
    Integrable (F' z₀) ∧
      HasDerivAt (fun z => ∫ t : ℝ, F z t) (∫ t : ℝ, F' z₀ t) z₀ := by
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
  have hd_bound : ∀ t : ℝ, ∀ w ∈ ball z₀ r, ‖F' w t‖ ≤ bound t / r := by
    intro t w hw
    have hdiff : DiffContOnCl ℂ (fun z => F z t) (ball w r) := by
      apply DiffContOnCl.mk_ball
      · intro v hv
        exact (hd t v (hsub hw (ball_subset_closedBall hv))).differentiableAt.differentiableWithinAt
      · intro v hv
        exact (hd t v (hsub hw hv)).continuousAt.continuousWithinAt
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff
      (fun v hv => hbound t v (hsub hw (sphere_subset_closedBall hv)))
    rwa [(hd t w (hsmall hw)).deriv] at hh
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => bound t / r) (ball_mem_nhds z₀ hr)
  · filter_upwards [ball_mem_nhds z₀ hr] with w hw
    exact (hcont w (hsmall hw)).aestronglyMeasurable
  · exact hbound_int.mono' (hcont z₀ hcenter).aestronglyMeasurable
      (ae_of_all _ (fun t => hbound t z₀ hcenter))
  · exact hcont'.aestronglyMeasurable
  · exact ae_of_all _ hd_bound
  · exact hbound_int.div_const r
  · exact ae_of_all _ (fun t w hw => hd t w (hsmall hw))

end HaagerupIzumi
