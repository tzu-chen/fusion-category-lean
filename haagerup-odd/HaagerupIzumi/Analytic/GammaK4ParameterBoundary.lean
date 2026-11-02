module

public import HaagerupIzumi.Analytic.ParametricRectBoundary
public import HaagerupIzumi.Analytic.GammaK4ParameterLine

/-! # Local parameter holomorphy of fixed contour pieces -/

@[expose] public section
noncomputable section

open Complex Set Metric Filter MeasureTheory
open scoped Topology

namespace HaagerupIzumi.GammaK4Contour

theorem differentiableAt_scaledKernel_lineIntegral {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (r s x y t₀ : ℂ) (σ : ℝ)
    (hc : K4Conv a b (t₀ * r) (t₀ * y))
    (havoid : ∀ᶠ w in 𝓝 t₀, AvoidsPoles a b (w * r) (w * s) (w * x) σ) :
    DifferentiableAt ℂ
      (fun w => lineIntegral (scaledKernel a b hb hba.le r s x y w) σ) t₀ := by
  have hd := (differentiableAt_scaledKernel_line_integral hb hba r s x y t₀ σ hc havoid).mul_const I
  simpa only [lineIntegral, integral_mul_const] using hd

theorem differentiableAt_scaledKernel_rectBoundary_of_eventually
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y t₀ z w : ℂ)
    (hzw : z.re ≤ w.re ∧ z.im ≤ w.im)
    (hp : ∀ᶠ t in 𝓝 t₀, ∀ ζ, OnBoundary ζ z w →
      ζ ∉ leftPoles a b (t * r) (t * s) (t * x) ∪
        rightPoles a b (t * r) (t * s) (t * x)) :
    DifferentiableAt ℂ
      (fun t => rectBoundary (scaledKernel a b hb hba r s x y t) z w) t₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hp
  apply differentiableAt_scaledKernel_rectBoundary a b hb hba r s x y
    (r := δ / 4) (div_pos hδ (by norm_num)) hzw
  intro t ht
  apply hball
  have hd := mem_closedBall.mp ht
  linarith

end HaagerupIzumi.GammaK4Contour
