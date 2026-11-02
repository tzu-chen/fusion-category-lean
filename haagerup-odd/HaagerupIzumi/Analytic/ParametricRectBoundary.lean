module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.ParametricCompactIntegral
public import HaagerupIzumi.Analytic.GammaKernelRegularity

/-! # Holomorphic integrals on a fixed rectangle boundary -/

@[expose] public section
noncomputable section

open Complex MeasureTheory Metric Set

namespace HaagerupIzumi

/-- A fixed rectangle integral is holomorphic in a parameter when its
boundary remains free of singularities on a parameter disk. -/
theorem differentiableAt_rectBoundary_of_holomorphic
    {F : ℂ → ℂ → ℂ} {z₀ z w : ℂ} {r : ℝ}
    (hr : 0 < r) (hzw : z.re ≤ w.re ∧ z.im ≤ w.im)
    (hmeas : Measurable (fun p : ℂ × ℂ => F p.1 p.2))
    (hc : ∀ t ∈ closedBall z₀ (2 * r), ∀ ζ, OnBoundary ζ z w →
      ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (t, ζ))
    (hd : ∀ t ∈ closedBall z₀ (2 * r), ∀ ζ, OnBoundary ζ z w →
      DifferentiableAt ℂ (fun v => F v ζ) t) :
    DifferentiableAt ℂ (fun t => rectBoundary (F t) z w) z₀ := by
  have key (g : ℝ → ℂ) (hg : Continuous g) (α β : ℝ) (hαβ : α ≤ β)
      (hside : ∀ u ∈ Icc α β, OnBoundary (g u) z w) :
      DifferentiableAt ℂ (fun t => ∫ u in α..β, F t (g u)) z₀ := by
    apply differentiableAt_intervalIntegral_of_compact hr hαβ
    · intro t
      exact (hmeas.comp (show Measurable (fun u => (t, g u)) by fun_prop)).aestronglyMeasurable
    · intro p hp
      exact ((hc p.1 hp.1 (g p.2) (hside p.2 hp.2)).comp
        (f := fun q : ℂ × ℝ => (q.1, g q.2)) (x := p) (by fun_prop)).continuousWithinAt
    · intro u hu t ht
      exact hd t ht (g u) (hside u hu)
  have hbottom := key (fun u => u + z.im * I) (by fun_prop) z.re w.re hzw.1 (by
    intro u hu
    refine ⟨?_, Or.inl (by simp)⟩
    rw [mem_closedRect]
    simp
    exact ⟨hu, hzw.2⟩)
  have htop := key (fun u => u + w.im * I) (by fun_prop) z.re w.re hzw.1 (by
    intro u hu
    refine ⟨?_, Or.inr (Or.inl (by simp))⟩
    rw [mem_closedRect]
    simp
    exact ⟨hu, hzw.2⟩)
  have hright := key (fun u => w.re + u * I) (by fun_prop) z.im w.im hzw.2 (by
    intro u hu
    refine ⟨?_, Or.inr (Or.inr (Or.inr (by simp)))⟩
    rw [mem_closedRect]
    simp
    exact ⟨hzw.1, hu⟩)
  have hleft := key (fun u => z.re + u * I) (by fun_prop) z.im w.im hzw.2 (by
    intro u hu
    refine ⟨?_, Or.inr (Or.inr (Or.inl (by simp)))⟩
    rw [mem_closedRect]
    simp
    exact ⟨hzw.1, hu⟩)
  exact ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)

namespace GammaK4Contour

/-- Holomorphy of a fixed rectangle correction for the actual gamma kernel. -/
theorem differentiableAt_scaledKernel_rectBoundary
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (R S X Y : ℂ)
    {t₀ z w : ℂ} {r : ℝ} (hr : 0 < r) (hzw : z.re ≤ w.re ∧ z.im ≤ w.im)
    (hp : ∀ t ∈ closedBall t₀ (2 * r), ∀ ζ, OnBoundary ζ z w →
      ζ ∉ leftPoles a b (t * R) (t * S) (t * X) ∪
        rightPoles a b (t * R) (t * S) (t * X)) :
    DifferentiableAt ℂ
      (fun t => rectBoundary (scaledKernel a b hb hba R S X Y t) z w) t₀ := by
  apply differentiableAt_rectBoundary_of_holomorphic hr hzw
    (measurable_scaledKernel a b hb hba R S X Y)
  · intro t ht ζ hζ
    exact continuousAt_scaledKernel a b hb hba R S X Y (t, ζ) (hp t ht ζ hζ)
  · intro t ht ζ hζ
    exact differentiableAt_scaledKernel_parameter a b hb hba R S X Y t ζ (hp t ht ζ hζ)

end GammaK4Contour
end HaagerupIzumi
