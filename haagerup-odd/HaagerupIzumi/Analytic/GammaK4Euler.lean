module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4EulerSmall
public import HaagerupIzumi.Analytic.GammaK4ScalingDomain
public import Mathlib.Analysis.Analytic.Uniqueness

/-! # Continuing the Euler transformation along a complex scaling parameter

The convergence inequalities define an open convex domain. Removing the
countable closed set of pinches leaves it connected, so the initial Euler
identity extends from the origin to every regular scaling parameter.
-/

@[expose] public section
noncomputable section

open Complex Filter Set
open scoped Topology
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma eventually_eulerSmall_scaled {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (r s x y : ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0, EulerSmall a b (t * r) (t * s) (t * x) (t * y) := by
  have ho : IsOpen {t : ℂ | EulerSmall a b (t * r) (t * s) (t * x) (t * y)} := by
    unfold EulerSmall
    exact isOpen_lt (by fun_prop) continuous_const
  apply ho.mem_nhds
  simp only [mem_setOf_eq, EulerSmall, zero_mul, zero_re, abs_zero, zero_add]
  positivity

/-- The global Euler identity from holomorphy of the concrete corrected
contour along scaling lines. This separates the identity theorem from the
local moving-pole contour construction supplying the holomorphy premise. -/
theorem K4_euler_of_scaled_holomorphic {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b))
    (hhol : ∀ r s x y t : ℂ,
      K4Conv a b (t * r) (t * y) → K4NoPinch a b (t * r) (t * s) (t * x) →
      DifferentiableAt ℂ (fun u => K4 a b hb hba.le (u * r) (u * s) (u * x) (u * y)) t)
    (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hconv' : K4Conv a b (-r) y)
    (hnp : K4NoPinch a b r s x) (hnp' : K4NoPinch a b (-r) s x) :
    Γr (gamma a b hb hba.le) a b r y * K4 a b hb hba.le r s x y =
      Γr (gamma a b hb hba.le) a b r s * Γr (gamma a b hb hba.le) a b r x *
        K4 a b hb hba.le (-r) s x y := by
  let D := eulerScaleDomain a b r y \ eulerScaleForbidden a b r s x
  have ha := hb.trans hba
  have ho : IsOpen D := eulerScaleRegular_isOpen ha hb r s x y
  have hc : IsConnected D := eulerScaleRegular_isConnected ha hb r s x y
  have h₀ : (0 : ℂ) ∈ D :=
    ⟨zero_mem_eulerScaleDomain ha hb r y, zero_not_mem_eulerScaleForbidden ha hb r s x⟩
  have h₁ : (1 : ℂ) ∈ D :=
    ⟨(one_mem_eulerScaleDomain_iff a b r y).mpr ⟨hconv, hconv'⟩,
      (one_not_mem_eulerScaleForbidden_iff a b r s x).mpr ⟨hnp, hnp'⟩⟩
  have hk : DifferentiableOn ℂ
      (fun t => K4 a b hb hba.le (t * r) (t * s) (t * x) (t * y)) D := by
    intro t ht
    exact (hhol r s x y t
      ((mem_eulerScaleDomain_iff a b r y t).mp ht.1).1
      ((not_mem_eulerScaleForbidden_iff a b r s x t).mp ht.2).1).differentiableWithinAt
  have hk' : DifferentiableOn ℂ
      (fun t => K4 a b hb hba.le (-(t * r)) (t * s) (t * x) (t * y)) D := by
    intro t ht
    have hd := hhol (-r) s x y t
      (by simpa only [mul_neg] using ((mem_eulerScaleDomain_iff a b r y t).mp ht.1).2)
      (by simpa only [mul_neg] using ((not_mem_eulerScaleForbidden_iff a b r s x t).mp ht.2).2)
    simpa only [mul_neg] using hd.differentiableWithinAt (s := D)
  have hf : AnalyticOnNhd ℂ
      (fun t => Γr (gamma a b hb hba.le) a b (t * r) (t * y) *
        K4 a b hb hba.le (t * r) (t * s) (t * x) (t * y)) D := by
    intro t ht
    exact (analyticAt_eulerScaleGamma_y hb hba.le r y ht.1).mul ((hk.analyticOnNhd ho) t ht)
  have hg : AnalyticOnNhd ℂ
      (fun t => Γr (gamma a b hb hba.le) a b (t * r) (t * s) *
        Γr (gamma a b hb hba.le) a b (t * r) (t * x) *
        K4 a b hb hba.le (-(t * r)) (t * s) (t * x) (t * y)) D := by
    intro t ht
    exact ((analyticAt_eulerScaleGamma_s hb hba.le r s x ht.2).mul
      (analyticAt_eulerScaleGamma_x hb hba.le r s x ht.2)).mul ((hk'.analyticOnNhd ho) t ht)
  have hnear :
      (fun t => Γr (gamma a b hb hba.le) a b (t * r) (t * y) *
        K4 a b hb hba.le (t * r) (t * s) (t * x) (t * y)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => Γr (gamma a b hb hba.le) a b (t * r) (t * s) *
        Γr (gamma a b hb hba.le) a b (t * r) (t * x) *
        K4 a b hb hba.le (-(t * r)) (t * s) (t * x) (t * y)) := by
    filter_upwards [eventually_eulerSmall_scaled ha hb r s x y] with t ht
    exact K4_euler_small hb hba hirr ht
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc.isPreconnected h₀ hnear h₁
  simpa only [one_mul] using heq

end HaagerupIzumi.GammaK4Contour
