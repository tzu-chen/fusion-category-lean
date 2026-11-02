module

public import HaagerupIzumi.Analytic.GammaK4LocalCorrection
public import HaagerupIzumi.Analytic.GammaK4ParameterBoundary

/-! # Holomorphy of the corrected four-gamma integral

Fixed contour pieces represent the corrected integral locally, including
when poles of the same orientation merge. Their parameter derivatives
therefore establish holomorphy throughout the convergent non-pinched domain.
-/

@[expose] public section
noncomputable section

open Complex Set Filter
open scoped Topology

namespace HaagerupIzumi.GammaK4Contour

theorem differentiableAt_K4_scaled {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) (r s x y t : ℂ)
    (hc : K4Conv a b (t * r) (t * y))
    (hnp : K4NoPinch a b (t * r) (t * s) (t * x)) :
    DifferentiableAt ℂ
      (fun u => K4 a b hb hba.le (u * r) (u * s) (u * x) (u * y)) t := by
  obtain ⟨σ, P, lo, hi, horder, hline, hboundary, heq⟩ :=
    exists_local_scaledK4_representation a b hb hba.le hirr r s x y t hc hnp
  have hl := differentiableAt_scaledKernel_lineIntegral hb hba r s x y t σ hc hline
  have hs : DifferentiableAt ℂ
      (fun u => ∑ p ∈ P, rectBoundary (scaledKernel a b hb hba.le r s x y u) (lo p) (hi p)) t := by
    apply DifferentiableAt.fun_sum
    intro p hp
    exact differentiableAt_scaledKernel_rectBoundary_of_eventually a b hb hba.le r s x y t
      (lo p) (hi p) ⟨(horder p hp).1.le, (horder p hp).2.le⟩ (hboundary p hp)
  exact ((hl.add hs).div_const (I * (Real.sqrt (a * b) : ℂ))).congr_of_eventuallyEq heq

end HaagerupIzumi.GammaK4Contour
