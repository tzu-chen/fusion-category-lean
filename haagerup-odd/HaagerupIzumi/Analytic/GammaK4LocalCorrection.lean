module

public import HaagerupIzumi.Analytic.GammaK4MovingGeometry
import all Mathlib.Data.Complex.Basic

/-! # A local fixed-contour representation of the corrected K4 function -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaMovingPoleRectangles
open HaagerupIzumi.MovingPoleRectangles

namespace HaagerupIzumi.GammaK4Contour

/-- Near each non-pinched convergent parameter, K4 is a fixed vertical line
integral plus finitely many fixed counterclockwise rectangle integrals. -/
theorem exists_local_scaledK4_representation (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y t₀ : ℂ)
    (hc : K4Conv a b (t₀ * r) (t₀ * y)) (hnp : K4NoPinch a b (t₀ * r) (t₀ * s) (t₀ * x)) :
    ∃ (σ : ℝ) (P : Finset ℂ) (lo hi : ℂ → ℂ),
      (∀ p ∈ P, (lo p).re < (hi p).re ∧ (lo p).im < (hi p).im) ∧
      (∀ᶠ t in 𝓝 t₀, AvoidsPoles a b (t * r) (t * s) (t * x) σ) ∧
      (∀ p ∈ P, ∀ᶠ t in 𝓝 t₀, ∀ z, OnBoundary z (lo p) (hi p) →
        z ∉ leftPoles a b (t * r) (t * s) (t * x) ∪ rightPoles a b (t * r) (t * s) (t * x)) ∧
      (∀ᶠ t in 𝓝 t₀, K4 a b hb hba (t * r) (t * s) (t * x) (t * y) =
        (lineIntegral (scaledKernel a b hb hba r s x y t) σ +
          ∑ p ∈ P, rectBoundary (scaledKernel a b hb hba r s x y t) (lo p) (hi p)) /
          (I * (Real.sqrt (a * b) : ℂ))) := by
  classical
  let L := scaledLeftOffsets a b r s x
  let R := scaledRightOffsets a b r s x
  let σ := startLine a b (t₀ * r) (t₀ * s) (t₀ * x)
  let P := crossedLeftPoints a b hb hba (fun i => L i t₀) σ
  have hL : ∀ i, ContinuousAt (L i) t₀ := fun i => (continuous_scaledLeftOffsets a b r s x i).continuousAt
  have hR : ∀ i, ContinuousAt (R i) t₀ := fun i => (continuous_scaledRightOffsets a b r s x i).continuousAt
  have hσL : ∀ i q, q ∈ leftFamily a b (L i t₀) → q.re ≠ σ := by
    intro i q hq
    exact (startLine_spec a b (t₀ * r) (t₀ * s) (t₀ * x)).2 q
      ((mem_leftPoles_scaled a b r s x t₀ q).mpr ⟨i, hq⟩)
  have hσR : ∀ i, σ < (R i t₀).re := by
    rw [Fin.forall_fin_two]
    exact lt_min_iff.mp (startLine_spec a b (t₀ * r) (t₀ * s) (t₀ * x)).1
  have hP : ∀ p ∈ P, ∃ i, p ∈ family a b (fun j => L j t₀) (fun j => R j t₀) i := by
    intro p hp
    obtain ⟨i, hi, _⟩ := (mem_crossedLeftPoints a b hb hba _ σ p).mp hp
    exact ⟨.inl i, hi⟩
  obtain ⟨ε, hε, hsep, hrect⟩ := exists_cluster_radii a b hb hba L R t₀ hL hR P hP
  have hcross := eventually_left_crossing_iff a b hb hba L t₀ σ hL hσL
  have hright := eventually_right_above a b hb hba R t₀ σ hR hσR
  have havoid : ∀ᶠ t in 𝓝 t₀, AvoidsPoles a b (t * r) (t * s) (t * x) σ := by
    filter_upwards [hcross, hright] with t htL htR
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := (mem_leftPoles_scaled a b r s x t z).mp hz
      let q := z - (L i t₀ - L i t)
      have hq : q ∈ leftFamily a b (L i t₀) := by
        apply (mem_family_translate a b L R t₀ t (.inl i) q).mp
        simpa only [q, displacement, sub_add_cancel, family, L] using hi
      simpa only [q, sub_add_cancel] using (htL i q hq).2
    · obtain ⟨i, hi⟩ := (mem_rightPoles_scaled a b r s x t z).mp hz
      exact ne_of_gt (htR i z hi)
  refine ⟨σ, P, (fun p => lower p (ε p)), (fun p => upper p (ε p)),
    fun p _ => lower_lt_upper p (hε p), havoid, ?_, ?_⟩
  · intro p hp
    filter_upwards [hrect] with t ht
    intro z hz hzp
    obtain ⟨i, hi⟩ := (mem_scaled_families a b r s x t z).mpr hzp
    exact (ht p hp).2.2 i z hi hz
  · filter_upwards [hrect, hcross, hright, havoid,
      eventually_scaled_conv a b r y t₀ hc, eventually_scaled_noPinch a b hb hba r s x t₀ hnp]
      with t htRect htCross htRight htAvoid htConv htNp
    have hSL : crossedLeft a b hb hba (t * r) (t * s) (t * x) σ =
        P.biUnion (clusters a b L R t₀ t) := by
      rw [crossedLeft_eq_points]
      exact crossedLeftPoints_eq_biUnion_clusters a b hb hba L R t₀ t σ
        (fun i q hq => (htCross i q hq).1) (scaled_families_disjoint a b r s x t₀ hnp)
    have hSR : crossedRight a b hb hba (t * r) (t * s) (t * x) σ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hz, hzσ⟩ := (mem_crossedRight a b hb hba _ _ _ σ z).mp hz
      obtain ⟨i, hi⟩ := (mem_rightPoles_scaled a b r s x t z).mp hz
      exact (not_lt_of_ge (htRight i z hi).le) hzσ
    have hd : ∀ z, z ∉ translatedUnion (family a b (fun i => L i t₀) (fun i => R i t₀))
        (fun i => displacement L R t₀ i t) →
        DifferentiableAt ℂ (scaledKernel a b hb hba r s x y t) z := by
      intro z hz
      apply kernel_differentiableAt a b hb hba (t * r) (t * s) (t * x) (t * y) z
      intro hzp
      obtain ⟨i, hi⟩ := (mem_scaled_families a b r s x t z).mpr hzp
      apply hz
      refine ⟨i, z - displacement L R t₀ i t, ?_, by ring⟩
      apply (mem_family_translate a b L R t₀ t i _).mp
      simpa only [sub_add_cancel] using hi
    have hsum := sum_rectBoundary_eq_sum_residues
      (family a b (fun i => L i t₀) (fun i => R i t₀)) (fun i => displacement L R t₀ i t) P ε
      (fun p _ => hε p) hsep (fun p hp => (htRect p hp).1) (fun p hp => (htRect p hp).2.1)
      (scaledKernel a b hb hba r s x y t)
      (fun z => kernel_exists_hasResidueGen a b hb hba hirr (t * r) (t * s) (t * x) (t * y) z htNp) hd
    change (∑ p ∈ P, rectBoundary (scaledKernel a b hb hba r s x y t) (lower p (ε p)) (upper p (ε p))) =
      2 * Real.pi * I * ∑ z ∈ P.biUnion (clusters a b L R t₀ t),
        residueValue (scaledKernel a b hb hba r s x y t) z at hsum
    rw [← hSL] at hsum
    have hline := (K4_line a b hb hba hirr (t * r) (t * s) (t * x) (t * y)
      htConv htNp σ htAvoid).2
    rw [hSR] at hline
    unfold CorrectedContour.value at hline
    simp only [Finset.sum_empty, mul_zero, sub_zero] at hline
    have hdenom : I * (Real.sqrt (a * b) : ℂ) ≠ 0 :=
      mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.mpr (mul_pos (hb.trans_le hba) hb))))
    apply (eq_div_iff hdenom).mpr
    rw [hsum]
    exact (mul_comm _ _).trans hline.symm

end HaagerupIzumi.GammaK4Contour
