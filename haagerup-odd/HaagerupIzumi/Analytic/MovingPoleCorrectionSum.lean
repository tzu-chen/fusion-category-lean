module

public import HaagerupIzumi.Analytic.MovingPoleClusters
import all Mathlib.Data.Complex.Basic

/-! # Summing fixed rectangle corrections over distinct moving clusters -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology

namespace HaagerupIzumi.MovingPoleRectangles

theorem sum_rectBoundary_eq_sum_residues {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (d : ι → ℂ) (P : Finset ℂ) (ε : ℂ → ℝ)
    (hε : ∀ p ∈ P, 0 < ε p)
    (hsep : Set.PairwiseDisjoint (P : Set ℂ)
      (fun p => closedRect (lower p (ε p)) (upper p (ε p))))
    (hopen : ∀ p ∈ P, ∀ i, InOpenRect (p + d i) (lower p (ε p)) (upper p (ε p)))
    (hcapture : ∀ p ∈ P, ∀ i q, q ∈ S i →
      (q + d i ∈ closedRect (lower p (ε p)) (upper p (ε p)) ↔ q = p))
    (f : ℂ → ℂ) (hres : ∀ z, ∃ ρ, HasResidueGen f z ρ)
    (hd : ∀ z, z ∉ translatedUnion S d → DifferentiableAt ℂ f z) :
    (∑ p ∈ P, rectBoundary f (lower p (ε p)) (upper p (ε p))) =
      2 * Real.pi * I * ∑ z ∈ P.biUnion (clusterPoints S d), residueValue f z := by
  classical
  have hdisj : Set.PairwiseDisjoint (P : Set ℂ) (clusterPoints S d) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro z hzp hzq
    exact Set.disjoint_left.mp (hsep hp hq hpq)
      ((clusterPoints_inOpenRect S d p (ε p) (hopen p hp) z hzp).mem_closedRect)
      ((clusterPoints_inOpenRect S d q (ε q) (hopen q hq) z hzq).mem_closedRect)
  calc
    _ = ∑ p ∈ P, 2 * Real.pi * I * ∑ z ∈ clusterPoints S d p, residueValue f z := by
      apply Finset.sum_congr rfl
      intro p hp
      exact rectBoundary_eq_cluster_sum S d p (ε p) (hε p hp) (hopen p hp) (hcapture p hp)
        f (fun z _ => hres z) hd
    _ = 2 * Real.pi * I * ∑ p ∈ P, ∑ z ∈ clusterPoints S d p, residueValue f z := by
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_biUnion hdisj]

end HaagerupIzumi.MovingPoleRectangles
