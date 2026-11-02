module

public import HaagerupIzumi.Analytic.MovingPoleRectangles
import all Mathlib.Data.Complex.Basic

/-! # Finite sets and residue sums for a moving pole cluster -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology

namespace HaagerupIzumi.MovingPoleRectangles

def clusterPoints {ι : Type*} [Fintype ι] (S : ι → Set ℂ) (d : ι → ℂ) (p : ℂ) : Finset ℂ := by
  classical
  exact (Finset.univ.filter (fun i => p ∈ S i)).image (fun i => p + d i)

lemma mem_clusterPoints {ι : Type*} [Fintype ι] (S : ι → Set ℂ) (d : ι → ℂ) (p z : ℂ) :
    z ∈ clusterPoints S d p ↔ ∃ i, p ∈ S i ∧ z = p + d i := by
  classical
  simp only [clusterPoints, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h.symm⟩

def translatedUnion {ι : Type*} (S : ι → Set ℂ) (d : ι → ℂ) : Set ℂ :=
  {z | ∃ i q, q ∈ S i ∧ z = q + d i}

lemma clusterPoints_inOpenRect {ι : Type*} [Fintype ι] (S : ι → Set ℂ) (d : ι → ℂ)
    (p : ℂ) (ε : ℝ) (hopen : ∀ i, InOpenRect (p + d i) (lower p ε) (upper p ε)) :
    ∀ z ∈ clusterPoints S d p, InOpenRect z (lower p ε) (upper p ε) := by
  intro z hz
  obtain ⟨i, _, rfl⟩ := (mem_clusterPoints S d p z).mp hz
  exact hopen i

lemma mem_clusterPoints_iff_of_mem_closedRect {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (d : ι → ℂ) (p : ℂ) (ε : ℝ)
    (hcapture : ∀ i q, q ∈ S i → (q + d i ∈ closedRect (lower p ε) (upper p ε) ↔ q = p))
    (z : ℂ) (hz : z ∈ closedRect (lower p ε) (upper p ε)) :
    z ∈ clusterPoints S d p ↔ z ∈ translatedUnion S d := by
  constructor
  · intro hm
    obtain ⟨i, hi, heq⟩ := (mem_clusterPoints S d p z).mp hm
    exact ⟨i, p, hi, heq⟩
  · rintro ⟨i, q, hi, rfl⟩
    have hqp := (hcapture i q hi).mp hz
    subst q
    exact (mem_clusterPoints S d p _).mpr ⟨i, hi, rfl⟩

/-- A collision cluster is counted once, independently of how many family
labels name the same point. The generalized residue handles double poles. -/
theorem rectBoundary_eq_cluster_sum {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (d : ι → ℂ) (p : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hopen : ∀ i, InOpenRect (p + d i) (lower p ε) (upper p ε))
    (hcapture : ∀ i q, q ∈ S i → (q + d i ∈ closedRect (lower p ε) (upper p ε) ↔ q = p))
    (f : ℂ → ℂ) (hres : ∀ z ∈ clusterPoints S d p, ∃ ρ, HasResidueGen f z ρ)
    (hd : ∀ z, z ∉ translatedUnion S d → DifferentiableAt ℂ f z) :
    rectBoundary f (lower p ε) (upper p ε) =
      2 * Real.pi * I * ∑ z ∈ clusterPoints S d p, residueValue f z := by
  apply rectBoundary_eq_sum_residues_gen f _ _ (lower_lt_upper p hε)
    (clusterPoints S d p) (clusterPoints_inOpenRect S d p ε hopen) (residueValue f)
    (fun z hz => hasResidueGen_residueValue (hres z hz))
  intro z hz
  apply hd
  intro hm
  exact hz.2 ((mem_clusterPoints_iff_of_mem_closedRect S d p ε hcapture z hz.1).mpr hm)

end HaagerupIzumi.MovingPoleRectangles
