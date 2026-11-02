module

public import HaagerupIzumi.Analytic.GammaMovingPoleLine
import all Mathlib.Data.Complex.Basic

/-! # Fixed rectangle decomposition of moving gamma residue corrections -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)
open HaagerupIzumi.MovingPoleRectangles

namespace HaagerupIzumi.GammaMovingPoleRectangles

def clusters {X : Type*} (a b : ℝ) (L R : Fin 2 → X → ℂ)
    (x₀ x : X) (p : ℂ) : Finset ℂ :=
  clusterPoints (family a b (fun i => L i x₀) (fun i => R i x₀))
    (fun i => displacement L R x₀ i x) p

lemma mem_clusters {X : Type*} (a b : ℝ) (L R : Fin 2 → X → ℂ)
    (x₀ x : X) (p z : ℂ) : z ∈ clusters a b L R x₀ x p ↔
      ∃ i, p ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i ∧
        z = p + displacement L R x₀ i x :=
  mem_clusterPoints _ _ p z

/-- Preserved crossings identify all nearby crossed poles with the disjoint
collection of base clusters. No new crossed pole arrives from infinity. -/
lemma crossedLeftPoints_eq_biUnion_clusters {X : Type*}
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (L R : Fin 2 → X → ℂ)
    (x₀ x : X) (σ : ℝ)
    (hcross : ∀ i q, q ∈ leftFamily a b (L i x₀) →
      (σ < (q + (L i x₀ - L i x)).re ↔ σ < q.re))
    (hnp : ∀ i j, Disjoint (leftFamily a b (L i x₀)) (rightFamily a b (R j x₀))) :
    crossedLeftPoints a b hb hba (fun i => L i x) σ =
      (crossedLeftPoints a b hb hba (fun i => L i x₀) σ).biUnion (clusters a b L R x₀ x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, hσz⟩ := (mem_crossedLeftPoints a b hb hba _ σ z).mp hz
    let q := z - displacement L R x₀ (.inl i) x
    have hq : q ∈ leftFamily a b (L i x₀) := by
      apply (mem_family_translate a b L R x₀ x (.inl i) q).mp
      simpa only [q, sub_add_cancel, family] using hi
    have hqσ : σ < q.re := by
      apply (hcross i q hq).mp
      simpa only [q, displacement, sub_add_cancel] using hσz
    apply Finset.mem_biUnion.mpr
    refine ⟨q, (mem_crossedLeftPoints a b hb hba _ σ q).mpr ⟨i, hq, hqσ⟩, ?_⟩
    apply (mem_clusters a b L R x₀ x q z).mpr
    exact ⟨.inl i, hq, by dsimp [q]; ring⟩
  · intro hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, hpL, hpσ⟩ := (mem_crossedLeftPoints a b hb hba _ σ p).mp hp
    obtain ⟨i, hi, rfl⟩ := (mem_clusters a b L R x₀ x p z).mp hz
    cases i with
    | inl i =>
      apply (mem_crossedLeftPoints a b hb hba _ σ _).mpr
      refine ⟨i, (mem_family_translate a b L R x₀ x (.inl i) p).mpr hi, ?_⟩
      exact (hcross i p hi).mpr hpσ
    | inr i => exact (Set.disjoint_left.mp (hnp j i) hpL hi).elim

/-- Simultaneous radii for a finite collection of base clusters. Distinct
clusters have disjoint closed rectangles and all four moving families avoid
each boundary throughout one common neighborhood of the parameter. -/
theorem exists_cluster_radii {X : Type*} [TopologicalSpace X]
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (L R : Fin 2 → X → ℂ) (x₀ : X)
    (hL : ∀ i, ContinuousAt (L i) x₀) (hR : ∀ i, ContinuousAt (R i) x₀)
    (P : Finset ℂ)
    (hP : ∀ p ∈ P, ∃ i, p ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i) :
    ∃ ε : ℂ → ℝ, (∀ p, 0 < ε p) ∧
      Set.PairwiseDisjoint (P : Set ℂ) (fun p => closedRect (lower p (ε p)) (upper p (ε p))) ∧
      ∀ᶠ x in 𝓝 x₀, ∀ p ∈ P,
        (∀ i, InOpenRect (p + displacement L R x₀ i x) (lower p (ε p)) (upper p (ε p))) ∧
        (∀ i q, q ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i →
          (q + displacement L R x₀ i x ∈ closedRect (lower p (ε p)) (upper p (ε p)) ↔ q = p)) ∧
        (∀ i z, z ∈ family a b (fun j => L j x) (fun j => R j x) i →
          ¬ OnBoundary z (lower p (ε p)) (upper p (ε p))) := by
  classical
  choose ε hε hsep hev using fun p => exists_fixed_rectangle a b hb hba L R x₀ p hL hR
  refine ⟨ε, hε, ?_, P.eventually_all.mpr (fun p _ => hev p)⟩
  intro p hp q hq hpq
  obtain ⟨i, hi⟩ := hP p hp
  obtain ⟨j, hj⟩ := hP q hq
  apply closedRect_disjoint hpq (hsep p j q hj hpq.symm)
  simpa only [norm_sub_rev] using hsep q i p hi hpq

end HaagerupIzumi.GammaMovingPoleRectangles
