module

public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Removing a countable set from an open convex domain

In real dimension greater than one, two points can be joined through a
nearby midpoint while avoiding the countably many obstructed segments.
-/

@[expose] public section

open Set
open scoped Convex

namespace HaagerupIzumi

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem isPathConnected_diff_countable_of_convex
    (hrank : 1 < Module.rank ℝ E) {U S : Set E}
    (hU : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty) (hS : S.Countable) :
    IsPathConnected (U \ S) := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨a, ha⟩ : (U \ S).Nonempty := (hS.dense_compl ℝ).inter_open_nonempty U ho hne
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have hc : c ∈ U := by
    have hh := hU ha.1 hb.1 (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
    simpa only [c, smul_add] using hh
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank hrank x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty, Ib] using hb.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty, Ia] using ha.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  let V : Set ℝ := {t | c + t • y ∈ U}
  have hVo : IsOpen V := ho.preimage (by fun_prop)
  have hVn : V.Nonempty := ⟨0, by simpa only [V, mem_ofPred_eq, zero_smul, add_zero] using hc⟩
  obtain ⟨t, htV, ht⟩ := ((A.union B).dense_compl ℝ).inter_open_nonempty V hVo hVn
  let z := c + t • y
  have hz : z ∈ U := htV
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at ht
  have hAS : [a -[ℝ] z] ⊆ Sᶜ := by
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.2
    exact Ia.symm
  have hBS : [b -[ℝ] z] ⊆ Sᶜ := by
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.1
    exact Ib.symm
  have JA : JoinedIn (U \ S) a z :=
    JoinedIn.of_segment_subset (subset_inter (hU.segment_subset ha.1 hz) hAS)
  have JB : JoinedIn (U \ S) b z :=
    JoinedIn.of_segment_subset (subset_inter (hU.segment_subset hb.1 hz) hBS)
  exact JA.trans JB.symm

theorem isConnected_diff_countable_of_convex
    (hrank : 1 < Module.rank ℝ E) {U S : Set E}
    (hU : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty) (hS : S.Countable) :
    IsConnected (U \ S) :=
  (isPathConnected_diff_countable_of_convex hrank hU ho hne hS).isConnected

end HaagerupIzumi
