module

public import HaagerupIzumi.Analytic.GammaK4Line

/-!
# A single-conjunct ablation of the four-gamma no-pinch condition

Take `r = x = 0` and `s = -(a+b)/2`. Then `U = 0`, `V = (a+b)/2`.
Exactly the first of the four `K4NoPinch` clauses fails: the first left
and first right pole families share the origin. The other three clauses hold
for every positive pair of periods.

The finite-set bookkeeping lemma `sum_crossedBetween` is consequently false
without its no-pinch hypothesis. A weight supported at the origin counts the
shared point once in the union and twice in the two oriented corrections.
This is a certificate for the actual project's pole geometry and accounting
lemma. The test weight is arbitrary, as allowed by that lemma; it is not
claimed here to be the residue function of the gamma kernel. In particular,
this file alone does not certify failure of the analytic integral identity.
-/

@[expose] public section
noncomputable section

open Complex
open scoped Classical
open HaagerupIzumi HaagerupIzumi.GammaContinuation HaagerupIzumi.GammaK4Contour

namespace HaagerupIzumi.GammaContourAblation

def pinchingS (a b : ℝ) : ℂ := -((a + b : ℝ) : ℂ) / 2

lemma pinching_U (a b : ℝ) : k4U a b 0 (pinchingS a b) = 0 := by
  unfold k4U pinchingS
  ring

lemma pinching_V (a b : ℝ) :
    k4V a b 0 (pinchingS a b) = ((a + b : ℝ) : ℂ) / 2 := by
  unfold k4V pinchingS
  ring

lemma origin_mem_poleLattice (a b : ℝ) : (0 : ℂ) ∈ poleLattice a b := by
  exact ⟨0, 0, by simp⟩

/-- The three untouched conjuncts of `K4NoPinch` still hold. -/
theorem retained_noPinch_clauses (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    2 * k4V a b 0 (pinchingS a b) ∉ poleSet a b ∧
    k4U a b 0 (pinchingS a b) + k4V a b 0 (pinchingS a b) - 0 ∉ poleSet a b ∧
    k4U a b 0 (pinchingS a b) + k4V a b 0 (pinchingS a b) + 0 ∉ poleSet a b := by
  have ha : 0 < a := hb.trans_le hba
  have hsum : 0 < a + b := add_pos ha hb
  have hfull : ((a + b : ℝ) : ℂ) ∉ poleSet a b :=
    not_mem_poleLattice_of_re_pos ha hb (by simpa using hsum)
  have hhalf : ((a + b : ℝ) : ℂ) / 2 ∉ poleSet a b :=
    not_mem_poleLattice_of_re_pos ha hb (by simpa using half_pos hsum)
  have hcancel : (2 : ℂ) * (((a + b : ℝ) : ℂ) / 2) = ((a + b : ℝ) : ℂ) := by ring
  simpa only [pinching_U, pinching_V, hcancel, zero_add, sub_zero, add_zero] using
    And.intro hfull (And.intro hhalf hhalf)

/-- The deleted clause is false, witnessed by the lattice index `(0,0)`. -/
theorem deleted_noPinch_clause_fails (a b : ℝ) :
    2 * k4U a b 0 (pinchingS a b) ∈ poleSet a b := by
  rw [pinching_U, mul_zero]
  exact origin_mem_poleLattice a b

theorem noPinch_fails (a b : ℝ) : ¬ K4NoPinch a b 0 (pinchingS a b) 0 := by
  intro h
  exact h.1 (deleted_noPinch_clause_fails a b)

lemma origin_in_both_orientations (a b : ℝ) :
    (0 : ℂ) ∈ leftPoles a b 0 (pinchingS a b) 0 ∧
    (0 : ℂ) ∈ rightPoles a b 0 (pinchingS a b) 0 := by
  constructor
  · apply Or.inl
    change k4U a b 0 (pinchingS a b) + 0 ∈ poleLattice a b
    simpa only [pinching_U, zero_add] using origin_mem_poleLattice a b
  · apply Or.inl
    change k4U a b 0 (pinchingS a b) - 0 ∈ poleLattice a b
    simpa only [pinching_U, sub_zero] using origin_mem_poleLattice a b

/-- The actual no-pinch-to-disjointness conclusion also becomes false. -/
theorem pole_families_not_disjoint (a b : ℝ) :
    ¬ Disjoint (leftPoles a b 0 (pinchingS a b) 0)
      (rightPoles a b 0 (pinchingS a b) 0) := by
  intro h
  have hz := origin_in_both_orientations a b
  exact Set.disjoint_left.mp h hz.1 hz.2

def originWeight (z : ℂ) : ℂ := by
  classical
  exact if z = 0 then 1 else 0

lemma sum_originWeight (S : Finset ℂ) :
    (∑ z ∈ S, originWeight z) = if (0 : ℂ) ∈ S then 1 else 0 := by
  classical
  simp [originWeight]

/-- Membership needed for the accounting failure, with no enumeration of the
remaining lattice poles. These line locations are used only in the finite-set
identity: `sum_crossedBetween` has no `AvoidsPoles` hypotheses. -/
lemma origin_crossings (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    (0 : ℂ) ∈ crossedLeft a b hb hba 0 (pinchingS a b) 0 (-1 / 4) ∧
    (0 : ℂ) ∉ crossedLeft a b hb hba 0 (pinchingS a b) 0 (1 / 4) ∧
    (0 : ℂ) ∈ crossedRight a b hb hba 0 (pinchingS a b) 0 (1 / 4) ∧
    (0 : ℂ) ∉ crossedRight a b hb hba 0 (pinchingS a b) 0 (-1 / 4) := by
  have hz := origin_in_both_orientations a b
  norm_num [mem_crossedLeft, mem_crossedRight, hz.1, hz.2]

/-- Removing only `hnp` from the actual `sum_crossedBetween` signature gives
a false statement. The union sum is `1`, whereas the correction difference
is `2`; `(-1/4 : ℝ) ≤ 1/4` is still satisfied. -/
theorem sum_crossedBetween_without_noPinch_is_false
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    (∑ z ∈ crossedBetween a b hb hba 0 (pinchingS a b) 0 (-1 / 4) (1 / 4),
      originWeight z) ≠
      (∑ z ∈ crossedLeft a b hb hba 0 (pinchingS a b) 0 (-1 / 4), originWeight z) -
        (∑ z ∈ crossedLeft a b hb hba 0 (pinchingS a b) 0 (1 / 4), originWeight z) +
      ((∑ z ∈ crossedRight a b hb hba 0 (pinchingS a b) 0 (1 / 4), originWeight z) -
        ∑ z ∈ crossedRight a b hb hba 0 (pinchingS a b) 0 (-1 / 4), originWeight z) := by
  classical
  obtain ⟨hl, hnL, hr, hnR⟩ := origin_crossings a b hb hba
  have hm : (0 : ℂ) ∈ crossedBetween a b hb hba 0 (pinchingS a b) 0 (-1 / 4) (1 / 4) := by
    simp only [crossedBetween, Finset.mem_union, Finset.mem_sdiff]
    exact Or.inl ⟨hl, hnL⟩
  simp only [sum_originWeight, if_pos hm, if_pos hl, if_neg hnL, if_pos hr, if_neg hnR]
  norm_num

end HaagerupIzumi.GammaContourAblation

#print axioms HaagerupIzumi.GammaContourAblation.retained_noPinch_clauses
#print axioms HaagerupIzumi.GammaContourAblation.sum_crossedBetween_without_noPinch_is_false
