module

public import HaagerupIzumi.Analytic.GammaK4Residues
public import HaagerupIzumi.Analytic.GammaKernelDecay
import all Mathlib.Data.Complex.Basic

/-!
# Independence of the corrected four-gamma contour

The residue theorem on a finite vertical strip identifies the change in the
line integral with exactly the change in the finite crossed-pole corrections.
The resulting value is independent of every admissible vertical line.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

/-- Candidate poles between two vertical lines, counted once even when two
factors of the same orientation have a pole at the same point. -/
def crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ τ : ℝ) : Finset ℂ := by
  classical
  exact (crossedLeft a b hb hba r s x σ \ crossedLeft a b hb hba r s x τ) ∪
    (crossedRight a b hb hba r s x τ \ crossedRight a b hb hba r s x σ)

lemma mem_crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ τ : ℝ) (hσ : AvoidsPoles a b r s x σ)
    (hτ : AvoidsPoles a b r s x τ) (z : ℂ) :
    z ∈ crossedBetween a b hb hba r s x σ τ ↔
      z ∈ leftPoles a b r s x ∪ rightPoles a b r s x ∧ σ < z.re ∧ z.re < τ := by
  classical
  simp only [crossedBetween, Finset.mem_union, Finset.mem_sdiff,
    mem_crossedLeft, mem_crossedRight]
  constructor
  · rintro (⟨⟨hz, hσz⟩, hτz⟩ | ⟨⟨hz, hzτ⟩, hzσ⟩)
    · have heq := hτ z (Or.inl hz)
      have hle : z.re ≤ τ := le_of_not_gt (fun h => hτz ⟨hz, h⟩)
      exact ⟨Or.inl hz, hσz, lt_of_le_of_ne hle heq⟩
    · have heq := hσ z (Or.inr hz)
      have hle : σ ≤ z.re := le_of_not_gt (fun h => hzσ ⟨hz, h⟩)
      exact ⟨Or.inr hz, lt_of_le_of_ne hle heq.symm, hzτ⟩
  · rintro ⟨hz | hz, hσz, hzτ⟩
    · exact Or.inl ⟨⟨hz, hσz⟩, fun h => (not_lt_of_ge hzτ.le) h.2⟩
    · exact Or.inr ⟨⟨hz, hzτ⟩, fun h => (not_lt_of_ge hσz.le) h.2⟩

lemma crossedLeft_antitone (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) :
    crossedLeft a b hb hba r s x τ ⊆ crossedLeft a b hb hba r s x σ := by
  intro z hz
  obtain ⟨hz, hτz⟩ := (mem_crossedLeft a b hb hba r s x τ z).mp hz
  exact (mem_crossedLeft a b hb hba r s x σ z).mpr ⟨hz, lt_of_le_of_lt hστ hτz⟩

lemma crossedRight_monotone (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) :
    crossedRight a b hb hba r s x σ ⊆ crossedRight a b hb hba r s x τ := by
  intro z hz
  obtain ⟨hz, hzσ⟩ := (mem_crossedRight a b hb hba r s x σ z).mp hz
  exact (mem_crossedRight a b hb hba r s x τ z).mpr ⟨hz, lt_of_lt_of_le hzσ hστ⟩

lemma sum_crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) (hnp : K4NoPinch a b r s x)
    (ρ : ℂ → ℂ) :
    (∑ z ∈ crossedBetween a b hb hba r s x σ τ, ρ z) =
      (∑ z ∈ crossedLeft a b hb hba r s x σ, ρ z) -
        (∑ z ∈ crossedLeft a b hb hba r s x τ, ρ z) +
      ((∑ z ∈ crossedRight a b hb hba r s x τ, ρ z) -
        ∑ z ∈ crossedRight a b hb hba r s x σ, ρ z) := by
  classical
  have hd : Disjoint
      (crossedLeft a b hb hba r s x σ \ crossedLeft a b hb hba r s x τ)
      (crossedRight a b hb hba r s x τ \ crossedRight a b hb hba r s x σ) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hl := ((mem_crossedLeft a b hb hba r s x σ z).mp (Finset.mem_sdiff.mp hz).1).1
    have hr := ((mem_crossedRight a b hb hba r s x τ z).mp (Finset.mem_sdiff.mp hz').1).1
    exact Set.disjoint_left.mp (noPinch_disjoint hnp) hl hr
  rw [crossedBetween, Finset.sum_union hd,
    Finset.sum_sdiff_eq_sub (crossedLeft_antitone a b hb hba r s x hστ),
    Finset.sum_sdiff_eq_sub (crossedRight_monotone a b hb hba r s x hστ)]

lemma periods_strictly_ordered (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) : b < a := by
  apply lt_of_le_of_ne hba
  intro h
  subst a
  simpa only [div_self hb.ne', not_irrational_one] using hirr

/-- The strip residue theorem applied to the actual kernel. -/
lemma kernel_strip_residues (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (σ τ : ℝ) (hστ : σ < τ) (hσ : AvoidsPoles a b r s x σ)
    (hτ : AvoidsPoles a b r s x τ) :
    Integrable (fun t : ℝ => kernel a b hb hba r s x y (σ + t * I)) ∧
    Integrable (fun t : ℝ => kernel a b hb hba r s x y (τ + t * I)) ∧
    lineIntegral (kernel a b hb hba r s x y) τ -
      lineIntegral (kernel a b hb hba r s x y) σ =
      2 * Real.pi * I * ∑ z ∈ crossedBetween a b hb hba r s x σ τ,
        residueValue (kernel a b hb hba r s x y) z := by
  classical
  obtain ⟨M, c, T, _, hc, hT, hbound⟩ := k4_tail_bound hb
    (periods_strictly_ordered a b hb hba hirr) r s x y hconv σ τ
  let S := crossedBetween a b hb hba r s x σ τ
  let T' := max T ((∑ w ∈ S, |w.im|) + 1)
  apply strip_residues_gen (kernel a b hb hba r s x y) σ τ hστ S T'
    (lt_of_lt_of_le hT (le_max_left _ _)) ?_
    (residueValue (kernel a b hb hba r s x y)) ?_ ?_ M c hc ?_
  · intro z hz
    have hmem := (mem_crossedBetween a b hb hba r s x σ τ hσ hτ z).mp hz
    refine ⟨hmem.2.1, hmem.2.2, ?_⟩
    have hzsum : |z.im| ≤ ∑ w ∈ S, |w.im| := Finset.single_le_sum (fun w _ => abs_nonneg w.im) hz
    have hmax := le_max_right T ((∑ w ∈ S, |w.im|) + 1)
    dsimp [T']
    linarith
  · intro z _
    exact kernel_hasResidueGen_residueValue a b hb hba hirr r s x y z hnp
  · intro z hzσ hzτ hzS
    apply kernel_differentiableAt a b hb hba r s x y z
    intro hz
    have hzσ' : σ < z.re := lt_of_le_of_ne hzσ (hσ z hz).symm
    have hzτ' : z.re < τ := lt_of_le_of_ne hzτ (hτ z hz)
    exact hzS ((mem_crossedBetween a b hb hba r s x σ τ hσ hτ z).mpr ⟨hz, hzσ', hzτ'⟩)
  · intro z hzσ hzτ hzT
    exact hbound z hzσ hzτ (le_trans (le_max_left _ _) hzT)

lemma corrected_value_eq_of_lt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (σ τ : ℝ) (hστ : σ < τ) (hσ : AvoidsPoles a b r s x σ)
    (hτ : AvoidsPoles a b r s x τ) :
    CorrectedContour.value (kernel a b hb hba r s x y) σ
      (crossedLeft a b hb hba r s x σ) (crossedRight a b hb hba r s x σ) =
    CorrectedContour.value (kernel a b hb hba r s x y) τ
      (crossedLeft a b hb hba r s x τ) (crossedRight a b hb hba r s x τ) := by
  have h := (kernel_strip_residues a b hb hba hirr r s x y hconv hnp σ τ hστ hσ hτ).2.2
  rw [sum_crossedBetween a b hb hba r s x hστ.le hnp] at h
  unfold CorrectedContour.value
  linear_combination -h

/-- The corrected contour has the same value on any two admissible lines. -/
lemma corrected_value_independent (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (σ τ : ℝ) (hσ : AvoidsPoles a b r s x σ) (hτ : AvoidsPoles a b r s x τ) :
    CorrectedContour.value (kernel a b hb hba r s x y) σ
      (crossedLeft a b hb hba r s x σ) (crossedRight a b hb hba r s x σ) =
    CorrectedContour.value (kernel a b hb hba r s x y) τ
      (crossedLeft a b hb hba r s x τ) (crossedRight a b hb hba r s x τ) := by
  rcases lt_trichotomy σ τ with h | rfl | h
  · exact corrected_value_eq_of_lt a b hb hba hirr r s x y hconv hnp σ τ h hσ hτ
  · rfl
  · exact (corrected_value_eq_of_lt a b hb hba hirr r s x y hconv hnp τ σ h hτ hσ).symm

lemma exists_avoidsPoles_gt (a b : ℝ) (r s x : ℂ) (σ : ℝ) :
    ∃ τ : ℝ, σ < τ ∧ AvoidsPoles a b r s x τ := by
  have hd := (((leftPoles_countable a b r s x).union
    (rightPoles_countable a b r s x)).image Complex.re).dense_compl ℝ
  obtain ⟨τ, hτ, hστ⟩ := hd.exists_gt σ
  refine ⟨τ, hστ, ?_⟩
  intro z hz heq
  exact hτ ⟨z, hz, heq⟩

lemma kernel_integrable_line (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (σ : ℝ) (hσ : AvoidsPoles a b r s x σ) :
    Integrable (fun t : ℝ => kernel a b hb hba r s x y (σ + t * I)) := by
  obtain ⟨τ, hστ, hτ⟩ := exists_avoidsPoles_gt a b r s x σ
  exact (kernel_strip_residues a b hb hba hirr r s x y hconv hnp σ τ hστ hσ hτ).1

/-- The concrete normalized K4 is represented by every admissible line with
its finite crossed-pole corrections. -/
theorem K4_line (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x)
    (σ : ℝ) (hσ : AvoidsPoles a b r s x σ) :
    Integrable (fun t : ℝ => kernel a b hb hba r s x y (σ + t * I)) ∧
    CorrectedContour.value (kernel a b hb hba r s x y) σ
      (crossedLeft a b hb hba r s x σ) (crossedRight a b hb hba r s x σ) =
        I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba r s x y := by
  refine ⟨kernel_integrable_line a b hb hba hirr r s x y hconv hnp σ hσ, ?_⟩
  have h := corrected_value_independent a b hb hba hirr r s x y hconv hnp σ
    (startLine a b r s x) hσ (startLine_avoidsPoles (lt_of_lt_of_le hb hba) hb r s x)
  rw [crossedRight_startLine] at h
  exact h.trans (K4_startLine a b hb hba r s x y)

end HaagerupIzumi.GammaK4Contour
