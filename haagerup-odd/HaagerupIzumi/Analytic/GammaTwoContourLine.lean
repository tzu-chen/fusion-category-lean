module

public import HaagerupIzumi.Analytic.GammaTwoContour
public import HaagerupIzumi.Analytic.GammaKernelDecay
import all Mathlib.Data.Complex.Basic

/-!
# Independence of the corrected two-gamma contour

The residue theorem on a finite vertical strip identifies the change in the
line integral with exactly the change in the finite crossed-pole corrections.
The resulting value is independent of every admissible vertical line.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaTwoFourier

/-- Candidate poles between two vertical lines, counted once even when two
candidate descriptions happen to name the same point. -/
def crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h : ℂ) (σ τ : ℝ) : Finset ℂ := by
  classical
  exact (crossedLeft a b hb hba f σ \ crossedLeft a b hb hba f τ) ∪
    (crossedRight a b hb hba h τ \ crossedRight a b hb hba h σ)

lemma mem_crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h : ℂ) (σ τ : ℝ) (hσ : AvoidsPoles a b f h σ)
    (hτ : AvoidsPoles a b f h τ) (z : ℂ) :
    z ∈ crossedBetween a b hb hba f h σ τ ↔
      z ∈ leftFamily a b f ∪ rightFamily a b h ∧ σ < z.re ∧ z.re < τ := by
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
    (f h : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) :
    crossedLeft a b hb hba f τ ⊆ crossedLeft a b hb hba f σ := by
  intro z hz
  obtain ⟨hz, hτz⟩ := (mem_crossedLeft a b hb hba f τ z).mp hz
  exact (mem_crossedLeft a b hb hba f σ z).mpr ⟨hz, lt_of_le_of_lt hστ hτz⟩

lemma crossedRight_monotone (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) :
    crossedRight a b hb hba h σ ⊆ crossedRight a b hb hba h τ := by
  intro z hz
  obtain ⟨hz, hzσ⟩ := (mem_crossedRight a b hb hba h σ z).mp hz
  exact (mem_crossedRight a b hb hba h τ z).mpr ⟨hz, lt_of_lt_of_le hzσ hστ⟩

lemma sum_crossedBetween (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) (hnp : f + h ∉ poleLattice a b)
    (ρ : ℂ → ℂ) :
    (∑ z ∈ crossedBetween a b hb hba f h σ τ, ρ z) =
      (∑ z ∈ crossedLeft a b hb hba f σ, ρ z) -
        (∑ z ∈ crossedLeft a b hb hba f τ, ρ z) +
      ((∑ z ∈ crossedRight a b hb hba h τ, ρ z) -
        ∑ z ∈ crossedRight a b hb hba h σ, ρ z) := by
  classical
  have hd : Disjoint
      (crossedLeft a b hb hba f σ \ crossedLeft a b hb hba f τ)
      (crossedRight a b hb hba h τ \ crossedRight a b hb hba h σ) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hl := ((mem_crossedLeft a b hb hba f σ z).mp (Finset.mem_sdiff.mp hz).1).1
    have hr := ((mem_crossedRight a b hb hba h τ z).mp (Finset.mem_sdiff.mp hz').1).1
    exact Set.disjoint_left.mp (GammaK4Contour.families_disjoint hnp) hl hr
  rw [crossedBetween, Finset.sum_union hd,
    Finset.sum_sdiff_eq_sub (crossedLeft_antitone a b hb hba f h hστ),
    Finset.sum_sdiff_eq_sub (crossedRight_monotone a b hb hba f h hστ)]

lemma periods_strictly_ordered (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) : b < a := by
  apply lt_of_le_of_ne hba
  intro h
  subst a
  simpa only [div_self hb.ne', not_irrational_one] using hirr

/-- The strip residue theorem applied to the actual kernel. -/
lemma kernel_strip_residues (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (hnp : f + h ∉ poleLattice a b)
    (σ τ : ℝ) (hστ : σ < τ) (hσ : AvoidsPoles a b f h σ)
    (hτ : AvoidsPoles a b f h τ) :
    Integrable (fun t : ℝ => kernel a b hb hba f h y (σ + t * I)) ∧
    Integrable (fun t : ℝ => kernel a b hb hba f h y (τ + t * I)) ∧
    lineIntegral (kernel a b hb hba f h y) τ -
      lineIntegral (kernel a b hb hba f h y) σ =
      2 * Real.pi * I * ∑ z ∈ crossedBetween a b hb hba f h σ τ,
        residueValue (kernel a b hb hba f h y) z := by
  classical
  obtain ⟨M, c, T, _, hc, hT, hbound⟩ := kernel_tail_bound a b hb
    (periods_strictly_ordered a b hb hba hirr) f h y hconv σ τ
  let S := crossedBetween a b hb hba f h σ τ
  let T' := max T ((∑ w ∈ S, |w.im|) + 1)
  apply strip_residues_gen (kernel a b hb hba f h y) σ τ hστ S T'
    (lt_of_lt_of_le hT (le_max_left _ _)) ?_
    (residueValue (kernel a b hb hba f h y)) ?_ ?_ M c hc ?_
  · intro z hz
    have hmem := (mem_crossedBetween a b hb hba f h σ τ hσ hτ z).mp hz
    refine ⟨hmem.2.1, hmem.2.2, ?_⟩
    have hzsum : |z.im| ≤ ∑ w ∈ S, |w.im| := Finset.single_le_sum (fun w _ => abs_nonneg w.im) hz
    have hmax := le_max_right T ((∑ w ∈ S, |w.im|) + 1)
    dsimp [T']
    linarith
  · intro z _
    exact kernel_hasResidueGen_residueValue a b hb hba hirr f h y z
  · intro z hzσ hzτ hzS
    apply kernel_differentiableAt_of_not_poles a b hb hba f h y z
    intro hz
    have hzσ' : σ < z.re := lt_of_le_of_ne hzσ (hσ z hz).symm
    have hzτ' : z.re < τ := lt_of_le_of_ne hzτ (hτ z hz)
    exact hzS ((mem_crossedBetween a b hb hba f h σ τ hσ hτ z).mpr ⟨hz, hzσ', hzτ'⟩)
  · intro z hzσ hzτ hzT
    exact hbound z hzσ hzτ (le_trans (le_max_left _ _) hzT)

lemma corrected_value_eq_of_lt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (hnp : f + h ∉ poleLattice a b)
    (σ τ : ℝ) (hστ : σ < τ) (hσ : AvoidsPoles a b f h σ)
    (hτ : AvoidsPoles a b f h τ) :
    CorrectedContour.value (kernel a b hb hba f h y) σ
      (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
    CorrectedContour.value (kernel a b hb hba f h y) τ
      (crossedLeft a b hb hba f τ) (crossedRight a b hb hba h τ) := by
  have hstripEq := (kernel_strip_residues a b hb hba hirr f h y hconv hnp σ τ hστ hσ hτ).2.2
  rw [sum_crossedBetween a b hb hba f h hστ.le hnp] at hstripEq
  unfold CorrectedContour.value
  linear_combination -hstripEq

/-- The corrected contour has the same value on any two admissible lines. -/
lemma corrected_value_independent (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (hnp : f + h ∉ poleLattice a b)
    (σ τ : ℝ) (hσ : AvoidsPoles a b f h σ) (hτ : AvoidsPoles a b f h τ) :
    CorrectedContour.value (kernel a b hb hba f h y) σ
      (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
    CorrectedContour.value (kernel a b hb hba f h y) τ
      (crossedLeft a b hb hba f τ) (crossedRight a b hb hba h τ) := by
  rcases lt_trichotomy σ τ with hlt | rfl | hlt
  · exact corrected_value_eq_of_lt a b hb hba hirr f h y hconv hnp σ τ hlt hσ hτ
  · rfl
  · exact (corrected_value_eq_of_lt a b hb hba hirr f h y hconv hnp τ σ hlt hτ hσ).symm

lemma exists_avoidsPoles_gt (a b : ℝ) (f h : ℂ) (σ : ℝ) :
    ∃ τ : ℝ, σ < τ ∧ AvoidsPoles a b f h τ := by
  have hd := (((GammaK4Contour.leftFamily_countable a b f).union
    (GammaK4Contour.rightFamily_countable a b h)).image Complex.re).dense_compl ℝ
  obtain ⟨τ, hτ, hστ⟩ := hd.exists_gt σ
  refine ⟨τ, hστ, ?_⟩
  intro z hz heq
  exact hτ ⟨z, hz, heq⟩

lemma kernel_integrable_line (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (hnp : f + h ∉ poleLattice a b)
    (σ : ℝ) (hσ : AvoidsPoles a b f h σ) :
    Integrable (fun t : ℝ => kernel a b hb hba f h y (σ + t * I)) := by
  obtain ⟨τ, hστ, hτ⟩ := exists_avoidsPoles_gt a b f h σ
  exact (kernel_strip_residues a b hb hba hirr f h y hconv hnp σ τ hστ hσ hτ).1

/-- The concrete corrected two-gamma transform is represented by every admissible line with
its finite crossed-pole corrections. -/
theorem correctedTransform_line (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (hnp : f + h ∉ poleLattice a b)
    (σ : ℝ) (hσ : AvoidsPoles a b f h σ) :
    Integrable (fun t : ℝ => kernel a b hb hba f h y (σ + t * I)) ∧
    CorrectedContour.value (kernel a b hb hba f h y) σ
      (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
        I * correctedTransform a b hb hba f h y := by
  refine ⟨kernel_integrable_line a b hb hba hirr f h y hconv hnp σ hσ, ?_⟩
  have hcomparison := corrected_value_independent a b hb hba hirr f h y hconv hnp σ
    (startLine a b f h) hσ (startLine_avoidsPoles a b hb hba f h)
  rw [crossedRight_startLine] at hcomparison
  exact hcomparison.trans (correctedTransform_startLine a b hb hba f h y)

end HaagerupIzumi.GammaTwoFourier
