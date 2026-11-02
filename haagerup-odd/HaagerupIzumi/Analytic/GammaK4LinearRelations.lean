module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4Line
public import HaagerupIzumi.Analytic.ContourLinearity

/-!
# Integrating finite linear relations between translated four-gamma kernels

All kernels are placed on one admissible line. Their finite pole corrections
are enlarged to common left and right sets. Disjointness of the two common
orientations ensures that every added candidate has zero residue.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

structure ShiftedKernel where
  r : ℂ
  s : ℂ
  x : ℂ
  y : ℂ
  shift : ℂ

namespace ShiftedKernel

def function (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ) : ℂ :=
  kernel a b hb hba k.r k.s k.x k.y (k.shift + z)

def left (k : ShiftedKernel) (a b : ℝ) : Set ℂ :=
  (fun z => k.shift + z) ⁻¹' leftPoles a b k.r k.s k.x

def right (k : ShiftedKernel) (a b : ℝ) : Set ℂ :=
  (fun z => k.shift + z) ⁻¹' rightPoles a b k.r k.s k.x

lemma left_countable (k : ShiftedKernel) (a b : ℝ) : (k.left a b).Countable :=
  (leftPoles_countable a b k.r k.s k.x).preimage (add_right_injective k.shift)

lemma right_countable (k : ShiftedKernel) (a b : ℝ) : (k.right a b).Countable :=
  (rightPoles_countable a b k.r k.s k.x).preimage (add_right_injective k.shift)

def crossedLeft (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (σ : ℝ) : Finset ℂ := by
  classical
  exact (GammaK4Contour.crossedLeft a b hb hba k.r k.s k.x (σ + k.shift.re)).image
    (fun w => w - k.shift)

def crossedRight (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (σ : ℝ) : Finset ℂ := by
  classical
  exact (GammaK4Contour.crossedRight a b hb hba k.r k.s k.x (σ + k.shift.re)).image
    (fun w => w - k.shift)

lemma mem_crossedLeft (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) (z : ℂ) : z ∈ k.crossedLeft a b hb hba σ ↔ z ∈ k.left a b ∧ σ < z.re := by
  classical
  simp only [crossedLeft, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hσ⟩ := (GammaK4Contour.mem_crossedLeft a b hb hba k.r k.s k.x _ w).mp hw
    refine ⟨?_, ?_⟩
    · change k.shift + (w - k.shift) ∈ leftPoles a b k.r k.s k.x
      simpa only [show k.shift + (w - k.shift) = w by ring] using hw
    · simp only [sub_re]
      linarith
  · rintro ⟨hz, hσ⟩
    refine ⟨k.shift + z, ?_, by ring⟩
    apply (GammaK4Contour.mem_crossedLeft a b hb hba k.r k.s k.x _ _).mpr
    refine ⟨hz, ?_⟩
    simp only [add_re]
    linarith

lemma mem_crossedRight (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) (z : ℂ) : z ∈ k.crossedRight a b hb hba σ ↔ z ∈ k.right a b ∧ z.re < σ := by
  classical
  simp only [crossedRight, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hσ⟩ := (GammaK4Contour.mem_crossedRight a b hb hba k.r k.s k.x _ w).mp hw
    refine ⟨?_, ?_⟩
    · change k.shift + (w - k.shift) ∈ rightPoles a b k.r k.s k.x
      simpa only [show k.shift + (w - k.shift) = w by ring] using hw
    · simp only [sub_re]
      linarith
  · rintro ⟨hz, hσ⟩
    refine ⟨k.shift + z, ?_, by ring⟩
    apply (GammaK4Contour.mem_crossedRight a b hb hba k.r k.s k.x _ _).mpr
    refine ⟨hz, ?_⟩
    simp only [add_re]
    linarith

lemma differentiableAt_function (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (z : ℂ) (hz : z ∉ k.left a b ∪ k.right a b) :
    DifferentiableAt ℂ (k.function a b hb hba) z := by
  exact (kernel_differentiableAt a b hb hba k.r k.s k.x k.y (k.shift + z) hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => k.shift + z) z)

lemma exists_hasResidueGen_function (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (hnp : K4NoPinch a b k.r k.s k.x) (z : ℂ) :
    ∃ ρ, HasResidueGen (k.function a b hb hba) z ρ := by
  obtain ⟨ρ, hρ⟩ := kernel_exists_hasResidueGen a b hb hba hirr k.r k.s k.x k.y (k.shift + z) hnp
  exact ⟨ρ, hρ.comp_const_add⟩

lemma eventually_not_mem_candidates (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (p : ℂ) : ∀ᶠ z in 𝓝[≠] p, z ∉ k.left a b ∪ k.right a b := by
  have ha := lt_of_lt_of_le hb hba
  have hL (c : ℂ) : ∀ᶠ z in 𝓝[≠] p, c + (k.shift + z) ∉ poleLattice a b := by
    have ht := tendsto_punctured_of_injective
      (by fun_prop : Continuous (fun z : ℂ => c + (k.shift + z)))
      (fun x y h => add_left_cancel (add_left_cancel h)) p
    exact ht.eventually (eventually_not_mem_poleLattice ha hb (c + (k.shift + p)))
  have hR (c : ℂ) : ∀ᶠ z in 𝓝[≠] p, c - (k.shift + z) ∉ poleLattice a b := by
    have ht := tendsto_punctured_of_injective
      (by fun_prop : Continuous (fun z : ℂ => c - (k.shift + z)))
      (fun x y h => add_left_cancel (sub_right_injective h)) p
    exact ht.eventually (eventually_not_mem_poleLattice ha hb (c - (k.shift + p)))
  filter_upwards [hL (k4U a b k.r k.s), hL (k4V a b k.r k.s + k.x),
    hR (k4U a b k.r k.s), hR (k4V a b k.r k.s - k.x)] with z h₁ h₂ h₃ h₄
  exact fun h => h.elim (fun hL => hL.elim h₁ h₂) (fun hR => hR.elim h₃ h₄)

lemma avoidsPoles_of_shift (k : ShiftedKernel) (a b : ℝ) (σ : ℝ)
    (hσ : ∀ z ∈ k.left a b ∪ k.right a b, z.re ≠ σ) :
    AvoidsPoles a b k.r k.s k.x (σ + k.shift.re) := by
  intro w hw heq
  have hm : w - k.shift ∈ k.left a b ∪ k.right a b := by
    change k.shift + (w - k.shift) ∈ leftPoles a b k.r k.s k.x ∪ rightPoles a b k.r k.s k.x
    simpa only [show k.shift + (w - k.shift) = w by ring] using hw
  apply hσ (w - k.shift) hm
  simp only [sub_re]
  linarith

lemma integrable_function_line (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (hconv : K4Conv a b k.r k.y) (hnp : K4NoPinch a b k.r k.s k.x)
    (σ : ℝ) (hσ : ∀ z ∈ k.left a b ∪ k.right a b, z.re ≠ σ) :
    Integrable (fun t : ℝ => k.function a b hb hba (σ + t * I)) := by
  have hf := kernel_integrable_line a b hb hba hirr k.r k.s k.x k.y hconv hnp
    (σ + k.shift.re) (k.avoidsPoles_of_shift a b σ hσ)
  have ht := hf.comp_add_right k.shift.im
  convert ht using 1
  funext t
  unfold function
  congr 1
  apply Complex.ext <;> simp <;> ring

lemma corrected_value_eq (k : ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (hconv : K4Conv a b k.r k.y) (hnp : K4NoPinch a b k.r k.s k.x)
    (σ : ℝ) (hσ : ∀ z ∈ k.left a b ∪ k.right a b, z.re ≠ σ) :
    CorrectedContour.value (k.function a b hb hba) σ
      (k.crossedLeft a b hb hba σ) (k.crossedRight a b hb hba σ) =
        I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba k.r k.s k.x k.y := by
  change CorrectedContour.value
      (fun z => kernel a b hb hba k.r k.s k.x k.y (k.shift + z)) σ
      (k.crossedLeft a b hb hba σ) (k.crossedRight a b hb hba σ) = _
  simp only [crossedLeft, crossedRight]
  rw [CorrectedContour.value_comp_const_add k.shift σ _ _
    (fun w _ => kernel_exists_hasResidueGen a b hb hba hirr k.r k.s k.x k.y w hnp)]
  exact (K4_line a b hb hba hirr k.r k.s k.x k.y hconv hnp
    (σ + k.shift.re) (k.avoidsPoles_of_shift a b σ hσ)).2

end ShiftedKernel

section FiniteFamily

variable {ι : Type*} [Fintype ι]

def commonLeft (k : ι → ShiftedKernel) (a b : ℝ) : Set ℂ := ⋃ i, (k i).left a b

def commonRight (k : ι → ShiftedKernel) (a b : ℝ) : Set ℂ := ⋃ i, (k i).right a b

def commonCrossedLeft (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) : Finset ℂ := by
  classical
  exact Finset.univ.biUnion (fun i => (k i).crossedLeft a b hb hba σ)

def commonCrossedRight (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) : Finset ℂ := by
  classical
  exact Finset.univ.biUnion (fun i => (k i).crossedRight a b hb hba σ)

lemma mem_commonCrossedLeft (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) (z : ℂ) :
    z ∈ commonCrossedLeft k a b hb hba σ ↔ ∃ i, z ∈ (k i).left a b ∧ σ < z.re := by
  classical
  simp only [commonCrossedLeft, Finset.mem_biUnion, Finset.mem_univ, true_and,
    ShiftedKernel.mem_crossedLeft]

lemma mem_commonCrossedRight (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (σ : ℝ) (z : ℂ) :
    z ∈ commonCrossedRight k a b hb hba σ ↔ ∃ i, z ∈ (k i).right a b ∧ z.re < σ := by
  classical
  simp only [commonCrossedRight, Finset.mem_biUnion, Finset.mem_univ, true_and,
    ShiftedKernel.mem_crossedRight]

lemma exists_commonLine (k : ι → ShiftedKernel) (a b : ℝ) :
    ∃ σ : ℝ, ∀ z ∈ commonLeft k a b ∪ commonRight k a b, z.re ≠ σ := by
  have hL : (commonLeft k a b).Countable := Set.countable_iUnion (fun i => (k i).left_countable a b)
  have hR : (commonRight k a b).Countable := Set.countable_iUnion (fun i => (k i).right_countable a b)
  have hd := ((hL.union hR).image Complex.re).dense_compl ℝ
  obtain ⟨σ, hσ, _⟩ := hd.exists_gt 0
  refine ⟨σ, ?_⟩
  intro z hz heq
  exact hσ ⟨z, hz, heq⟩

omit [Fintype ι] in
lemma commonLine_avoids (k : ι → ShiftedKernel) (a b : ℝ) (σ : ℝ)
    (hσ : ∀ z ∈ commonLeft k a b ∪ commonRight k a b, z.re ≠ σ) (i : ι) :
    ∀ z ∈ (k i).left a b ∪ (k i).right a b, z.re ≠ σ := by
  intro z hz
  apply hσ z
  rcases hz with hz | hz
  · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hz⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hz⟩)

lemma value_eq_common (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hd : Disjoint (commonLeft k a b) (commonRight k a b)) (σ : ℝ) (i : ι) :
    CorrectedContour.value ((k i).function a b hb hba) σ
      ((k i).crossedLeft a b hb hba σ) ((k i).crossedRight a b hb hba σ) =
    CorrectedContour.value ((k i).function a b hb hba) σ
      (commonCrossedLeft k a b hb hba σ) (commonCrossedRight k a b hb hba σ) := by
  apply CorrectedContour.value_enlarge
  · intro z hz
    exact (mem_commonCrossedLeft k a b hb hba σ z).mpr
      ⟨i, ((k i).mem_crossedLeft a b hb hba σ z).mp hz⟩
  · intro z hz
    exact (mem_commonCrossedRight k a b hb hba σ z).mpr
      ⟨i, ((k i).mem_crossedRight a b hb hba σ z).mp hz⟩
  · intro z hz hz'
    obtain ⟨j, hj, hσz⟩ := (mem_commonCrossedLeft k a b hb hba σ z).mp hz
    apply residueValue_of_continuousAt
    apply ((k i).differentiableAt_function a b hb hba z ?_).continuousAt
    rintro (hL | hR)
    · exact hz' (((k i).mem_crossedLeft a b hb hba σ z).mpr ⟨hL, hσz⟩)
    · exact Set.disjoint_left.mp hd (Set.mem_iUnion.mpr ⟨j, hj⟩) (Set.mem_iUnion.mpr ⟨i, hR⟩)
  · intro z hz hz'
    obtain ⟨j, hj, hzσ⟩ := (mem_commonCrossedRight k a b hb hba σ z).mp hz
    apply residueValue_of_continuousAt
    apply ((k i).differentiableAt_function a b hb hba z ?_).continuousAt
    rintro (hL | hR)
    · exact Set.disjoint_left.mp hd (Set.mem_iUnion.mpr ⟨i, hL⟩) (Set.mem_iUnion.mpr ⟨j, hj⟩)
    · exact hz' (((k i).mem_crossedRight a b hb hba σ z).mpr ⟨hR, hzσ⟩)

/-- Any pointwise finite linear relation between compatible translated
four-gamma kernels yields the same linear relation between their K4 values. -/
theorem linear_relation (k : ι → ShiftedKernel) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (c : ι → ℂ)
    (hconv : ∀ i, K4Conv a b (k i).r (k i).y)
    (hnp : ∀ i, K4NoPinch a b (k i).r (k i).s (k i).x)
    (hd : Disjoint (commonLeft k a b) (commonRight k a b))
    (hid : ∀ z : ℂ, (∀ i, z ∉ (k i).left a b ∪ (k i).right a b) →
      ∑ i, c i * (k i).function a b hb hba z = 0) :
    ∑ i, c i * K4 a b hb hba (k i).r (k i).s (k i).x (k i).y = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_commonLine k a b
  let SL := commonCrossedLeft k a b hb hba σ
  let SR := commonCrossedRight k a b hb hba σ
  have hσi := commonLine_avoids k a b σ hσ
  have hint (i : ι) : Integrable (fun t : ℝ => (k i).function a b hb hba (σ + t * I)) :=
    (k i).integrable_function_line a b hb hba hirr (hconv i) (hnp i) σ (hσi i)
  have hres (i : ι) (w : ℂ) : ∃ ρ, HasResidueGen ((k i).function a b hb hba) w ρ :=
    (k i).exists_hasResidueGen_function a b hb hba hirr (hnp i) w
  have heq : CorrectedContour.value (fun z => ∑ i, c i * (k i).function a b hb hba z) σ SL SR =
      CorrectedContour.value (fun _ : ℂ => 0) σ SL SR := by
    apply CorrectedContour.value_congr
    · intro t
      apply hid
      intro i hi
      exact hσi i (σ + t * I) hi (by simp)
    · intro w _
      have he : ∀ᶠ z in 𝓝[≠] w, ∀ i, z ∉ (k i).left a b ∪ (k i).right a b :=
        Filter.eventually_all.mpr (fun i => (k i).eventually_not_mem_candidates a b hb hba w)
      exact he.mono (fun z hz => hid z hz)
  have hzero : CorrectedContour.value (fun _ : ℂ => 0) σ SL SR = 0 := by
    have hz (w : ℂ) : residueValue (fun _ : ℂ => 0) w = 0 :=
      residueValue_of_continuousAt continuousAt_const
    simp only [CorrectedContour.value, lineIntegral, hz, zero_mul, integral_zero,
      Finset.sum_const_zero, mul_zero, add_zero, sub_zero]
  rw [hzero, CorrectedContour.value_linearCombination Finset.univ
    (fun i => (k i).function a b hb hba) c σ SL SR (fun i _ => hint i)
    (fun i _ w _ => hres i w)] at heq
  have hval (i : ι) : CorrectedContour.value ((k i).function a b hb hba) σ SL SR =
      I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba (k i).r (k i).s (k i).x (k i).y := by
    rw [← value_eq_common k a b hb hba hd σ i]
    exact (k i).corrected_value_eq a b hb hba hirr (hconv i) (hnp i) σ (hσi i)
  simp_rw [hval] at heq
  have heq' : (I * (Real.sqrt (a * b) : ℂ)) *
      (∑ i, c i * K4 a b hb hba (k i).r (k i).s (k i).x (k i).y) = 0 := by
    rw [Finset.mul_sum]
    convert heq using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (mul_eq_zero.mp heq').resolve_left (mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hb hba) hb)).ne'))

end FiniteFamily

end HaagerupIzumi.GammaK4Contour
