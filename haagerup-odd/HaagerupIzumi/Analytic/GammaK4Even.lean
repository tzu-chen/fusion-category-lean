module

public import HaagerupIzumi.Analytic.GammaK4Line
public import HaagerupIzumi.Analytic.ContourAffine
import all Mathlib.Data.Complex.Basic

/-! # Reflection symmetry of the concrete four-gamma contour -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma noPinch_neg {a b : ℝ} {r s x : ℂ} (h : K4NoPinch a b r s x) :
    K4NoPinch a b r s (-x) := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₁, h₂, by simpa only [sub_neg_eq_add] using h₄,
    by simpa only [← sub_eq_add_neg] using h₃⟩

lemma conv_neg {a b : ℝ} {r y : ℂ} (h : K4Conv a b r y) :
    K4Conv a b r (-y) := by
  simpa only [K4Conv, neg_re, abs_neg] using h

lemma leftPoles_neg_iff (a b : ℝ) (r s x z : ℂ) :
    z ∈ leftPoles a b r s (-x) ↔ -z ∈ rightPoles a b r s x := by
  simp only [leftPoles, rightPoles, Set.mem_union, leftFamily, rightFamily,
    Set.mem_ofPred_eq, sub_neg_eq_add, ← sub_eq_add_neg]

lemma rightPoles_neg_iff (a b : ℝ) (r s x z : ℂ) :
    z ∈ rightPoles a b r s (-x) ↔ -z ∈ leftPoles a b r s x := by
  simp only [leftPoles, rightPoles, Set.mem_union, leftFamily, rightFamily,
    Set.mem_ofPred_eq, sub_neg_eq_add, ← sub_eq_add_neg]

lemma avoidsPoles_neg {a b : ℝ} {r s x : ℂ} {σ : ℝ}
    (h : AvoidsPoles a b r s x σ) : AvoidsPoles a b r s (-x) (-σ) := by
  intro z hz heq
  have hz' : -z ∈ leftPoles a b r s x ∪ rightPoles a b r s x := by
    rcases hz with hz | hz
    · exact Or.inr ((leftPoles_neg_iff a b r s x z).mp hz)
    · exact Or.inl ((rightPoles_neg_iff a b r s x z).mp hz)
  apply h (-z) hz'
  simp only [neg_re]
  linarith

lemma crossedLeft_neg (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) :
    crossedLeft a b hb hba r s (-x) (-σ) =
      (crossedRight a b hb hba r s x σ).image (fun w => -w) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hz, hσ⟩ := (mem_crossedLeft a b hb hba r s (-x) (-σ) z).mp hz
    apply Finset.mem_image.mpr
    refine ⟨-z, (mem_crossedRight a b hb hba r s x σ (-z)).mpr
      ⟨(leftPoles_neg_iff a b r s x z).mp hz, ?_⟩, by simp⟩
    simp only [neg_re]
    linarith
  · rintro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hσ⟩ := (mem_crossedRight a b hb hba r s x σ w).mp hw
    apply (mem_crossedLeft a b hb hba r s (-x) (-σ) (-w)).mpr
    refine ⟨(leftPoles_neg_iff a b r s x (-w)).mpr (by simpa using hw), ?_⟩
    simp only [neg_re]
    linarith

lemma crossedRight_neg (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) :
    crossedRight a b hb hba r s (-x) (-σ) =
      (crossedLeft a b hb hba r s x σ).image (fun w => -w) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hz, hσ⟩ := (mem_crossedRight a b hb hba r s (-x) (-σ) z).mp hz
    apply Finset.mem_image.mpr
    refine ⟨-z, (mem_crossedLeft a b hb hba r s x σ (-z)).mpr
      ⟨(rightPoles_neg_iff a b r s x z).mp hz, ?_⟩, by simp⟩
    simp only [neg_re]
    linarith
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hσ⟩ := (mem_crossedLeft a b hb hba r s x σ w).mp hw
    apply (mem_crossedRight a b hb hba r s (-x) (-σ) (-w)).mpr
    refine ⟨(rightPoles_neg_iff a b r s x (-w)).mpr (by simpa using hw), ?_⟩
    simp only [neg_re]
    linarith

lemma kernel_neg_arguments (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y : ℂ) :
    kernel a b hb hba r s (-x) (-y) = fun z => kernel a b hb hba r s x y (-z) := by
  funext z
  unfold kernel k4Integrand
  have he : 2 * Real.pi * I * (-y) * z / ((a : ℂ) * b) =
      2 * Real.pi * I * y * (-z) / ((a : ℂ) * b) := by ring
  rw [he]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- Simultaneously negating `x` and `y` leaves the normalized contour unchanged. -/
theorem K4_even (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x) :
    K4 a b hb hba r s x y = K4 a b hb hba r s (-x) (-y) := by
  classical
  let σ := startLine a b r s x
  have hσ : AvoidsPoles a b r s x σ := startLine_avoidsPoles (lt_of_lt_of_le hb hba) hb r s x
  have ho := (K4_line a b hb hba hirr r s x y hconv hnp σ hσ).2
  have hn := (K4_line a b hb hba hirr r s (-x) (-y) (conv_neg hconv)
    (noPinch_neg hnp) (-σ) (avoidsPoles_neg hσ)).2
  have ht := CorrectedContour.value_comp_const_sub (f := kernel a b hb hba r s x y)
    0 (-σ) (crossedLeft a b hb hba r s x σ) (crossedRight a b hb hba r s x σ)
    (fun w _ => kernel_exists_hasResidueGen a b hb hba hirr r s x y w hnp)
  simp only [zero_sub, zero_re, neg_neg] at ht
  rw [← kernel_neg_arguments, ← crossedLeft_neg, ← crossedRight_neg] at ht
  have hs : I * (Real.sqrt (a * b) : ℂ) ≠ 0 := mul_ne_zero I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hb hba) hb)).ne')
  apply mul_left_cancel₀ hs
  exact ho.symm.trans (ht.symm.trans hn)

end HaagerupIzumi.GammaK4Contour
