module

public import HaagerupIzumi.Analytic.GammaK4Line
public import HaagerupIzumi.Analytic.ContourAffine
import all Mathlib.Data.Complex.Basic

/-! # Parameter interchange of the concrete four-gamma contour -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

def swapShift (s x : ℂ) : ℂ := (s - x) / 2

def swapMultiplier (a b : ℝ) (s x y : ℂ) : ℂ :=
  Complex.exp (Real.pi * I * y * (s - x) / ((a : ℂ) * b))

lemma swap_arguments (a b : ℝ) (r s x z : ℂ) :
    k4U a b r s + (swapShift s x + z) = (k4V a b r x + s) + z ∧
    (k4V a b r s + x) + (swapShift s x + z) = k4U a b r x + z ∧
    k4U a b r s - (swapShift s x + z) = k4U a b r x - z ∧
    (k4V a b r s - x) - (swapShift s x + z) = (k4V a b r x - s) - z := by
  unfold k4U k4V swapShift
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma noPinch_swap {a b : ℝ} {r s x : ℂ} (h : K4NoPinch a b r s x) :
    K4NoPinch a b r x s := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 2 * k4U a b r x = k4U a b r s + k4V a b r s + x by
      unfold k4U k4V; ring]
    exact h₄
  · rw [show 2 * k4V a b r x = k4U a b r s + k4V a b r s - x by
      unfold k4U k4V; ring]
    exact h₃
  · rw [show k4U a b r x + k4V a b r x - s = 2 * k4V a b r s by
      unfold k4U k4V; ring]
    exact h₂
  · rw [show k4U a b r x + k4V a b r x + s = 2 * k4U a b r s by
      unfold k4U k4V; ring]
    exact h₁

lemma leftPoles_swap_iff (a b : ℝ) (r s x z : ℂ) :
    z ∈ leftPoles a b r x s ↔ swapShift s x + z ∈ leftPoles a b r s x := by
  obtain ⟨h₁, h₂, _, _⟩ := swap_arguments a b r s x z
  simp only [leftPoles, leftFamily, Set.mem_union, Set.mem_ofPred_eq, h₁, h₂, or_comm]

lemma rightPoles_swap_iff (a b : ℝ) (r s x z : ℂ) :
    z ∈ rightPoles a b r x s ↔ swapShift s x + z ∈ rightPoles a b r s x := by
  obtain ⟨_, _, h₃, h₄⟩ := swap_arguments a b r s x z
  simp only [rightPoles, rightFamily, Set.mem_union, Set.mem_ofPred_eq, h₃, h₄]

lemma avoidsPoles_swap {a b : ℝ} {r s x : ℂ} {σ : ℝ}
    (h : AvoidsPoles a b r x s σ) :
    AvoidsPoles a b r s x (σ + (swapShift s x).re) := by
  intro z hz heq
  have hz' : z - swapShift s x ∈ leftPoles a b r x s ∪ rightPoles a b r x s := by
    have he : swapShift s x + (z - swapShift s x) = z := by ring
    rcases hz with hz | hz
    · exact Or.inl ((leftPoles_swap_iff a b r s x (z - swapShift s x)).mpr (by rwa [he]))
    · exact Or.inr ((rightPoles_swap_iff a b r s x (z - swapShift s x)).mpr (by rwa [he]))
  apply h (z - swapShift s x) hz'
  simp only [sub_re]
  linarith

lemma crossedLeft_swap (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) :
    crossedLeft a b hb hba r x s σ =
      (crossedLeft a b hb hba r s x (σ + (swapShift s x).re)).image
        (fun w => w - swapShift s x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hz, hσ⟩ := (mem_crossedLeft a b hb hba r x s σ z).mp hz
    apply Finset.mem_image.mpr
    refine ⟨swapShift s x + z,
      (mem_crossedLeft a b hb hba r s x (σ + (swapShift s x).re) _).mpr
        ⟨(leftPoles_swap_iff a b r s x z).mp hz, ?_⟩, by ring⟩
    simp only [add_re]
    linarith
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hσ⟩ := (mem_crossedLeft a b hb hba r s x (σ + (swapShift s x).re) w).mp hw
    apply (mem_crossedLeft a b hb hba r x s σ _).mpr
    refine ⟨(leftPoles_swap_iff a b r s x _).mpr ?_, ?_⟩
    · rwa [show swapShift s x + (w - swapShift s x) = w by ring]
    · simp only [sub_re]; linarith

lemma crossedRight_swap (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) :
    crossedRight a b hb hba r x s σ =
      (crossedRight a b hb hba r s x (σ + (swapShift s x).re)).image
        (fun w => w - swapShift s x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hz, hσ⟩ := (mem_crossedRight a b hb hba r x s σ z).mp hz
    apply Finset.mem_image.mpr
    refine ⟨swapShift s x + z,
      (mem_crossedRight a b hb hba r s x (σ + (swapShift s x).re) _).mpr
        ⟨(rightPoles_swap_iff a b r s x z).mp hz, ?_⟩, by ring⟩
    simp only [add_re]
    linarith
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hσ⟩ := (mem_crossedRight a b hb hba r s x (σ + (swapShift s x).re) w).mp hw
    apply (mem_crossedRight a b hb hba r x s σ _).mpr
    refine ⟨(rightPoles_swap_iff a b r s x _).mpr ?_, ?_⟩
    · rwa [show swapShift s x + (w - swapShift s x) = w by ring]
    · simp only [sub_re]; linarith

lemma kernel_comp_swap (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y : ℂ) :
    (fun z => kernel a b hb hba r s x y (swapShift s x + z)) =
      fun z => swapMultiplier a b s x y * kernel a b hb hba r x s y z := by
  funext z
  obtain ⟨h₁, h₂, h₃, h₄⟩ := swap_arguments a b r s x z
  unfold kernel k4Integrand swapMultiplier
  have he : 2 * Real.pi * I * y * (swapShift s x + z) / ((a : ℂ) * b) =
      Real.pi * I * y * (s - x) / ((a : ℂ) * b) +
        2 * Real.pi * I * y * z / ((a : ℂ) * b) := by unfold swapShift; ring
  have hv₁ : k4V a b r s + (swapShift s x + z) + x =
      (k4V a b r s + x) + (swapShift s x + z) := by ring
  have hv₂ : k4V a b r s - (swapShift s x + z) - x =
      (k4V a b r s - x) - (swapShift s x + z) := by ring
  rw [he, Complex.exp_add, hv₁, hv₂, h₁, h₂, h₃, h₄]
  have hv₃ : (k4V a b r x + s) + z = k4V a b r x + z + s := by ring
  have hv₄ : (k4V a b r x - s) - z = k4V a b r x - z - s := by ring
  rw [hv₃, hv₄]
  ring

/-- Interchange of the two geometric parameters, with its exact exponential
factor, follows by translating the corrected contour. -/
theorem K4_swap (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hnp : K4NoPinch a b r s x) :
    K4 a b hb hba r s x y =
      Complex.exp (Real.pi * I * y * (s - x) / ((a : ℂ) * b)) * K4 a b hb hba r x s y := by
  classical
  let σ := startLine a b r x s
  have hnps := noPinch_swap hnp
  have hσ : AvoidsPoles a b r x s σ := startLine_avoidsPoles (lt_of_lt_of_le hb hba) hb r x s
  have ho := (K4_line a b hb hba hirr r s x y hconv hnp
    (σ + (swapShift s x).re) (avoidsPoles_swap hσ)).2
  have hn := (K4_line a b hb hba hirr r x s y hconv hnps σ hσ).2
  have ht := CorrectedContour.value_comp_const_add (f := kernel a b hb hba r s x y)
    (swapShift s x) σ (crossedLeft a b hb hba r s x (σ + (swapShift s x).re))
    (crossedRight a b hb hba r s x (σ + (swapShift s x).re))
    (fun w _ => kernel_exists_hasResidueGen a b hb hba hirr r s x y w hnp)
  rw [kernel_comp_swap, ← crossedLeft_swap, ← crossedRight_swap,
    CorrectedContour.value_const_mul (swapMultiplier a b s x y) σ _ _
      (fun w _ => kernel_exists_hasResidueGen a b hb hba hirr r x s y w hnps)] at ht
  have hs : I * (Real.sqrt (a * b) : ℂ) ≠ 0 := mul_ne_zero I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hb hba) hb)).ne')
  apply mul_left_cancel₀ hs
  calc
    _ = _ := ho.symm
    _ = _ := ht.symm
    _ = swapMultiplier a b s x y * (I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba r x s y) := by rw [hn]
    _ = _ := by unfold swapMultiplier; ring

end HaagerupIzumi.GammaK4Contour
