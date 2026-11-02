module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4LinearRelations
public import HaagerupIzumi.Analytic.GammaFourTermSpecialization
public import Mathlib.Data.Fin.VecNotation

/-!
# The six compatible contours in the four-term identity

The four products and the two translates of the primitive form a finite
family of translated centered kernels. Their pole orientations lie in four
fixed base families, allowing the pointwise identity to be integrated on a
single corrected contour.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

def fourTermKernels (a b : ℝ) (R X Y Z : ℂ) : Fin 6 → ShiftedKernel :=
  ![⟨R, X, Y + b, Z, -b⟩,
    ⟨R, X, Y - a, Z, a⟩,
    ⟨R, X - a, Y, Z, a / 2⟩,
    ⟨R, X + b, Y, Z, -b / 2⟩,
    ⟨R, X, Y, Z, 0⟩,
    ⟨R, X, Y, Z, -b⟩]

lemma fourTerm_left_arguments (a b : ℝ) (R X Y Z z : ℂ) (i : Fin 6) :
    let k := fourTermKernels a b R X Y Z i
    let ζ := k4U a b R X - b + z
    let ξ := k4V a b R X - b + Y + z
    k4U a b k.r k.s + (k.shift + z) = ![ζ, ζ + a + b, ζ + b, ζ + b, ζ + b, ζ] i ∧
    (k4V a b k.r k.s + k.x) + (k.shift + z) =
      ![ξ + b, ξ + b, ξ + a + b, ξ, ξ + b, ξ] i := by
  dsimp only
  fin_cases i <;> norm_num [fourTermKernels, k4U, k4V] <;> (try constructor) <;> ring

lemma fourTerm_right_arguments (a b : ℝ) (R X Y Z z : ℂ) (i : Fin 6) :
    let k := fourTermKernels a b R X Y Z i
    let η := k4U a b R X - a - z
    let ν := k4V a b R X - Y - z
    k4U a b k.r k.s - (k.shift + z) = ![η + a + b, η, η, η + a + b, η + a, η + a + b] i ∧
    (k4V a b k.r k.s - k.x) - (k.shift + z) = ![ν, ν, ν, ν, ν, ν + b] i := by
  dsimp only
  fin_cases i <;> norm_num [fourTermKernels, k4U, k4V] <;> (try constructor) <;> ring

lemma mem_poleLattice_of_add_first {a b : ℝ} {z : ℂ} (hz : z + a ∈ poleLattice a b) :
    z ∈ poleLattice a b := by
  by_contra h
  exact not_mem_poleLattice_add_first h hz

lemma mem_poleLattice_of_add_second {a b : ℝ} {z : ℂ} (hz : z + b ∈ poleLattice a b) :
    z ∈ poleLattice a b := by
  by_contra h
  exact not_mem_poleLattice_add_second h hz

lemma mem_poleLattice_of_add_sum {a b : ℝ} {z : ℂ} (hz : z + a + b ∈ poleLattice a b) :
    z ∈ poleLattice a b :=
  mem_poleLattice_of_add_first (mem_poleLattice_of_add_second hz)

lemma fourTerm_commonLeft_subset (a b : ℝ) (R X Y Z : ℂ) :
    commonLeft (fourTermKernels a b R X Y Z) a b ⊆
      leftFamily a b (k4U a b R X - b) ∪ leftFamily a b (k4V a b R X - b + Y) := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  change k4U a b (fourTermKernels a b R X Y Z i).r (fourTermKernels a b R X Y Z i).s +
      ((fourTermKernels a b R X Y Z i).shift + z) ∈ poleLattice a b ∨
    (k4V a b (fourTermKernels a b R X Y Z i).r (fourTermKernels a b R X Y Z i).s +
      (fourTermKernels a b R X Y Z i).x) + ((fourTermKernels a b R X Y Z i).shift + z) ∈
        poleLattice a b at hi
  obtain ⟨h₁, h₂⟩ := fourTerm_left_arguments a b R X Y Z z i
  rw [h₁, h₂] at hi
  change k4U a b R X - b + z ∈ poleLattice a b ∨ k4V a b R X - b + Y + z ∈ poleLattice a b
  fin_cases i <;> norm_num at hi
  · exact hi.imp id mem_poleLattice_of_add_second
  · exact hi.imp mem_poleLattice_of_add_sum mem_poleLattice_of_add_second
  · exact hi.imp mem_poleLattice_of_add_second mem_poleLattice_of_add_sum
  · exact hi.imp mem_poleLattice_of_add_second id
  · exact hi.imp mem_poleLattice_of_add_second mem_poleLattice_of_add_second
  · exact hi

lemma fourTerm_commonRight_subset (a b : ℝ) (R X Y Z : ℂ) :
    commonRight (fourTermKernels a b R X Y Z) a b ⊆
      rightFamily a b (k4U a b R X - a) ∪ rightFamily a b (k4V a b R X - Y) := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  change k4U a b (fourTermKernels a b R X Y Z i).r (fourTermKernels a b R X Y Z i).s -
      ((fourTermKernels a b R X Y Z i).shift + z) ∈ poleLattice a b ∨
    (k4V a b (fourTermKernels a b R X Y Z i).r (fourTermKernels a b R X Y Z i).s -
      (fourTermKernels a b R X Y Z i).x) - ((fourTermKernels a b R X Y Z i).shift + z) ∈
        poleLattice a b at hi
  obtain ⟨h₁, h₂⟩ := fourTerm_right_arguments a b R X Y Z z i
  rw [h₁, h₂] at hi
  change k4U a b R X - a - z ∈ poleLattice a b ∨ k4V a b R X - Y - z ∈ poleLattice a b
  fin_cases i <;> norm_num at hi
  · exact hi.imp mem_poleLattice_of_add_sum id
  · exact hi
  · exact hi
  · exact hi.imp mem_poleLattice_of_add_sum id
  · exact hi.imp mem_poleLattice_of_add_first id
  · exact hi.imp mem_poleLattice_of_add_sum mem_poleLattice_of_add_second

/-- The four opposite sums for the common unshifted gamma factors are
sufficient for compatibility of all six corrected contours. -/
lemma fourTerm_common_disjoint (a b : ℝ) (R X Y Z : ℂ)
    (h₁ : 2 * k4U a b R X - a - b ∉ poleLattice a b)
    (h₂ : k4U a b R X + k4V a b R X - b - Y ∉ poleLattice a b)
    (h₃ : k4U a b R X + k4V a b R X - a - b + Y ∉ poleLattice a b)
    (h₄ : 2 * k4V a b R X - b ∉ poleLattice a b) :
    Disjoint (commonLeft (fourTermKernels a b R X Y Z) a b)
      (commonRight (fourTermKernels a b R X Y Z) a b) := by
  have hd₁ : Disjoint (leftFamily a b (k4U a b R X - b))
      (rightFamily a b (k4U a b R X - a)) := by
    apply families_disjoint
    convert h₁ using 1 <;> ring
  have hd₂ : Disjoint (leftFamily a b (k4U a b R X - b))
      (rightFamily a b (k4V a b R X - Y)) := by
    apply families_disjoint
    convert h₂ using 1 <;> ring
  have hd₃ : Disjoint (leftFamily a b (k4V a b R X - b + Y))
      (rightFamily a b (k4U a b R X - a)) := by
    apply families_disjoint
    convert h₃ using 1 <;> ring
  have hd₄ : Disjoint (leftFamily a b (k4V a b R X - b + Y))
      (rightFamily a b (k4V a b R X - Y)) := by
    apply families_disjoint
    convert h₄ using 1 <;> ring
  exact ((hd₁.union_right hd₂).union_left (hd₃.union_right hd₄)).mono
    (fourTerm_commonLeft_subset a b R X Y Z) (fourTerm_commonRight_subset a b R X Y Z)

lemma ShiftedKernel.not_mem_pole_arguments (k : ShiftedKernel) (a b : ℝ) (z : ℂ)
    (hz : z ∉ k.left a b ∪ k.right a b) :
    k4U a b k.r k.s + (k.shift + z) ∉ poleLattice a b ∧
    (k4V a b k.r k.s + k.x) + (k.shift + z) ∉ poleLattice a b ∧
    k4U a b k.r k.s - (k.shift + z) ∉ poleLattice a b ∧
    (k4V a b k.r k.s - k.x) - (k.shift + z) ∉ poleLattice a b :=
  ⟨fun h => hz (Or.inl (Or.inl h)), fun h => hz (Or.inl (Or.inr h)),
    fun h => hz (Or.inr (Or.inl h)), fun h => hz (Or.inr (Or.inr h))⟩

lemma fourTerm_unshifted_not_poles (a b : ℝ) (R X Y Z z : ℂ)
    (hz : ∀ i, z ∉ (fourTermKernels a b R X Y Z i).left a b ∪
      (fourTermKernels a b R X Y Z i).right a b) :
    k4U a b R X - b + z ∉ poleLattice a b ∧ k4U a b R X - a - z ∉ poleLattice a b ∧
    k4V a b R X - b + Y + z ∉ poleLattice a b ∧ k4V a b R X - Y - z ∉ poleLattice a b := by
  have h₀ := (fourTermKernels a b R X Y Z 0).not_mem_pole_arguments a b z (hz 0)
  have h₁ := (fourTermKernels a b R X Y Z 1).not_mem_pole_arguments a b z (hz 1)
  have h₃ := (fourTermKernels a b R X Y Z 3).not_mem_pole_arguments a b z (hz 3)
  have hζ := h₀.1
  have hη := h₁.2.2.1
  have hξ := h₃.2.1
  have hν := h₀.2.2.2
  rw [(fourTerm_left_arguments a b R X Y Z z 0).1] at hζ
  rw [(fourTerm_right_arguments a b R X Y Z z 1).1] at hη
  rw [(fourTerm_left_arguments a b R X Y Z z 3).2] at hξ
  rw [(fourTerm_right_arguments a b R X Y Z z 0).2] at hν
  exact ⟨hζ, hη, hξ, hν⟩

lemma fourTerm_terms_eq_shifted (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (R X Y Z z : ℂ) :
    fourTermTerm₁ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
      fourTermExp a b Z b * (fourTermKernels a b R X Y Z 0).function a b hb hba z ∧
    fourTermTerm₂ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
      fourTermExp a b Z (-a) * (fourTermKernels a b R X Y Z 1).function a b hb hba z ∧
    fourTermTerm₃ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
      fourTermExp a b Z (-a / 2) * (fourTermKernels a b R X Y Z 2).function a b hb hba z ∧
    fourTermTerm₄ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
      fourTermExp a b Z (b / 2) * (fourTermKernels a b R X Y Z 3).function a b hb hba z := by
  constructor
  · change _ = fourTermExp a b Z b * k4Integrand (gamma a b hb hba) a b R X (Y + b) Z (-b + z)
    have ht := fourTermTerm₁_eq_kernel (gamma a b hb hba) a b R X Y Z (z - b)
    rw [sub_add_cancel] at ht
    simpa only [sub_eq_add_neg, add_comm] using ht
  constructor
  · change _ = fourTermExp a b Z (-a) * k4Integrand (gamma a b hb hba) a b R X (Y - a) Z (a + z)
    simpa only [add_sub_cancel_right, add_comm] using
      fourTermTerm₂_eq_kernel (gamma a b hb hba) a b R X Y Z (z + a)
  constructor
  · change _ = fourTermExp a b Z (-a / 2) * k4Integrand (gamma a b hb hba) a b R (X - a) Y Z (a / 2 + z)
    simpa only [add_sub_cancel_right, add_comm] using
      fourTermTerm₃_eq_kernel (gamma a b hb hba) a b R X Y Z (z + a / 2)
  · change _ = fourTermExp a b Z (b / 2) * k4Integrand (gamma a b hb hba) a b R (X + b) Y Z (-b / 2 + z)
    have ht := fourTermTerm₄_eq_kernel (gamma a b hb hba) a b R X Y Z (z - b / 2)
    rw [sub_add_cancel] at ht
    simpa only [sub_eq_add_neg, neg_div, add_comm] using ht

lemma fourTerm_primitive_eq_shifted (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (R X Y Z z : ℂ) :
    fourTermPrimitive (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z (z + b) -
      fourTermPrimitive (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
    fourTermExp a b Z b *
      ((fourTermKernels a b R X Y Z 4).function a b hb hba z -
        (fourTermKernels a b R X Y Z 5).function a b hb hba z) := by
  change _ = fourTermExp a b Z b * (k4Integrand (gamma a b hb hba) a b R X Y Z (0 + z) -
    k4Integrand (gamma a b hb hba) a b R X Y Z (-b + z))
  rw [zero_add]
  simpa only [sub_eq_add_neg, add_comm] using
    fourTermPrimitive_difference (gamma a b hb hba) a b R X Y Z z

/-- Integrating the pointwise primitive relation gives the four-term
relation between the actual normalized K4 values. -/
theorem fourTerm_contour_relation (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (R X Y Z d κ₁ κ₂ κ₃ κ₄ : ℂ)
    (hconv : K4Conv a b R Z)
    (hnp₁ : K4NoPinch a b R X (Y + b)) (hnp₂ : K4NoPinch a b R X (Y - a))
    (hnp₃ : K4NoPinch a b R (X - a) Y) (hnp₄ : K4NoPinch a b R (X + b) Y)
    (hc₁ : 2 * k4U a b R X - a - b ∉ poleLattice a b)
    (hc₂ : k4U a b R X + k4V a b R X - b - Y ∉ poleLattice a b)
    (hc₃ : k4U a b R X + k4V a b R X - a - b + Y ∉ poleLattice a b)
    (hc₄ : 2 * k4V a b R X - b ∉ poleLattice a b)
    (hpoint : ∀ z : ℂ, k4U a b R X - b + z ∉ poleLattice a b →
      k4U a b R X - a - z ∉ poleLattice a b → k4V a b R X - b + Y + z ∉ poleLattice a b →
      k4V a b R X - Y - z ∉ poleLattice a b →
      κ₁ * fourTermTerm₁ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z +
      κ₂ * fourTermTerm₂ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z +
      κ₃ * fourTermTerm₃ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z +
      κ₄ * fourTermTerm₄ (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z =
      d * (fourTermPrimitive (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z (z + b) -
        fourTermPrimitive (gamma a b hb hba) a b (k4U a b R X) (k4V a b R X) Y Z z)) :
    κ₁ * fourTermExp a b Z b * K4 a b hb hba R X (Y + b) Z +
      κ₂ * fourTermExp a b Z (-a) * K4 a b hb hba R X (Y - a) Z +
      κ₃ * fourTermExp a b Z (-a / 2) * K4 a b hb hba R (X - a) Y Z +
      κ₄ * fourTermExp a b Z (b / 2) * K4 a b hb hba R (X + b) Y Z = 0 := by
  let k := fourTermKernels a b R X Y Z
  let c : Fin 6 → ℂ := ![κ₁ * fourTermExp a b Z b, κ₂ * fourTermExp a b Z (-a),
    κ₃ * fourTermExp a b Z (-a / 2), κ₄ * fourTermExp a b Z (b / 2),
    -d * fourTermExp a b Z b, d * fourTermExp a b Z b]
  have hbase := fourTerm_base_noPinch a b R X Y hnp₁ hnp₃
  have hconvi (i : Fin 6) : K4Conv a b (k i).r (k i).y := by
    fin_cases i <;> exact hconv
  have hnpi (i : Fin 6) : K4NoPinch a b (k i).r (k i).s (k i).x := by
    fin_cases i
    · exact hnp₁
    · exact hnp₂
    · exact hnp₃
    · exact hnp₄
    · exact hbase
    · exact hbase
  have hrel := linear_relation k a b hb hba hirr c hconvi hnpi
    (fourTerm_common_disjoint a b R X Y Z hc₁ hc₂ hc₃ hc₄) (by
      intro z hz
      obtain ⟨hζ, hη, hξ, hν⟩ := fourTerm_unshifted_not_poles a b R X Y Z z hz
      have hp := hpoint z hζ hη hξ hν
      obtain ⟨ht₁, ht₂, ht₃, ht₄⟩ := fourTerm_terms_eq_shifted a b hb hba R X Y Z z
      rw [ht₁, ht₂, ht₃, ht₄, fourTerm_primitive_eq_shifted] at hp
      norm_num [c, k, Fin.sum_univ_succ, Fin.succ]
      dsimp [fourTermKernels, Matrix.vecCons, Fin.cons] at hp ⊢
      linear_combination hp)
  norm_num [c, k, fourTermKernels, Fin.sum_univ_succ, Fin.succ] at hrel
  linear_combination hrel

end HaagerupIzumi.GammaK4Contour
