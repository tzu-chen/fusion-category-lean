module

public import HaagerupIzumi.Analytic.GammaK4Contour
public import HaagerupIzumi.Analytic.GammaLocalFactors
import all Mathlib.Data.Complex.Basic

/-!
# Generalized residues of the concrete four-gamma kernel

No pinch prevents a left pole from meeting a right pole. Two factors of the
same orientation can still meet; their product has order at most two, and the
intrinsic generalized residue records that collision without choosing labels.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

def leftProduct (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x z : ℂ) : ℂ :=
  gamma a b hb hba (k4U a b r s + z) * gamma a b hb hba ((k4V a b r s + x) + z)

def rightProduct (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x z : ℂ) : ℂ :=
  gamma a b hb hba (k4U a b r s - z) * gamma a b hb hba ((k4V a b r s - x) - z)

def exponentialFactor (a b : ℝ) (y z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * y * z / (a * b))

lemma kernel_factorization (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y : ℂ) :
    kernel a b hb hba r s x y = fun z =>
      leftProduct a b hb hba r s x z * rightProduct a b hb hba r s x z *
        exponentialFactor a b y z := by
  funext z
  unfold kernel k4Integrand leftProduct rightProduct exponentialFactor
  have h₁ : k4V a b r s + z + x = (k4V a b r s + x) + z := by ring
  have h₂ : k4V a b r s - z - x = (k4V a b r s - x) - z := by ring
  rw [h₁, h₂]
  ring

lemma leftProduct_differentiableAt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x z : ℂ) (hz : z ∉ leftPoles a b r s x) :
    DifferentiableAt ℂ (leftProduct a b hb hba r s x) z := by
  have h₁ : k4U a b r s + z ∉ poleLattice a b := fun h => hz (Or.inl h)
  have h₂ : (k4V a b r s + x) + z ∉ poleLattice a b := fun h => hz (Or.inr h)
  exact (gamma_differentiableAt_add a b hb hba _ z h₁).mul
    (gamma_differentiableAt_add a b hb hba _ z h₂)

lemma rightProduct_differentiableAt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x z : ℂ) (hz : z ∉ rightPoles a b r s x) :
    DifferentiableAt ℂ (rightProduct a b hb hba r s x) z := by
  have h₁ : k4U a b r s - z ∉ poleLattice a b := fun h => hz (Or.inl h)
  have h₂ : (k4V a b r s - x) - z ∉ poleLattice a b := fun h => hz (Or.inr h)
  exact (gamma_differentiableAt_sub a b hb hba _ z h₁).mul
    (gamma_differentiableAt_sub a b hb hba _ z h₂)

lemma exponentialFactor_differentiable (a b : ℝ) (y : ℂ) :
    Differentiable ℂ (exponentialFactor a b y) := by
  unfold exponentialFactor
  fun_prop

lemma kernel_differentiableAt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y z : ℂ) (hz : z ∉ leftPoles a b r s x ∪ rightPoles a b r s x) :
    DifferentiableAt ℂ (kernel a b hb hba r s x y) z := by
  rw [kernel_factorization]
  exact ((leftProduct_differentiableAt a b hb hba r s x z (fun h => hz (Or.inl h))).mul
    (rightProduct_differentiableAt a b hb hba r s x z (fun h => hz (Or.inr h)))).mul
      (exponentialFactor_differentiable a b y z)

lemma leftProduct_exists_hasResidueGen (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x z : ℂ) :
    ∃ ρ, HasResidueGen (leftProduct a b hb hba r s x) z ρ :=
  exists_hasResidueGen_mul (gamma_atMostSimple_add a b hb hba hirr _ z)
    (gamma_atMostSimple_add a b hb hba hirr _ z)

lemma rightProduct_exists_hasResidueGen (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x z : ℂ) :
    ∃ ρ, HasResidueGen (rightProduct a b hb hba r s x) z ρ :=
  exists_hasResidueGen_mul (gamma_atMostSimple_sub a b hb hba hirr _ z)
    (gamma_atMostSimple_sub a b hb hba hirr _ z)

/-- At every point the no-pinch kernel has a pole of order at most two. -/
lemma kernel_exists_hasResidueGen (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y z : ℂ) (hnp : K4NoPinch a b r s x) :
    ∃ ρ, HasResidueGen (kernel a b hb hba r s x y) z ρ := by
  by_cases hz : z ∈ leftPoles a b r s x
  · have hr : z ∉ rightPoles a b r s x :=
      fun h => Set.disjoint_left.mp (noPinch_disjoint hnp) hz h
    obtain ⟨ρ, hρ⟩ := leftProduct_exists_hasResidueGen a b hb hba hirr r s x z
    obtain ⟨ρ', hρ'⟩ := hρ.mul_differentiableAt
      ((rightProduct_differentiableAt a b hb hba r s x z hr).mul
        (exponentialFactor_differentiable a b y z))
    refine ⟨ρ', ?_⟩
    have heq : kernel a b hb hba r s x y = fun w =>
        leftProduct a b hb hba r s x w *
          (rightProduct a b hb hba r s x w * exponentialFactor a b y w) := by
      rw [kernel_factorization]
      funext w
      ring
    rw [heq]
    exact hρ'
  · obtain ⟨ρ, hρ⟩ := rightProduct_exists_hasResidueGen a b hb hba hirr r s x z
    obtain ⟨ρ', hρ'⟩ := hρ.mul_differentiableAt
      ((leftProduct_differentiableAt a b hb hba r s x z hz).mul
        (exponentialFactor_differentiable a b y z))
    refine ⟨ρ', ?_⟩
    have heq : kernel a b hb hba r s x y = fun w =>
        rightProduct a b hb hba r s x w *
          (leftProduct a b hb hba r s x w * exponentialFactor a b y w) := by
      rw [kernel_factorization]
      funext w
      ring
    rw [heq]
    exact hρ'

lemma kernel_hasResidueGen_residueValue (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y z : ℂ) (hnp : K4NoPinch a b r s x) :
    HasResidueGen (kernel a b hb hba r s x y) z
      (residueValue (kernel a b hb hba r s x y) z) :=
  hasResidueGen_residueValue (kernel_exists_hasResidueGen a b hb hba hirr r s x y z hnp)

lemma kernel_residueValue_eq_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y z : ℂ) (hz : z ∉ leftPoles a b r s x ∪ rightPoles a b r s x) :
    residueValue (kernel a b hb hba r s x y) z = 0 :=
  residueValue_of_continuousAt (kernel_differentiableAt a b hb hba r s x y z hz).continuousAt

end HaagerupIzumi.GammaK4Contour
