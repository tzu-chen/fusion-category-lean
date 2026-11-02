module

public import HaagerupIzumi.Analytic.GammaK4Residues
public import HaagerupIzumi.Analytic.ParametricHolomorphic
import all Mathlib.Data.Complex.Basic

/-!
# Measurability and parameter regularity of the concrete kernel

The exceptional pole set is countable, so the total gamma function is
measurable. Along the Euler scaling family, the kernel is jointly continuous
and holomorphic in the scaling parameter wherever its four arguments avoid
the pole lattice.
-/

@[expose] public section
noncomputable section

open Complex Set MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaContinuation

lemma measurable_gamma (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    Measurable (gamma a b hb hba) := by
  apply ContinuousOn.measurable_of_countable_compl (s := (poleLattice a b)ᶜ)
  · intro z hz
    exact (gamma_differentiableAt a b hb hba z hz).continuousAt.continuousWithinAt
  · simpa only [compl_compl] using poleLattice_countable a b

end HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

def scaledKernel (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y t z : ℂ) : ℂ := kernel a b hb hba (t * r) (t * s) (t * x) (t * y) z

lemma measurable_scaledKernel (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y : ℂ) :
    Measurable (fun p : ℂ × ℂ => scaledKernel a b hb hba r s x y p.1 p.2) := by
  unfold scaledKernel kernel k4Integrand k4U k4V
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.mul
        · fun_prop
        · exact (measurable_gamma a b hb hba).comp (by fun_prop)
      · exact (measurable_gamma a b hb hba).comp (by fun_prop)
    · exact (measurable_gamma a b hb hba).comp (by fun_prop)
  · exact (measurable_gamma a b hb hba).comp (by fun_prop)

lemma scaled_args_not_poles (a b : ℝ) (r s x t z : ℂ)
    (hp : z ∉ leftPoles a b (t * r) (t * s) (t * x) ∪
      rightPoles a b (t * r) (t * s) (t * x)) :
    k4U a b (t * r) (t * s) + z ∉ poleLattice a b ∧
    k4U a b (t * r) (t * s) - z ∉ poleLattice a b ∧
    k4V a b (t * r) (t * s) + z + t * x ∉ poleLattice a b ∧
    k4V a b (t * r) (t * s) - z - t * x ∉ poleLattice a b := by
  refine ⟨fun h => hp (Or.inl (Or.inl h)), fun h => hp (Or.inr (Or.inl h)), ?_, ?_⟩
  · intro h
    apply hp (Or.inl (Or.inr ?_))
    change (k4V a b (t * r) (t * s) + t * x) + z ∈ poleLattice a b
    simpa only [add_assoc, add_left_comm, add_comm] using h
  · intro h
    apply hp (Or.inr (Or.inr ?_))
    change (k4V a b (t * r) (t * s) - t * x) - z ∈ poleLattice a b
    have heq : (k4V a b (t * r) (t * s) - t * x) - z =
        k4V a b (t * r) (t * s) - z - t * x := by ring
    rw [heq]
    exact h

lemma continuousAt_scaledKernel (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y : ℂ) (p : ℂ × ℂ)
    (hp : p.2 ∉ leftPoles a b (p.1 * r) (p.1 * s) (p.1 * x) ∪
      rightPoles a b (p.1 * r) (p.1 * s) (p.1 * x)) :
    ContinuousAt (fun v : ℂ × ℂ => scaledKernel a b hb hba r s x y v.1 v.2) p := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scaled_args_not_poles a b r s x p.1 p.2 hp
  have hc₁ := (gamma_differentiableAt a b hb hba _ h₁).continuousAt.comp
    (x := p) (f := fun v : ℂ × ℂ => k4U a b (v.1 * r) (v.1 * s) + v.2) (by
      unfold k4U; fun_prop)
  have hc₂ := (gamma_differentiableAt a b hb hba _ h₂).continuousAt.comp
    (x := p) (f := fun v : ℂ × ℂ => k4U a b (v.1 * r) (v.1 * s) - v.2) (by
      unfold k4U; fun_prop)
  have hc₃ := (gamma_differentiableAt a b hb hba _ h₃).continuousAt.comp
    (x := p) (f := fun v : ℂ × ℂ => k4V a b (v.1 * r) (v.1 * s) + v.2 + v.1 * x) (by
      unfold k4V; fun_prop)
  have hc₄ := (gamma_differentiableAt a b hb hba _ h₄).continuousAt.comp
    (x := p) (f := fun v : ℂ × ℂ => k4V a b (v.1 * r) (v.1 * s) - v.2 - v.1 * x) (by
      unfold k4V; fun_prop)
  have he : ContinuousAt (fun v : ℂ × ℂ =>
      Complex.exp (2 * Real.pi * I * (v.1 * y) * v.2 / ((a : ℂ) * b))) p := by fun_prop
  exact (((he.mul hc₁).mul hc₂).mul hc₃).mul hc₄

lemma differentiableAt_scaledKernel_parameter (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y t z : ℂ)
    (hp : z ∉ leftPoles a b (t * r) (t * s) (t * x) ∪
      rightPoles a b (t * r) (t * s) (t * x)) :
    DifferentiableAt ℂ (fun w => scaledKernel a b hb hba r s x y w z) t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scaled_args_not_poles a b r s x t z hp
  have hd₁ := (gamma_differentiableAt a b hb hba _ h₁).comp t
    (show DifferentiableAt ℂ (fun w => k4U a b (w * r) (w * s) + z) t by unfold k4U; fun_prop)
  have hd₂ := (gamma_differentiableAt a b hb hba _ h₂).comp t
    (show DifferentiableAt ℂ (fun w => k4U a b (w * r) (w * s) - z) t by unfold k4U; fun_prop)
  have hd₃ := (gamma_differentiableAt a b hb hba _ h₃).comp t
    (show DifferentiableAt ℂ (fun w => k4V a b (w * r) (w * s) + z + w * x) t by unfold k4V; fun_prop)
  have hd₄ := (gamma_differentiableAt a b hb hba _ h₄).comp t
    (show DifferentiableAt ℂ (fun w => k4V a b (w * r) (w * s) - z - w * x) t by unfold k4V; fun_prop)
  have he : DifferentiableAt ℂ (fun w : ℂ =>
      Complex.exp (2 * Real.pi * I * (w * y) * z / ((a : ℂ) * b))) t := by fun_prop
  exact (((he.mul hd₁).mul hd₂).mul hd₃).mul hd₄

end HaagerupIzumi.GammaK4Contour
