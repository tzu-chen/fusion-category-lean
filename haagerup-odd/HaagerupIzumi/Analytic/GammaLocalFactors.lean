module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaPoleResidues

/-!
# Translated and reflected gamma factors

These local regularity statements supply the simple factors from which the
two-gamma and four-gamma contour kernels are formed.
-/

@[expose] public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace HaagerupIzumi

lemma HasResidue.comp_const_add {f : ℂ → ℂ} {c w ρ : ℂ}
    (hf : HasResidue f (c + w) ρ) :
    HasResidue (fun z => f (c + z)) w ρ := by
  have ht := hf.comp (tendsto_punctured_of_injective
    (continuous_const_add c) (add_right_injective c) w)
  apply ht.congr'
  filter_upwards with z
  simp only [Function.comp_def]
  ring

lemma HasResidue.comp_const_sub {f : ℂ → ℂ} {c w ρ : ℂ}
    (hf : HasResidue f (c - w) ρ) :
    HasResidue (fun z => f (c - z)) w (-ρ) := by
  have ht := (hf.comp (tendsto_punctured_of_injective
    (continuous_const.sub continuous_id) sub_right_injective w)).neg
  apply ht.congr'
  filter_upwards with z
  simp only [Function.comp_def, Pi.sub_apply, id_eq]
  ring

namespace GammaContinuation

lemma gamma_eventually_differentiableAt_add (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (c w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ (fun z => gamma a b hb hba (c + z)) z := by
  have ht := (tendsto_punctured_of_injective (continuous_const_add c)
    (add_right_injective c) w).eventually
      (eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb (c + w))
  filter_upwards [ht] with z hz
  exact (gamma_differentiableAt a b hb hba (c + z) hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c + z) z)

lemma gamma_eventually_differentiableAt_sub (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (c w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ (fun z => gamma a b hb hba (c - z)) z := by
  have ht := (tendsto_punctured_of_injective (continuous_const.sub continuous_id)
    sub_right_injective w).eventually
      (eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb (c - w))
  filter_upwards [ht] with z hz
  exact (gamma_differentiableAt a b hb hba (c - z) hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c - z) z)

lemma gamma_differentiableAt_add (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (c w : ℂ) (hw : c + w ∉ poleLattice a b) :
    DifferentiableAt ℂ (fun z => gamma a b hb hba (c + z)) w :=
  (gamma_differentiableAt a b hb hba (c + w) hw).comp w
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c + z) w)

lemma gamma_differentiableAt_sub (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (c w : ℂ) (hw : c - w ∉ poleLattice a b) :
    DifferentiableAt ℂ (fun z => gamma a b hb hba (c - z)) w :=
  (gamma_differentiableAt a b hb hba (c - w) hw).comp w
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c - z) w)

lemma gamma_atMostSimple_add (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (c w : ℂ) :
    AtMostSimple (fun z => gamma a b hb hba (c + z)) w := by
  by_cases hw : c + w ∈ poleLattice a b
  · obtain ⟨ρ, _, hρ⟩ := gamma_has_nonzero_residue a b hb hba hirr (c + w) hw
    exact Or.inr ⟨⟨ρ, hρ.comp_const_add⟩, gamma_eventually_differentiableAt_add a b hb hba c w⟩
  · exact Or.inl (gamma_differentiableAt_add a b hb hba c w hw)

lemma gamma_atMostSimple_sub (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (c w : ℂ) :
    AtMostSimple (fun z => gamma a b hb hba (c - z)) w := by
  by_cases hw : c - w ∈ poleLattice a b
  · obtain ⟨ρ, _, hρ⟩ := gamma_has_nonzero_residue a b hb hba hirr (c - w) hw
    exact Or.inr ⟨⟨-ρ, hρ.comp_const_sub⟩, gamma_eventually_differentiableAt_sub a b hb hba c w⟩
  · exact Or.inl (gamma_differentiableAt_sub a b hb hba c w hw)

end GammaContinuation
end HaagerupIzumi
