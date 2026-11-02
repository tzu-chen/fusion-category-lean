module

public import HaagerupIzumi.Analytic.ResidueAlgebra
public import HaagerupIzumi.Analytic.HypGamma
public import Mathlib.MeasureTheory.Group.Integral
import all Mathlib.Data.Complex.Basic

/-!
# Affine changes of variables in corrected contour integrals

Translation preserves residues. Reflection reverses their signs and exchanges
the left and right crossed-pole sets. These rules also apply to double poles.
-/

@[expose] public section
noncomputable section

open Complex Filter Set Topology MeasureTheory

namespace HaagerupIzumi

lemma HasResidueGen.comp_const_add {f : ℂ → ℂ} {c w ρ : ℂ}
    (hf : HasResidueGen f (c + w) ρ) :
    HasResidueGen (fun z => f (c + z)) w ρ := by
  obtain ⟨d, hd⟩ := hf
  refine ⟨d, ?_⟩
  have ht := hd.comp (tendsto_punctured_of_injective
    (continuous_const_add c) (add_right_injective c) w)
  apply ht.congr'
  filter_upwards with z
  simp only [Function.comp_def, show c + z - (c + w) = z - w by ring]

lemma HasResidueGen.comp_const_sub {f : ℂ → ℂ} {c w ρ : ℂ}
    (hf : HasResidueGen f (c - w) ρ) :
    HasResidueGen (fun z => f (c - z)) w (-ρ) := by
  obtain ⟨d, hd⟩ := hf
  refine ⟨d, ?_⟩
  have ht := (hd.comp (tendsto_punctured_of_injective
    (continuous_const.sub continuous_id) sub_right_injective w)).neg
  apply ht.congr'
  filter_upwards with z
  simp only [Function.comp_def, Pi.sub_apply, id_eq, show c - z - (c - w) = -(z - w) by ring, inv_neg]
  ring

lemma residueValue_comp_const_add {f : ℂ → ℂ} (c w : ℂ)
    (hf : ∃ ρ, HasResidueGen f (c + w) ρ) :
    residueValue (fun z => f (c + z)) w = residueValue f (c + w) :=
  residueValue_eq (hasResidueGen_residueValue hf).comp_const_add

lemma residueValue_comp_const_sub {f : ℂ → ℂ} (c w : ℂ)
    (hf : ∃ ρ, HasResidueGen f (c - w) ρ) :
    residueValue (fun z => f (c - z)) w = -residueValue f (c - w) :=
  residueValue_eq (hasResidueGen_residueValue hf).comp_const_sub

namespace CorrectedContour

lemma lineIntegral_comp_const_add (f : ℂ → ℂ) (c : ℂ) (σ : ℝ) :
    lineIntegral (fun z => f (c + z)) σ = lineIntegral f (σ + c.re) := by
  unfold lineIntegral
  have heq : (fun t : ℝ => f (c + (σ + t * I)) * I) =
      fun t : ℝ => f (((σ + c.re : ℝ) : ℂ) + (t + c.im) * I) * I := by
    funext t
    congr 2
    apply Complex.ext <;> simp <;> ring
  rw [heq]
  simpa only [Complex.ofReal_add] using
    integral_add_right_eq_self (μ := volume)
      (fun t : ℝ => f (((σ + c.re : ℝ) : ℂ) + t * I) * I) c.im

lemma lineIntegral_comp_const_sub (f : ℂ → ℂ) (c : ℂ) (σ : ℝ) :
    lineIntegral (fun z => f (c - z)) σ = lineIntegral f (c.re - σ) := by
  unfold lineIntegral
  have heq : (fun t : ℝ => f (c - (σ + t * I)) * I) =
      fun t : ℝ => f (((c.re - σ : ℝ) : ℂ) + (-t + c.im) * I) * I := by
    funext t
    congr 2
    apply Complex.ext <;> simp
    ring
  rw [heq]
  calc
    _ = ∫ t : ℝ, f (((c.re - σ : ℝ) : ℂ) + (t + c.im) * I) * I :=
      by simpa only [Complex.ofReal_neg, Complex.ofReal_add] using
        integral_neg_eq_self
          (fun t : ℝ => f (((c.re - σ : ℝ) : ℂ) + (t + c.im) * I) * I) volume
    _ = _ := by
      simpa only [Complex.ofReal_add] using
        integral_add_right_eq_self (μ := volume)
          (fun t : ℝ => f (((c.re - σ : ℝ) : ℂ) + t * I) * I) c.im

lemma lineIntegral_const_mul (f : ℂ → ℂ) (α : ℂ) (σ : ℝ) :
    lineIntegral (fun z => α * f z) σ = α * lineIntegral f σ := by
  simp only [lineIntegral, mul_assoc, integral_const_mul]

lemma value_const_mul {f : ℂ → ℂ} (α : ℂ) (σ : ℝ) (SL SR : Finset ℂ)
    (hf : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen f w ρ) :
    value (fun z => α * f z) σ SL SR = α * value f σ SL SR := by
  have hsum (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S, residueValue (fun z => α * f z) w) = α * ∑ w ∈ S, residueValue f w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_const_mul (hf w (hS hw)) α
  rw [value, lineIntegral_const_mul, hsum SL Finset.subset_union_left,
    hsum SR Finset.subset_union_right]
  unfold value
  ring

/-- Translate both the line and its pole corrections by the same complex
amount. The imaginary displacement is handled by translation invariance of
the ordinary real integral. -/
lemma value_comp_const_add {f : ℂ → ℂ} (c : ℂ) (σ : ℝ) (SL SR : Finset ℂ)
    (hf : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen f w ρ) :
    value (fun z => f (c + z)) σ (SL.image (fun w => w - c)) (SR.image (fun w => w - c)) =
      value f (σ + c.re) SL SR := by
  classical
  have hinj : Function.Injective (fun w : ℂ => w - c) := by
    intro u v h
    linear_combination h
  have hsum (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S.image (fun w => w - c), residueValue (fun z => f (c + z)) w) =
        ∑ w ∈ S, residueValue f w := by
    rw [Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro w hw
    have hp : ∃ ρ, HasResidueGen f (c + (w - c)) ρ := by
      rw [show c + (w - c) = w by ring]
      exact hf w (hS hw)
    rw [residueValue_comp_const_add c (w - c) hp]
    congr 1
    ring
  rw [value, lineIntegral_comp_const_add, hsum SL Finset.subset_union_left,
    hsum SR Finset.subset_union_right]
  rfl

/-- Reflection exchanges crossed left and right poles; its residue sign
cancels that exchange in the corrected contour value. -/
lemma value_comp_const_sub {f : ℂ → ℂ} (c : ℂ) (σ : ℝ) (SL SR : Finset ℂ)
    (hf : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen f w ρ) :
    value (fun z => f (c - z)) σ (SR.image (fun w => c - w)) (SL.image (fun w => c - w)) =
      value f (c.re - σ) SL SR := by
  classical
  have hinj : Function.Injective (fun w : ℂ => c - w) := by
    intro u v h
    linear_combination -h
  have hsum (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S.image (fun w => c - w), residueValue (fun z => f (c - z)) w) =
        -(∑ w ∈ S, residueValue f w) := by
    rw [Finset.sum_image hinj.injOn, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    have hp : ∃ ρ, HasResidueGen f (c - (c - w)) ρ := by
      simpa only [sub_sub_cancel] using hf w (hS hw)
    rw [residueValue_comp_const_sub c (c - w) hp, sub_sub_cancel]
  rw [value, lineIntegral_comp_const_sub, hsum SR Finset.subset_union_right,
    hsum SL Finset.subset_union_left]
  unfold value
  ring

end CorrectedContour
end HaagerupIzumi
