module

public import HaagerupIzumi.Analytic.Residue
import all Mathlib.Data.Complex.Basic

/-!
# Algebra of residues with poles of order at most two

Uniqueness makes the residue used in a corrected contour integral intrinsic.
Linearity will permit pointwise kernel identities to be integrated even when
two poles of the same orientation coincide.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace HaagerupIzumi

private lemma tendsto_sq_mul_of_principal {f : ℂ → ℂ} {w c ρ : ℂ}
    (hc : Tendsto (fun z => (z - w) * f z - c * (z - w)⁻¹) (𝓝[≠] w) (𝓝 ρ)) :
    Tendsto (fun z => (z - w) ^ 2 * f z) (𝓝[≠] w) (𝓝 c) := by
  have hzero : Tendsto (fun z : ℂ => z - w) (𝓝[≠] w) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z) (𝓝[≠] w) (𝓝 w) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa only [sub_self] using h.sub_const w
  have hh := (hzero.mul hc).add_const c
  simp only [zero_mul, zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ w at hz
  field_simp [sub_ne_zero.mpr hz]
  ring

lemma HasResidueGen.unique {f : ℂ → ℂ} {w ρ σ : ℂ}
    (hρ : HasResidueGen f w ρ) (hσ : HasResidueGen f w σ) : ρ = σ := by
  obtain ⟨c, hc⟩ := hρ
  obtain ⟨d, hd⟩ := hσ
  have hcd : c = d := tendsto_nhds_unique
    (tendsto_sq_mul_of_principal hc) (tendsto_sq_mul_of_principal hd)
  subst d
  exact tendsto_nhds_unique hc hd

lemma HasResidueGen.add {f g : ℂ → ℂ} {w ρ σ : ℂ}
    (hf : HasResidueGen f w ρ) (hg : HasResidueGen g w σ) :
    HasResidueGen (fun z => f z + g z) w (ρ + σ) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c + d, (hc.add hd).congr' ?_⟩
  filter_upwards with z
  ring

lemma HasResidueGen.const_mul {f : ℂ → ℂ} {w ρ : ℂ}
    (hf : HasResidueGen f w ρ) (a : ℂ) :
    HasResidueGen (fun z => a * f z) w (a * ρ) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨a * c, (hc.const_mul a).congr' ?_⟩
  filter_upwards with z
  ring

lemma HasResidueGen.neg {f : ℂ → ℂ} {w ρ : ℂ} (hf : HasResidueGen f w ρ) :
    HasResidueGen (fun z => -f z) w (-ρ) := by
  simpa using hf.const_mul (-1)

lemma HasResidueGen.sub {f g : ℂ → ℂ} {w ρ σ : ℂ}
    (hf : HasResidueGen f w ρ) (hg : HasResidueGen g w σ) :
    HasResidueGen (fun z => f z - g z) w (ρ - σ) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The unique residue when a pole has order at most two, and zero otherwise.
Its value is used only at points where existence has been established. -/
def residueValue (f : ℂ → ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ ρ, HasResidueGen f w ρ then h.choose else 0

lemma residueValue_eq {f : ℂ → ℂ} {w ρ : ℂ} (h : HasResidueGen f w ρ) :
    residueValue f w = ρ := by
  have he : ∃ σ, HasResidueGen f w σ := ⟨ρ, h⟩
  rw [residueValue, dif_pos he]
  exact he.choose_spec.unique h

lemma hasResidueGen_residueValue {f : ℂ → ℂ} {w : ℂ}
    (h : ∃ ρ, HasResidueGen f w ρ) : HasResidueGen f w (residueValue f w) := by
  rw [residueValue, dif_pos h]
  exact h.choose_spec

lemma residueValue_of_continuousAt {f : ℂ → ℂ} {w : ℂ} (h : ContinuousAt f w) :
    residueValue f w = 0 := residueValue_eq (HasResidue.of_continuousAt h).hasResidueGen

lemma residueValue_add {f g : ℂ → ℂ} {w : ℂ}
    (hf : ∃ ρ, HasResidueGen f w ρ) (hg : ∃ ρ, HasResidueGen g w ρ) :
    residueValue (fun z => f z + g z) w = residueValue f w + residueValue g w :=
  residueValue_eq ((hasResidueGen_residueValue hf).add (hasResidueGen_residueValue hg))

lemma residueValue_const_mul {f : ℂ → ℂ} {w : ℂ}
    (hf : ∃ ρ, HasResidueGen f w ρ) (a : ℂ) :
    residueValue (fun z => a * f z) w = a * residueValue f w :=
  residueValue_eq ((hasResidueGen_residueValue hf).const_mul a)

namespace CorrectedContour

/-- A vertical line with crossed left poles added and crossed right poles
subtracted, using the intrinsic residue. -/
def value (f : ℂ → ℂ) (σ : ℝ) (SL SR : Finset ℂ) : ℂ :=
  lineIntegral f σ + 2 * Real.pi * I * ∑ w ∈ SL, residueValue f w -
    2 * Real.pi * I * ∑ w ∈ SR, residueValue f w

lemma lineIntegral_add {f g : ℂ → ℂ} (σ : ℝ)
    (hf : Integrable (fun t : ℝ => f (σ + t * I)))
    (hg : Integrable (fun t : ℝ => g (σ + t * I))) :
    lineIntegral (fun z => f z + g z) σ = lineIntegral f σ + lineIntegral g σ := by
  simp only [lineIntegral, add_mul]
  exact integral_add (hf.mul_const I) (hg.mul_const I)

lemma value_add {f g : ℂ → ℂ} (σ : ℝ) (SL SR : Finset ℂ)
    (hf : Integrable (fun t : ℝ => f (σ + t * I)))
    (hg : Integrable (fun t : ℝ => g (σ + t * I)))
    (hresf : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen f w ρ)
    (hresg : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen g w ρ) :
    value (fun z => f z + g z) σ SL SR = value f σ SL SR + value g σ SL SR := by
  have hsum (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S, residueValue (fun z => f z + g z) w) =
        (∑ w ∈ S, residueValue f w) + ∑ w ∈ S, residueValue g w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_add (hresf w (hS hw)) (hresg w (hS hw))
  rw [value, lineIntegral_add σ hf hg, hsum SL Finset.subset_union_left,
    hsum SR Finset.subset_union_right]
  unfold value
  ring

end CorrectedContour

end HaagerupIzumi
