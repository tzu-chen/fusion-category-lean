module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.ContourAffine

/-!
# Linearity on a common corrected contour

A pointwise identity away from isolated poles induces the same identity of
corrected contour values. Extra candidate poles contribute zero whenever
the corresponding function is regular there.
-/

@[expose] public section

noncomputable section

open Complex Filter Set Topology MeasureTheory

namespace HaagerupIzumi

lemma HasResidueGen.congr_eventually {f g : ℂ → ℂ} {w ρ : ℂ}
    (hf : HasResidueGen f w ρ) (hfg : f =ᶠ[𝓝[≠] w] g) : HasResidueGen g w ρ := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, hc.congr' ?_⟩
  exact hfg.mono fun z hz => by dsimp only; rw [hz]

lemma residueValue_congr_eventually {f g : ℂ → ℂ} {w : ℂ}
    (hfg : f =ᶠ[𝓝[≠] w] g) : residueValue f w = residueValue g w := by
  classical
  by_cases hf : ∃ ρ, HasResidueGen f w ρ
  · exact (residueValue_eq ((hasResidueGen_residueValue hf).congr_eventually hfg)).symm
  · have hg : ¬∃ ρ, HasResidueGen g w ρ := by
      rintro ⟨ρ, hρ⟩
      exact hf ⟨ρ, hρ.congr_eventually hfg.symm⟩
    simp only [residueValue, dif_neg hf, dif_neg hg]

lemma residueValue_sub {f g : ℂ → ℂ} {w : ℂ}
    (hf : ∃ ρ, HasResidueGen f w ρ) (hg : ∃ ρ, HasResidueGen g w ρ) :
    residueValue (fun z => f z - g z) w = residueValue f w - residueValue g w :=
  residueValue_eq ((hasResidueGen_residueValue hf).sub (hasResidueGen_residueValue hg))

lemma hasResidueGen_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (ρ : ι → ℂ) (w : ℂ) (hf : ∀ i ∈ S, HasResidueGen (f i) w (ρ i)) :
    HasResidueGen (fun z => ∑ i ∈ S, f i z) w (∑ i ∈ S, ρ i) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty] using
      (HasResidue.of_continuousAt (continuousAt_const (y := (0 : ℂ)))).hasResidueGen
  | @insert i S hi ih =>
    intro hf
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma residueValue_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (w : ℂ)
    (hf : ∀ i ∈ S, ∃ ρ, HasResidueGen (f i) w ρ) :
    residueValue (fun z => ∑ i ∈ S, f i z) w = ∑ i ∈ S, residueValue (f i) w :=
  residueValue_eq (hasResidueGen_finsetSum S f (fun i => residueValue (f i) w) w
    (fun i hi => hasResidueGen_residueValue (hf i hi)))

namespace CorrectedContour

/-- Equality along the line and on each residue germ suffices; arbitrary
total values at poles do not enter corrected contour integrals. -/
lemma value_congr {f g : ℂ → ℂ} (σ : ℝ) (SL SR : Finset ℂ)
    (hline : ∀ t : ℝ, f (σ + t * I) = g (σ + t * I))
    (hres : ∀ w ∈ SL ∪ SR, f =ᶠ[𝓝[≠] w] g) : value f σ SL SR = value g σ SL SR := by
  have hl : lineIntegral f σ = lineIntegral g σ := by
    unfold lineIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by dsimp only; rw [hline t]
  have hs (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S, residueValue f w) = ∑ w ∈ S, residueValue g w := by
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_congr_eventually (hres w (hS hw))
  rw [value, hl, hs SL Finset.subset_union_left, hs SR Finset.subset_union_right]
  rfl

/-- A contour can be enlarged to a common finite candidate set, provided
the added candidates have zero residue for this function. -/
lemma value_enlarge (f : ℂ → ℂ) (σ : ℝ) (SL SR TL TR : Finset ℂ)
    (hL : SL ⊆ TL) (hR : SR ⊆ TR)
    (hzL : ∀ w ∈ TL, w ∉ SL → residueValue f w = 0)
    (hzR : ∀ w ∈ TR, w ∉ SR → residueValue f w = 0) :
    value f σ SL SR = value f σ TL TR := by
  unfold value
  rw [Finset.sum_subset hL hzL, Finset.sum_subset hR hzR]

lemma value_sub {f g : ℂ → ℂ} (σ : ℝ) (SL SR : Finset ℂ)
    (hf : Integrable (fun t : ℝ => f (σ + t * I)))
    (hg : Integrable (fun t : ℝ => g (σ + t * I)))
    (hresf : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen f w ρ)
    (hresg : ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen g w ρ) :
    value (fun z => f z - g z) σ SL SR = value f σ SL SR - value g σ SL SR := by
  have hl : lineIntegral (fun z => f z - g z) σ = lineIntegral f σ - lineIntegral g σ := by
    simp only [lineIntegral, sub_mul]
    exact integral_sub (hf.mul_const I) (hg.mul_const I)
  have hs (S : Finset ℂ) (hS : S ⊆ SL ∪ SR) :
      (∑ w ∈ S, residueValue (fun z => f z - g z) w) =
        (∑ w ∈ S, residueValue f w) - ∑ w ∈ S, residueValue g w := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    exact residueValue_sub (hresf w (hS hw)) (hresg w (hS hw))
  rw [value, hl, hs SL Finset.subset_union_left, hs SR Finset.subset_union_right]
  unfold value
  ring

lemma lineIntegral_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (σ : ℝ)
    (hf : ∀ i ∈ S, Integrable (fun t : ℝ => f i (σ + t * I))) :
    lineIntegral (fun z => ∑ i ∈ S, f i z) σ = ∑ i ∈ S, lineIntegral (f i) σ := by
  simp only [lineIntegral, Finset.sum_mul]
  exact integral_finsetSum S (fun i hi => (hf i hi).mul_const I)

lemma value_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (σ : ℝ) (SL SR : Finset ℂ)
    (hf : ∀ i ∈ S, Integrable (fun t : ℝ => f i (σ + t * I)))
    (hres : ∀ i ∈ S, ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen (f i) w ρ) :
    value (fun z => ∑ i ∈ S, f i z) σ SL SR = ∑ i ∈ S, value (f i) σ SL SR := by
  have hs (T : Finset ℂ) (hT : T ⊆ SL ∪ SR) :
      (∑ w ∈ T, residueValue (fun z => ∑ i ∈ S, f i z) w) =
        ∑ i ∈ S, ∑ w ∈ T, residueValue (f i) w := by
    calc
      _ = ∑ w ∈ T, ∑ i ∈ S, residueValue (f i) w := by
        apply Finset.sum_congr rfl
        intro w hw
        exact residueValue_finsetSum S f w (fun i hi => hres i hi w (hT hw))
      _ = _ := Finset.sum_comm
  rw [value, lineIntegral_finsetSum S f σ hf,
    hs SL Finset.subset_union_left, hs SR Finset.subset_union_right]
  simp only [value, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma value_linearCombination {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (c : ι → ℂ) (σ : ℝ) (SL SR : Finset ℂ)
    (hf : ∀ i ∈ S, Integrable (fun t : ℝ => f i (σ + t * I)))
    (hres : ∀ i ∈ S, ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen (f i) w ρ) :
    value (fun z => ∑ i ∈ S, c i * f i z) σ SL SR =
      ∑ i ∈ S, c i * value (f i) σ SL SR := by
  have hres' : ∀ i ∈ S, ∀ w ∈ SL ∪ SR, ∃ ρ, HasResidueGen (fun z => c i * f i z) w ρ := by
    intro i hi w hw
    obtain ⟨ρ, hρ⟩ := hres i hi w hw
    exact ⟨c i * ρ, hρ.const_mul (c i)⟩
  rw [value_finsetSum S (fun i z => c i * f i z) σ SL SR
    (fun i hi => (hf i hi).const_mul (c i)) hres']
  apply Finset.sum_congr rfl
  intro i hi
  exact value_const_mul (c i) σ SL SR (hres i hi)

end CorrectedContour
end HaagerupIzumi
