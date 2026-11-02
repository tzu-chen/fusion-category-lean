module

public import HaagerupIzumi.Analytic.GammaTwoContourLine
public import HaagerupIzumi.Analytic.GammaTwoFourierShifts
import all Mathlib.Data.Complex.Basic

/-!
# Gamma shifts on a common corrected two-gamma contour

Shifting either gamma parameter by the smaller period removes candidate
poles from that orientation. The removed candidates have zero residue, so
all terms in the pointwise shift identity can use the original contour.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaTwoFourier

lemma leftFamily_add_second_subset (a b : ℝ) (f : ℂ) :
    leftFamily a b (f + b) ⊆ leftFamily a b f := by
  intro z hz
  by_contra hz'
  apply not_mem_poleLattice_add_second hz'
  rw [show (f + z) + (b : ℂ) = (f + b) + z by ring]
  exact hz

lemma rightFamily_add_second_subset (a b : ℝ) (h : ℂ) :
    rightFamily a b (h + b) ⊆ rightFamily a b h := by
  intro z hz
  by_contra hz'
  apply not_mem_poleLattice_add_second hz'
  rw [show (h - z) + (b : ℂ) = (h + b) - z by ring]
  exact hz

lemma avoidsPoles_shift_first {a b : ℝ} {f h : ℂ} {σ : ℝ}
    (hσ : AvoidsPoles a b f h σ) : AvoidsPoles a b (f + b) h σ := by
  intro z hz
  rcases hz with hz | hz
  · exact hσ z (Or.inl (leftFamily_add_second_subset a b f hz))
  · exact hσ z (Or.inr hz)

lemma avoidsPoles_shift_second {a b : ℝ} {f h : ℂ} {σ : ℝ}
    (hσ : AvoidsPoles a b f h σ) : AvoidsPoles a b f (h + b) σ := by
  intro z hz
  rcases hz with hz | hz
  · exact hσ z (Or.inl hz)
  · exact hσ z (Or.inr (rightFamily_add_second_subset a b h hz))

lemma noPinch_shift_first {a b : ℝ} {f h : ℂ} (hnp : f + h ∉ poleLattice a b) :
    (f + b) + h ∉ poleLattice a b := by
  rw [show (f + (b : ℂ)) + h = (f + h) + b by ring]
  exact not_mem_poleLattice_add_second hnp

lemma noPinch_shift_second {a b : ℝ} {f h : ℂ} (hnp : f + h ∉ poleLattice a b) :
    f + (h + b) ∉ poleLattice a b := by
  rw [show f + (h + (b : ℂ)) = (f + h) + b by ring]
  exact not_mem_poleLattice_add_second hnp

lemma corrected_line_shift_first (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hc : |y.im| < (a + b - (f + (b : ℂ)).re - h.re) / 2)
    (hnp : f + h ∉ poleLattice a b) (σ : ℝ) (hσ : AvoidsPoles a b f h σ) :
    CorrectedContour.value (kernel a b hb hba (f + b) h y) σ
      (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
        I * correctedTransform a b hb hba (f + b) h y := by
  have hL : crossedLeft a b hb hba (f + b) σ ⊆ crossedLeft a b hb hba f σ := by
    intro z hz
    obtain ⟨hz, hσz⟩ := (mem_crossedLeft a b hb hba (f + b) σ z).mp hz
    exact (mem_crossedLeft a b hb hba f σ z).mpr
      ⟨leftFamily_add_second_subset a b f hz, hσz⟩
  have he := CorrectedContour.value_enlarge (kernel a b hb hba (f + b) h y) σ
    (crossedLeft a b hb hba (f + b) σ) (crossedRight a b hb hba h σ)
    (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) hL (fun _ hz => hz) ?_ ?_
  · exact he.symm.trans
      (correctedTransform_line a b hb hba hirr (f + b) h y hc (noPinch_shift_first hnp) σ
        (avoidsPoles_shift_first hσ)).2
  · intro z hz hz'
    obtain ⟨hzL, hσz⟩ := (mem_crossedLeft a b hb hba f σ z).mp hz
    apply kernel_residueValue_eq_zero a b hb hba (f + b) h y z
    intro hzP
    rcases hzP with hzP | hzP
    · exact hz' ((mem_crossedLeft a b hb hba (f + b) σ z).mpr ⟨hzP, hσz⟩)
    · exact Set.disjoint_left.mp (GammaK4Contour.families_disjoint hnp) hzL hzP
  · intro z hz hz'
    exact (hz' hz).elim

lemma corrected_line_shift_second (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ)
    (hc : |y.im| < (a + b - f.re - (h + (b : ℂ)).re) / 2)
    (hnp : f + h ∉ poleLattice a b) (σ : ℝ) (hσ : AvoidsPoles a b f h σ) :
    CorrectedContour.value (kernel a b hb hba f (h + b) y) σ
      (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
        I * correctedTransform a b hb hba f (h + b) y := by
  have hR : crossedRight a b hb hba (h + b) σ ⊆ crossedRight a b hb hba h σ := by
    intro z hz
    obtain ⟨hz, hzσ⟩ := (mem_crossedRight a b hb hba (h + b) σ z).mp hz
    exact (mem_crossedRight a b hb hba h σ z).mpr
      ⟨rightFamily_add_second_subset a b h hz, hzσ⟩
  have he := CorrectedContour.value_enlarge (kernel a b hb hba f (h + b) y) σ
    (crossedLeft a b hb hba f σ) (crossedRight a b hb hba (h + b) σ)
    (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) (fun _ hz => hz) hR ?_ ?_
  · exact he.symm.trans
      (correctedTransform_line a b hb hba hirr f (h + b) y hc (noPinch_shift_second hnp) σ
        (avoidsPoles_shift_second hσ)).2
  · intro z hz hz'
    exact (hz' hz).elim
  · intro z hz hz'
    obtain ⟨hzR, hzσ⟩ := (mem_crossedRight a b hb hba h σ z).mp hz
    apply kernel_residueValue_eq_zero a b hb hba f (h + b) y z
    intro hzP
    rcases hzP with hzP | hzP
    · exact Set.disjoint_left.mp (GammaK4Contour.families_disjoint hnp) hzP hzR
    · exact hz' ((mem_crossedRight a b hb hba (h + b) σ z).mpr ⟨hzP, hzσ⟩)

private lemma common_contour_three_term (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h : ℂ) (F G H : ℂ → ℂ) (c p q : ℂ) (σ : ℝ) (hσ : AvoidsPoles a b f h σ)
    (hG : Integrable (fun t : ℝ => G (σ + t * I)))
    (hH : Integrable (fun t : ℝ => H (σ + t * I)))
    (hFres : ∀ w, ∃ ρ, HasResidueGen F w ρ)
    (hGres : ∀ w, ∃ ρ, HasResidueGen G w ρ)
    (hHres : ∀ w, ∃ ρ, HasResidueGen H w ρ)
    (heq : ∀ z, z ∉ leftFamily a b f ∪ rightFamily a b h → c * F z = p * G z - q * H z) :
    c * CorrectedContour.value F σ (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) =
      p * CorrectedContour.value G σ (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) -
      q * CorrectedContour.value H σ (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) := by
  have hpres : ∀ w, ∃ ρ, HasResidueGen (fun z => p * G z) w ρ := by
    intro w
    obtain ⟨ρ, hρ⟩ := hGres w
    exact ⟨p * ρ, hρ.const_mul p⟩
  have hqres : ∀ w, ∃ ρ, HasResidueGen (fun z => q * H z) w ρ := by
    intro w
    obtain ⟨ρ, hρ⟩ := hHres w
    exact ⟨q * ρ, hρ.const_mul q⟩
  have hv := CorrectedContour.value_congr (f := fun z => c * F z)
    (g := fun z => p * G z - q * H z) σ
    (crossedLeft a b hb hba f σ) (crossedRight a b hb hba h σ) ?_ ?_
  · rw [CorrectedContour.value_const_mul c σ _ _ (fun w _ => hFres w),
      CorrectedContour.value_sub σ _ _ (hG.const_mul p) (hH.const_mul q)
        (fun w _ => hpres w) (fun w _ => hqres w),
      CorrectedContour.value_const_mul p σ _ _ (fun w _ => hGres w),
      CorrectedContour.value_const_mul q σ _ _ (fun w _ => hHres w)] at hv
    exact hv
  · intro t
    apply heq
    intro hz
    exact hσ (σ + t * I) hz (by simp)
  · intro w _
    filter_upwards [eventually_not_mem_families a b hb hba f h w] with z hz
    exact heq z hz

/-- The first-parameter smaller-period shift holds on the full corrected
contour, including when the sum of real gamma parameters is nonpositive. -/
theorem correctedTransform_shift_first (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ) (hnp : f + h ∉ poleLattice a b)
    (hc : |y.im| < (a + b - f.re - h.re - b) / 2) :
    I * correctedTransform a b hb hba (f + b) h y =
      Complex.exp (Real.pi * I * f / a) * correctedTransform a b hb hba f h (y + b * I / 2) -
      Complex.exp (-(Real.pi * I * f / a)) * correctedTransform a b hb hba f h (y - b * I / 2) := by
  let σ := startLine a b f h
  have hσ := startLine_avoidsPoles a b hb hba f h
  have hhalf := half_shift_convergence (a := a) (b := b) hb f h y hc
  have hp := correctedTransform_line a b hb hba hirr f h (y + b * I / 2) hhalf.1 hnp σ hσ
  have hm := correctedTransform_line a b hb hba hirr f h (y - b * I / 2) hhalf.2 hnp σ hσ
  have hhigh := corrected_line_shift_first a b hb hba hirr f h y
    (by simp only [add_re, ofReal_re]; linarith) hnp σ hσ
  have hv := common_contour_three_term a b hb hba f h
    (kernel a b hb hba (f + b) h y) (kernel a b hb hba f h (y + b * I / 2))
    (kernel a b hb hba f h (y - b * I / 2)) I
    (Complex.exp (Real.pi * I * f / a)) (Complex.exp (-(Real.pi * I * f / a))) σ hσ hp.1 hm.1
    (kernel_exists_hasResidueGen a b hb hba hirr (f + b) h y)
    (kernel_exists_hasResidueGen a b hb hba hirr f h (y + b * I / 2))
    (kernel_exists_hasResidueGen a b hb hba hirr f h (y - b * I / 2)) ?_
  · rw [hhigh, hp.2, hm.2] at hv
    apply mul_left_cancel₀ I_ne_zero
    linear_combination hv
  · intro z hz
    exact kernel_shift_first hb hba hb.ne' (lt_of_lt_of_le hb hba).ne' (by ring)
      (gamma_shift₂ a b hb hba) f h y z (fun h => hz (Or.inl h))

/-- The second-parameter smaller-period shift on the same corrected contour. -/
theorem correctedTransform_shift_second (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y : ℂ) (hnp : f + h ∉ poleLattice a b)
    (hc : |y.im| < (a + b - f.re - h.re - b) / 2) :
    I * correctedTransform a b hb hba f (h + b) y =
      Complex.exp (Real.pi * I * h / a) * correctedTransform a b hb hba f h (y - b * I / 2) -
      Complex.exp (-(Real.pi * I * h / a)) * correctedTransform a b hb hba f h (y + b * I / 2) := by
  let σ := startLine a b f h
  have hσ := startLine_avoidsPoles a b hb hba f h
  have hhalf := half_shift_convergence (a := a) (b := b) hb f h y hc
  have hp := correctedTransform_line a b hb hba hirr f h (y + b * I / 2) hhalf.1 hnp σ hσ
  have hm := correctedTransform_line a b hb hba hirr f h (y - b * I / 2) hhalf.2 hnp σ hσ
  have hhigh := corrected_line_shift_second a b hb hba hirr f h y
    (by simp only [add_re, ofReal_re]; linarith) hnp σ hσ
  have hv := common_contour_three_term a b hb hba f h
    (kernel a b hb hba f (h + b) y) (kernel a b hb hba f h (y - b * I / 2))
    (kernel a b hb hba f h (y + b * I / 2)) I
    (Complex.exp (Real.pi * I * h / a)) (Complex.exp (-(Real.pi * I * h / a))) σ hσ hm.1 hp.1
    (kernel_exists_hasResidueGen a b hb hba hirr f (h + b) y)
    (kernel_exists_hasResidueGen a b hb hba hirr f h (y - b * I / 2))
    (kernel_exists_hasResidueGen a b hb hba hirr f h (y + b * I / 2)) ?_
  · rw [hhigh, hm.2, hp.2] at hv
    apply mul_left_cancel₀ I_ne_zero
    linear_combination hv
  · intro z hz
    exact kernel_shift_second hb hba hb.ne' (lt_of_lt_of_le hb hba).ne' (by ring)
      (gamma_shift₂ a b hb hba) f h y z (fun h => hz (Or.inr h))

end HaagerupIzumi.GammaTwoFourier
