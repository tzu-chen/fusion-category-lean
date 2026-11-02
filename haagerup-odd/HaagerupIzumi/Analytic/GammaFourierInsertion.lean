module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.FourierInsertion
public import HaagerupIzumi.Analytic.GammaFourierEvaluation

/-! # Inserting the complementary hyperbolic-gamma Fourier transform -/

@[expose] public section
noncomputable section

open Complex MeasureTheory

namespace HaagerupIzumi.GammaContinuation

def complementaryParameter (a b : ℝ) (q : ℂ) : ℂ := ((a : ℂ) + b) / 2 - q

def shiftedGammaPair (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (q x : ℂ) (t : ℝ) : ℂ :=
  gamma a b hb hba (q + x + t * I) * gamma a b hb hba (q - x - t * I)

lemma complementaryParameter_re (a b : ℝ) (q : ℂ) :
    (complementaryParameter a b q).re = (a + b) / 2 - q.re := by
  simp [complementaryParameter]

lemma gamma_two_mul_reflection {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (hqΩ : q.re < (a + b) / 2) :
    gamma a b hb hba (2 * q) *
      gamma a b hb hba (2 * complementaryParameter a b q) = 1 := by
  have hp : 2 * q ∉ poleLattice a b :=
    not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb (by simp; linarith)
  have hz : 2 * q ∉ zeroLattice a b :=
    not_mem_zeroLattice_of_re_lt (hb.trans_le hba) hb (by simp; linarith)
  convert gamma_reflection a b hb hba (2 * q) hp hz using 1 <;>
    congr 1 <;> unfold complementaryParameter <;> ring

/-- An inverse representation obtained from the direct Fourier formula at
the complementary gamma parameter and the reflection equation. -/
theorem shiftedGammaPair_eq_transform {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {q x : ℂ}
    (hq : 0 < q.re) (hqΩ : q.re < (a + b) / 2) (hx : |x.re| < q.re) (t : ℝ) :
    (Real.sqrt (a * b) : ℂ) * shiftedGammaPair a b hb hba.le q x t =
      gamma a b hb hba.le (2 * q) *
        symmetricTransform a b hb hba.le (complementaryParameter a b q) (t - I * x) := by
  have hp : 0 < (complementaryParameter a b q).re := by
    rw [complementaryParameter_re]; linarith
  have ht : |((t : ℂ) - I * x).im| <
      (a + b) / 2 - (complementaryParameter a b q).re := by
    simpa [complementaryParameter_re] using hx
  rw [symmetricTransform_evaluation hb hba hirr hp ht]
  have hc : fourierCandidate a b hb hba.le (complementaryParameter a b q) (t - I * x) =
      shiftedGammaPair a b hb hba.le q x t := by
    unfold fourierCandidate fourierCandidateOf complementaryParameter shiftedGammaPair
    congr 1 <;> congr 1 <;> ring_nf <;> simp only [I_sq] <;> ring
  rw [hc, show gamma a b hb hba.le (2 * q) *
      ((Real.sqrt (a * b) : ℂ) * gamma a b hb hba.le (2 * complementaryParameter a b q) *
        shiftedGammaPair a b hb hba.le q x t) =
      (Real.sqrt (a * b) : ℂ) *
        (gamma a b hb hba.le (2 * q) *
          gamma a b hb hba.le (2 * complementaryParameter a b q)) *
        shiftedGammaPair a b hb hba.le q x t by ring,
    gamma_two_mul_reflection hb hba.le hq hqΩ, mul_one]

lemma phase_mul_symmetricIntegrand (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (t u : ℝ) :
    FourierInsertion.phase (2 * Real.pi / (a * b)) t u *
      symmetricIntegrand a b hb hba q y t =
        symmetricIntegrand a b hb hba q (u + y) t := by
  unfold FourierInsertion.phase symmetricIntegrand
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma symmetricIntegrand_inverse_factor (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (q x : ℂ) (t u : ℝ) :
    symmetricIntegrand a b hb hba q (t - I * x) u =
      FourierInsertion.phase (2 * Real.pi / (a * b)) t u *
        symmetricIntegrand a b hb hba q (-I * x) u := by
  rw [show FourierInsertion.phase (2 * Real.pi / (a * b)) t u =
      FourierInsertion.phase (2 * Real.pi / (a * b)) u t by
    simp only [FourierInsertion.phase]; congr 1; push_cast; ring,
    phase_mul_symmetricIntegrand]
  congr 1
  ring

end HaagerupIzumi.GammaContinuation
