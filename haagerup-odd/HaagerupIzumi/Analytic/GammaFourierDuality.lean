module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaFourierInsertion

/-! # Four-gamma Fourier duality by an absolutely convergent insertion -/

@[expose] public section
noncomputable section

open Complex MeasureTheory

namespace HaagerupIzumi.GammaContinuation

def pairProductIntegrand (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (U V x y : ℂ) (t : ℝ) : ℂ :=
  symmetricIntegrand a b hb hba U (I * y) t * shiftedGammaPair a b hb hba V x t

lemma pairProduct_dual_factor (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (U V x y : ℂ) (u : ℝ) :
    symmetricIntegrand a b hb hba (complementaryParameter a b V) (-I * x) u *
      fourierCandidate a b hb hba U (u + I * y) =
        pairProductIntegrand a b hb hba (complementaryParameter a b V)
          (complementaryParameter a b U) y x (-u) := by
  unfold pairProductIntegrand symmetricIntegrand fourierCandidate fourierCandidateOf
    shiftedGammaPair complementaryParameter
  have he : 2 * (Real.pi : ℂ) * I * (-I * x) * u / ((a : ℂ) * b) =
      2 * Real.pi * I * (I * x) * (-u) / ((a : ℂ) * b) := by ring
  rw [he]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- Four-gamma duality in a tube where the insertion is absolutely
integrable in both variables. -/
theorem integral_pairProduct_duality {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {U V x y : ℂ}
    (hU : 0 < U.re) (_hUΩ : U.re < (a + b) / 2)
    (hV : 0 < V.re) (hVΩ : V.re < (a + b) / 2)
    (hx : |x.re| < V.re) (hy : |y.re| < (a + b) / 2 - U.re) :
    (∫ t : ℝ, pairProductIntegrand a b hb hba.le U V x y t) =
      gamma a b hb hba.le (2 * U) * gamma a b hb hba.le (2 * V) *
        ∫ t : ℝ, pairProductIntegrand a b hb hba.le
          (complementaryParameter a b V) (complementaryParameter a b U) y x t := by
  let f := symmetricIntegrand a b hb hba.le U (I * y)
  let g := symmetricIntegrand a b hb hba.le (complementaryParameter a b V) (-I * x)
  have hf : Integrable f := integrable_symmetricIntegrand hb hba hU (by simpa using hy)
  have hg : Integrable g := integrable_symmetricIntegrand hb hba
    (by rw [complementaryParameter_re]; linarith) (by
      simpa [complementaryParameter_re] using hx)
  have hswap := FourierInsertion.integral_mul_integral_phase hf hg (2 * Real.pi / (a * b))
  have hinner₁ (t : ℝ) :
      (∫ u : ℝ, FourierInsertion.phase (2 * Real.pi / (a * b)) t u * g u) =
        symmetricTransform a b hb hba.le (complementaryParameter a b V) (t - I * x) := by
    apply integral_congr_ae
    filter_upwards [] with u
    exact (symmetricIntegrand_inverse_factor a b hb hba.le _ x t u).symm
  have hinner₂ (u : ℝ) :
      (∫ t : ℝ, FourierInsertion.phase (2 * Real.pi / (a * b)) t u * f t) =
        symmetricTransform a b hb hba.le U (u + I * y) := by
    apply integral_congr_ae
    filter_upwards [] with t
    exact phase_mul_symmetricIntegrand a b hb hba.le U (I * y) t u
  simp_rw [hinner₁, hinner₂] at hswap
  have heval (u : ℝ) : symmetricTransform a b hb hba.le U (u + I * y) =
      (Real.sqrt (a * b) : ℂ) * gamma a b hb hba.le (2 * U) *
        fourierCandidate a b hb hba.le U (u + I * y) :=
    symmetricTransform_evaluation hb hba hirr hU (by simpa using hy)
  have hs : (Real.sqrt (a * b) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (hb.trans hba) hb)).ne'
  apply mul_left_cancel₀ hs
  calc
    _ = gamma a b hb hba.le (2 * V) *
        (∫ t : ℝ, f t * symmetricTransform a b hb hba.le
          (complementaryParameter a b V) (t - I * x)) := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      have ht := shiftedGammaPair_eq_transform hb hba hirr hV hVΩ hx t
      change (Real.sqrt (a * b) : ℂ) * (f t * shiftedGammaPair a b hb hba.le V x t) = _
      linear_combination f t * ht
    _ = gamma a b hb hba.le (2 * V) *
        (∫ u : ℝ, g u * symmetricTransform a b hb hba.le U (u + I * y)) := by rw [hswap]
    _ = (Real.sqrt (a * b) : ℂ) *
        (gamma a b hb hba.le (2 * U) * gamma a b hb hba.le (2 * V) *
          ∫ u : ℝ, pairProductIntegrand a b hb hba.le
            (complementaryParameter a b V) (complementaryParameter a b U) y x (-u)) := by
      simp_rw [heval]
      rw [show (fun u : ℝ => g u * ((Real.sqrt (a * b) : ℂ) *
          gamma a b hb hba.le (2 * U) * fourierCandidate a b hb hba.le U (u + I * y))) =
          (fun u : ℝ => ((Real.sqrt (a * b) : ℂ) * gamma a b hb hba.le (2 * U)) *
            pairProductIntegrand a b hb hba.le (complementaryParameter a b V)
              (complementaryParameter a b U) y x (-u)) by
        funext u
        rw [← pairProduct_dual_factor]
        dsimp only [g]
        ring, integral_const_mul]
      ring
    _ = _ := by rw [integral_neg_eq_self]

end HaagerupIzumi.GammaContinuation
