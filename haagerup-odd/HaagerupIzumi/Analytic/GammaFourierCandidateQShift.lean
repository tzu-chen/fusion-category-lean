module

public import HaagerupIzumi.Analytic.GammaFourierCandidateShift
public import HaagerupIzumi.Analytic.GammaFourierShiftKernel
import all Mathlib.Data.Complex.Basic

/-!
# Shifting the gamma parameter of the Fourier candidate

The weighted difference of the two Fourier half-shifts is the candidate at
`q + A/2`, multiplied by the gamma shift factor at `2q`.
-/

@[expose] public section
noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

lemma weighted_midpoint_factor {B : ℝ} (hB : B ≠ 0) (q y : ℂ) :
    Complex.exp (Real.pi * I * q / B) * factor B ((B : ℂ) / 2 - q - I * y) -
      Complex.exp (-(Real.pi * I * q / B)) * factor B ((B : ℂ) / 2 - q + I * y) =
      I * Complex.exp (-(Real.pi * y / B)) * factor B (2 * q) := by
  have hp : Complex.exp (Real.pi * I * q / B) * Complex.exp (Real.pi * I * q / B) =
      Complex.exp (Real.pi * I * (2 * q) / B) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hn : Complex.exp (-(Real.pi * I * q / B)) * Complex.exp (-(Real.pi * I * q / B)) =
      Complex.exp (-(Real.pi * I * (2 * q) / B)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hy : Complex.exp (-(Real.pi * y / B)) * Complex.exp (-(Real.pi * y / B)) =
      Complex.exp (-2 * Real.pi * y / B) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-(Real.pi * y / B)))
  calc
    _ = Complex.exp (Real.pi * I * q / B) * fourierCoeffMinus B q y -
        Complex.exp (-(Real.pi * I * q / B)) * fourierCoeffPlus B q y := by
      rw [← exp_mul_factor_midpoint_minus hB, ← exp_mul_factor_midpoint_plus hB]
      ring
    _ = Complex.exp (-2 * Real.pi * y / B) *
        (Complex.exp (Real.pi * I * (2 * q) / B) - Complex.exp (-(Real.pi * I * (2 * q) / B))) := by
      rw [← hp, ← hn]
      unfold fourierCoeffMinus fourierCoeffPlus
      ring
    _ = _ := by
      rw [← I_mul_factor, ← hy]
      ring

lemma fourierCandidate_q_shift_of_shift {A B : ℝ} (hB : B ≠ 0) (g : ℂ → ℂ) (q y : ℂ)
    (hplus : g ((B : ℂ) / 2 - q + I * y + A) =
      factor B ((B : ℂ) / 2 - q + I * y) * g ((B : ℂ) / 2 - q + I * y))
    (hminus : g ((B : ℂ) / 2 - q - I * y + A) =
      factor B ((B : ℂ) / 2 - q - I * y) * g ((B : ℂ) / 2 - q - I * y)) :
    Complex.exp (Real.pi * I * q / B) * fourierCandidateOf g A B q (y + A * I / 2) -
      Complex.exp (-(Real.pi * I * q / B)) * fourierCandidateOf g A B q (y - A * I / 2) =
      I * Complex.exp (-(Real.pi * y / B)) * factor B (2 * q) *
        fourierCandidateOf g A B (q + A / 2) y := by
  have h₁ : ((A : ℂ) + B) / 2 - q + I * (y + A * I / 2) =
      (B : ℂ) / 2 - q + I * y := by ring_nf; simp [Complex.I_sq]
  have h₂ : ((A : ℂ) + B) / 2 - q - I * (y + A * I / 2) =
      (B : ℂ) / 2 - q - I * y + A := by ring_nf; simp [Complex.I_sq]; ring
  have h₃ : ((A : ℂ) + B) / 2 - q + I * (y - A * I / 2) =
      (B : ℂ) / 2 - q + I * y + A := by ring_nf; simp [Complex.I_sq]; ring
  have h₄ : ((A : ℂ) + B) / 2 - q - I * (y - A * I / 2) =
      (B : ℂ) / 2 - q - I * y := by ring_nf; simp [Complex.I_sq]
  have hn₁ : ((A : ℂ) + B) / 2 - (q + A / 2) + I * y =
      (B : ℂ) / 2 - q + I * y := by ring
  have hn₂ : ((A : ℂ) + B) / 2 - (q + A / 2) - I * y =
      (B : ℂ) / 2 - q - I * y := by ring
  simp only [fourierCandidateOf, h₁, h₂, h₃, h₄, hn₁, hn₂, hplus, hminus]
  calc
    _ = (Complex.exp (Real.pi * I * q / B) * factor B ((B : ℂ) / 2 - q - I * y) -
        Complex.exp (-(Real.pi * I * q / B)) * factor B ((B : ℂ) / 2 - q + I * y)) *
        (g ((B : ℂ) / 2 - q + I * y) * g ((B : ℂ) / 2 - q - I * y)) := by ring
    _ = _ := by rw [weighted_midpoint_factor hB]

theorem fourierCandidate_q_shift_first {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hconv : |y.im| < b / 2 - q.re) :
    Complex.exp (Real.pi * I * q / b) * fourierCandidate a b hb hba q (y + a * I / 2) -
      Complex.exp (-(Real.pi * I * q / b)) * fourierCandidate a b hb hba q (y - a * I / 2) =
      I * Complex.exp (-(Real.pi * y / b)) * factor b (2 * q) *
        fourierCandidate a b hb hba (q + a / 2) y := by
  have hh := midpoint_args_re_pos hconv
  exact fourierCandidate_q_shift_of_shift hb.ne' (gamma a b hb hba) q y
    (gamma_shift₁ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.1))
    (gamma_shift₁ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.2))

theorem fourierCandidate_q_shift_second {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hconv : |y.im| < a / 2 - q.re) :
    Complex.exp (Real.pi * I * q / a) * fourierCandidate a b hb hba q (y + b * I / 2) -
      Complex.exp (-(Real.pi * I * q / a)) * fourierCandidate a b hb hba q (y - b * I / 2) =
      I * Complex.exp (-(Real.pi * y / a)) * factor a (2 * q) *
        fourierCandidate a b hb hba (q + b / 2) y := by
  have hh := midpoint_args_re_pos hconv
  have heq := fourierCandidate_q_shift_of_shift (hb.trans_le hba).ne' (gamma a b hb hba) q y
    (gamma_shift₂ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.1))
    (gamma_shift₂ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.2))
  simpa only [fourierCandidateOf, fourierCandidate, add_comm] using heq

theorem normalizedCandidate_q_shift_first_of_not_mem {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hp : 2 * q ∉ poleLattice a b) (hconv : |y.im| < b / 2 - q.re) :
    Complex.exp (Real.pi * I * q / b) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y + a * I / 2)) -
      Complex.exp (-(Real.pi * I * q / b)) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y - a * I / 2)) =
      I * Complex.exp (-(Real.pi * y / b)) *
        (gamma a b hb hba (2 * (q + a / 2)) * fourierCandidate a b hb hba (q + a / 2) y) := by
  have hg := gamma_shift₁ a b hb hba (2 * q) hp
  have heq := congrArg (gamma a b hb hba (2 * q) * ·)
    (fourierCandidate_q_shift_first hb hba q y hconv)
  rw [show 2 * (q + (a : ℂ) / 2) = 2 * q + a by ring, hg]
  linear_combination heq

theorem normalizedCandidate_q_shift_second_of_not_mem {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hp : 2 * q ∉ poleLattice a b) (hconv : |y.im| < a / 2 - q.re) :
    Complex.exp (Real.pi * I * q / a) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y + b * I / 2)) -
      Complex.exp (-(Real.pi * I * q / a)) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y - b * I / 2)) =
      I * Complex.exp (-(Real.pi * y / a)) *
        (gamma a b hb hba (2 * (q + b / 2)) * fourierCandidate a b hb hba (q + b / 2) y) := by
  have hg := gamma_shift₂ a b hb hba (2 * q) hp
  have heq := congrArg (gamma a b hb hba (2 * q) * ·)
    (fourierCandidate_q_shift_second hb hba q y hconv)
  rw [show 2 * (q + (b : ℂ) / 2) = 2 * q + b by ring, hg]
  linear_combination heq

theorem normalizedCandidate_q_shift_first {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hq : 0 < q.re) (hconv : |y.im| < b / 2 - q.re) :
    Complex.exp (Real.pi * I * q / b) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y + a * I / 2)) -
      Complex.exp (-(Real.pi * I * q / b)) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y - a * I / 2)) =
      I * Complex.exp (-(Real.pi * y / b)) *
        (gamma a b hb hba (2 * (q + a / 2)) * fourierCandidate a b hb hba (q + a / 2) y) := by
  apply normalizedCandidate_q_shift_first_of_not_mem hb hba q y _ hconv
  exact not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb (by simp; linarith)

theorem normalizedCandidate_q_shift_second {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hq : 0 < q.re) (hconv : |y.im| < a / 2 - q.re) :
    Complex.exp (Real.pi * I * q / a) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y + b * I / 2)) -
      Complex.exp (-(Real.pi * I * q / a)) *
        (gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q (y - b * I / 2)) =
      I * Complex.exp (-(Real.pi * y / a)) *
        (gamma a b hb hba (2 * (q + b / 2)) * fourierCandidate a b hb hba (q + b / 2) y) := by
  apply normalizedCandidate_q_shift_second_of_not_mem hb hba q y _ hconv
  exact not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb (by simp; linarith)

lemma gamma_two_mul_ne_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q : ℂ} (hq : 0 < q.re) (hqup : q.re < (a + b) / 2) : gamma a b hb hba (2 * q) ≠ 0 := by
  have hlo : 0 < (2 * q).re := by simp; linarith
  have hhi : (2 * q).re < a + b := by simp; linarith
  rw [gamma_eq_on_strip a b hb hba _ hlo hhi]
  exact GammaIntegral.gamma_ne_zero a b _

lemma gamma_mul_fourierCandidate_ne_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {q y : ℂ} (hq : 0 < q.re) (hconv : |y.im| < (a + b) / 2 - q.re) :
    gamma a b hb hba (2 * q) * fourierCandidate a b hb hba q y ≠ 0 := by
  exact mul_ne_zero (gamma_two_mul_ne_zero hb hba hq (by linarith [abs_nonneg y.im]))
    (fourierCandidate_ne_zero hb hba hq hconv)

end HaagerupIzumi.GammaContinuation
