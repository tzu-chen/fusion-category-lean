module

public import HaagerupIzumi.Analytic.GammaFourierCandidate
public import HaagerupIzumi.Analytic.GammaIdentities
import all Mathlib.Data.Complex.Basic

/-!
# Half-period recurrences for the Fourier product candidate

The two shifted products share the same unshifted gamma pair. Their remaining
sine multipliers give the exponential coefficients of the Fourier recurrence.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

def fourierCoeffPlus (B : ℝ) (q y : ℂ) : ℂ :=
  Complex.exp (Real.pi * I * q / B) +
    Complex.exp (-2 * Real.pi * y / B) * Complex.exp (-(Real.pi * I * q / B))

def fourierCoeffMinus (B : ℝ) (q y : ℂ) : ℂ :=
  Complex.exp (-(Real.pi * I * q / B)) +
    Complex.exp (-2 * Real.pi * y / B) * Complex.exp (Real.pi * I * q / B)

lemma exp_mul_factor_midpoint_plus {B : ℝ} (hB : B ≠ 0) (q y : ℂ) :
    Complex.exp (-(Real.pi * y / B)) * factor B ((B : ℂ) / 2 - q + I * y) =
      fourierCoeffPlus B q y := by
  have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  have harg : Real.pi * ((B : ℂ) / 2 - q + I * y) / B =
      (Real.pi : ℂ) / 2 - Real.pi * (q - I * y) / B := by
    field_simp
    ring
  unfold factor
  rw [harg, Complex.sin_pi_div_two_sub, Complex.two_cos, mul_add,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold fourierCoeffPlus
  rw [← Complex.exp_add]
  congr 1 <;> congr 1 <;> ring_nf <;> simp [Complex.I_sq]
  ring

lemma exp_mul_factor_midpoint_minus {B : ℝ} (hB : B ≠ 0) (q y : ℂ) :
    Complex.exp (-(Real.pi * y / B)) * factor B ((B : ℂ) / 2 - q - I * y) =
      fourierCoeffMinus B q y := by
  have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  have harg : Real.pi * ((B : ℂ) / 2 - q - I * y) / B =
      (Real.pi : ℂ) / 2 - Real.pi * (q + I * y) / B := by
    field_simp
    ring
  unfold factor
  rw [harg, Complex.sin_pi_div_two_sub, Complex.two_cos, mul_add,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold fourierCoeffMinus
  rw [← Complex.exp_add, add_comm]
  congr 1 <;> congr 1 <;> ring_nf <;> simp [Complex.I_sq]
  ring

lemma fourierCandidateOf_swap (g : ℂ → ℂ) (a b : ℝ) (q y : ℂ) :
    fourierCandidateOf g b a q y = fourierCandidateOf g a b q y := by
  simp only [fourierCandidateOf, add_comm]

/-- Pure shift algebra, independent of any analytic construction. -/
lemma fourierCandidate_shift_of_shift {A B : ℝ} (hB : B ≠ 0) (g : ℂ → ℂ) (q y : ℂ)
    (hplus : g ((B : ℂ) / 2 - q + I * y + A) =
      factor B ((B : ℂ) / 2 - q + I * y) * g ((B : ℂ) / 2 - q + I * y))
    (hminus : g ((B : ℂ) / 2 - q - I * y + A) =
      factor B ((B : ℂ) / 2 - q - I * y) * g ((B : ℂ) / 2 - q - I * y)) :
    fourierCoeffPlus B q y * fourierCandidateOf g A B q (y + A * I / 2) =
      fourierCoeffMinus B q y * fourierCandidateOf g A B q (y - A * I / 2) := by
  have h₁ : ((A : ℂ) + B) / 2 - q + I * (y + A * I / 2) =
      (B : ℂ) / 2 - q + I * y := by ring_nf; simp [Complex.I_sq]
  have h₂ : ((A : ℂ) + B) / 2 - q - I * (y + A * I / 2) =
      (B : ℂ) / 2 - q - I * y + A := by ring_nf; simp [Complex.I_sq]; ring
  have h₃ : ((A : ℂ) + B) / 2 - q + I * (y - A * I / 2) =
      (B : ℂ) / 2 - q + I * y + A := by ring_nf; simp [Complex.I_sq]; ring
  have h₄ : ((A : ℂ) + B) / 2 - q - I * (y - A * I / 2) =
      (B : ℂ) / 2 - q - I * y := by ring_nf; simp [Complex.I_sq]
  rw [fourierCandidateOf, fourierCandidateOf, h₁, h₂, h₃, h₄, hplus, hminus,
    ← exp_mul_factor_midpoint_plus hB, ← exp_mul_factor_midpoint_minus hB]
  ring

lemma midpoint_args_re_pos {B : ℝ} {q y : ℂ} (hconv : |y.im| < B / 2 - q.re) :
    0 < ((B : ℂ) / 2 - q + I * y).re ∧ 0 < ((B : ℂ) / 2 - q - I * y).re := by
  simp only [add_re, sub_re, div_ofNat_re, ofReal_re, I_mul_re]
  have hh := abs_lt.mp hconv
  constructor <;> linarith

lemma fourierCoeffPlus_ne_zero {B : ℝ} (hB : 0 < B) {q y : ℂ}
    (hq : 0 < q.re) (hconv : |y.im| < B / 2 - q.re) : fourierCoeffPlus B q y ≠ 0 := by
  rw [← exp_mul_factor_midpoint_plus hB.ne']
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply factor_ne_zero_on_strip hB _ (midpoint_args_re_pos hconv).1
  simp only [add_re, sub_re, div_ofNat_re, ofReal_re, I_mul_re]
  linarith [(abs_lt.mp hconv).1]

lemma fourierCoeffMinus_ne_zero {B : ℝ} (hB : 0 < B) {q y : ℂ}
    (hq : 0 < q.re) (hconv : |y.im| < B / 2 - q.re) : fourierCoeffMinus B q y ≠ 0 := by
  rw [← exp_mul_factor_midpoint_minus hB.ne']
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply factor_ne_zero_on_strip hB _ (midpoint_args_re_pos hconv).2
  simp only [sub_re, div_ofNat_re, ofReal_re, I_mul_re]
  linarith [(abs_lt.mp hconv).2]

theorem fourierCandidate_shift_first {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hconv : |y.im| < b / 2 - q.re) :
    fourierCoeffPlus b q y * fourierCandidate a b hb hba q (y + a * I / 2) =
      fourierCoeffMinus b q y * fourierCandidate a b hb hba q (y - a * I / 2) := by
  have hh := midpoint_args_re_pos hconv
  exact fourierCandidate_shift_of_shift hb.ne' (gamma a b hb hba) q y
    (gamma_shift₁ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.1))
    (gamma_shift₁ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.2))

theorem fourierCandidate_shift_second {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) (hconv : |y.im| < a / 2 - q.re) :
    fourierCoeffPlus a q y * fourierCandidate a b hb hba q (y + b * I / 2) =
      fourierCoeffMinus a q y * fourierCandidate a b hb hba q (y - b * I / 2) := by
  have hh := midpoint_args_re_pos hconv
  have heq := fourierCandidate_shift_of_shift (hb.trans_le hba).ne' (gamma a b hb hba) q y
    (gamma_shift₂ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.1))
    (gamma_shift₂ a b hb hba _ (not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb hh.2))
  simpa only [fourierCandidateOf, fourierCandidate, add_comm] using heq

end HaagerupIzumi.GammaContinuation
