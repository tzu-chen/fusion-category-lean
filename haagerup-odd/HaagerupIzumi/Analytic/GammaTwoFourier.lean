module

public import HaagerupIzumi.Analytic.GammaKernelDecay
public import HaagerupIzumi.Analytic.GammaLocalFactors
public import HaagerupIzumi.Analytic.GammaFourierBounds
public import HaagerupIzumi.Analytic.ContourAffine
import all Mathlib.Data.Complex.Basic

/-!
# The asymmetric two-gamma Fourier integral

The kernel uses `exp(2π y z/(ab))`; on `z = it` this is the usual Fourier
multiplier `exp(2π i y t/(ab))`. Moving the line through a strip with positive
real parts in both gamma arguments gives the real-shift transport identity.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

def kernel (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * y * z / ((a : ℂ) * b)) *
    gamma a b hb hba (f + z) * gamma a b hb hba (h - z)

def transform (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) : ℂ :=
  ∫ t : ℝ, kernel a b hb hba f h y (t * I)

lemma transform_diag_eq_symmetricTransform (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (q y : ℂ) :
    transform a b hb hba q q y = symmetricTransform a b hb hba q y := by
  unfold transform symmetricTransform kernel symmetricIntegrand
  apply integral_congr_ae
  filter_upwards with t
  have he : 2 * (Real.pi : ℂ) * y * (t * I) / ((a : ℂ) * b) =
      2 * Real.pi * I * y * t / ((a : ℂ) * b) := by ring
  rw [he]

lemma kernel_differentiableAt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h y z : ℂ) (hf : 0 < (f + z).re) (hh : 0 < (h - z).re) :
    DifferentiableAt ℂ (kernel a b hb hba f h y) z := by
  have hg₁ := gamma_differentiableAt_add a b hb hba f z
    (not_mem_poleLattice_of_re_pos (lt_of_lt_of_le hb hba) hb hf)
  have hg₂ := gamma_differentiableAt_sub a b hb hba h z
    (not_mem_poleLattice_of_re_pos (lt_of_lt_of_le hb hba) hb hh)
  have he : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (2 * Real.pi * y * w / ((a : ℂ) * b))) z := by fun_prop
  exact (he.mul hg₁).mul hg₂

lemma kernel_tail_bound (a b : ℝ) (hb : 0 < b) (hba : b < a) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (L U : ℝ) :
    ∃ M c T : ℝ, 0 < M ∧ 0 < c ∧ 0 < T ∧ ∀ z : ℂ,
      L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖kernel a b hb hba.le f h y z‖ ≤ M * Real.exp (-c * |z.im|) := by
  let lam : ℂ := 2 * Real.pi * y / ((a : ℂ) * b)
  let c : ℝ := Real.pi * (a + b - f.re - h.re - 2 * |y.im|) / (a * b)
  have hab : 0 < a * b := mul_pos (hb.trans hba) hb
  have hc : 0 < c := by
    apply div_pos _ hab
    apply mul_pos Real.pi_pos
    linarith
  have hlam : |lam.im| = 2 * Real.pi * |y.im| / (a * b) := by
    have him : lam.im = 2 * Real.pi * y.im / (a * b) := by
      simp [lam, ← Complex.ofReal_mul]
    rw [him, abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
      abs_of_pos hab]
  have hrate : |lam.im| + Real.pi * (f.re + h.re - (a + b)) / (a * b) = -c := by
    rw [hlam]
    unfold c
    ring
  obtain ⟨M, T, hM, hT, hbound⟩ := two_gamma_kernel_bound hb hba f h lam L U
  refine ⟨M, c, T, hM, hc, hT, ?_⟩
  intro z hL hU hTz
  have hz := hbound z hL hU hTz
  rw [hrate] at hz
  unfold kernel
  rw [show 2 * (Real.pi : ℂ) * y * z / ((a : ℂ) * b) = lam * z by dsimp [lam]; ring]
  exact hz

/-- Cauchy's theorem on a strip where both gamma arguments have positive
real part. Exponential decay removes the two horizontal ends. -/
lemma kernel_strip_integrals (a b : ℝ) (hb : 0 < b) (hba : b < a) (f h y : ℂ)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) (L U : ℝ) (hLU : L < U)
    (hf : 0 < f.re + L) (hh : U < h.re) :
    Integrable (fun t : ℝ => kernel a b hb hba.le f h y (L + t * I)) ∧
    Integrable (fun t : ℝ => kernel a b hb hba.le f h y (U + t * I)) ∧
    lineIntegral (kernel a b hb hba.le f h y) U =
      lineIntegral (kernel a b hb hba.le f h y) L := by
  obtain ⟨M, c, T, _, hc, hT, hbound⟩ := kernel_tail_bound a b hb hba f h y hconv L U
  have hd : ∀ z : ℂ, L ≤ z.re → z.re ≤ U → z ∉ (∅ : Finset ℂ) →
      DifferentiableAt ℂ (kernel a b hb hba.le f h y) z := by
    intro z hzL hzU _
    apply kernel_differentiableAt a b hb hba.le f h y z
    · simp only [add_re]; linarith
    · simp only [sub_re]; linarith
  have h := strip_residues (kernel a b hb hba.le f h y) L U hLU ∅ T hT
    (by simp) (fun _ => 0) (by simp) hd M c hc hbound
  refine ⟨h.1, h.2.1, ?_⟩
  have he := h.2.2
  simpa only [Finset.sum_empty, mul_zero, sub_eq_zero] using he

lemma integrable_zero_line (a b : ℝ) (hb : 0 < b) (hba : b < a) (f h y : ℂ)
    (hf : 0 < f.re) (hh : 0 < h.re)
    (hconv : |y.im| < (a + b - f.re - h.re) / 2) :
    Integrable (fun t : ℝ => kernel a b hb hba.le f h y (t * I)) := by
  have ht := (kernel_strip_integrals a b hb hba f h y hconv 0 (h.re / 2)
    (by positivity) (by simpa using hf) (by linarith)).1
  simpa only [Complex.ofReal_zero, zero_add] using ht

lemma lineIntegral_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) :
    lineIntegral (kernel a b hb hba f h y) 0 = transform a b hb hba f h y * I := by
  simp only [lineIntegral, Complex.ofReal_zero, zero_add, transform, integral_mul_const]

lemma kernel_shift_real (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h y : ℂ) (A : ℝ) :
    kernel a b hb hba (f + A) h y = fun z =>
      Complex.exp (-2 * Real.pi * A * y / ((a : ℂ) * b)) *
        kernel a b hb hba f (h + A) y ((A : ℂ) + z) := by
  funext z
  unfold kernel
  have h₁ : f + ((A : ℂ) + z) = (f + A) + z := by ring
  have h₂ : (h + (A : ℂ)) - ((A : ℂ) + z) = h - z := by ring
  rw [h₁, h₂, ← mul_assoc, ← mul_assoc, ← Complex.exp_add]
  have he : 2 * (Real.pi : ℂ) * y * z / ((a : ℂ) * b) =
      -2 * Real.pi * A * y / ((a : ℂ) * b) +
        2 * Real.pi * y * ((A : ℂ) + z) / ((a : ℂ) * b) := by ring
  rw [he]

/-- Transfer a positive real increment from the first gamma parameter to the
second. The intervening vertical strip contains no poles. -/
theorem transform_shift_real (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (f h y : ℂ) (A : ℝ) (hA : 0 < A) (hf : 0 < f.re) (hh : 0 < h.re)
    (hconv : |y.im| < (a + b - f.re - h.re - A) / 2) :
    transform a b hb hba.le (f + A) h y =
      Complex.exp (-2 * Real.pi * A * y / ((a : ℂ) * b)) *
        transform a b hb hba.le f (h + A) y := by
  have hc : |y.im| < (a + b - f.re - (h + (A : ℂ)).re) / 2 := by
    simp only [add_re, ofReal_re]
    linarith
  have hstrip := (kernel_strip_integrals a b hb hba f (h + A) y hc 0 A hA
    (by simpa using hf) (by simp; linarith)).2.2
  have hline : lineIntegral (kernel a b hb hba.le (f + A) h y) 0 =
      Complex.exp (-2 * Real.pi * A * y / ((a : ℂ) * b)) *
        lineIntegral (kernel a b hb hba.le f (h + A) y) 0 := by
    rw [kernel_shift_real, CorrectedContour.lineIntegral_const_mul,
      CorrectedContour.lineIntegral_comp_const_add]
    simp only [ofReal_re, zero_add]
    rw [hstrip]
  rw [lineIntegral_zero, lineIntegral_zero] at hline
  apply mul_right_cancel₀ I_ne_zero
  simpa only [mul_assoc] using hline

end HaagerupIzumi.GammaTwoFourier
