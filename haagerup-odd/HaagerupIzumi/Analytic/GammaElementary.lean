module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

/-!
# Elementary integral identities for the hyperbolic gamma function

The shift of the logarithmic integral reduces to a one-period hyperbolic
integral. The paired cotangent expansion below has the indexing obtained
by expanding the reciprocal hyperbolic sine as a geometric series.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace HaagerupIzumi
namespace GammaElementary

/-- Finite paired partial fractions differ from the standard cotangent
partial sums by a single boundary term. -/
lemma sum_paired_reciprocals (z : ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / (z + j) - 1 / ((j : ℂ) + 1 - z))) =
      1 / z + ∑ j ∈ Finset.range n, cotTerm z j - 1 / (z + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hneg : (n : ℂ) + 1 - z = -(z - (n + 1)) := by ring
      have hfrac : 1 / ((n : ℂ) + 1 - z) = -(1 / (z - (n + 1))) := by
        rw [hneg, div_neg]
      simp only [cotTerm, Nat.cast_add, Nat.cast_one]
      rw [hfrac]
      ring

/-- The paired form of the Mittag-Leffler expansion needed for the
hyperbolic-gamma shift integral. -/
lemma tendsto_sum_paired_reciprocals {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n,
      (1 / (z + j) - 1 / ((j : ℂ) + 1 - z))) atTop
      (𝓝 (Real.pi * Complex.cot (Real.pi * z))) := by
  have hi : Tendsto (fun n : ℕ => 1 / (z + n)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [one_div, Function.comp_def] using
      (Filter.tendsto_inv₀_cobounded.comp
        ((tendsto_const_add_cobounded z).comp tendsto_natCast_atTop_cobounded))
  have hs := ((tendsto_logDeriv_euler_cot_sub hz).const_add (1 / z)).sub hi
  simpa only [sum_paired_reciprocals, add_sub_cancel, sub_zero] using hs

/-- A complex number strictly between the real parts zero and one is
outside the integer lattice. -/
lemma mem_integerComplement_of_re_between {z : ℂ} (hz₀ : 0 < z.re) (hz₁ : z.re < 1) :
    z ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hre := congrArg Complex.re hm
  simp only [Complex.intCast_re] at hre
  have hm₀ : (0 : ℝ) < m := by simpa only [hre] using hz₀
  have hm₁ : (m : ℝ) < 1 := by simpa only [hre] using hz₁
  have : (0 : ℤ) < m := by exact_mod_cast hm₀
  have : m < (1 : ℤ) := by exact_mod_cast hm₁
  omega

/-- Each paired exponential in the geometric expansion has an elementary
Laplace integral. -/
lemma integrableOn_paired_exponentials (b : ℝ) (z : ℂ) (n : ℕ)
    (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    IntegrableOn (fun t : ℝ =>
      Complex.exp (-2 * (((n : ℂ) + 1) * b - z) * t) -
        Complex.exp (-2 * ((n : ℂ) * b + z) * t)) (Ioi 0) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply Integrable.sub
  · apply integrableOn_exp_mul_complex_Ioi
    simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, neg_zero, add_re, natCast_re,
      one_re, ofReal_re, sub_re, add_im, natCast_im, one_im, ofReal_im, zero_mul,
      mul_zero, sub_zero, zero_add]
    nlinarith
  · apply integrableOn_exp_mul_complex_Ioi
    simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, neg_zero, add_re, natCast_re,
      ofReal_re, add_im, natCast_im, ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith

lemma integral_paired_exponentials (b : ℝ) (z : ℂ) (n : ℕ)
    (hb : 0 < b) (hz₀ : 0 < z.re) (hz₁ : z.re < b) :
    (∫ t : ℝ in Ioi 0,
      (Complex.exp (-2 * (((n : ℂ) + 1) * b - z) * t) -
        Complex.exp (-2 * ((n : ℂ) * b + z) * t))) =
      1 / (2 * (((n : ℂ) + 1) * b - z)) -
        1 / (2 * ((n : ℂ) * b + z)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : (-2 * (((n : ℂ) + 1) * b - z)).re < 0 := by
    simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, neg_zero, add_re, natCast_re,
      one_re, ofReal_re, sub_re, add_im, natCast_im, one_im, ofReal_im, zero_mul,
      mul_zero, sub_zero, zero_add]
    nlinarith
  have hc : (-2 * ((n : ℂ) * b + z)).re < 0 := by
    simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, neg_zero, add_re, natCast_re,
      ofReal_re, add_im, natCast_im, ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi ha 0)
    (integrableOn_exp_mul_complex_Ioi hc 0), integral_exp_mul_complex_Ioi ha 0,
    integral_exp_mul_complex_Ioi hc 0]
  simp only [ofReal_zero, mul_zero, exp_zero, neg_mul, div_neg, neg_div, neg_neg]

/-- The exact algebraic cancellation behind the first gamma shift. -/
lemma sinh_shift_quotient (A B w : ℂ) (hA : Complex.sinh A ≠ 0)
    (hB : Complex.sinh B ≠ 0) :
    (Complex.sinh (w + A) - Complex.sinh (w - A)) /
        (2 * Complex.sinh A * Complex.sinh B) = Complex.cosh w / Complex.sinh B := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  field_simp
  ring

/-- Geometric cutoffs converge under the integral on the positive real
axis. Their absolute values are at most one, so the integrand itself
supplies a dominating function. -/
lemma tendsto_integral_geometric_cutoff (b : ℝ) (hb : 0 < b) (f : ℝ → ℂ)
    (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      f t * (1 - (Real.exp (-2 * b * t) : ℂ) ^ n)) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, f t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
  · intro n
    exact hf.aestronglyMeasurable.mul
      (show Continuous (fun t : ℝ => 1 - (Real.exp (-2 * b * t) : ℂ) ^ n) by
        fun_prop).aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hq₀ : 0 ≤ Real.exp (-2 * b * t) := (Real.exp_pos _).le
    have hq₁ : Real.exp (-2 * b * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hb ht])
    have hp₀ := pow_nonneg hq₀ n
    have hp₁ := pow_le_one₀ hq₀ hq₁ (n := n)
    have hnorm : ‖(1 : ℂ) - (Real.exp (-2 * b * t) : ℂ) ^ n‖ ≤ 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp₁)]
      linarith
    simpa only [norm_mul, mul_one] using mul_le_mul_of_nonneg_left hnorm (norm_nonneg (f t))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hq₀ : 0 ≤ Real.exp (-2 * b * t) := (Real.exp_pos _).le
    have hq₁ : Real.exp (-2 * b * t) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hb ht])
    have hp := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
    simpa only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero, sub_zero, mul_one]
      using (hp.const_sub 1).const_mul (f t)

/-- Rewriting a hyperbolic quotient as the numerator of a geometric
series. This identity is purely algebraic in the two complex arguments. -/
lemma sinh_div_mul_one_sub_exp (w B : ℂ) (hB : Complex.sinh B ≠ 0) :
    Complex.sinh w / Complex.sinh B * (1 - Complex.exp (-2 * B)) =
      Complex.exp (w - B) - Complex.exp (-w - B) := by
  have hden : 1 - Complex.exp (-2 * B) =
      2 * Complex.sinh B * Complex.exp (-B) := by
    rw [Complex.sinh]
    have h₁ : Complex.exp B * Complex.exp (-B) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h₂ : Complex.exp (-B) * Complex.exp (-B) = Complex.exp (-2 * B) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      1 - Complex.exp (-2 * B) =
          Complex.exp B * Complex.exp (-B) - Complex.exp (-B) * Complex.exp (-B) := by
            rw [h₁, h₂]
      _ = 2 * ((Complex.exp B - Complex.exp (-B)) / 2) * Complex.exp (-B) := by ring
  rw [hden]
  have hnum : 2 * Complex.sinh w * Complex.exp (-B) =
      Complex.exp (w - B) - Complex.exp (-w - B) := by
    rw [Complex.sinh]
    simp only [sub_eq_add_neg, Complex.exp_add]
    ring
  rw [← hnum]
  field_simp

/-- Factoring the `n`th paired exponential into its first term and a
geometric power. -/
lemma paired_exponentials_factor (b : ℝ) (z : ℂ) (t : ℝ) (n : ℕ) :
    Complex.exp (-2 * (((n : ℂ) + 1) * b - z) * t) -
        Complex.exp (-2 * ((n : ℂ) * b + z) * t) =
      (Complex.exp (-2 * ((b : ℂ) - z) * t) - Complex.exp (-2 * z * t)) *
        (Real.exp (-2 * b * t) : ℂ) ^ n := by
  rw [Complex.ofReal_exp]
  push_cast
  rw [← Complex.exp_nat_mul, sub_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> congr 1 <;> ring

/-- The partial geometric expansion of the hyperbolic sine quotient. -/
lemma sum_paired_exponentials (b : ℝ) (hb : 0 < b) (z : ℂ) (t : ℝ) (ht : 0 < t)
    (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (Complex.exp (-2 * (((j : ℂ) + 1) * b - z) * t) -
        Complex.exp (-2 * ((j : ℂ) * b + z) * t))) =
      Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t) *
        (1 - (Real.exp (-2 * b * t) : ℂ) ^ n) := by
  have hB : Complex.sinh ((b : ℂ) * t) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh, Complex.ofReal_ne_zero]
    exact Real.sinh_ne_zero.mpr (ne_of_gt (mul_pos hb ht))
  have hbase := sinh_div_mul_one_sub_exp ((2 * z - b) * t) ((b : ℂ) * t) hB
  have ha : (2 * z - b) * (t : ℂ) - b * t = -2 * ((b : ℂ) - z) * t := by ring
  have hc : -((2 * z - b) * (t : ℂ)) - b * t = -2 * z * t := by ring
  have he : Complex.exp (-2 * ((b : ℂ) * t)) = (Real.exp (-2 * b * t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [ha, hc, he] at hbase
  simp_rw [paired_exponentials_factor]
  rw [← Finset.mul_sum, ← hbase, mul_assoc, mul_neg_geom_sum]

/-- The integrated Laplace terms are exactly the rescaled paired
cotangent terms. -/
lemma paired_reciprocals_rescale (b : ℝ) (hb : b ≠ 0) (z : ℂ) (n : ℕ) :
    1 / (2 * (((n : ℂ) + 1) * b - z)) - 1 / (2 * ((n : ℂ) * b + z)) =
      -(1 / (2 * (b : ℂ))) *
        (1 / (z / b + n) - 1 / ((n : ℂ) + 1 - z / b)) := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have ha : ((n : ℂ) + 1) * b - z = b * ((n : ℂ) + 1 - z / b) := by
    field_simp
  have hc : (n : ℂ) * b + z = b * (z / b + n) := by
    field_simp
    ring
  rw [ha, hc]
  simp only [one_div, mul_inv_rev]
  ring

/-- Evaluation of the elementary hyperbolic integral used after
differentiating a logarithmic gamma shift. Integrability is separated
from the evaluation so that the same strip estimates can serve both
the logarithmic integral and this identity. -/
theorem integral_sinh_div_sinh (b : ℝ) (z : ℂ) (hb : 0 < b)
    (hz₀ : 0 < z.re) (hz₁ : z.re < b)
    (hf : IntegrableOn (fun t : ℝ =>
      Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t)) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0,
      Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t)) =
      -(Real.pi / (2 * (b : ℂ))) * Complex.cot (Real.pi * (z / b)) := by
  have hw₀ : 0 < (z / b).re := by
    rw [Complex.div_ofReal_re]
    exact div_pos hz₀ hb
  have hw₁ : (z / b).re < 1 := by
    rw [Complex.div_ofReal_re]
    exact (div_lt_one hb).mpr hz₁
  have hs := (tendsto_sum_paired_reciprocals
    (mem_integerComplement_of_re_between hw₀ hw₁)).const_mul (-(1 / (2 * (b : ℂ))))
  have hc := tendsto_integral_geometric_cutoff b hb
    (fun t : ℝ => Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t)) hf
  have heq (n : ℕ) :
      (∫ t : ℝ in Ioi 0,
        Complex.sinh ((2 * z - b) * t) / Complex.sinh ((b : ℂ) * t) *
          (1 - (Real.exp (-2 * b * t) : ℂ) ^ n)) =
        -(1 / (2 * (b : ℂ))) *
          ∑ j ∈ Finset.range n, (1 / (z / b + j) - 1 / ((j : ℂ) + 1 - z / b)) := by
    calc
      _ = ∫ t : ℝ in Ioi 0, ∑ j ∈ Finset.range n,
          (Complex.exp (-2 * (((j : ℂ) + 1) * b - z) * t) -
            Complex.exp (-2 * ((j : ℂ) * b + z) * t)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (sum_paired_exponentials b hb z t ht n).symm
      _ = ∑ j ∈ Finset.range n,
          (1 / (2 * (((j : ℂ) + 1) * b - z)) -
            1 / (2 * ((j : ℂ) * b + z))) := by
        rw [integral_finsetSum _ (fun j _ =>
          integrableOn_paired_exponentials b z j hb hz₀ hz₁)]
        apply Finset.sum_congr rfl
        intro j _
        exact integral_paired_exponentials b z j hb hz₀ hz₁
      _ = _ := by
        simp_rw [paired_reciprocals_rescale b hb.ne', Finset.mul_sum]
  have hlim := tendsto_nhds_unique hc (hs.congr (fun n => (heq n).symm))
  rw [hlim]
  ring

end GammaElementary
end HaagerupIzumi
