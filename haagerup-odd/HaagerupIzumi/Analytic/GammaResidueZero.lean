module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaShift
public import HaagerupIzumi.Analytic.Residue
public import Mathlib.Analysis.Real.Sqrt

/-!
# Special strip values and the residue at the origin

The two shift identities, reflection, and positivity determine the values
at the periods. A single backward shift then gives a local meromorphic
germ at the origin, with the BSS residue normalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace HaagerupIzumi.GammaIntegral

lemma continuousAt_gamma_strip (a b : ℝ) (z : ℂ) (ha : 0 < a) (hb : 0 < b)
    (hz₀ : 0 < z.re) (hz₁ : z.re < a + b) : ContinuousAt (gamma a b) z :=
  (hasDerivAt_logGamma ha hb hz₀ hz₁).cexp.continuousAt

lemma tendsto_sin_mul_div (c : ℂ) :
    Tendsto (fun z : ℂ => Complex.sin (c * z) / z) (𝓝[≠] 0) (𝓝 c) := by
  have hd := ((hasDerivAt_id (0 : ℂ)).const_mul c).csin
  have hs := hd.tendsto_slope_zero
  simpa only [zero_add, vsub_eq_sub, sub_zero, mul_zero, Complex.sin_zero,
    Complex.cos_zero, one_mul, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm, id_eq,
    Function.comp_def] using hs

lemma tendsto_sin_mul_div_real (c : ℂ) :
    Tendsto (fun x : ℝ => Complex.sin (c * x) / (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have hd := (((hasDerivAt_id (0 : ℂ)).const_mul c).csin).comp_ofReal
  have hs := hd.tendsto_slope_zero_right
  simpa only [zero_add, Complex.ofReal_zero, mul_zero, Complex.sin_zero,
    Complex.cos_zero, one_mul, mul_one, sub_zero, Complex.real_smul, Complex.ofReal_inv,
    div_eq_mul_inv, mul_comm, id_eq, Function.comp_def] using hs

lemma tendsto_gamma_add_real (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc₀ : 0 < c) (hc₁ : c < a + b) :
    Tendsto (fun x : ℝ => gamma a b ((x : ℂ) + c))
      (𝓝[>] (0 : ℝ)) (𝓝 (gamma a b c)) := by
  have hgc := continuousAt_gamma_strip a b (c : ℂ) ha hb hc₀ hc₁
  have hx : Tendsto (fun x : ℝ => (x : ℂ) + c) (𝓝 0) (𝓝 (c : ℂ)) := by
    simpa only [Complex.ofReal_zero, zero_add] using
      (Complex.continuous_ofReal.tendsto 0).add_const (c : ℂ)
  exact (hgc.tendsto.comp hx).mono_left nhdsWithin_le_nhds

/-- Comparing the two shifts along the positive real axis determines
the ratio of the two values at the periods. -/
lemma gamma_period_relation (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b : ℂ) * gamma a b a = (a : ℂ) * gamma a b b := by
  have hA := (tendsto_sin_mul_div_real ((Real.pi : ℂ) / a)).mul
    (tendsto_gamma_add_real a b a ha hb ha (by linarith))
  have hB := (tendsto_sin_mul_div_real ((Real.pi : ℂ) / b)).mul
    (tendsto_gamma_add_real a b b ha hb hb (by linarith))
  have heq : (fun x : ℝ => Complex.sin (((Real.pi : ℂ) / a) * x) / (x : ℂ) *
      gamma a b ((x : ℂ) + a)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => Complex.sin (((Real.pi : ℂ) / b) * x) / (x : ℂ) *
        gamma a b ((x : ℂ) + b)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ha),
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with x hx hxa hxb
    have hargA : ((Real.pi : ℂ) / a) * x = Real.pi * ((x : ℂ) / a) := by ring
    have hargB : ((Real.pi : ℂ) / b) * x = Real.pi * ((x : ℂ) / b) := by ring
    rw [hargA, hargB, gamma_shift₁_strip a b (x : ℂ) ha hb hx hxb,
      gamma_shift₂_strip a b (x : ℂ) ha hb hx hxa]
    ring
  have he := tendsto_nhds_unique hA (hB.congr' heq.symm)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp at he
  simpa only [mul_comm] using he

lemma gamma_period_product (a b : ℝ) : gamma a b a * gamma a b b = 1 := by
  have hf := gamma_reflection a b (a : ℂ)
  rw [show (a : ℂ) + b - a = b by ring] at hf
  exact hf

/-- The value of the strip gamma function at the first period. -/
theorem gamma_at_first_period (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gamma a b a = (Real.sqrt (a / b) : ℂ) := by
  have hA := gamma_real_pos a b a
  have hB := gamma_real_pos a b b
  have hprop := congrArg Complex.re (gamma_period_relation a b ha hb)
  have hprod := congrArg Complex.re (gamma_period_product a b)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hprop
  simp only [Complex.mul_re, hA.2, hB.2, zero_mul, sub_zero, Complex.one_re] at hprod
  have hsq : b * (gamma a b a).re ^ 2 = a := by
    linear_combination (gamma a b a).re * hprop + a * hprod
  have hsq' : (gamma a b a).re ^ 2 = a / b := by
    apply (eq_div_iff hb.ne').mpr
    nlinarith [hsq]
  have hroot : Real.sqrt (a / b) = (gamma a b a).re :=
    (Real.sqrt_eq_iff_eq_sq (div_pos ha hb).le hA.1.le).mpr hsq'.symm
  apply Complex.ext
  · exact hroot.symm
  · simpa only [Complex.ofReal_im] using hA.2

/-- The value of the strip gamma function at the second period. -/
theorem gamma_at_second_period (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gamma a b b = (Real.sqrt (b / a) : ℂ) := by
  rw [← gamma_swap a b b, gamma_at_first_period b a hb ha]

/-- The meromorphic germ obtained from one backward shift by `b`. -/
def originGerm (a b : ℝ) (z : ℂ) : ℂ :=
  gamma a b (z + b) / (2 * Complex.sin (Real.pi * (z / a)))

lemma originGerm_eq_gamma (a b : ℝ) (z : ℂ) (ha : 0 < a) (hb : 0 < b)
    (hz₀ : 0 < z.re) (hz₁ : z.re < a) : originGerm a b z = gamma a b z := by
  have hsin := sin_shift_ne_zero a z ha hz₀ hz₁
  unfold originGerm
  rw [gamma_shift₂_strip a b z ha hb hz₀ hz₁]
  exact mul_div_cancel_left₀ (gamma a b z) (mul_ne_zero two_ne_zero hsin)

lemma first_period_mul_sqrt_ratio (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  rw [Real.sqrt_div hb.le, Real.sqrt_mul ha.le]
  calc
    a * (Real.sqrt b / Real.sqrt a) = (a / Real.sqrt a) * Real.sqrt b := by ring
    _ = Real.sqrt a * Real.sqrt b := by rw [Real.div_sqrt]

/-- The residue normalization is obtained directly from the explicit
strip construction; no hyperbolic-gamma interface is assumed. -/
theorem tendsto_mul_originGerm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun z : ℂ => z * originGerm a b z) (𝓝[≠] 0)
      (𝓝 ((Real.sqrt (a * b) : ℂ) / (2 * Real.pi))) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Tendsto (fun z : ℂ => gamma a b (z + b)) (𝓝[≠] 0)
      (𝓝 (gamma a b b)) := by
    have hgc := continuousAt_gamma_strip a b (b : ℂ) ha hb hb
      (by simp only [Complex.ofReal_re]; linarith)
    have hz : Tendsto (fun z : ℂ => z + b) (𝓝 (0 : ℂ)) (𝓝 (b : ℂ)) := by
      simpa only [id_eq, zero_add] using (continuous_id.tendsto (0 : ℂ)).add_const (b : ℂ)
    exact (hgc.tendsto.comp hz).mono_left nhdsWithin_le_nhds
  have hs := (tendsto_sin_mul_div ((Real.pi : ℂ) / a)).const_mul (2 : ℂ)
  have hlim := hg.div hs (mul_ne_zero two_ne_zero (div_ne_zero hpiC haC))
  have hv : gamma a b b / (2 * ((Real.pi : ℂ) / a)) =
      (Real.sqrt (a * b) : ℂ) / (2 * Real.pi) := by
    rw [gamma_at_second_period a b ha hb]
    have hroot : (a : ℂ) * (Real.sqrt (b / a) : ℂ) = (Real.sqrt (a * b) : ℂ) := by
      exact_mod_cast first_period_mul_sqrt_ratio a b ha hb
    calc
      _ = ((a : ℂ) * (Real.sqrt (b / a) : ℂ)) / (2 * Real.pi) := by field_simp
      _ = _ := by rw [hroot]
  rw [hv] at hlim
  apply hlim.congr
  intro z
  simp only [Pi.div_apply]
  have harg : ((Real.pi : ℂ) / a) * z = Real.pi * (z / a) := by ring
  rw [harg, show 2 * (Complex.sin (Real.pi * (z / a)) / z) =
    (2 * Complex.sin (Real.pi * (z / a))) / z by ring, div_div_eq_mul_div]
  unfold originGerm
  ring

/-- The local backward-shift germ has the residue required by the
analytic interface. -/
theorem hasResidue_originGerm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasResidue (originGerm a b) 0 ((Real.sqrt (a * b) : ℂ) / (2 * Real.pi)) := by
  simpa only [HasResidue, sub_zero] using tendsto_mul_originGerm a b ha hb

end HaagerupIzumi.GammaIntegral
