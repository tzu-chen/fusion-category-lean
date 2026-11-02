module

public import HaagerupIzumi.Analytic.GammaIdentities
public import HaagerupIzumi.Analytic.GammaResidueZero
public import HaagerupIzumi.Analytic.GammaSech
import all Mathlib.Data.Complex.Basic

/-!
# Normalization of the two-gamma transform

Reflection and a shift reduce the symmetric product at half the first
period to `1 / (2 * cosh)`. Its integral fixes the Fourier transform's
constant without a pinching limit.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory

namespace HaagerupIzumi.GammaContinuation

lemma factor_half_period (a t : ℝ) (ha : 0 < a) :
    factor a ((a : ℂ) / 2 - t * I) = (2 * Real.cosh (Real.pi * t / a) : ℝ) := by
  unfold factor
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have harg : (Real.pi : ℂ) * ((a : ℂ) / 2 - t * I) / a =
      Real.pi / 2 - ((Real.pi * t / a : ℝ) : ℂ) * I := by
    push_cast
    field_simp [haC]
  rw [harg, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

lemma gamma_half_period_pair (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (t : ℝ) :
    gamma a b hb hba ((a : ℂ) / 2 + t * I) *
      gamma a b hb hba ((a : ℂ) / 2 - t * I) =
        ((1 / (2 * Real.cosh (Real.pi * t / a)) : ℝ) : ℂ) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hp (ε : ℝ) : (a : ℂ) / 2 + ε * I ∉ poleLattice a b := by
    apply not_mem_poleLattice_of_re_pos ha hb
    simp
    positivity
  have hz : (a : ℂ) / 2 + t * I ∉ zeroLattice a b := by
    apply not_mem_zeroLattice_of_re_lt ha hb
    simp
    linarith
  have hleft : (a : ℂ) / 2 - t * I ∉ poleLattice a b := by
    simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hp (-t)
  have hs := gamma_shift₂ a b hb hba ((a : ℂ) / 2 - t * I) hleft
  rw [factor_half_period a t ha] at hs
  have hr := gamma_reflection a b hb hba ((a : ℂ) / 2 + t * I) (hp t) hz
  have harg : (a : ℂ) + b - ((a : ℂ) / 2 + t * I) =
      ((a : ℂ) / 2 - t * I) + b := by ring
  rw [harg, hs] at hr
  have hc : ((2 * Real.cosh (Real.pi * t / a) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [Complex.ofReal_div, Complex.ofReal_one]
  apply (eq_div_iff hc).2
  linear_combination hr

theorem integral_gamma_half_period_pair (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    (∫ t : ℝ, gamma a b hb hba ((a : ℂ) / 2 + t * I) *
      gamma a b hb hba ((a : ℂ) / 2 - t * I)) = (a : ℂ) / 2 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  simp_rw [gamma_half_period_pair a b hb hba]
  have hi : Integrable (fun t : ℝ => 1 / (2 * Real.cosh (Real.pi * t / a))) := by
    by_contra hni
    have he := GammaSech.integral_scaled ha
    rw [integral_undef hni] at he
    linarith
  have he := Complex.ofRealCLM.integral_comp_comm hi
  simpa only [Complex.ofRealCLM_apply, GammaSech.integral_scaled ha,
    Complex.ofReal_div, Complex.ofReal_ofNat] using he

lemma gamma_half_second_period_sq (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    gamma a b hb hba ((b : ℂ) / 2) ^ 2 = (1 : ℂ) / 2 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hp : (b : ℂ) / 2 ∉ poleLattice a b :=
    not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)
  have hz : (b : ℂ) / 2 ∉ zeroLattice a b :=
    not_mem_zeroLattice_of_re_lt ha hb (by simp; linarith)
  have hs := gamma_shift₁ a b hb hba ((b : ℂ) / 2) hp
  have hfactor : factor b ((b : ℂ) / 2) = 2 := by
    unfold factor
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    have harg : (Real.pi : ℂ) * ((b : ℂ) / 2) / b = Real.pi / 2 := by
      field_simp [hbC]
    rw [harg, Complex.sin_pi_div_two, mul_one]
  rw [hfactor] at hs
  have hr := gamma_reflection a b hb hba ((b : ℂ) / 2) hp hz
  rw [show (a : ℂ) + b - (b : ℂ) / 2 = (b : ℂ) / 2 + a by ring, hs] at hr
  linear_combination hr / 2

lemma gamma_at_first_period_global (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    gamma a b hb hba a = (Real.sqrt (a / b) : ℂ) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  rw [gamma_eq_on_strip a b hb hba a (by simpa) (by simp; linarith)]
  exact GammaIntegral.gamma_at_first_period a b ha hb

end HaagerupIzumi.GammaContinuation
