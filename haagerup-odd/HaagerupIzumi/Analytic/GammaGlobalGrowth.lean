module

public import HaagerupIzumi.Analytic.GammaContinuation
public import HaagerupIzumi.Analytic.GammaGrowth
public import HaagerupIzumi.Analytic.GammaSineGrowth
import all Mathlib.Data.Complex.Basic

/-!
# Growth of the continued gamma function

The finite products contribute their exact linear exponents. On a bounded
vertical strip the number of factors is bounded, so their logarithmic errors
remain uniformly bounded.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaContinuation

lemma factor_ne_zero_of_im_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im ≠ 0) :
    factor a z ≠ 0 := by
  intro hf
  obtain ⟨k, hk⟩ := (factor_eq_zero_iff ha.ne' z).mp hf
  apply hz
  simp [hk]

lemma shiftProduct_ne_zero_of_im_ne_zero {a : ℝ} (ha : 0 < a) (b : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) : shiftProduct a b z m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply factor_ne_zero_of_im_ne_zero ha
  simpa using hz

lemma log_norm_shiftProduct {a : ℝ} (ha : 0 < a) (b : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    Real.log ‖shiftProduct a b z m‖ =
      ∑ j ∈ Finset.range m, Real.log ‖factor a (z + (j : ℂ) * b)‖ := by
  rw [shiftProduct, norm_prod, Real.log_prod]
  intro j _
  apply norm_ne_zero_iff.mpr
  apply factor_ne_zero_of_im_ne_zero ha
  simpa using hz

lemma log_norm_shiftProduct_bound {a B : ℝ} (ha : 0 < a) (b : ℝ)
    (hB : ∀ z : ℂ, 1 ≤ |z.im| →
      |Real.log ‖factor a z‖ - Real.pi * |z.im| / a| ≤ B)
    {z : ℂ} (hz : 1 ≤ |z.im|) (m : ℕ) :
    |Real.log ‖shiftProduct a b z m‖ - (m : ℝ) * (Real.pi * |z.im| / a)| ≤ m * B := by
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hz
  rw [log_norm_shiftProduct ha b hzne]
  have heq : (∑ j ∈ Finset.range m, Real.log ‖factor a (z + (j : ℂ) * b)‖) -
      (m : ℝ) * (Real.pi * |z.im| / a) =
      ∑ j ∈ Finset.range m,
        (Real.log ‖factor a (z + (j : ℂ) * b)‖ - Real.pi * |z.im| / a) := by
    simp [Finset.sum_sub_distrib]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range m, B := by
      apply Finset.sum_le_sum
      intro j _
      simpa using hB (z + (j : ℂ) * b) (by simpa using hz)
    _ = _ := by simp

@[simp] lemma representative_im (b : ℝ) (z : ℂ) : (representative b z).im = z.im := by
  simp [representative]

lemma gamma_ne_zero_of_im_ne_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    {z : ℂ} (hz : z.im ≠ 0) : gamma a b hb hba z ≠ 0 := by
  let G := integralStripData a b hb hba
  have hrep : G.gamma (representative b z) ≠ 0 := G.representative_ne_zero z
  change G.extension z ≠ 0
  unfold StripData.extension
  split_ifs
  · exact mul_ne_zero hrep (shiftProduct_ne_zero_of_im_ne_zero (hb.trans_le hba) b
      (by simpa using hz) _)
  · exact div_ne_zero hrep (shiftProduct_ne_zero_of_im_ne_zero (hb.trans_le hba) b hz _)

lemma verticalExponent_representative {a b : ℝ} (hb : 0 < b) (z : ℂ) :
    GammaIntegral.verticalExponent a b z.re z.im =
      GammaIntegral.verticalExponent a b (representative b z).re z.im +
        (shiftIndex b z : ℝ) * (Real.pi * |z.im| / a) := by
  rw [representative_re]
  unfold GammaIntegral.verticalExponent
  field_simp
  ring

lemma log_norm_gamma_bound_by_index {a b A B : ℝ} (hb : 0 < b) (hba : b < a)
    (hA : ∀ x ∈ Icc b (2 * b), ∀ y : ℝ,
      |Real.log ‖GammaIntegral.gamma a b ((x : ℂ) + y * I)‖ -
        GammaIntegral.verticalExponent a b x y| ≤ A)
    (hB : ∀ z : ℂ, 1 ≤ |z.im| →
      |Real.log ‖factor a z‖ - Real.pi * |z.im| / a| ≤ B)
    {z : ℂ} (hz : 1 ≤ |z.im|) :
    |Real.log ‖gamma a b hb hba.le z‖ - GammaIntegral.verticalExponent a b z.re z.im| ≤
      A + |(shiftIndex b z : ℝ)| * B := by
  let G := integralStripData a b hb hba.le
  have ha := hb.trans hba
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hz
  have hrne : (representative b z).im ≠ 0 := by simpa using hzne
  have hrep : |Real.log ‖G.gamma (representative b z)‖ -
      GammaIntegral.verticalExponent a b (representative b z).re z.im| ≤ A := by
    have hh := hA (representative b z).re
      ⟨(representative_bounds hb z).1, (representative_bounds hb z).2.le⟩ z.im
    simpa only [G, integralStripData, ← representative_im b z, Complex.re_add_im] using hh
  have hrepne := norm_ne_zero_iff.mpr (G.representative_ne_zero z)
  have hv := verticalExponent_representative hb (a := a) z
  change |Real.log ‖G.extension z‖ - _| ≤ _
  by_cases hk : 0 ≤ shiftIndex b z
  · have hm : ((shiftIndex b z).toNat : ℝ) = (shiftIndex b z : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hk)
    have hprod := log_norm_shiftProduct_bound ha b hB (z := representative b z)
      (by simpa using hz) (shiftIndex b z).toNat
    have hpne := norm_ne_zero_iff.mpr
      (shiftProduct_ne_zero_of_im_ne_zero ha b hrne (shiftIndex b z).toNat)
    rw [StripData.extension, if_pos hk, norm_mul, Real.log_mul hrepne hpne, hv,
      abs_of_nonneg (show (0 : ℝ) ≤ shiftIndex b z by exact_mod_cast hk)]
    have heq : Real.log ‖G.gamma (representative b z)‖ +
        Real.log ‖shiftProduct a b (representative b z) (shiftIndex b z).toNat‖ -
        (GammaIntegral.verticalExponent a b (representative b z).re z.im +
          (shiftIndex b z : ℝ) * (Real.pi * |z.im| / a)) =
        (Real.log ‖G.gamma (representative b z)‖ -
          GammaIntegral.verticalExponent a b (representative b z).re z.im) +
        (Real.log ‖shiftProduct a b (representative b z) (shiftIndex b z).toNat‖ -
          (shiftIndex b z : ℝ) * (Real.pi * |z.im| / a)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hrep (by simpa only [representative_im, hm] using hprod))
  · have hkn : shiftIndex b z < 0 := by omega
    have hm : ((-shiftIndex b z).toNat : ℝ) = -(shiftIndex b z : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -shiftIndex b z))
    have hprod := log_norm_shiftProduct_bound ha b hB hz (-shiftIndex b z).toNat
    have hpne := norm_ne_zero_iff.mpr
      (shiftProduct_ne_zero_of_im_ne_zero ha b hzne (-shiftIndex b z).toNat)
    rw [StripData.extension, if_neg hk, norm_div, Real.log_div hrepne hpne, hv,
      abs_of_neg (show (shiftIndex b z : ℝ) < 0 by exact_mod_cast hkn)]
    have heq : Real.log ‖G.gamma (representative b z)‖ -
        Real.log ‖shiftProduct a b z (-shiftIndex b z).toNat‖ -
        (GammaIntegral.verticalExponent a b (representative b z).re z.im +
          (shiftIndex b z : ℝ) * (Real.pi * |z.im| / a)) =
        (Real.log ‖G.gamma (representative b z)‖ -
          GammaIntegral.verticalExponent a b (representative b z).re z.im) -
        (Real.log ‖shiftProduct a b z (-shiftIndex b z).toNat‖ -
          (-(shiftIndex b z : ℝ)) * (Real.pi * |z.im| / a)) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hrep (by simpa only [hm] using hprod))

lemma shiftIndex_abs_le {b L U : ℝ} (hb : 0 < b) {z : ℂ}
    (hL : L ≤ z.re) (hU : z.re ≤ U) :
    |(shiftIndex b z : ℝ)| ≤ (|L| + |U|) / b + 2 := by
  have hlo := Int.floor_le (z.re / b)
  have hhi := Int.lt_floor_add_one (z.re / b)
  have hzabs : |z.re| ≤ |L| + |U| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le L, le_abs_self U, abs_nonneg L, abs_nonneg U]
  have hqabs : |z.re / b| ≤ (|L| + |U|) / b := by
    rw [abs_div, abs_of_pos hb]
    exact div_le_div_of_nonneg_right hzabs hb.le
  simp only [shiftIndex, Int.cast_sub, Int.cast_one]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hqabs).1, (abs_le.mp hqabs).2]

theorem log_norm_gamma_uniform {a b : ℝ} (hb : 0 < b) (hba : b < a) (L U : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, L ≤ z.re → z.re ≤ U → 1 ≤ |z.im| →
      |Real.log ‖gamma a b hb hba.le z‖ - GammaIntegral.verticalExponent a b z.re z.im| ≤ C := by
  obtain ⟨A, hA⟩ := GammaIntegral.log_norm_gamma_vertical_uniform_exact (hb.trans hba) hb
    hb (show 2 * b < a + b by linarith)
  obtain ⟨B, hBpos, hB⟩ := GammaIntegral.exists_log_sine_bound (hb.trans hba)
  refine ⟨A + ((|L| + |U|) / b + 2) * B, fun z hL hU hz => ?_⟩
  apply (log_norm_gamma_bound_by_index hb hba hA hB hz).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (shiftIndex_abs_le hb hL hU) hBpos)

/-- The exact-rate ratio bound on arbitrary bounded vertical strips. -/
theorem ratio_bound {a b : ℝ} (hb : 0 < b) (hba : b < a) (c L U : ℝ) :
    ∃ C T : ℝ, 0 < T ∧ ∀ z : ℂ, L ≤ z.re → z.re ≤ U → T ≤ |z.im| →
      ‖gamma a b hb hba.le (z + c)‖ ≤
        C * Real.exp (Real.pi * c * |z.im| / (a * b)) * ‖gamma a b hb hba.le z‖ := by
  obtain ⟨B, hB⟩ := log_norm_gamma_uniform hb hba (min L (L + c)) (max U (U + c))
  refine ⟨Real.exp (2 * B), 1, one_pos, fun z hL hU hz => ?_⟩
  have h₀ := hB z ((min_le_left _ _).trans hL) (hU.trans (le_max_left _ _)) hz
  have h₁ := hB (z + c)
    (by simpa using (min_le_right L (L + c)).trans (add_le_add hL (le_refl c)))
    (by simpa using (add_le_add hU (le_refl c)).trans (le_max_right U (U + c))) (by simpa using hz)
  have hdiff := GammaIntegral.verticalExponent_add_sub a b z.re c z.im
  have hlog : Real.log ‖gamma a b hb hba.le (z + c)‖ ≤
      Real.log ‖gamma a b hb hba.le z‖ + Real.pi * c * |z.im| / (a * b) + 2 * B := by
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero] at h₁
    linarith [(abs_le.mp h₀).1, (abs_le.mp h₁).2]
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hz
  have hp₀ := norm_pos_iff.mpr (gamma_ne_zero_of_im_ne_zero a b hb hba.le hzne)
  have hp₁ := norm_pos_iff.mpr (gamma_ne_zero_of_im_ne_zero a b hb hba.le
    (z := z + c) (by simpa using hzne))
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp₁, Real.exp_add, Real.exp_add, Real.exp_log hp₀] at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

end HaagerupIzumi.GammaContinuation
