module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaFourierDuality
public import HaagerupIzumi.Analytic.GammaK4StraightLine
public import HaagerupIzumi.Analytic.GammaK4Swap

/-! # Fourier duality for the concrete four-gamma contour -/

@[expose] public section
noncomputable section

open Complex MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma kernel_eq_pairProduct (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x y : ℂ) (t : ℝ) :
    kernel a b hb hba r s x y (t * I) =
      pairProductIntegrand a b hb hba (k4U a b r s) (k4V a b r s) x y t := by
  unfold kernel k4Integrand pairProductIntegrand symmetricIntegrand shiftedGammaPair
  ring_nf

lemma complementary_centers (a b : ℝ) (r s : ℂ) :
    complementaryParameter a b (k4V a b r s) = k4U a b (-r) s ∧
    complementaryParameter a b (k4U a b r s) = k4V a b (-r) s := by
  unfold complementaryParameter k4U k4V
  push_cast
  constructor <;> ring

/-- The D symmetry on the tube of absolute two-variable convergence. -/
theorem K4_duality {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {r s x y : ℂ}
    (hU : 0 < (k4U a b r s).re) (hUΩ : (k4U a b r s).re < (a + b) / 2)
    (hV : 0 < (k4V a b r s).re) (hVΩ : (k4V a b r s).re < (a + b) / 2)
    (hx : |x.re| < (k4V a b r s).re)
    (hy : |y.re| < (a + b) / 2 - (k4U a b r s).re) :
    K4 a b hb hba.le r s x y =
      Γr (gamma a b hb hba.le) a b r s * K4 a b hb hba.le (-r) s y x := by
  have hUV : (k4U a b r s).re + (k4V a b r s).re = (a + b) / 2 + r.re := by
    simp only [k4U, k4V, add_re, sub_re, div_ofNat_re, ofReal_re]
    ring
  have hc : K4Conv a b r y := by unfold K4Conv; linarith
  have hc' : K4Conv a b (-r) x := by unfold K4Conv; simp only [neg_re]; linarith
  obtain ⟨hcent₁, hcent₂⟩ := complementary_centers a b r s
  have hU' : 0 < (k4U a b (-r) s).re := by
    rw [← hcent₁, complementaryParameter_re]; linarith
  have hx' : |y.re| < (k4V a b (-r) s).re := by
    rw [← hcent₂, complementaryParameter_re]; exact hy
  have hD := integral_pairProduct_duality hb hba hirr hU hUΩ hV hVΩ hx hy
  simp_rw [← kernel_eq_pairProduct] at hD
  rw [hcent₁, hcent₂] at hD
  simp_rw [← kernel_eq_pairProduct] at hD
  have hΓ : gamma a b hb hba.le (2 * k4U a b r s) *
      gamma a b hb hba.le (2 * k4V a b r s) = Γr (gamma a b hb hba.le) a b r s := by
    unfold Γr k4U k4V
    congr 1 <;> congr 1 <;> ring
  rw [hΓ, ← K4_eq_integral_zero hb hba.le hirr hc hU hx,
    ← K4_eq_integral_zero hb hba.le hirr hc' hU' hx'] at hD
  apply mul_left_cancel₀ (ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (mul_pos (hb.trans hba) hb)).ne')
  linear_combination hD

end HaagerupIzumi.GammaK4Contour
