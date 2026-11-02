module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4Duality

/-! # The Euler transformation in an open neighborhood of the origin

The six successive D/P symmetries have cancelling exponential phases.
The domain used here is stable under their permutations and sign changes.
-/

@[expose] public section
noncomputable section

open Complex
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

def EulerSmall (a b : ℝ) (r s x y : ℂ) : Prop :=
  |r.re| + |s.re| + |x.re| + |y.re| < (a + b) / 4

lemma EulerSmall.duality_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x y : ℂ}
    (h : EulerSmall a b r s x y) :
    0 < (k4U a b r s).re ∧ (k4U a b r s).re < (a + b) / 2 ∧
    0 < (k4V a b r s).re ∧ (k4V a b r s).re < (a + b) / 2 ∧
    |x.re| < (k4V a b r s).re ∧
    |y.re| < (a + b) / 2 - (k4U a b r s).re := by
  have hr₀ := neg_abs_le r.re
  have hr₁ := le_abs_self r.re
  have hs₀ := neg_abs_le s.re
  have hs₁ := le_abs_self s.re
  have hx := abs_nonneg x.re
  have hy := abs_nonneg y.re
  have hr := abs_nonneg r.re
  have hs := abs_nonneg s.re
  dsimp only [EulerSmall] at h
  simp only [k4U, k4V, add_re, sub_re, div_ofNat_re, ofReal_re]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma EulerSmall.conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x y : ℂ}
    (h : EulerSmall a b r s x y) : K4Conv a b r y := by
  dsimp only [EulerSmall] at h
  unfold K4Conv
  linarith [le_abs_self r.re, abs_nonneg s.re, abs_nonneg x.re]

lemma EulerSmall.noPinch {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r s x y : ℂ}
    (h : EulerSmall a b r s x y) : K4NoPinch a b r s x := by
  obtain ⟨hU, _, _, _, hx, _⟩ := h.duality_bounds ha hb
  exact noPinch_of_straight ha hb hU hx

lemma K4_duality_small {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {r s x y : ℂ} (h : EulerSmall a b r s x y) :
    K4 a b hb hba.le r s x y =
      Γr (gamma a b hb hba.le) a b r s * K4 a b hb hba.le (-r) s y x := by
  obtain ⟨hU, hUΩ, hV, hVΩ, hx, hy⟩ := h.duality_bounds (hb.trans hba) hb
  exact K4_duality hb hba hirr hU hUΩ hV hVΩ hx hy

lemma gammaMultiplier_reflection_small {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {r s x y : ℂ} (h : EulerSmall a b r s x y) :
    Γr (gamma a b hb hba) a b r y * Γr (gamma a b hb hba) a b (-r) y = 1 := by
  have ha := hb.trans_le hba
  have hp₁ : 0 < ((((a + b : ℝ) : ℂ) / 2 + r + y)).re := by
    simp only [add_re, div_ofNat_re, ofReal_re]
    dsimp only [EulerSmall] at h
    linarith [neg_abs_le r.re, neg_abs_le y.re, abs_nonneg s.re, abs_nonneg x.re]
  have hz₁ : ((((a + b : ℝ) : ℂ) / 2 + r + y)).re < a + b := by
    simp only [add_re, div_ofNat_re, ofReal_re]
    dsimp only [EulerSmall] at h
    linarith [le_abs_self r.re, le_abs_self y.re, abs_nonneg s.re, abs_nonneg x.re]
  have hp₂ : 0 < ((((a + b : ℝ) : ℂ) / 2 + r - y)).re := by
    simp only [add_re, sub_re, div_ofNat_re, ofReal_re]
    dsimp only [EulerSmall] at h
    linarith [neg_abs_le r.re, le_abs_self y.re, abs_nonneg s.re, abs_nonneg x.re]
  have hz₂ : ((((a + b : ℝ) : ℂ) / 2 + r - y)).re < a + b := by
    simp only [add_re, sub_re, div_ofNat_re, ofReal_re]
    dsimp only [EulerSmall] at h
    linarith [le_abs_self r.re, neg_abs_le y.re, abs_nonneg s.re, abs_nonneg x.re]
  have h₁ := gamma_reflection a b hb hba _
    (not_mem_poleLattice_of_re_pos ha hb hp₁) (not_mem_zeroLattice_of_re_lt ha hb hz₁)
  have h₂ := gamma_reflection a b hb hba _
    (not_mem_poleLattice_of_re_pos ha hb hp₂) (not_mem_zeroLattice_of_re_lt ha hb hz₂)
  have harg₁ : (a : ℂ) + b - (((a + b : ℝ) : ℂ) / 2 + r + y) =
      ((a + b : ℝ) : ℂ) / 2 + -r - y := by push_cast; ring
  have harg₂ : (a : ℂ) + b - (((a + b : ℝ) : ℂ) / 2 + r - y) =
      ((a + b : ℝ) : ℂ) / 2 + -r + y := by push_cast; ring
  rw [harg₁] at h₁
  rw [harg₂] at h₂
  calc
    _ = (gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + r + y) *
          gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + -r - y)) *
        (gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + r - y) *
          gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + -r + y)) := by unfold Γr; ring
    _ = 1 := by rw [h₁, h₂]; ring

lemma swap_phases_cycle (a b : ℝ) (s x y : ℂ) :
    Complex.exp (Real.pi * I * x * (s - y) / ((a : ℂ) * b)) *
      Complex.exp (Real.pi * I * s * (y - x) / ((a : ℂ) * b)) *
      Complex.exp (Real.pi * I * y * (x - s) / ((a : ℂ) * b)) = 1 := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  ring

/-- The Euler identity follows from three dualities and three swaps on
an open parameter neighborhood; it is ready for analytic continuation. -/
theorem K4_euler_small {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) {r s x y : ℂ} (h : EulerSmall a b r s x y) :
    Γr (gamma a b hb hba.le) a b r y * K4 a b hb hba.le r s x y =
      Γr (gamma a b hb hba.le) a b r s * Γr (gamma a b hb hba.le) a b r x *
        K4 a b hb hba.le (-r) s x y := by
  have h₁ : EulerSmall a b (-r) s y x := by
    simpa [EulerSmall, abs_neg, add_comm, add_left_comm, add_assoc] using h
  have h₂ : EulerSmall a b (-r) y s x := by
    simpa [EulerSmall, abs_neg, add_comm, add_left_comm, add_assoc] using h
  have h₃ : EulerSmall a b r y x s := by
    simpa [EulerSmall, add_comm, add_left_comm, add_assoc] using h
  have h₄ : EulerSmall a b r x y s := by
    simpa [EulerSmall, add_comm, add_left_comm, add_assoc] using h
  have h₅ : EulerSmall a b (-r) x s y := by
    simpa [EulerSmall, abs_neg, add_comm, add_left_comm, add_assoc] using h
  have d₁ := K4_duality_small hb hba hirr h
  have d₂ := K4_duality_small hb hba hirr h₂
  simp only [neg_neg] at d₂
  have d₃ := K4_duality_small hb hba hirr h₄
  have p₁ := K4_swap a b hb hba.le hirr (-r) s y x
    (h₁.conv (hb.trans hba) hb) (h₁.noPinch (hb.trans hba) hb)
  have p₂ := K4_swap a b hb hba.le hirr r y x s
    (h₃.conv (hb.trans hba) hb) (h₃.noPinch (hb.trans hba) hb)
  have p₃ := K4_swap a b hb hba.le hirr (-r) x s y
    (h₅.conv (hb.trans hba) hb) (h₅.noPinch (hb.trans hba) hb)
  rw [d₁, p₁, d₂, p₂, d₃, p₃]
  calc
    _ = (Γr (gamma a b hb hba.le) a b r y * Γr (gamma a b hb hba.le) a b (-r) y) *
        (Complex.exp (Real.pi * I * x * (s - y) / ((a : ℂ) * b)) *
          Complex.exp (Real.pi * I * s * (y - x) / ((a : ℂ) * b)) *
          Complex.exp (Real.pi * I * y * (x - s) / ((a : ℂ) * b))) *
        (Γr (gamma a b hb hba.le) a b r s * Γr (gamma a b hb hba.le) a b r x *
          K4 a b hb hba.le (-r) s x y) := by ring
    _ = _ := by rw [gammaMultiplier_reflection_small hb hba.le h, swap_phases_cycle]; ring

end HaagerupIzumi.GammaK4Contour
