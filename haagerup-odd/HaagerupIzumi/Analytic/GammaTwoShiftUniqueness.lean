module

public import HaagerupIzumi.Analytic.GammaTwoContourShifts
import all Mathlib.Data.Complex.Basic

/-!
# Finite propagation of the two-gamma Fourier identity

The two parameter shifts form a nonsingular two-by-two system whenever the
parameter sum has nonpositive real part and is not a pole. Moving the Fourier
parameter half a period towards the real axis keeps that system inside its
convergence domain. Induction then propagates an identity from positive sums
to every non-pole sum in the full convergence domain.
-/

@[expose] public section
noncomputable section

open Complex
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaTwoFourier

def SatisfiesTwoShifts (a b : ℝ) (F : ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ f h y, f + h ∉ poleLattice a b →
    |y.im| < (a + b - f.re - h.re - b) / 2 →
    (I * F (f + b) h y = Complex.exp (Real.pi * I * f / a) * F f h (y + b * I / 2) -
      Complex.exp (-(Real.pi * I * f / a)) * F f h (y - b * I / 2)) ∧
    (I * F f (h + b) y = Complex.exp (Real.pi * I * h / a) * F f h (y - b * I / 2) -
      Complex.exp (-(Real.pi * I * h / a)) * F f h (y + b * I / 2))

lemma two_shift_linear_system (p q r s Xp Xm Yp Ym : ℂ)
    (hd : p * r - q * s ≠ 0)
    (h₁ : p * Xp - q * Xm = p * Yp - q * Ym)
    (h₂ : r * Xm - s * Xp = r * Ym - s * Yp) :
    Xp = Yp ∧ Xm = Ym := by
  have hplus : (p * r - q * s) * (Xp - Yp) = 0 := by
    linear_combination r * h₁ + q * h₂
  have hminus : (p * r - q * s) * (Xm - Ym) = 0 := by
    linear_combination s * h₁ + p * h₂
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hplus).resolve_left hd),
    sub_eq_zero.mp ((mul_eq_zero.mp hminus).resolve_left hd)⟩

lemma two_shift_determinant_ne_zero {a b : ℝ} (ha : 0 < a) (f h : ℂ)
    (hsum : f.re + h.re ≤ 0) (hnp : f + h ∉ poleLattice a b) :
    Complex.exp (Real.pi * I * f / a) * Complex.exp (Real.pi * I * h / a) -
      Complex.exp (-(Real.pi * I * f / a)) * Complex.exp (-(Real.pi * I * h / a)) ≠ 0 := by
  have hf : factor a (f + h) ≠ 0 := by
    intro hz
    apply hnp
    apply mem_poleLattice_of_factor_eq_zero ha (f + h) 0
    · simp only [Nat.cast_zero, zero_mul, add_zero, add_re]
      linarith
    · simpa only [Nat.cast_zero, zero_mul, add_zero] using hz
  rw [← Complex.exp_add, ← Complex.exp_add,
    show Real.pi * I * f / a + Real.pi * I * h / a = Real.pi * I * (f + h) / a by ring,
    show -(Real.pi * I * f / a) + -(Real.pi * I * h / a) =
      -(Real.pi * I * (f + h) / a) by ring, ← I_mul_factor]
  exact mul_ne_zero I_ne_zero hf

/-- Agreement on positive parameter sums and the two shift equations uniquely
determine the full transform. No analytic continuation hypothesis is needed. -/
theorem eq_of_satisfiesTwoShifts {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (F G : ℂ → ℂ → ℂ → ℂ) (hF : SatisfiesTwoShifts a b F)
    (hG : SatisfiesTwoShifts a b G)
    (hbase : ∀ f h y, 0 < f.re + h.re →
      |y.im| < (a + b - f.re - h.re) / 2 → F f h y = G f h y)
    (f h y : ℂ) (hnp : f + h ∉ poleLattice a b)
    (hc : |y.im| < (a + b - f.re - h.re) / 2) : F f h y = G f h y := by
  suffices hall : ∀ n : ℕ, ∀ f h y : ℂ, -(n : ℝ) * b < f.re + h.re →
      f + h ∉ poleLattice a b →
      |y.im| < (a + b - f.re - h.re) / 2 → F f h y = G f h y by
    obtain ⟨n, hn⟩ := exists_nat_gt (-(f.re + h.re) / b)
    have hn' := (div_lt_iff₀ hb).mp hn
    exact hall n f h y (by linarith) hnp hc
  intro n
  induction n with
  | zero =>
    intro f h y hn _ hc
    apply hbase f h y _ hc
    simpa only [Nat.cast_zero, neg_zero, zero_mul] using hn
  | succ n ih =>
    intro f h y hn hnp hc
    by_cases hpos : 0 < f.re + h.re
    · exact hbase f h y hpos hc
    have hsum : f.re + h.re ≤ 0 := le_of_not_gt hpos
    have hdet := two_shift_determinant_ne_zero (hb.trans hba) f h hsum hnp
    have hbound₁ : -(n : ℝ) * b < (f + (b : ℂ)).re + h.re := by
      simp only [add_re, ofReal_re]
      push_cast at hn
      nlinarith
    have hbound₂ : -(n : ℝ) * b < f.re + (h + (b : ℂ)).re := by
      simp only [add_re, ofReal_re]
      push_cast at hn
      nlinarith
    have hpair : ∀ v : ℂ, |v.im| < (a + b - f.re - h.re - b) / 2 →
        F f h (v + b * I / 2) = G f h (v + b * I / 2) ∧
        F f h (v - b * I / 2) = G f h (v - b * I / 2) := by
      intro v hv
      have he₁ := ih (f + b) h v hbound₁ (noPinch_shift_first hnp)
        (by simp only [add_re, ofReal_re]; linarith)
      have he₂ := ih f (h + b) v hbound₂ (noPinch_shift_second hnp)
        (by simp only [add_re, ofReal_re]; linarith)
      have hFv := hF f h v hnp hv
      have hGv := hG f h v hnp hv
      apply two_shift_linear_system _ _ _ _ _ _ _ _ hdet
      · exact hFv.1.symm.trans ((congrArg (I * ·) he₁).trans hGv.1)
      · exact hFv.2.symm.trans ((congrArg (I * ·) he₂).trans hGv.2)
    by_cases hy : 0 ≤ y.im
    · have hv : |(y - (b : ℂ) * I / 2).im| <
          (a + b - f.re - h.re - b) / 2 := by
        simp only [sub_im, div_ofNat_im, mul_im, ofReal_re, I_im, mul_one,
          ofReal_im, I_re, mul_zero, add_zero]
        rw [abs_of_nonneg hy] at hc
        apply abs_lt.mpr
        constructor <;> linarith
      have he := (hpair (y - b * I / 2) hv).1
      rwa [show y - (b : ℂ) * I / 2 + b * I / 2 = y by ring] at he
    · have hy' : y.im ≤ 0 := le_of_not_ge hy
      have hv : |(y + (b : ℂ) * I / 2).im| <
          (a + b - f.re - h.re - b) / 2 := by
        simp only [add_im, div_ofNat_im, mul_im, ofReal_re, I_im, mul_one,
          ofReal_im, I_re, mul_zero, add_zero]
        rw [abs_of_nonpos hy'] at hc
        apply abs_lt.mpr
        constructor <;> linarith
      have he := (hpair (y + b * I / 2) hv).2
      rwa [show y + (b : ℂ) * I / 2 - b * I / 2 = y by ring] at he

end HaagerupIzumi.GammaTwoFourier
