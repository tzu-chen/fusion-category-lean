module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaK4FourTerm

/-! # The four-term identity in the exact hyperbolic-gamma interface notation -/

@[expose] public section
noncomputable section

open Complex
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

theorem K4_four_term (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (n g h l : ℕ) (Z : ℂ)
    (hdiff : a - b = n) (hnorm : a * b = a + b)
    (hg : 1 ≤ g) (hh : 1 ≤ h) (hgh : g + h < n) (hl : 1 ≤ l) (hlh : l ≤ h)
    (hZ : |Z.re| < (a + b - g) / 2)
    (hnp₁ : K4NoPinch a b ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l) ((n + g : ℂ) / 2 + h + b))
    (hnp₂ : K4NoPinch a b ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l) ((n + g : ℂ) / 2 + h - a))
    (hnp₃ : K4NoPinch a b ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l - a) ((n + g : ℂ) / 2 + h))
    (hnp₄ : K4NoPinch a b ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l + b) ((n + g : ℂ) / 2 + h)) :
    0 = Complex.sin (Real.pi * h / a) *
        K4 a b hb hba ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l) ((n + g : ℂ) / 2 + h + b) Z +
      (-1) ^ (g + l + 1) * Complex.sin (Real.pi * (g + h : ℕ) / a) *
        Complex.exp (-2 * Real.pi * I * Z * a / (a * b)) *
        K4 a b hb hba ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l) ((n + g : ℂ) / 2 + h - a) Z +
      (-1) ^ (g + h) * Complex.sin (Real.pi * (g + l : ℕ) / a) *
        Complex.exp (-Real.pi * I * Z * a / (a * b)) *
        K4 a b hb hba ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l - a) ((n + g : ℂ) / 2 + h) Z -
      Complex.sin (Real.pi * l / a) * Complex.exp (-Real.pi * I * Z * b / (a * b)) *
        K4 a b hb hba ((g : ℂ) / 2) ((n + g : ℂ) / 2 + l + b) ((n + g : ℂ) / 2 + h) Z := by
  have hnp₁' := hnp₁
  have hnp₂' := hnp₂
  have hnp₃' := hnp₃
  have hnp₄' := hnp₄
  simp only [← Nat.cast_add] at hnp₁' hnp₂' hnp₃' hnp₄'
  have ht := K4_four_term_sine a b hb hba hirr n g h l Z hdiff hnorm
    hg hh hgh hl hlh hZ hnp₁' hnp₂' hnp₃' hnp₄'
  dsimp only at ht
  convert ht using 1
  simp only [periodSin, fourTermExp]
  push_cast
  ring_nf

end HaagerupIzumi.GammaK4Contour
