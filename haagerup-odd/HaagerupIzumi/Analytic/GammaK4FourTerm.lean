module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaFourTermContours
public import HaagerupIzumi.Analytic.GammaK4Swap

/-!
# The concrete four-term identity

For unequal integer labels the pointwise primitive identity is integrated
on a common corrected contour. Equal labels cancel in pairs by parameter
interchange. Both period relations are explicit in the theorem.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

lemma fourTermExp_mul (a b : ℝ) (Z x y : ℂ) :
    fourTermExp a b Z x * fourTermExp a b Z y = fourTermExp a b Z (x + y) := by
  rw [fourTermExp_add]
  ring

lemma fourTerm_swap_shift (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (R X Z c : ℂ) (hconv : K4Conv a b R Z)
    (hnp : K4NoPinch a b R (X + c) X) :
    K4 a b hb hba R (X + c) X Z =
      fourTermExp a b Z (c / 2) * K4 a b hb hba R X (X + c) Z := by
  have h := K4_swap a b hb hba hirr R (X + c) X Z hconv hnp
  convert h using 1
  unfold fourTermExp
  congr 1
  congr 1
  ring

lemma fourTerm_equal_labels (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (R X Z : ℂ) (g l : ℕ) (hconv : K4Conv a b R Z)
    (hnp₃ : K4NoPinch a b R (X - a) X) (hnp₄ : K4NoPinch a b R (X + b) X) :
    0 = periodSin a (l : ℂ) * K4 a b hb hba R X (X + b) Z +
      (-1 : ℂ) ^ (g + l + 1) * periodSin a ((g + l : ℕ) : ℂ) *
        fourTermExp a b Z (-a) * K4 a b hb hba R X (X - a) Z +
      (-1 : ℂ) ^ (g + l) * periodSin a ((g + l : ℕ) : ℂ) *
        fourTermExp a b Z (-a / 2) * K4 a b hb hba R (X - a) X Z -
      periodSin a (l : ℂ) * fourTermExp a b Z (-b / 2) * K4 a b hb hba R (X + b) X Z := by
  have h₃ : K4 a b hb hba R (X - a) X Z =
      fourTermExp a b Z (-a / 2) * K4 a b hb hba R X (X - a) Z := by
    simpa only [sub_eq_add_neg] using
      fourTerm_swap_shift a b hb hba hirr R X Z (-a) hconv (by simpa only [sub_eq_add_neg] using hnp₃)
  have h₄ := fourTerm_swap_shift a b hb hba hirr R X Z (b : ℂ) hconv hnp₄
  have hA : fourTermExp a b Z (-a / 2) * fourTermExp a b Z (-a / 2) =
      fourTermExp a b Z (-a) := by
    rw [fourTermExp_mul]
    congr 1
    ring
  have hB : fourTermExp a b Z (-b / 2) * fourTermExp a b Z (b / 2) = 1 := by
    rw [fourTermExp_mul, show -(b : ℂ) / 2 + b / 2 = 0 by ring]
    simp only [fourTermExp, mul_zero, zero_div, Complex.exp_zero]
  rw [h₃, h₄, pow_succ]
  linear_combination -((-1 : ℂ) ^ (g + l) * periodSin a ((g + l : ℕ) : ℂ) *
      K4 a b hb hba R X (X - a) Z) * hA +
    (periodSin a (l : ℂ) * K4 a b hb hba R X (X + b) Z) * hB

/-- The full four-term identity for the explicitly constructed K4, with
the two normalization relations required in Chapter 7. -/
theorem K4_four_term_sine (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (n g h l : ℕ) (Z : ℂ)
    (hdiff : a - b = n) (hnorm : a * b = a + b)
    (hg : 1 ≤ g) (hh : 1 ≤ h) (hgh : g + h < n) (hl : 1 ≤ l) (hlh : l ≤ h)
    (hZ : |Z.re| < (a + b - g) / 2)
    (hnp₁ : K4NoPinch a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l)
      (((n + g : ℕ) : ℂ) / 2 + h + b))
    (hnp₂ : K4NoPinch a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l)
      (((n + g : ℕ) : ℂ) / 2 + h - a))
    (hnp₃ : K4NoPinch a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l - a)
      (((n + g : ℕ) : ℂ) / 2 + h))
    (hnp₄ : K4NoPinch a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l + b)
      (((n + g : ℕ) : ℂ) / 2 + h)) :
    let R : ℂ := (g : ℂ) / 2
    let X : ℂ := ((n + g : ℕ) : ℂ) / 2 + l
    let Y : ℂ := ((n + g : ℕ) : ℂ) / 2 + h
    0 = periodSin a (h : ℂ) * K4 a b hb hba R X (Y + b) Z +
      (-1 : ℂ) ^ (g + l + 1) * periodSin a ((g + h : ℕ) : ℂ) *
        fourTermExp a b Z (-a) * K4 a b hb hba R X (Y - a) Z +
      (-1 : ℂ) ^ (g + h) * periodSin a ((g + l : ℕ) : ℂ) *
        fourTermExp a b Z (-a / 2) * K4 a b hb hba R (X - a) Y Z -
      periodSin a (l : ℂ) * fourTermExp a b Z (-b / 2) * K4 a b hb hba R (X + b) Y Z := by
  let R : ℂ := (g : ℂ) / 2
  let X : ℂ := ((n + g : ℕ) : ℂ) / 2 + l
  let Y : ℂ := ((n + g : ℕ) : ℂ) / 2 + h
  have hconv : K4Conv a b R Z := by
    unfold K4Conv R
    norm_num
    linarith
  rcases lt_or_eq_of_le hlh with hlt | heq
  · have ha : 0 < a := lt_of_lt_of_le hb hba
    have hc : (a : ℂ) - b = (n : ℂ) := by exact_mod_cast hdiff
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hba' : b < a := by linarith
    have hb₂ : b < 2 := by
      apply (mul_lt_mul_iff_right₀ ha).mp
      nlinarith [hnorm]
    obtain ⟨hu, hv⟩ := fourTerm_center_specialization a b n g l hdiff
    have hc₁ : 2 * k4U a b R X - a - b ∉ poleLattice a b := by
      rw [show 2 * k4U a b R X - a - b = ((g + l : ℕ) : ℂ) - b by rw [hu]; ring]
      apply not_mem_poleLattice_of_re_pos ha hb
      simp only [sub_re, natCast_re, ofReal_re]
      have ht : (2 : ℝ) ≤ (g + l : ℕ) := by exact_mod_cast (show 2 ≤ g + l by omega)
      linarith
    have hc₂ : k4U a b R X + k4V a b R X - b - Y ∉ poleLattice a b := by
      rw [show k4U a b R X + k4V a b R X - b - Y =
        k4U a b R X + k4V a b R X - (Y + b) by ring]
      exact hnp₁.2.2.1
    have hc₃ : k4U a b R X + k4V a b R X - a - b + Y ∉ poleLattice a b := by
      have he : k4U a b R X + k4V a b R X - a - b + Y = ((g + h : ℕ) : ℂ) - b := by
        rw [hu, hv]
        dsimp only [Y]
        push_cast
        linear_combination -hc / 2
      rw [he]
      apply not_mem_poleLattice_of_re_pos ha hb
      simp only [sub_re, natCast_re, ofReal_re]
      have hp : (2 : ℝ) ≤ (g + h : ℕ) := by exact_mod_cast (show 2 ≤ g + h by omega)
      linarith
    have hc₄ : 2 * k4V a b R X - b ∉ poleLattice a b := by
      rw [show 2 * k4V a b R X - b = 2 * k4V a b R (X + b) by unfold k4V; ring]
      exact hnp₄.2.1
    have hct := fourTerm_contour_relation a b hb hba hirr R X Y Z
      (periodSin a ((h - l : ℕ) : ℂ)) (periodSin a (h : ℂ))
      (fourTermExp a b Z b * (-1 : ℂ) ^ (g + l + 1) * periodSin a ((g + h : ℕ) : ℂ))
      (fourTermExp a b Z b * (-1 : ℂ) ^ (g + h) * periodSin a ((g + l : ℕ) : ℂ))
      (-periodSin a (l : ℂ)) hconv hnp₁ hnp₂ hnp₃ hnp₄ hc₁ hc₂ hc₃ hc₄ (by
        intro z hζ hη hξ hν
        simpa only [neg_mul, sub_eq_add_neg] using
          fourTerm_integer_primitive a b hb hba n g h l hdiff hnorm hlt (by omega)
            (k4U a b R X) (k4V a b R X) Y Z z hu hv rfl hζ hη hξ hν)
    have hphase : fourTermExp a b Z (b / 2) =
        fourTermExp a b Z b * fourTermExp a b Z (-b / 2) := by
      rw [fourTermExp_mul]
      congr 1
      ring
    rw [hphase] at hct
    have hnz : fourTermExp a b Z b ≠ 0 := Complex.exp_ne_zero _
    apply Eq.symm
    apply (mul_eq_zero.mp (show fourTermExp a b Z b *
      (periodSin a (h : ℂ) * K4 a b hb hba R X (Y + b) Z +
        (-1 : ℂ) ^ (g + l + 1) * periodSin a ((g + h : ℕ) : ℂ) *
          fourTermExp a b Z (-a) * K4 a b hb hba R X (Y - a) Z +
        (-1 : ℂ) ^ (g + h) * periodSin a ((g + l : ℕ) : ℂ) *
          fourTermExp a b Z (-a / 2) * K4 a b hb hba R (X - a) Y Z -
        periodSin a (l : ℂ) * fourTermExp a b Z (-b / 2) * K4 a b hb hba R (X + b) Y Z) = 0 from ?_)).resolve_left hnz
    linear_combination hct
  · subst h
    exact fourTerm_equal_labels a b hb hba hirr R X Z g l hconv hnp₃ hnp₄

end HaagerupIzumi.GammaK4Contour
