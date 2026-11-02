module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaFourTermKernel

/-!
# Integer-label specialization of the four-term kernel identity

The two period relations have different roles: `a-b=n` identifies the
centered kernel parameters, while `a*b=a+b` converts the second-period sine
coefficients to signed first-period sines.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

lemma periodSin_ofReal (a x : ℝ) :
    periodSin a (x : ℂ) = (Real.sin (Real.pi * x / a) : ℂ) := by
  simp only [periodSin, Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_mul]

lemma periodSin_neg (a : ℝ) (z : ℂ) : periodSin a (-z) = -periodSin a z := by
  unfold periodSin
  rw [show (Real.pi : ℂ) * -z / a = -(Real.pi * z / a) by ring, Complex.sin_neg]

lemma periodSin_sub_period (a : ℝ) (ha : a ≠ 0) (z : ℂ) :
    periodSin a (z - a) = -periodSin a z := by
  have haC := Complex.ofReal_ne_zero.mpr ha
  unfold periodSin
  rw [show (Real.pi : ℂ) * (z - a) / a = Real.pi * z / a - Real.pi by field_simp,
    Complex.sin_sub_pi]

lemma periodSin_nat_reciprocal (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b = a + b) (m : ℕ) :
    periodSin b (m : ℂ) = (-1 : ℂ) ^ (m + 1) * periodSin a (m : ℂ) := by
  have harg : Real.pi * (m : ℝ) / b = (m : ℝ) * Real.pi - Real.pi * m / a := by
    field_simp
    linear_combination -(m : ℝ) * hab
  have hs : Real.sin (Real.pi * (m : ℝ) / b) =
      (-1 : ℝ) ^ (m + 1) * Real.sin (Real.pi * m / a) := by
    rw [harg, Real.sin_nat_mul_pi_sub, pow_succ]
    ring
  have hc := congrArg Complex.ofReal hs
  simpa only [periodSin, Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast] using hc

lemma periodSin_nat_sub_period (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b = a + b) (m : ℕ) :
    periodSin b ((m : ℂ) - b) = (-1 : ℂ) ^ m * periodSin a (m : ℂ) := by
  rw [periodSin_sub_period b hb, periodSin_nat_reciprocal a b ha hb hab, pow_succ]
  ring

lemma fourTermTerm₁_eq_kernel (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermTerm₁ γ a b (k4U a b R X) (k4V a b R X) Y Z (z + b) =
      fourTermExp a b Z b * k4Integrand γ a b R X (Y + b) Z z := by
  unfold fourTermTerm₁ k4Integrand
  rw [fourTermExp_add]
  unfold fourTermExp
  ring_nf

lemma fourTermTerm₂_eq_kernel (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermTerm₂ γ a b (k4U a b R X) (k4V a b R X) Y Z (z - a) =
      fourTermExp a b Z (-a) * k4Integrand γ a b R X (Y - a) Z z := by
  unfold fourTermTerm₂ k4Integrand
  rw [show z - (a : ℂ) = z + (-a) by ring, fourTermExp_add]
  unfold fourTermExp
  ring_nf

lemma fourTermTerm₃_eq_kernel (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermTerm₃ γ a b (k4U a b R X) (k4V a b R X) Y Z (z - a / 2) =
      fourTermExp a b Z (-a / 2) * k4Integrand γ a b R (X - a) Y Z z := by
  unfold fourTermTerm₃ k4Integrand
  rw [show z - (a : ℂ) / 2 = z + (-a / 2) by ring, fourTermExp_add]
  unfold fourTermExp k4U k4V
  push_cast
  ring_nf

lemma fourTermTerm₄_eq_kernel (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermTerm₄ γ a b (k4U a b R X) (k4V a b R X) Y Z (z + b / 2) =
      fourTermExp a b Z (b / 2) * k4Integrand γ a b R (X + b) Y Z z := by
  unfold fourTermTerm₄ k4Integrand
  rw [fourTermExp_add]
  unfold fourTermExp k4U k4V
  push_cast
  ring_nf

/-- The primitive is a translate of the original centered kernel, so its
finite difference has zero corrected contour integral by translation. -/
lemma fourTermPrimitive_eq_kernel (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermPrimitive γ a b (k4U a b R X) (k4V a b R X) Y Z (z + b) =
      fourTermExp a b Z b * k4Integrand γ a b R X Y Z z := by
  unfold fourTermPrimitive k4Integrand
  rw [fourTermExp_add]
  unfold fourTermExp
  ring_nf

lemma fourTermPrimitive_difference (γ : ℂ → ℂ) (a b : ℝ) (R X Y Z z : ℂ) :
    fourTermPrimitive γ a b (k4U a b R X) (k4V a b R X) Y Z (z + b) -
        fourTermPrimitive γ a b (k4U a b R X) (k4V a b R X) Y Z z =
      fourTermExp a b Z b *
        (k4Integrand γ a b R X Y Z z - k4Integrand γ a b R X Y Z (z - b)) := by
  rw [fourTermPrimitive_eq_kernel,
    show fourTermPrimitive γ a b (k4U a b R X) (k4V a b R X) Y Z z =
        fourTermExp a b Z b * k4Integrand γ a b R X Y Z (z - b) by
      simpa only [sub_add_cancel] using fourTermPrimitive_eq_kernel γ a b R X Y Z (z - b)]
  ring

/-- The no-pinch hypotheses for the first and third shifted kernels imply
the condition needed for the primitive's original centered kernel. -/
lemma fourTerm_base_noPinch (a b : ℝ) (r s x : ℂ)
    (h₁ : K4NoPinch a b r s (x + b)) (h₃ : K4NoPinch a b r (s - a) x) :
    K4NoPinch a b r s x := by
  have he : k4U a b r (s - a) + k4V a b r (s - a) =
      k4U a b r s + k4V a b r s := by unfold k4U k4V; ring
  refine ⟨h₁.1, h₁.2.1, ?_, ?_⟩
  · simpa only [he] using h₃.2.2.1
  · simpa only [he] using h₃.2.2.2

/-- The integer specialization of the two centered gamma parameters. -/
lemma fourTerm_center_specialization (a b : ℝ) (n g l : ℕ) (hdiff : a - b = n) :
    k4U a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l) =
      (a : ℂ) / 2 + ((g + l : ℕ) : ℂ) / 2 ∧
    k4V a b ((g : ℂ) / 2) (((n + g : ℕ) : ℂ) / 2 + l) =
      (b : ℂ) / 2 - (l : ℂ) / 2 := by
  have hc : (a : ℂ) - b = (n : ℂ) := by exact_mod_cast hdiff
  unfold k4U k4V
  push_cast
  constructor
  · linear_combination -hc / 4
  · linear_combination hc / 4

lemma fourTerm_sign_second (g h l : ℕ) (hlh : l ≤ h) :
    (-1 : ℂ) ^ (g + h) = (-1 : ℂ) ^ (g + l + 1) * (-1 : ℂ) ^ (h - l + 1) := by
  rw [← pow_add, show g + l + 1 + (h - l + 1) = g + h + 2 by omega]
  simp only [pow_add]
  norm_num

lemma fourTerm_sign_third (g h l : ℕ) (hlh : l ≤ h) :
    -(-1 : ℂ) ^ (g + l) = (-1 : ℂ) ^ (g + h) * (-1 : ℂ) ^ (h - l + 1) := by
  rw [← pow_add, show g + h + (h - l + 1) = g + l + 1 + 2 * (h - l) by omega]
  simp [pow_add, pow_mul]

/-- After clearing the first-period sine denominator, the four coefficients
are precisely the signed coefficients in Chapter 7. -/
lemma fourTerm_specialized_coefficients (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b = a + b) (g h l : ℕ) (hlh : l ≤ h) (lam : ℂ)
    (hD : periodSin a ((h - l : ℕ) : ℂ) ≠ 0) :
    periodSin a ((h - l : ℕ) : ℂ) *
        (lam * periodSin b (((g + h : ℕ) : ℂ) - b) /
          periodSin b ((h - l : ℕ) : ℂ)) =
      lam * (-1 : ℂ) ^ (g + l + 1) * periodSin a ((g + h : ℕ) : ℂ) ∧
    periodSin a ((h - l : ℕ) : ℂ) *
        (-lam * periodSin b (((g + l : ℕ) : ℂ) - b) /
          periodSin b ((h - l : ℕ) : ℂ)) =
      lam * (-1 : ℂ) ^ (g + h) * periodSin a ((g + l : ℕ) : ℂ) := by
  rw [periodSin_nat_sub_period a b ha hb hab,
    periodSin_nat_sub_period a b ha hb hab, periodSin_nat_reciprocal a b ha hb hab]
  have hsign : (-1 : ℂ) ^ (h - l + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h₂ := fourTerm_sign_second g h l hlh
  have h₃ := fourTerm_sign_third g h l hlh
  constructor
  · rw [h₂]
    field_simp
  · have he : -lam * ((-1 : ℂ) ^ (g + l) * periodSin a ((g + l : ℕ) : ℂ)) =
        lam * ((-(-1 : ℂ) ^ (g + l)) * periodSin a ((g + l : ℕ) : ℂ)) := by ring
    rw [he, h₃]
    field_simp

/-- The specialized pointwise primitive identity for `l<h`. Together with
the four translation lemmas above, its coefficients are exactly those of
the four-term contour identity. -/
theorem fourTerm_integer_primitive (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (n g h l : ℕ) (hdiff : a - b = n) (hnorm : a * b = a + b)
    (hlh : l < h) (hhn : h < n) (u v Y Z z : ℂ)
    (hu : u = (a : ℂ) / 2 + ((g + l : ℕ) : ℂ) / 2)
    (hv : v = (b : ℂ) / 2 - (l : ℂ) / 2)
    (hY : Y = ((n + g : ℕ) : ℂ) / 2 + h)
    (hζ : u - b + z ∉ poleLattice a b) (hη : u - a - z ∉ poleLattice a b)
    (hξ : v - b + Y + z ∉ poleLattice a b) (hν : v - Y - z ∉ poleLattice a b) :
    periodSin a (h : ℂ) * fourTermTerm₁ (gamma a b hb hba) a b u v Y Z z +
      (fourTermExp a b Z b * (-1 : ℂ) ^ (g + l + 1) *
          periodSin a ((g + h : ℕ) : ℂ)) *
        fourTermTerm₂ (gamma a b hb hba) a b u v Y Z z +
      (fourTermExp a b Z b * (-1 : ℂ) ^ (g + h) *
          periodSin a ((g + l : ℕ) : ℂ)) *
        fourTermTerm₃ (gamma a b hb hba) a b u v Y Z z -
      periodSin a (l : ℂ) * fourTermTerm₄ (gamma a b hb hba) a b u v Y Z z =
    periodSin a ((h - l : ℕ) : ℂ) *
      (fourTermPrimitive (gamma a b hb hba) a b u v Y Z (z + b) -
        fourTermPrimitive (gamma a b hb hba) a b u v Y Z z) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hc : (a : ℂ) - b = (n : ℂ) := by exact_mod_cast hdiff
  have hD : v + Y - u = ((h - l : ℕ) : ℂ) := by
    rw [hu, hv, hY, Nat.cast_sub hlh.le]
    push_cast
    linear_combination -hc / 2
  have hA : u + v - b - Y = -(h : ℂ) := by
    rw [hu, hv, hY]
    push_cast
    linear_combination hc / 2
  have hB : u + v - a - b + Y = ((g + h : ℕ) : ℂ) - b := by
    rw [hu, hv, hY]
    push_cast
    linear_combination -hc / 2
  have hC : 2 * u - a - b = ((g + l : ℕ) : ℂ) - b := by rw [hu]; ring
  have hE : 2 * v - b = -(l : ℂ) := by rw [hv]; ring
  have hdpos : (0 : ℝ) < ((h - l : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hlh)
  have hdlt : ((h - l : ℕ) : ℝ) < a := by
    have hh : (h : ℝ) < n := by exact_mod_cast hhn
    have hdle : ((h - l : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.sub_le h l
    linarith
  have hDa : periodSin a ((h - l : ℕ) : ℂ) ≠ 0 := by
    simpa only [periodSin, mul_div_assoc, Complex.ofReal_natCast] using
      GammaIntegral.sin_shift_ne_zero a (((h - l : ℕ) : ℝ) : ℂ) ha hdpos hdlt
  have hDb : periodSin b ((h - l : ℕ) : ℂ) ≠ 0 := by
    rw [periodSin_nat_reciprocal a b ha.ne' hb.ne' hnorm]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hDa
  have hp := fourTerm_primitive a b hb hba u v Y Z z hζ hη hξ hν
    (by rwa [hD]) (by rwa [hD])
  rw [hD, hA, hB, hC, hE] at hp
  obtain ⟨h₂, h₃⟩ := fourTerm_specialized_coefficients a b ha.ne' hb.ne' hnorm
    g h l hlh.le (fourTermExp a b Z b) hDa
  have h₁ : periodSin a ((h - l : ℕ) : ℂ) *
      (-periodSin a (-(h : ℂ)) / periodSin a ((h - l : ℕ) : ℂ)) = periodSin a (h : ℂ) := by
    rw [periodSin_neg]
    field_simp
  have h₄ : periodSin a ((h - l : ℕ) : ℂ) *
      (periodSin a (-(l : ℂ)) / periodSin a ((h - l : ℕ) : ℂ)) = -periodSin a (l : ℂ) := by
    rw [periodSin_neg]
    field_simp
  have hm := congrArg (fun w : ℂ => periodSin a ((h - l : ℕ) : ℂ) * w) hp
  simp only [mul_add, ← mul_assoc] at hm
  rw [h₁, h₂, h₃, h₄] at hm
  simpa only [neg_mul, sub_eq_add_neg] using hm

end HaagerupIzumi.GammaContinuation
