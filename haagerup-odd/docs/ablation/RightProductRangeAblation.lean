module

public import HaagerupIzumi.Analytic.RightProduct

/-!
# A sharp range failure in the right-product residue calculation

Keep the original gamma function and set `n = 3`, `g = 1`, `h = 4`,
`l = 1`, `k = v = 0`.  Of the ordered-range hypotheses in
`Concrete.right_residue_sum`, only `g + h < n` fails.

The three integer samples are `-6, -5, -4`.  At the middle sample, both
interpolation corrections occur: `4` and `1` represent the same element of
`ZMod 3`.  The displayed formula nevertheless tests the integer equality
`h = l`, so it omits the product of the two corrections, namely `ω₂ ^ 2`.

The statements below use the actual `tz` and `Rz` gamma ratios.  They do
not replace those ratios by an artificial model.  The raw residue bridge
also proves that the missing normalized term has a nonzero multiplier.
-/

@[expose] public section

open Complex Real ZMod Finset

namespace HaagerupIzumi.Concrete.RangeAblation

open Periods

variable (G : HypGamma (ω₁ 3) (ω₂ 3))

noncomputable abbrev B : ZMod 3 → ZMod 3 → ℂ :=
  (toCoeffData 3 (by decide) G (by decide)).B

private lemma negative_sample_zero : tz 3 G (-2) (-6) = B G 0 1 := by
  have h1 := tz_add_n 3 (by decide) G (by decide) (-2) (-6)
    (by norm_num) (by norm_num)
  have h2 := tz_add_n 3 (by decide) G (by decide) (-2) (-3)
    (by norm_num) (by norm_num)
  have h3 := tz_neg_nonneg 3 (by decide) G (by decide) 2
    (by decide) (by decide) 0 (by decide)
  norm_num at h1 h2 h3
  exact h1.symm.trans (h2.symm.trans h3)

private lemma negative_sample_one :
    tz 3 G (-2) (-5) = B G 1 1 + (ω₂ 3 : ℂ) := by
  have h1 := tz_add_n 3 (by decide) G (by decide) (-2) (-5)
    (by norm_num) (by norm_num)
  have h2 := tz_neg_neg 3 (by decide) G (by decide) 2
    (by decide) (by decide) 2 (by decide) (by decide)
  norm_num at h1 h2
  exact h1.symm.trans h2

private lemma negative_sample_two : tz 3 G (-2) (-4) = B G 2 1 := by
  have h1 := tz_add_n 3 (by decide) G (by decide) (-2) (-4)
    (by norm_num) (by norm_num)
  have h2 := tz_add_n 3 (by decide) G (by decide) (-2) (-1)
    (by norm_num) (by norm_num)
  have h3 := tz_neg_nonneg 3 (by decide) G (by decide) 2
    (by decide) (by decide) 2 (by decide)
  norm_num at h1 h2 h3
  exact h1.symm.trans (h2.symm.trans h3)

private lemma positive_sample_zero : tz 3 G 1 0 = B G 0 1 := by
  have h := tz_pos 3 (by decide) G (by decide) 1
    (by decide) (by decide) 0 (by decide)
  simpa using h

private lemma positive_sample_one : tz 3 G 1 1 = B G 1 1 + (ω₂ 3 : ℂ) := by
  have h := tz_pos 3 (by decide) G (by decide) 1
    (by decide) (by decide) 1 (by decide)
  simpa using h

private lemma positive_sample_two : tz 3 G 1 2 = B G 2 1 := by
  have h := tz_pos 3 (by decide) G (by decide) 1
    (by decide) (by decide) 2 (by decide)
  simpa using h

/-- Removing only the strict lower sample bound already loses one correction. -/
theorem lower_window_endpoint_defect :
    tz 3 G (-2) (-5) -
      (B G ((-5 : ℤ) : ZMod 3) ((-2 : ℤ) : ZMod 3) +
        (ω₂ 3 : ℂ) * (if (-5 : ℤ) = -2 then 1 else 0)) = (ω₂ 3 : ℂ) := by
  rw [negative_sample_one]
  norm_num
  rw [show (-5 : ZMod 3) = 1 by decide, show (-2 : ZMod 3) = 1 by decide]
  ring

/-- The original sample window's other bounds hold at this counterexample. -/
theorem lower_window_retained_hypotheses :
    1 ≤ (2 : ℕ) ∧ 2 ≤ 3 - 1 ∧ (-5 : ℤ) ≤ 3 - 1 ∧
      ¬ (-(3 : ℤ) - 2 < -5) := by decide

/-- The actual normalized residue sum, before expanding the sample corrections. -/
noncomputable def actualNormalized : ℂ :=
  tz 3 G (-2) (-6) * tz 3 G 1 0 +
  tz 3 G (-2) (-5) * tz 3 G 1 1 +
  tz 3 G (-2) (-4) * tz 3 G 1 2

/-- The bracket displayed by `right_residue_sum` at these parameter values.
Its cross term vanishes because `h = 4` and `l = 1` are different integers. -/
noncomputable def claimedNormalized : ℂ :=
  (∑ a : ZMod 3, B G a 1 * B G a 1) +
    (ω₂ 3 : ℂ) * B G 1 1 + (ω₂ 3 : ℂ) * B G 1 1

private lemma sum_three :
    (∑ a : ZMod 3, B G a 1 * B G a 1) =
      B G 0 1 * B G 0 1 + B G 1 1 * B G 1 1 + B G 2 1 * B G 2 1 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Exactly one product of correction terms is missing. -/
theorem normalized_residue_defect :
    actualNormalized G - claimedNormalized G = (ω₂ 3 : ℂ) ^ 2 := by
  unfold actualNormalized claimedNormalized
  rw [negative_sample_zero, negative_sample_one, negative_sample_two,
    positive_sample_zero, positive_sample_one, positive_sample_two, sum_three]
  ring

theorem normalized_residue_failure : actualNormalized G ≠ claimedNormalized G := by
  intro heq
  have h := normalized_residue_defect G
  rw [heq, sub_self] at h
  have hb : (ω₂ 3 : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos 3).ne'
  exact (pow_ne_zero 2 hb) h.symm

/-- The common multiplier in `right_residue_sum` at `p = -2`, `q = 1`, `s = 6`. -/
noncomputable def rawPrefactor : ℂ :=
  -(d 3 : ℂ) * F 3 G (-2) * F 3 G 1

theorem rawPrefactor_ne_zero : rawPrefactor G ≠ 0 := by
  have hd : (d 3 : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero 3
  have hp := F_int_ne_zero 3 (by decide) G (-2)
  have hq := F_int_ne_zero 3 (by decide) G 1
  norm_num at hp hq
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hd) hp) hq

theorem rawPrefactor_eq_square : rawPrefactor G = (d 3 : ℂ) * F 3 G 1 ^ 2 := by
  have h := F_int_add_n 3 (by decide) G (-2) (by norm_num)
  norm_num at h
  unfold rawPrefactor
  rw [h]
  ring

private lemma ratio_eq_sample (p a : ℤ) :
    Rz 3 G p (a : ℂ) = tz 3 G p a *
      (Real.sqrt (d 3) * F 3 G p) * (-1 : ℂ) ^ (p * (a + 1)) := by
  have hd0 := sqrt_d_ne_zero 3
  have hp := F_int_ne_zero 3 (by decide) G p
  have hs := neg_one_zpow_sq (p * (a + 1))
  unfold tz
  field_simp
  linear_combination (-(Rz 3 G p (a : ℂ))) * hs

/-- The three genuine integer residues on the left side of `right_residue_sum`.
Here `θ = 0`, and the integer signs are `+1, -1, +1`. -/
noncomputable def actualRaw : ℂ :=
  Rz 3 G (-2) (-6) * Rz 3 G 1 0 -
  Rz 3 G (-2) (-5) * Rz 3 G 1 1 +
  Rz 3 G (-2) (-4) * Rz 3 G 1 2

/-- An exact bridge from the actual gamma residues to the normalized samples. -/
theorem actualRaw_eq_prefactor_mul :
    actualRaw G = rawPrefactor G * actualNormalized G := by
  have h00 := ratio_eq_sample G (-2) (-6)
  have h01 := ratio_eq_sample G 1 0
  have h10 := ratio_eq_sample G (-2) (-5)
  have h11 := ratio_eq_sample G 1 1
  have h20 := ratio_eq_sample G (-2) (-4)
  have h21 := ratio_eq_sample G 1 2
  norm_num at h00 h01 h10 h11 h20 h21
  unfold actualRaw actualNormalized
  rw [h00, h01, h10, h11, h20, h21]
  unfold rawPrefactor
  rw [← sqrt_d_sq 3]
  ring

/-- The failed residue formula has an explicit nonzero error. -/
theorem raw_residue_defect :
    actualRaw G - rawPrefactor G * claimedNormalized G =
      rawPrefactor G * (ω₂ 3 : ℂ) ^ 2 := by
  rw [actualRaw_eq_prefactor_mul, ← mul_sub, normalized_residue_defect]

theorem raw_residue_failure : actualRaw G ≠ rawPrefactor G * claimedNormalized G := by
  intro heq
  have h := raw_residue_defect G
  rw [heq, sub_self] at h
  have hb : (ω₂ 3 : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos 3).ne'
  exact (mul_ne_zero (rawPrefactor_ne_zero G) (pow_ne_zero 2 hb)) h.symm

/-- The left side of `Concrete.right_residue_sum`, with the literal substitutions
`n = 3`, `g = 1`, `h = 4`, `l = 1`, and `k = v = 0`. -/
noncomputable def originalLHS : ℂ :=
  ∑ a : ZMod 3, (-1 : ℂ) ^ ((a.val : ℤ) - ((1 + 4 + 1 : ℕ) : ℤ)) *
    Complex.exp (-I * (θL 3 (0 : ℤ)) * wR 3 1 4 1 a) *
    (Rz 3 G (pR 1 1) (wR 3 1 4 1 a) *
      Rz 3 G (qR 1) (wR 3 1 4 1 a + (sR 1 4 1)))

/-- The right side of that same literal substitution in `right_residue_sum`.
`B G` is only an abbreviation for its original `toCoeffData` coefficient matrix. -/
noncomputable def originalRHS : ℂ :=
  (-1 : ℂ) ^ ((pR 1 1) + (qR 1) + (qR 1) * (sR 1 4 1)) *
    (d 3 * F 3 G (pR 1 1) * F 3 G (qR 1)) *
    ((∑ b : ZMod 3, ZMod.stdAddChar (-(b * ((0 : ℤ) : ZMod 3))) *
        B G b (-((1 + 1 : ℕ) : ZMod 3)) *
        B G (b + ((1 + 4 + 1 : ℕ) : ZMod 3)) (1 : ZMod 3)) +
      ω₂ 3 * Complex.exp (2 * π * I * (0 : ℤ) * ((1 + 1 : ℕ) : ℂ) / 3) *
        B G (4 : ZMod 3) (1 : ZMod 3) +
      ω₂ 3 * Complex.exp (2 * π * I * (0 : ℤ) * ((1 + 4 : ℕ) : ℂ) / 3) *
        B G (-((1 + 4 : ℕ) : ZMod 3)) (-((1 + 1 : ℕ) : ZMod 3)) +
      ω₂ 3 ^ 2 * (if (4 : ℕ) = 1 then 1 else 0) *
        Complex.exp (2 * π * I * (0 : ℤ) * ((1 + 1 : ℕ) : ℂ) / 3))

/-- The explicit raw residue expression is exactly the original theorem's left side. -/
theorem originalLHS_eq_actualRaw : originalLHS G = actualRaw G := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have hv0 : (0 : ZMod 3).val = 0 := by decide
  have hv1 : (1 : ZMod 3).val = 1 := by decide
  have hv2 : (2 : ZMod 3).val = 2 := by decide
  unfold originalLHS
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [wR, hv0, hv1, hv2]
  norm_num [actualRaw, θL, pR, qR, sR] <;> ring

/-- The normalized claimed expression is exactly the original theorem's right side. -/
theorem originalRHS_eq_prefactor_mul :
    originalRHS G = rawPrefactor G * claimedNormalized G := by
  norm_num [originalRHS, rawPrefactor, claimedNormalized, pR, qR, sR]
  left
  simp only [show (-2 : ZMod 3) = 1 by decide,
    show (-5 : ZMod 3) = 1 by decide, show (4 : ZMod 3) = 1 by decide,
    show (6 : ZMod 3) = 0 by decide, add_zero]

/-- The exact original `right_residue_sum` statement has this nonzero defect after
only its ordered-range hypothesis has been removed. -/
theorem original_right_residue_sum_defect :
    originalLHS G - originalRHS G = rawPrefactor G * (ω₂ 3 : ℂ) ^ 2 := by
  rw [originalLHS_eq_actualRaw, originalRHS_eq_prefactor_mul]
  exact raw_residue_defect G

theorem original_right_residue_sum_false : originalLHS G ≠ originalRHS G := by
  rw [originalLHS_eq_actualRaw, originalRHS_eq_prefactor_mul]
  exact raw_residue_failure G

/-- Only the ordered upper range is deleted; the other integer hypotheses survive. -/
theorem retained_right_product_hypotheses :
    Odd (3 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (4 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (4 : ℕ) ∧
      ¬ ((1 : ℕ) + 4 < 3) ∧
      (2 * 3 : ℤ) ∣ 0 - (2 * 0 - 3 * (1 + 1)) := by decide

end HaagerupIzumi.Concrete.RangeAblation

#print axioms HaagerupIzumi.Concrete.RangeAblation.raw_residue_defect
#print axioms HaagerupIzumi.Concrete.RangeAblation.raw_residue_failure
#print axioms HaagerupIzumi.Concrete.RangeAblation.original_right_residue_sum_false
