module

public import HaagerupIzumi.Analytic.LeftProduct

/-!
# A sharp range failure in the Section 6 residue sum

Remove only `l ≤ h` from `Concrete.left_residue_sum` and take
`n = 3`, `g = h = 1`, `l = 2`, `k = v = 0`. The exact discrepancy is
`ω₂ 3 * (F 3 G 2)^2`, which is nonzero for every valid gamma interface.
All gamma values below are regular integer samples. The failed step is
the replacement of `tz (-1) 3` by the coefficient at the residue class zero.

The two expressions below are the left and right sides of that theorem
after simplifying these parameters and their zero-frequency phases.
-/

@[expose] public section

open Complex Real

namespace HaagerupIzumi.LeftProductRangeAblation

open Periods Concrete

variable (G : HypGamma (ω₁ 3) (ω₂ 3))

theorem odd_three : Odd (3 : ℕ) := by decide

/-- Every retained arithmetic hypothesis holds; exactly `l ≤ h` fails. -/
theorem retained_hypotheses :
    Odd (3 : ℕ) ∧ 1 ≤ (3 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
      (1 : ℕ) + 1 < 3 ∧ 1 ≤ (2 : ℕ) ∧
      (2 * 3 : ℤ) ∣ (0 : ℤ) - (2 * 0 + 3 * ((1 : ℕ) - 1)) ∧
      ¬ ((2 : ℕ) ≤ 1) := by
  norm_num

noncomputable abbrev coeff : CoeffData 3 ℂ :=
  toCoeffData 3 (by norm_num) G odd_three

/-- The original integer-residue sum at the chosen parameters. -/
noncomputable def actual : ℂ :=
  ∑ a : ZMod 3, (-1 : ℂ) ^ (a.val : ℤ) *
    (Rz 3 G 2 (a.val : ℂ) * Rz 3 G (-1) ((a.val : ℂ) + 1))

/-- The unchanged proposed answer from `left_residue_sum`. -/
noncomputable def proposed : ℂ :=
  (d 3 : ℂ) * F 3 G 2 * F 3 G (-1) *
    ((∑ a : ZMod 3, (coeff G).B a 2 * (coeff G).B (a + 1) 2)
      + (ω₂ 3 : ℂ) * (coeff G).B 0 2)

/-- Syntactic bridge to the left side of `left_residue_sum` at the witness. -/
theorem actual_is_original_lhs : actual G =
    ∑ a : ZMod 3, (-1 : ℂ) ^ (a.val : ℤ) *
      Complex.exp (-I * (θL 3 0) * ((a.val : ℤ) : ℂ)) *
      (Rz 3 G (pL 1 1) ((a.val : ℤ) : ℂ) *
        Rz 3 G (qL 1) (((a.val : ℤ) : ℂ) + sL 1 2)) := by
  simp [actual, θL, pL, qL, sL]

/-- Syntactic bridge to the right side of `left_residue_sum` at the witness. -/
theorem proposed_is_original_rhs : proposed G =
    (-1 : ℂ) ^ (pL 1 1 + qL 1 + qL 1 * sL 1 2) *
      (d 3 * F 3 G (pL 1 1) * F 3 G (qL 1)) *
      ((∑ a : ZMod 3, ZMod.stdAddChar (-(a * ((0 : ℤ) : ZMod 3))) *
        (coeff G).B a ((1 + 1 : ℕ) : ZMod 3) *
        (coeff G).B (a + ((sL 1 2 : ℤ) : ZMod 3)) (-(1 : ZMod 3))) +
        ω₂ 3 * Complex.exp (-(2 * π * I * (0 : ℤ) * ((1 + 1 : ℕ) : ℂ) / 3)) *
          (coeff G).B ((1 + 2 : ℕ) : ZMod 3) (-(1 : ZMod 3))) := by
  have hneg : (-(1 : ZMod 3)) = 2 := by decide
  have hthree : (3 : ZMod 3) = 0 := by decide
  norm_num [proposed, pL, qL, sL, hneg, hthree]
  left
  simp only [hneg, hthree]

private theorem small_sample_values :
    F 3 G (-1) = F 3 G 2 ∧
    F 3 G 1 = 1 / F 3 G 2 ∧
    F 3 G (-2) = -1 / F 3 G 2 ∧
    F 3 G 4 = 1 / F 3 G 2 := by
  have hf : F 3 G 2 ≠ 0 := by simpa using F_int_ne_zero 3 (by norm_num) G 2
  have hneg : F 3 G (-1) = F 3 G 2 := by
    have h := F_int_add_n 3 (by norm_num) G (-1) (by norm_num)
    norm_num at h
    exact h.symm
  have hone : F 3 G 1 = 1 / F 3 G 2 := by
    apply (eq_div_iff hf).2
    have h := F_int_mul_F_sub 3 (by norm_num) G 1
    norm_num at h
    exact h
  have hnegtwo : F 3 G (-2) = -1 / F 3 G 2 := by
    apply (eq_div_iff hf).2
    have h := F_neg_mul_F 3 (by norm_num) G 2 (by norm_num)
    norm_num at h
    exact h
  refine ⟨hneg, hone, hnegtwo, ?_⟩
  have h := F_int_add_n 3 (by norm_num) G 1 (by norm_num)
  norm_num at h
  exact h.trans hone

private theorem middle_coefficient :
    (coeff G).B 1 2 = 1 / ((Real.sqrt (d 3) : ℂ) * (F 3 G 2) ^ 3) := by
  obtain ⟨hneg, hone, _, _⟩ := small_sample_values G
  have hf : F 3 G 2 ≠ 0 := by simpa using F_int_ne_zero 3 (by norm_num) G 2
  have hr := sqrt_d_ne_zero 3
  have h := tz_pos 3 (by norm_num) G odd_three 2 (by norm_num) (by norm_num)
    1 (by norm_num)
  norm_num [tz, Rz_eq_F] at h
  rw [hneg, hone] at h
  change (toCoeffData 3 (by norm_num) G odd_three).B 1 2 = _
  rw [← h]
  field_simp [hf, hr]
  <;> ring

/-- The sample point just outside the permitted window has a nonzero correction. -/
theorem escaped_sample :
    tz 3 G (-1) 3 - (coeff G).B 0 2 = (ω₂ 3 : ℂ) := by
  obtain ⟨hneg, _, _, hfour⟩ := small_sample_values G
  have hf : F 3 G 2 ≠ 0 := by simpa using F_int_ne_zero 3 (by norm_num) G 2
  have hr := sqrt_d_ne_zero 3
  have hs := sqrt_d_sq 3
  have hB : (coeff G).B 0 2 = -1 := (coeff G).B_zero_left (by decide)
  have hthree : F 3 G 3 = ((Real.sqrt (d 3) : ℂ))⁻¹ :=
    F_n 3 (by norm_num) G
  rw [hB]
  norm_num [tz, Rz_eq_F, hneg, hthree, hfour]
  have hb : (ω₂ 3 : ℂ) = 1 + (d 3 : ℂ)⁻¹ := by
    unfold ω₂
    push_cast
    ring
  rw [hb, ← hs]
  field_simp [hf, hr]
  <;> ring

private theorem sum_three (f : ZMod 3 → ℂ) :
    (∑ a : ZMod 3, f a) = f 0 + f 1 + f 2 := by
  have hU : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hU, Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
    Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
    Finset.sum_singleton]
  ring

/-- Exact failure of the unchanged Section 6 residue-sum formula. -/
theorem exact_residue_sum_defect :
    actual G - proposed G = (ω₂ 3 : ℂ) * (F 3 G 2) ^ 2 := by
  classical
  obtain ⟨hneg, hone, hnegtwo, hfour⟩ := small_sample_values G
  have hf : F 3 G 2 ≠ 0 := by simpa using F_int_ne_zero 3 (by norm_num) G 2
  have hr := sqrt_d_ne_zero 3
  have hs := sqrt_d_sq 3
  have hzero : F 3 G 0 = (Real.sqrt (d 3) : ℂ) := F_zero 3 (by norm_num) G
  have hthree : F 3 G 3 = ((Real.sqrt (d 3) : ℂ))⁻¹ := F_n 3 (by norm_num) G
  have hB0 : (coeff G).B 0 2 = -1 := (coeff G).B_zero_left (by decide)
  have hB2 : (coeff G).B 2 2 = -1 := (coeff G).B_diag (by decide)
  have hB1 := middle_coefficient G
  have hval0 : (0 : ZMod 3).val = 0 := by decide
  have hval1 : (1 : ZMod 3).val = 1 := by decide
  have hval2 : (2 : ZMod 3).val = 2 := by decide
  have hadd1 : (1 : ZMod 3) + 1 = 2 := by decide
  have hadd2 : (2 : ZMod 3) + 1 = 0 := by decide
  have hcast3 : (3 : ZMod 3) = 0 := by decide
  unfold actual proposed
  rw [sum_three, sum_three]
  norm_num [Rz_eq_F, hneg, hone, hnegtwo, hfour, hzero, hthree,
    hB0, hB1, hB2, hval0, hval1, hval2, hadd1, hadd2]
  simp only [hcast3, hB0]
  have hb : (ω₂ 3 : ℂ) = 1 + (d 3 : ℂ)⁻¹ := by
    unfold ω₂
    push_cast
    ring
  rw [hb, ← hs]
  field_simp [hf, hr]
  <;> ring

/-- The discrepancy cannot vanish for any valid gamma interface. -/
theorem residue_sum_counterexample : actual G ≠ proposed G := by
  intro h
  have he := exact_residue_sum_defect G
  rw [h, sub_self] at he
  have hb : (ω₂ 3 : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos 3).ne'
  have hf : F 3 G 2 ≠ 0 := by simpa using F_int_ne_zero 3 (by norm_num) G 2
  exact (mul_ne_zero hb (pow_ne_zero 2 hf)) he.symm

end HaagerupIzumi.LeftProductRangeAblation

#print axioms HaagerupIzumi.LeftProductRangeAblation.exact_residue_sum_defect
#print axioms HaagerupIzumi.LeftProductRangeAblation.residue_sum_counterexample
