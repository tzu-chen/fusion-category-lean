module

public import HaagerupIzumi.Analytic.HypGamma

@[expose] public section

/-!
# The periods of the construction

Lemma 3.1 of the expanded proof: `d`, `δ`, `ω₁ = d + 1`, `ω₂ = 1 + d⁻¹`, their
relations, irrationality, and the lattice lemma (no nonzero integer lies in
`ω₁ ℕ + ω₂ ℕ`).
-/

open Complex

namespace HaagerupIzumi
namespace Periods

variable (n : ℕ)

/-- The positive root `d = (n + √(n² + 4)) / 2`. -/
noncomputable def d : ℝ := (n + Real.sqrt ((n : ℝ) ^ 2 + 4)) / 2
/-- The negative root `δ = -1/d`. -/
noncomputable def δ : ℝ := -(d n)⁻¹
/-- `ω₁ = d + 1`. -/
noncomputable def ω₁ : ℝ := d n + 1
/-- `ω₂ = 1 + 1/d`. -/
noncomputable def ω₂ : ℝ := 1 + (d n)⁻¹

lemma sqrt_pos : 0 < Real.sqrt ((n : ℝ) ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)

lemma sqrt_sq : Real.sqrt ((n : ℝ) ^ 2 + 4) ^ 2 = (n : ℝ) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

lemma d_pos : 0 < d n := by
  unfold d; have := sqrt_pos n; positivity

lemma d_ne_zero : d n ≠ 0 := (d_pos n).ne'

lemma d_sq : d n ^ 2 = n * d n + 1 := by
  unfold d
  linear_combination (1 / 4 : ℝ) * sqrt_sq n

lemma n_lt_d : (n : ℝ) < d n := by
  unfold d
  have h1 := sqrt_sq n
  have h2 := sqrt_pos n
  nlinarith

lemma one_lt_d (hn : 1 ≤ n) : 1 < d n := by
  have := n_lt_d n
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma δ_sq : δ n ^ 2 = n * δ n + 1 := by
  unfold δ
  have hd := d_ne_zero n
  have := d_sq n
  field_simp
  linear_combination -this

lemma δ_eq : δ n = (n - Real.sqrt ((n : ℝ) ^ 2 + 4)) / 2 := by
  unfold δ d
  have h1 := sqrt_sq n
  have h2 : (n : ℝ) + Real.sqrt ((n : ℝ) ^ 2 + 4) ≠ 0 := by have := sqrt_pos n; positivity
  field_simp
  linear_combination h1

lemma ω₁_pos : 0 < ω₁ n := by unfold ω₁; have := d_pos n; linarith

lemma ω₂_pos : 0 < ω₂ n := by unfold ω₂; have := d_pos n; positivity

lemma ω₁_sub_ω₂ : ω₁ n - ω₂ n = n := by
  unfold ω₁ ω₂
  have hd := d_ne_zero n
  have := d_sq n
  field_simp
  try linear_combination this

lemma ω₁_mul_ω₂ : ω₁ n * ω₂ n = ω₁ n + ω₂ n := by
  unfold ω₁ ω₂
  have hd := d_ne_zero n
  field_simp
  try ring

lemma ω₁_eq : ω₁ n = n + ω₂ n := by linarith [ω₁_sub_ω₂ n]

lemma n_lt_ω₁ : (n : ℝ) < ω₁ n := by have := ω₂_pos n; linarith [ω₁_eq n]

lemma one_lt_ω₂ : 1 < ω₂ n := by unfold ω₂; have := d_pos n; have := inv_pos.mpr this; linarith

lemma ω₂_lt_two (hn : 1 ≤ n) : ω₂ n < 2 := by
  unfold ω₂
  have := one_lt_d n hn
  have : (d n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
  linarith

lemma Ω_eq_d_mul_ω₂_sq : ω₁ n * ω₂ n = d n * ω₂ n ^ 2 := by
  unfold ω₁ ω₂
  have hd := d_ne_zero n
  field_simp
  try ring

lemma sqrt_Ω : Real.sqrt (ω₁ n * ω₂ n) = ω₂ n * Real.sqrt (d n) := by
  rw [Ω_eq_d_mul_ω₂_sq, Real.sqrt_mul (d_pos n).le, Real.sqrt_sq (ω₂_pos n).le, mul_comm]

lemma inv_ω₁_add_inv_ω₂ : (ω₁ n)⁻¹ + (ω₂ n)⁻¹ = 1 := by
  have h1 := (ω₁_pos n).ne'
  have h2 := (ω₂_pos n).ne'
  have := ω₁_mul_ω₂ n
  field_simp
  linear_combination -this

lemma τ_eq : δ n - 1 = -ω₂ n := by unfold δ ω₂; ring

/-! ### Irrationality and the lattice lemma -/

lemma not_isSquare (hn : 1 ≤ n) : ¬ IsSquare (n ^ 2 + 4) := by
  rintro ⟨m, hm⟩
  rcases Nat.lt_or_ge m (n + 1) with h | h
  · have : m ≤ n := by omega
    nlinarith
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      have : m ≤ 2 := by nlinarith
      interval_cases m
      all_goals omega
    · nlinarith [Nat.mul_le_mul h h]

lemma irrational_sqrt (hn : 1 ≤ n) : Irrational (Real.sqrt ((n : ℝ) ^ 2 + 4)) := by
  have : ((n : ℝ) ^ 2 + 4) = ((n ^ 2 + 4 : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  exact irrational_sqrt_natCast_iff.mpr (not_isSquare n hn)

lemma irrational_d (hn : 1 ≤ n) : Irrational (d n) := by
  unfold d
  have := (irrational_sqrt n hn).natCast_add n
  exact this.div_natCast (by norm_num)

lemma irrational_ω₂ (hn : 1 ≤ n) : Irrational (ω₂ n) := by
  unfold ω₂
  have := ((irrational_d n hn).inv).natCast_add 1
  simpa using this

/-- The lattice lemma: an integer of the form `r ω₁ + s ω₂` with `r, s ∈ ℕ` is zero, and then
`r = s = 0`. -/
lemma lattice (hn : 1 ≤ n) (m : ℤ) (r s : ℕ) (h : (m : ℝ) = r * ω₁ n + s * ω₂ n) :
    r = 0 ∧ s = 0 ∧ m = 0 := by
  have hω := ω₁_eq n
  have hq : ((r + s : ℕ) : ℝ) * ω₂ n = (m - r * n : ℤ) := by
    push_cast; rw [h, hω]; ring
  have hrs : r + s = 0 := by
    by_contra hne
    have hpos : (0 : ℝ) < ((r + s : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
    have : ω₂ n = ((m - r * n : ℤ) : ℝ) / ((r + s : ℕ) : ℝ) := by
      rw [eq_div_iff hpos.ne', mul_comm]; exact hq
    apply irrational_ω₂ n hn
    rw [this]
    exact ⟨((m - r * n : ℤ) : ℚ) / ((r + s : ℕ) : ℚ), by push_cast; ring⟩
  have hr : r = 0 := by omega
  have hs : s = 0 := by omega
  subst hr hs
  simp at h
  exact ⟨rfl, rfl, by exact_mod_cast h⟩

/-- An integer is a pole only if it is zero. -/
lemma intCast_mem_poleSet_iff (hn : 1 ≤ n) (m : ℤ) :
    (m : ℂ) ∈ poleSet (ω₁ n) (ω₂ n) ↔ m = 0 := by
  constructor
  · rintro ⟨r, s, hrs⟩
    have : ((-m : ℤ) : ℝ) = r * ω₁ n + s * ω₂ n := by
      have := congrArg Complex.re hrs
      simp only [intCast_re, neg_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im,
        ofReal_im, mul_zero, sub_zero] at this
      push_cast; linarith
    have := (lattice n hn (-m) r s this).2.2
    omega
  · rintro rfl; exact ⟨0, 0, by simp⟩

/-- No integer is a zero. -/
lemma intCast_not_mem_zeroSet (hn : 1 ≤ n) (m : ℤ) : (m : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have : ((m : ℤ) : ℝ) = (r + 1 : ℕ) * ω₁ n + (s + 1 : ℕ) * ω₂ n := by
    have := congrArg Complex.re hrs
    simp only [intCast_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero] at this
    push_cast; linarith
  have := (lattice n hn m (r + 1) (s + 1) this).1
  omega

/-- `ω₂ + m` is neither a pole nor a zero, for every integer `m`. -/
lemma ω₂_add_int_not_pole (hn : 1 ≤ n) (m : ℤ) :
    ((ω₂ n : ℂ) + m) ∉ poleSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have : ((-m : ℤ) : ℝ) = r * ω₁ n + (s + 1 : ℕ) * ω₂ n := by
    have := congrArg Complex.re hrs
    simp only [intCast_re, add_re, neg_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero] at this
    push_cast; linarith
  have := (lattice n hn (-m) r (s + 1) this).2.1
  omega

lemma ω₂_add_int_not_zero (hn : 1 ≤ n) (m : ℤ) :
    ((ω₂ n : ℂ) + m) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have : ((m : ℤ) : ℝ) = (r + 1 : ℕ) * ω₁ n + s * ω₂ n := by
    have := congrArg Complex.re hrs
    simp only [intCast_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero] at this
    push_cast; linarith
  have := (lattice n hn m (r + 1) s this).1
  omega

/-- `ω₁ + m` is neither a pole nor a zero, for every integer `m`. -/
lemma ω₁_add_int_not_pole (hn : 1 ≤ n) (m : ℤ) :
    ((ω₁ n : ℂ) + m) ∉ poleSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have : ((-m : ℤ) : ℝ) = (r + 1 : ℕ) * ω₁ n + s * ω₂ n := by
    have := congrArg Complex.re hrs
    simp only [intCast_re, add_re, neg_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero] at this
    push_cast; linarith
  have := (lattice n hn (-m) (r + 1) s this).1
  omega

lemma ω₁_add_int_not_zero (hn : 1 ≤ n) (m : ℤ) :
    ((ω₁ n : ℂ) + m) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have : ((m : ℤ) : ℝ) = r * ω₁ n + (s + 1 : ℕ) * ω₂ n := by
    have := congrArg Complex.re hrs
    simp only [intCast_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero] at this
    push_cast; linarith
  have := (lattice n hn m r (s + 1) this).2.1
  omega

/-- The quadratic relation `ω₂² + (n - 2) ω₂ - n = 0`. -/
lemma ω₂_quad : ω₂ n ^ 2 + (n - 2) * ω₂ n - n = 0 := by
  unfold ω₂
  have hd := d_ne_zero n
  have := d_sq n
  field_simp
  linear_combination (-1 : ℝ) * this

/-- `1` and `ω₂` are linearly independent over `ℚ`. -/
lemma indep (hn : 1 ≤ n) (a b : ℚ) (h : (a : ℝ) + b * ω₂ n = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irrational_ω₂ n hn
    refine ⟨-a / b, ?_⟩
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    rw [div_eq_iff hb']
    linear_combination -h

/-- A real number `q₁ + q₂ ω₂` with rational `q₁, q₂` is a pole only if `q₂ = -(r + s)` and
`q₁ = -r n` for some naturals `r, s`. -/
lemma pole_coeff (hn : 1 ≤ n) (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n)
    (hmem : (x : ℂ) ∈ poleSet (ω₁ n) (ω₂ n)) :
    ∃ r s : ℕ, q₁ = -(r * n : ℚ) ∧ q₂ = -((r + s : ℕ) : ℚ) := by
  obtain ⟨r, s, hrs⟩ := hmem
  refine ⟨r, s, ?_⟩
  have hre := congrArg Complex.re hrs
  simp only [ofReal_re, neg_re, add_re, mul_re, natCast_re, ofReal_im, natCast_im, mul_zero,
    sub_zero] at hre
  rw [hx, ω₁_eq] at hre
  have := indep n hn (q₁ + r * n) (q₂ + (r + s : ℕ)) (by push_cast; linear_combination hre)
  constructor
  · linear_combination this.1
  · linear_combination this.2

/-- A real number `q₁ + q₂ ω₂` with rational `q₁, q₂` is a zero only if `q₂ = r + s + 2` and
`q₁ = (r + 1) n` for some naturals `r, s`. -/
lemma zero_coeff (hn : 1 ≤ n) (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n)
    (hmem : (x : ℂ) ∈ zeroSet (ω₁ n) (ω₂ n)) :
    ∃ r s : ℕ, q₁ = ((r + 1) * n : ℚ) ∧ q₂ = ((r + s + 2 : ℕ) : ℚ) := by
  obtain ⟨r, s, hrs⟩ := hmem
  refine ⟨r, s, ?_⟩
  have hre := congrArg Complex.re hrs
  simp only [ofReal_re, add_re, mul_re, natCast_re, ofReal_im, natCast_im, mul_zero,
    sub_zero] at hre
  rw [hx, ω₁_eq] at hre
  have := indep n hn (q₁ - (r + 1) * n) (q₂ - (r + s + 2 : ℕ)) (by push_cast; linear_combination hre)
  constructor
  · linear_combination this.1
  · linear_combination this.2

end Periods
end HaagerupIzumi
