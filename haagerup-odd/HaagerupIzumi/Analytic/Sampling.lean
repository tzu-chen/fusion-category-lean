module

public import HaagerupIzumi.Analytic.Periods
public import HaagerupIzumi.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# The sampling function `F` and the coefficients `W`

Section 3.2–3.3 of the expanded proof: `F z = 1 / γ (ω₂ + z)`, the identities
of Lemma 3.2, the coefficients `W a`, the reciprocal products, and the
resulting `CoeffData` instance. The sign `(-1)^(a(a+n)/2)` of (3.5) is written
as `I ^ (a (a + n))`, which is the same number.
-/

open Complex Filter Topology Real

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

/-- The sampling function `F z = 1 / γ (ω₂ + z)`. -/
noncomputable def F (z : ℂ) : ℂ := (G.γ ((ω₂ n : ℂ) + z))⁻¹

lemma F_def (z : ℂ) : F n G z = (G.γ ((ω₂ n : ℂ) + z))⁻¹ := rfl

include hn

/-! ### Domain facts -/

lemma ω₂_add_int_ne_zero (m : ℤ) : G.γ ((ω₂ n : ℂ) + m) ≠ 0 :=
  G.ne_zero _ (ω₂_add_int_not_pole n hn m) (ω₂_add_int_not_zero n hn m)

lemma F_int_ne_zero (m : ℤ) : F n G m ≠ 0 :=
  inv_ne_zero (ω₂_add_int_ne_zero n hn G m)

lemma F_nat_ne_zero (m : ℕ) : F n G m ≠ 0 := by
  have := F_int_ne_zero n hn G m
  simpa using this

lemma γ_int_ne_zero (m : ℤ) (hm : m ≠ 0) : G.γ m ≠ 0 :=
  G.ne_zero _ (fun h => hm ((intCast_mem_poleSet_iff n hn m).mp h))
    (intCast_not_mem_zeroSet n hn m)

lemma int_not_pole (m : ℤ) (hm : m ≠ 0) : (m : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) :=
  fun h => hm ((intCast_mem_poleSet_iff n hn m).mp h)

lemma sin_int_div_ω₂_ne_zero (m : ℤ) (hm : m ≠ 0) :
    Complex.sin (π * m / ω₂ n) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have h2 : (m : ℂ) = k * ω₂ n := by
    field_simp at hk
    linear_combination hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h2
    exact hm (by exact_mod_cast h2)
  apply irrational_ω₂ n hn
  refine ⟨(m : ℚ) / (k : ℚ), ?_⟩
  have h3 : (m : ℝ) = k * ω₂ n := by exact_mod_cast h2
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  push_cast
  rw [div_eq_iff hk', h3]; ring

lemma sin_int_div_ω₁_ne_zero (m : ℤ) (hm : m ≠ 0) :
    Complex.sin (π * m / ω₁ n) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have h2 : (m : ℂ) = k * ω₁ n := by
    field_simp at hk
    linear_combination hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h2
    exact hm (by exact_mod_cast h2)
  apply irrational_ω₂ n hn
  refine ⟨((m - k * n : ℤ) : ℚ) / (k : ℚ), ?_⟩
  have h3 : (m : ℝ) = k * ω₁ n := by exact_mod_cast h2
  rw [ω₁_eq] at h3
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  push_cast
  rw [div_eq_iff hk', h3]; ring

/-- The sine relation between the two periods: `sin (π m / ω₁) = (-1)^(m+1) sin (π m / ω₂)`
for integers `m`. -/
lemma sin_div_ω₁_eq (m : ℤ) :
    Complex.sin (π * m / ω₁ n) = (-1) ^ (m + 1) * Complex.sin (π * m / ω₂ n) := by
  have h : (π * m / ω₁ n : ℂ) = π * m - π * m / ω₂ n := by
    have := inv_ω₁_add_inv_ω₂ n
    have h' : ((ω₁ n : ℂ))⁻¹ = 1 - ((ω₂ n : ℂ))⁻¹ := by
      have : ((ω₁ n : ℂ))⁻¹ + ((ω₂ n : ℂ))⁻¹ = 1 := by exact_mod_cast this
      linear_combination this
    rw [div_eq_mul_inv, div_eq_mul_inv, h']; ring
  have hc : Complex.cos ((m : ℂ) * π) = (-1 : ℂ) ^ m := by
    rw [show ((m : ℂ) * π) = (((m * π : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_int_mul_pi]
    push_cast; ring
  rw [h, Complex.sin_sub, show (π : ℂ) * m = m * π by ring, Complex.sin_int_mul_pi, hc]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  ring

/-! ### Lemma 3.2 -/

/-- `γ ω₁ = √d`. -/
lemma γ_ω₁ : G.γ (ω₁ n) = Real.sqrt (d n) := by
  -- limit of the first shift identity at `z → 0`
  have hpole : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ poleSet (ω₁ n) (ω₂ n) := by
    have hmin : 0 < min (ω₁ n) (ω₂ n) := lt_min (ω₁_pos n) (ω₂_pos n)
    have hballmem : Metric.ball (0 : ℂ) (min (ω₁ n) (ω₂ n)) ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hmin)
    filter_upwards [self_mem_nhdsWithin, hballmem] with z hz hball
    rintro ⟨r, s, hrs⟩
    have hz0 : z ≠ 0 := hz
    rw [Metric.mem_ball, dist_zero_right, hrs, norm_neg] at hball
    have : ((r : ℂ) * ω₁ n + (s : ℂ) * ω₂ n) = ((r * ω₁ n + s * ω₂ n : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (add_nonneg
      (mul_nonneg (Nat.cast_nonneg r) (ω₁_pos n).le)
      (mul_nonneg (Nat.cast_nonneg s) (ω₂_pos n).le))] at hball
    have hω₁ := ω₁_pos n
    have hω₂ := ω₂_pos n
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs; simp at hrs; exact hz0 hrs
      · have : (1 : ℝ) ≤ s := by exact_mod_cast hs
        have : ω₂ n ≤ s * ω₂ n := by nlinarith
        have := min_le_right (ω₁ n) (ω₂ n)
        simp at hball
        linarith
    · have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have : ω₁ n ≤ r * ω₁ n := by nlinarith
      have := min_le_left (ω₁ n) (ω₂ n)
      nlinarith [mul_nonneg (Nat.cast_nonneg s) hω₂.le]
  -- the two limits
  have h1 : Tendsto (fun z : ℂ => G.γ (z + ω₁ n)) (𝓝[≠] 0) (𝓝 (G.γ (ω₁ n))) := by
    have hc := G.continuousAt (ω₁ n) (HypGamma.not_mem_poleSet_of_re_pos (ω₁_pos n) (ω₂_pos n)
      (by simpa using ω₁_pos n))
    have : Tendsto (fun z : ℂ => z + ω₁ n) (𝓝[≠] 0) (𝓝 (ω₁ n)) := by
      have := Continuous.tendsto (f := fun z : ℂ => z + (ω₁ n : ℂ)) (by fun_prop) 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp this
  have h2 : Tendsto (fun z : ℂ => 2 * Complex.sin (π * z / ω₂ n) * G.γ z) (𝓝[≠] 0)
      (𝓝 (2 * (π / ω₂ n) * (Real.sqrt (ω₁ n * ω₂ n) / (2 * π)))) := by
    have hs : Tendsto (fun z : ℂ => Complex.sin (π * z / ω₂ n) / z) (𝓝[≠] 0) (𝓝 (π / ω₂ n)) := by
      have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z / ω₂ n)) (π / ω₂ n) 0 := by
        have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z / ω₂ n) (π / ω₂ n) 0 := by
          have := ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).div_const (ω₂ n : ℂ)
          simpa using this
        have h2 := (Complex.hasDerivAt_sin ((π : ℂ) * (0 : ℂ) / ω₂ n)).comp (0 : ℂ) h1
        simp only [mul_zero, zero_div, Complex.cos_zero, one_mul] at h2
        exact h2
      have := hd.tendsto_slope_zero
      simp only [mul_zero, zero_div, Complex.sin_zero, sub_zero, zero_add, smul_eq_mul] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [inv_mul_eq_div]
    have hr := G.residue_zero
    unfold HasResidue at hr
    simp only [sub_zero] at hr
    have := (hs.const_mul 2).mul hr
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    field_simp
    try ring
  have heq : (fun z : ℂ => G.γ (z + ω₁ n)) =ᶠ[𝓝[≠] 0]
      fun z => 2 * Complex.sin (π * z / ω₂ n) * G.γ z := by
    filter_upwards [hpole] with z hz
    exact G.shift₁ z hz
  have := tendsto_nhds_unique (h1.congr' heq) h2
  rw [this, sqrt_Ω]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  push_cast
  try field_simp
  try ring

/-- `γ ω₂ = 1 / √d`. -/
lemma γ_ω₂ : G.γ (ω₂ n) = ((Real.sqrt (d n) : ℂ))⁻¹ := by
  have h := G.reflect (ω₁ n) (HypGamma.not_mem_poleSet_of_re_pos (ω₁_pos n) (ω₂_pos n)
    (by simpa using ω₁_pos n)) (HypGamma.not_mem_zeroSet_of_re_lt (ω₁_pos n) (ω₂_pos n)
    (by simpa using ω₂_pos n))
  rw [show (ω₁ n : ℂ) + ω₂ n - ω₁ n = ω₂ n by ring, γ_ω₁ n hn G] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `F 0 = √d`. -/
lemma F_zero : F n G 0 = Real.sqrt (d n) := by
  rw [F_def, add_zero, γ_ω₂ n hn G, inv_inv]

/-- `F n = 1 / √d`. -/
lemma F_n : F n G n = ((Real.sqrt (d n) : ℂ))⁻¹ := by
  rw [F_def, show (ω₂ n : ℂ) + n = ω₁ n by rw [ω₁_eq]; push_cast; ring, γ_ω₁ n hn G]

/-- Lemma 3.2 (2): `F z * F (n - z) = 1`. -/
lemma F_mul_F_sub {z : ℂ} (hp : (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n))
    (hz : (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n)) : F n G z * F n G (n - z) = 1 := by
  have h := G.reflect _ hp hz
  rw [F_def, F_def, show (ω₂ n : ℂ) + (n - z) = ω₁ n + ω₂ n - (ω₂ n + z) by
    rw [ω₁_eq]; push_cast; ring]
  rw [← mul_inv, h, inv_one]

lemma F_int_mul_F_sub (m : ℤ) : F n G m * F n G (n - m) = 1 :=
  F_mul_F_sub n hn G (ω₂_add_int_not_pole n hn m) (ω₂_add_int_not_zero n hn m)

/-- Lemma 3.2 (3), at nonzero integers: `F (a + n) = F a * sin (π a / ω₁) / sin (π a / ω₂)`. -/
lemma F_int_add_n_eq (a : ℤ) (ha : a ≠ 0) :
    F n G (a + n) = F n G a * Complex.sin (π * a / ω₁ n) / Complex.sin (π * a / ω₂ n) := by
  have hp := int_not_pole n hn a ha
  have h1 := G.shift₁ a hp
  have h2 := G.shift₂ a hp
  have hγ := γ_int_ne_zero n hn G a ha
  have hs2 := sin_int_div_ω₂_ne_zero n hn a ha
  have hs1 := sin_int_div_ω₁_ne_zero n hn a ha
  rw [F_def, F_def, show (ω₂ n : ℂ) + (a + n) = a + ω₁ n by rw [ω₁_eq]; push_cast; ring, h1,
    show (ω₂ n : ℂ) + a = a + ω₂ n by ring, h2]
  field_simp

/-- Lemma 3.2 (4): `F (a + n) = (-1)^(a+1) F a` for nonzero integers `a`. -/
lemma F_int_add_n (a : ℤ) (ha : a ≠ 0) : F n G (a + n) = (-1) ^ (a + 1) * F n G a := by
  rw [F_int_add_n_eq n hn G a ha, sin_div_ω₁_eq n hn]
  have := sin_int_div_ω₂_ne_zero n hn a ha
  field_simp

/-- Lemma 3.2 (5): `F (-a) * F a = (-1)^(a+1)` for nonzero integers `a`. -/
lemma F_neg_mul_F (a : ℤ) (ha : a ≠ 0) : F n G (-a) * F n G a = (-1) ^ (a + 1) := by
  have h := F_int_mul_F_sub n hn G (a + n)
  rw [show ((a + n : ℤ) : ℂ) = a + n by push_cast; ring,
    show (n : ℂ) - (a + n) = ((-a : ℤ) : ℂ) by push_cast; ring, F_int_add_n n hn G a ha] at h
  push_cast at h
  have hsq : ((-1 : ℂ) ^ (a + 1)) ^ 2 = 1 := by
    rcases Int.even_or_odd (a + 1) with he | ho
    · rw [he.neg_one_zpow]; norm_num
    · rw [ho.neg_one_zpow]; norm_num
  calc F n G (-a) * F n G a = ((-1 : ℂ) ^ (a + 1)) ^ 2 * (F n G (-a) * F n G a) := by
        rw [hsq, one_mul]
    _ = (-1 : ℂ) ^ (a + 1) * ((-1) ^ (a + 1) * F n G a * F n G (-a)) := by ring
    _ = (-1 : ℂ) ^ (a + 1) := by rw [h, mul_one]

/-- Lemma 3.2 (6): `γ (ω₁ + a) = F (-a)` for integers `a`. -/
lemma γ_ω₁_add_int (a : ℤ) : G.γ ((ω₁ n : ℂ) + a) = F n G (-a) := by
  have h := G.reflect _ (ω₁_add_int_not_pole n hn a) (ω₁_add_int_not_zero n hn a)
  rw [show (ω₁ n : ℂ) + ω₂ n - (ω₁ n + a) = ω₂ n + ((-a : ℤ) : ℂ) by push_cast; ring] at h
  push_cast at h
  rw [F_def]
  push_cast
  exact eq_inv_of_mul_eq_one_left h

lemma γ_ω₂_sub_int (a : ℤ) : G.γ ((ω₂ n : ℂ) - a) = (F n G (-a))⁻¹ := by
  rw [F_def, inv_inv]; push_cast; ring_nf

/-- Lemma 3.2 (7): `2 sin (π a / ω₁) γ (-a) = (-1)^a F a` for nonzero integers `a`. -/
lemma two_sin_mul_γ_neg (a : ℤ) (ha : a ≠ 0) :
    2 * Complex.sin (π * a / ω₁ n) * G.γ (-a) = (-1) ^ a * F n G a := by
  have hp : ((-a : ℤ) : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := int_not_pole n hn (-a) (neg_ne_zero.mpr ha)
  have h := G.shift₂ _ hp
  rw [show ((-a : ℤ) : ℂ) + ω₂ n = ω₂ n - a by push_cast; ring, γ_ω₂_sub_int n hn G a] at h
  have h5 := F_neg_mul_F n hn G a ha
  have hF : F n G (-(a : ℂ)) ≠ 0 := by
    have := F_int_ne_zero n hn G (-a); push_cast at this; exact this
  have hFa := F_int_ne_zero n hn G a
  push_cast at h h5
  rw [show (π : ℂ) * (-(a : ℂ)) / ω₁ n = -(π * a / ω₁ n) by ring, Complex.sin_neg] at h
  have hz : ((-1 : ℂ) ^ (a + 1)) = -(-1) ^ a := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]; ring
  rw [hz] at h5
  have hsq : ((-1 : ℂ) ^ a) ^ 2 = 1 := by
    rcases Int.even_or_odd a with he | ho
    · rw [he.neg_one_zpow]; norm_num
    · rw [ho.neg_one_zpow]; norm_num
  have key : 2 * Complex.sin (π * a / ω₁ n) * G.γ (-(a : ℂ)) = -(F n G (-(a : ℂ)))⁻¹ := by
    rw [h]; ring
  rw [key]
  field_simp
  linear_combination (-(-1 : ℂ) ^ a) * h5 + hsq

/-! ### The coefficients `W` -/

omit hn in
/-- The sign `I ^ (a (a + n)) = (-1) ^ (a (a + n) / 2)`. -/
noncomputable def sgn (a : ℕ) : ℂ := I ^ (a * (a + n))

omit hn in
/-- The coefficients `W`. -/
noncomputable def W (a : ZMod n) : ℂ :=
  if a = 0 then -1 else -(sgn n a.val) * F n G a.val / Real.sqrt (d n)

omit hn in
lemma sgn_mul_sgn (hodd : Odd n) (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ n - 1) :
    sgn n a * sgn n (n - a) = -1 := by
  unfold sgn
  rw [← pow_add]
  have hle : a ≤ n := by omega
  have hle' : a * n ≤ a * a + n * n := by nlinarith
  have hexp : a * (a + n) + (n - a) * (n - a + n) = 2 * (a * a + n * n - a * n) := by
    zify [hle, hle']
    ring
  rw [hexp, pow_mul, Complex.I_sq]
  apply Odd.neg_one_pow
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have h1 : (a * a) % 2 = a % 2 := by
    rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
  have h2 : (n * n) % 2 = 1 := by rw [Nat.mul_mod, hn2]
  have h3 : (a * n) % 2 = a % 2 := by
    rw [Nat.mul_mod, hn2]; rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
  rw [Nat.odd_iff]
  generalize a * a = x at *
  generalize n * n = y at *
  generalize a * n = z at *
  omega

omit hn in
lemma sgn_ne_zero (a : ℕ) : sgn n a ≠ 0 := pow_ne_zero _ Complex.I_ne_zero

omit hn in
lemma sqrt_d_ne_zero : (Real.sqrt (d n) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (d_pos n)).ne'

omit hn in
lemma sqrt_d_sq : (Real.sqrt (d n) : ℂ) ^ 2 = d n := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos n).le]

omit hn in
/-- `sgn` is real: `a (a + n)` is even, so `I ^ (a (a + n))` is `±1`. -/
lemma sgn_conj (hodd : Odd n) (a : ℕ) : (starRingEnd ℂ) (sgn n a) = sgn n a := by
  unfold sgn
  have : Even (a * (a + n)) := by
    rcases Nat.even_or_odd a with ha | ha
    · exact ha.mul_right _
    · exact Even.mul_left (ha.add_odd hodd) _
  obtain ⟨c, hc⟩ := this
  rw [hc, ← two_mul, pow_mul, Complex.I_sq, map_pow, map_neg, map_one]

/-- `F` is real at integers. -/
lemma F_int_conj (m : ℤ) : (starRingEnd ℂ) (F n G m) = F n G m := by
  rw [F_def, map_inv₀]
  congr 1
  have h := G.real_axis (ω₂ n + m)
  rw [Complex.conj_eq_iff_im]
  convert h using 2
  push_cast; ring

/-- `W` is real. -/
lemma W_conj (hodd : Odd n) (a : ZMod n) : (starRingEnd ℂ) (W n G a) = W n G a := by
  unfold W
  split_ifs
  · simp
  · rw [map_div₀, map_mul, map_neg, sgn_conj n hodd, Complex.conj_ofReal]
    have := F_int_conj n hn G a.val
    push_cast at this
    rw [this]

/-- The concrete coefficient data of Section 3, built from the gamma interface. -/
noncomputable def toCoeffData (hodd : Odd n) : CoeffData n ℂ where
  δ := (δ n : ℂ)
  W := W n G
  hδ := by
    have := δ_sq n
    exact_mod_cast this
  hW0 := by simp [W]
  hWne := by
    intro a
    unfold W
    split_ifs
    · norm_num
    · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (sgn_ne_zero n _)) (F_nat_ne_zero n hn G _))
        (sqrt_d_ne_zero n)
  hrec := by
    intro a ha
    haveI : NeZero n := ⟨by omega⟩
    have hv1 : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr (fun e => ha ((ZMod.val_eq_zero a).mp e))
    have hv2 : a.val ≤ n - 1 := by have := ZMod.val_lt a; omega
    have hval : (-a).val = n - a.val := by rw [ZMod.neg_val, if_neg ha]
    simp only [W, if_neg ha, if_neg (neg_ne_zero.mpr ha), hval]
    have hs := sgn_mul_sgn n hodd a.val hv1 hv2
    have hF : F n G (a.val : ℕ) * F n G ((n - a.val : ℕ) : ℂ) = 1 := by
      have := F_int_mul_F_sub n hn G (a.val : ℤ)
      rw [Nat.cast_sub (by omega)]
      push_cast at this ⊢
      exact this
    have hsq := sqrt_d_sq n
    have hδd : ((δ n : ℝ) : ℂ) = -((d n : ℂ))⁻¹ := by unfold δ; push_cast; ring
    rw [hδd]
    calc -(sgn n a.val) * F n G (a.val : ℕ) / (Real.sqrt (d n) : ℂ)
          * (-(sgn n (n - a.val)) * F n G ((n - a.val : ℕ) : ℂ) / (Real.sqrt (d n) : ℂ))
        = (sgn n a.val * sgn n (n - a.val)) * (F n G (a.val : ℕ) * F n G ((n - a.val : ℕ) : ℂ))
          / ((Real.sqrt (d n) : ℂ)) ^ 2 := by ring
      _ = -((d n : ℂ))⁻¹ := by rw [hs, hF, hsq]; ring

end Concrete
end HaagerupIzumi
