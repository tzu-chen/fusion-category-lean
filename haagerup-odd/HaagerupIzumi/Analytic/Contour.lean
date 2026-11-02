module

public import HaagerupIzumi.Analytic.Sampling
public import HaagerupIzumi.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# The contour argument for the column Fourier formula

Proposition 4.1 of the expanded proof. The samples `B_{a,h}` are the residues
at the integers of the kernel `K_h(z) = π e^{-iθz} R_h(z) / sin(π z)`, where
`R_h(z) = F(z)/F(z-h)`. The residue theorem on a strip of width `n`
(`strip_residues`), the kernel difference identity (Step 2), and the two-gamma
integral of the interface (`HypGamma.two_gamma`) combine into the closed form.

This file contains the sample rule (Lemma 3.9), the kernel, its residues, its
decay, and the final assembly.
-/

open Complex Real Filter Topology Set
open scoped ComplexConjugate

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

/-! ### The ratio `R_h` and the kernel -/

/-- `R_h(z) = F(z)/F(z-h) = γ(ω₂ + z - h)/γ(ω₂ + z)`. -/
noncomputable def Rh (h : ℕ) (z : ℂ) : ℂ := G.γ ((ω₂ n : ℂ) + (z - h)) / G.γ ((ω₂ n : ℂ) + z)

omit hn in
lemma Rh_eq_F (h : ℕ) (z : ℂ) : Rh n G h z = F n G z / F n G (z - h) := by
  rw [Rh, F_def, F_def, inv_div_inv]

/-- The kernel `K_h(z) = π e^{-iθz} R_h(z) / sin(π z)`. -/
noncomputable def Kh (h : ℕ) (θ : ℝ) (z : ℂ) : ℂ :=
  π * Complex.exp (-I * θ * z) / Complex.sin (π * z) * Rh n G h z

/-- The two-gamma integrand `Φ_h(z) = e^{-iθz} γ(-z) γ(z-h)`. -/
noncomputable def Φh (h : ℕ) (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-I * θ * z) * G.γ (-z) * G.γ (z - h)

/-! ### Signs modulo four -/

/-- `I ^ e` depends only on `e mod 4`. -/
lemma I_pow_congr (e₁ e₂ : ℕ) (h : (e₁ : ZMod 4) = (e₂ : ZMod 4)) : I ^ e₁ = I ^ e₂ := by
  have h' : e₁ % 4 = e₂ % 4 := (ZMod.natCast_eq_natCast_iff' e₁ e₂ 4).1 h
  rw [← Nat.mod_add_div e₁ 4, ← Nat.mod_add_div e₂ 4, pow_add, pow_add, pow_mul, pow_mul,
    I_pow_four, one_pow, one_pow, mul_one, mul_one, h']

lemma neg_one_pow_eq_I_pow (m : ℕ) : (-1 : ℂ) ^ m = I ^ (2 * m) := by
  rw [pow_mul, I_sq]

omit hn G in
lemma natCast_zmod4_of_odd (hodd : Odd n) : (n : ZMod 4) = 1 ∨ (n : ZMod 4) = 3 := by
  obtain ⟨m, hm⟩ := hodd
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [show n = 4 * k + 1 by omega]
    push_cast
    rw [show (4 : ZMod 4) = 0 from rfl]; ring
  · right
    rw [show n = 4 * k + 3 by omega]
    push_cast
    rw [show (4 : ZMod 4) = 0 from rfl]; ring

lemma zmod4_case1 (a c x : ZMod 4) (hx : x = 1 ∨ x = 3) :
    2 + a * (a + x) + c * (c + x) + 2 * (c + 1) = (a + c) * (a + c + x) + 2 * ((a + c) * (a + 1)) := by
  revert a c x; decide

lemma zmod4_case2 (h c e : ZMod 4) (hx : c + e = 1 ∨ c + e = 3) :
    2 + (h + c) * (h + c + (c + e)) + e * (e + (c + e))
      = h * (h + (c + e)) + 2 * (h * (h + c + 1)) := by
  revert h c e; decide

/-! ### The sample rule (Lemma 3.9, Step 1) -/

section sample
variable [NeZero n]

omit hn in
lemma natCast_ne_zero' (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ n - 1) : (a : ZMod n) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (ZMod n) n] at h
  have := Nat.le_of_dvd (by omega) h
  omega

omit hn in
lemma val_natCast' (a : ℕ) (ha2 : a ≤ n - 1) : (a : ZMod n).val = a := by
  have := NeZero.pos n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

omit hn in
lemma W_natCast (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ n - 1) :
    W n G (a : ZMod n) = -(sgn n a) * F n G a / Real.sqrt (d n) := by
  rw [W, if_neg (natCast_ne_zero' n a ha1 ha2), val_natCast' n a ha2]

lemma B_eq (hodd : Odd n) (x y : ZMod n) (hy : y ≠ 0) :
    (toCoeffData n hn G hodd).B x y = W n G x * W n G (y - x) / W n G y := by
  simp [toCoeffData, CoeffData.B, hy]

/-- Lemma 3.9 in the form (3.16): for `1 ≤ h ≤ n-1` and `0 ≤ a ≤ n-1`,
`B_{a,h} + ω₂ 1_{a=h} = (-1)^{h(a+1)} / (√d F(h)) · R_h(a)`. -/
theorem sample_rule (hodd : Odd n) (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (a : ℕ) (ha : a ≤ n - 1) :
    (toCoeffData n hn G hodd).B (a : ZMod n) (h : ZMod n) + (ω₂ n : ℂ) * (if a = h then 1 else 0)
      = (-1) ^ (h * (a + 1)) / (Real.sqrt (d n) * F n G h) * Rh n G h a := by
  have hd0 := sqrt_d_ne_zero n
  have hFh := F_nat_ne_zero n hn G h
  have hh0 : (h : ZMod n) ≠ 0 := natCast_ne_zero' n h hh1 hh2
  have hn4 := natCast_zmod4_of_odd n hodd
  rw [Rh_eq_F]
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · -- `a = 0`
    simp only [Nat.cast_zero, zero_sub, zero_add, mul_one]
    rw [(toCoeffData n hn G hodd).B_zero_left hh0, if_neg (by omega), F_zero n hn G]
    have hneg := F_neg_mul_F n hn G h (by omega : (h : ℤ) ≠ 0)
    push_cast at hneg
    rw [show ((h : ℤ) + 1 : ℤ) = ((h + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      pow_succ] at hneg
    have hF := F_int_ne_zero n hn G (-h)
    push_cast at hF
    field_simp
    linear_combination (-1 : ℂ) * hneg
  rcases lt_trichotomy a h with hah | rfl | hha
  · -- `0 < a < h`
    obtain ⟨c, rfl⟩ : ∃ c, h = a + c := ⟨h - a, by omega⟩
    have hc1 : 1 ≤ c := by omega
    rw [B_eq n hn G hodd _ _ hh0, if_neg (by omega), mul_zero, add_zero,
      show ((a + c : ℕ) : ZMod n) - (a : ZMod n) = (c : ZMod n) by push_cast; ring,
      W_natCast n G a ha0 (by omega), W_natCast n G c hc1 (by omega),
      W_natCast n G (a + c) hh1 hh2,
      show ((a : ℂ)) - ((a + c : ℕ) : ℂ) = -(c : ℂ) by push_cast; ring]
    have hneg := F_neg_mul_F n hn G c (by omega : (c : ℤ) ≠ 0)
    push_cast at hneg
    rw [show ((c : ℤ) + 1 : ℤ) = ((c + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at hneg
    have hFc := F_int_ne_zero n hn G (-c)
    push_cast at hFc
    have hFc' := F_nat_ne_zero n hn G c
    have hFa := F_nat_ne_zero n hn G a
    have hsc := sgn_ne_zero n c
    have hsa := sgn_ne_zero n a
    have hsh := sgn_ne_zero n (a + c)
    -- the sign identity
    have hsign : -(sgn n a * sgn n c) * (-1) ^ (c + 1) = sgn n (a + c) * (-1) ^ ((a + c) * (a + 1)) := by
      unfold sgn
      rw [neg_one_pow_eq_I_pow, neg_one_pow_eq_I_pow, neg_eq_neg_one_mul,
        show (-1 : ℂ) = I ^ 2 by rw [I_sq], ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      apply I_pow_congr
      push_cast
      linear_combination zmod4_case1 (a : ZMod 4) c n hn4
    field_simp
    linear_combination (-(sgn n a * sgn n c)) * hneg + hsign
  · -- `a = h`
    rw [(toCoeffData n hn G hodd).B_diag hh0, if_pos rfl, mul_one, sub_self, F_zero n hn G]
    have hev : Even (a * (a + 1)) := Nat.even_mul_succ_self a
    rw [hev.neg_one_pow]
    have hsq := sqrt_d_sq n
    have hω : (ω₂ n : ℂ) = 1 + ((d n : ℂ))⁻¹ := by unfold ω₂; push_cast; ring
    have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
    rw [hω]
    field_simp
    linear_combination hsq
  · -- `h < a ≤ n - 1`
    obtain ⟨c, rfl⟩ : ∃ c, a = h + c := ⟨a - h, by omega⟩
    have hc1 : 1 ≤ c := by omega
    have hcn : c ≤ n - 1 := by omega
    obtain ⟨e, hne⟩ : ∃ e, n = c + e := ⟨n - c, by omega⟩
    have he1 : 1 ≤ e := by omega
    rw [B_eq n hn G hodd _ _ hh0, if_neg (by omega), mul_zero, add_zero,
      show (h : ZMod n) - ((h + c : ℕ) : ZMod n) = ((n - c : ℕ) : ZMod n) by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; push_cast; ring,
      W_natCast n G (h + c) ha0 ha, W_natCast n G (n - c) (by omega) (by omega),
      W_natCast n G h hh1 hh2,
      show (((h + c : ℕ) : ℂ)) - (h : ℂ) = (c : ℂ) by push_cast; ring]
    have hFF := F_int_mul_F_sub n hn G c
    push_cast at hFF
    rw [show ((n - c : ℕ) : ℂ) = (n : ℂ) - c by rw [Nat.cast_sub (by omega)]] at *
    have hFc := F_nat_ne_zero n hn G c
    have hFnc : F n G ((n : ℂ) - c) ≠ 0 := by
      have := F_int_ne_zero n hn G (n - c); push_cast at this; exact this
    have hFa := F_nat_ne_zero n hn G (h + c)
    have hsc := sgn_ne_zero n (n - c)
    have hsa := sgn_ne_zero n (h + c)
    have hsh := sgn_ne_zero n h
    have hsign : -(sgn n (h + c) * sgn n (n - c)) = sgn n h * (-1) ^ (h * (h + c + 1)) := by
      unfold sgn
      rw [neg_one_pow_eq_I_pow, neg_eq_neg_one_mul, show (-1 : ℂ) = I ^ 2 by rw [I_sq],
        ← pow_add, ← pow_add, ← pow_add]
      apply I_pow_congr
      rw [show n - c = e by omega, hne]
      push_cast
      have hce : (c : ZMod 4) + e = 1 ∨ (c : ZMod 4) + e = 3 := by
        rw [hne] at hn4; push_cast at hn4; exact hn4
      linear_combination zmod4_case2 (h : ZMod 4) c e hce
    field_simp
    linear_combination (-(sgn n (h + c) * sgn n (n - c))) * hFF + hsign

end sample

/-! ### Trigonometric identities -/

omit hn G in
lemma cos_nat_mul_pi' (m : ℕ) : Complex.cos (m * π) = (-1) ^ m := by
  rw [show ((m : ℂ) * π) = (((m * π : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast; ring

omit hn G in
lemma sin_sub_nat_mul_pi' (x : ℂ) (m : ℕ) : Complex.sin (x - m * π) = (-1) ^ m * Complex.sin x := by
  rw [Complex.sin_sub, Complex.sin_nat_mul_pi, cos_nat_mul_pi']; ring

omit hn G in
lemma sin_add_nat_mul_pi' (x : ℂ) (m : ℕ) : Complex.sin (x + m * π) = (-1) ^ m * Complex.sin x := by
  rw [Complex.sin_add, Complex.sin_nat_mul_pi, cos_nat_mul_pi']; ring

omit hn G in
/-- The identity (2.6) of the expanded proof, in the form used in Step 2. -/
lemma trig_identity (h : ℕ) (z : ℂ) :
    (-1) ^ h * Complex.sin (π * (z - h) / ω₂ n) * Complex.sin (π * z / ω₁ n)
      - Complex.sin (π * (z - h) / ω₁ n) * Complex.sin (π * z / ω₂ n)
      = Complex.sin (π * h / ω₁ n) * Complex.sin (π * z) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hΩ : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have e1 : (π : ℂ) * (z - h) / ω₂ n = (π * z / ω₂ n + π * h / ω₁ n) - h * π := by
    field_simp
    linear_combination (h : ℂ) * hΩ
  have e2 : (π : ℂ) * (z - h) / ω₁ n = π * z / ω₁ n - π * h / ω₁ n := by ring
  have e3 : (π : ℂ) * z = π * z / ω₁ n + π * z / ω₂ n := by
    field_simp
    linear_combination z * hΩ
  rw [e1, e2]
  conv_rhs => rw [e3]
  rw [sin_sub_nat_mul_pi', Complex.sin_add, Complex.sin_sub, Complex.sin_add]
  have hsq : ((-1 : ℂ) ^ h) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linear_combination (Complex.sin (π * z / ω₂ n) * Complex.cos (π * h / ω₁ n)
    * Complex.sin (π * z / ω₁ n) + Complex.cos (π * z / ω₂ n) * Complex.sin (π * h / ω₁ n)
    * Complex.sin (π * z / ω₁ n)) * hsq

/-! ### The kernel difference identity (Step 2) -/

/-- Step 2: `K_h(z + n) - K_h(z) = -4π sin(πh/ω₁) Φ_h(z)`, at every point where the shift and
reflection identities apply. -/
theorem Kh_shift (hodd : Odd n) (h : ℕ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -(-1) ^ h) (z : ℂ)
    (h1 : z - h ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : -z ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n)) (h4 : (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n))
    (h5 : (ω₁ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n)) (h6 : (ω₁ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n))
    (h7 : Complex.sin (π * z) ≠ 0) :
    Kh n G h θ (z + n) - Kh n G h θ z
      = -4 * π * Complex.sin (π * h / ω₁ n) * Φh n G h θ z := by
  have hω : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  -- the four gamma values
  have hA : G.γ ((ω₂ n : ℂ) + (z - h)) = 2 * Complex.sin (π * (z - h) / ω₁ n) * G.γ (z - h) := by
    rw [add_comm]; exact G.shift₂ _ h1
  have hA' : G.γ ((ω₂ n : ℂ) + (z + n - h)) = 2 * Complex.sin (π * (z - h) / ω₂ n) * G.γ (z - h) := by
    rw [show (ω₂ n : ℂ) + (z + n - h) = (z - h) + ω₁ n by rw [hω]; ring]; exact G.shift₁ _ h1
  have hB : G.γ ((ω₂ n : ℂ) + z) * (2 * Complex.sin (π * (-z) / ω₂ n) * G.γ (-z)) = 1 := by
    have := G.reflect _ h3 h4
    rw [show (ω₁ n : ℂ) + ω₂ n - (ω₂ n + z) = -z + ω₁ n by ring, G.shift₁ _ h2] at this
    exact this
  have hB' : G.γ ((ω₂ n : ℂ) + (z + n)) * (2 * Complex.sin (π * (-z) / ω₁ n) * G.γ (-z)) = 1 := by
    have := G.reflect _ h5 h6
    rw [show (ω₁ n : ℂ) + ω₂ n - (ω₁ n + z) = -z + ω₂ n by ring, G.shift₂ _ h2] at this
    rw [show (ω₂ n : ℂ) + (z + n) = ω₁ n + z by rw [hω]; ring]
    exact this
  have hBinv := inv_eq_of_mul_eq_one_right hB
  have hB'inv := inv_eq_of_mul_eq_one_right hB'
  -- the exponential and the sine across one period
  have hexp : Complex.exp (-I * θ * (z + n)) = Complex.exp (-I * θ * z) * (-(-1) ^ h) := by
    rw [← hθ, ← Complex.exp_add]; congr 1; ring
  have hsin : Complex.sin (π * (z + n)) = -Complex.sin (π * z) := by
    rw [show (π : ℂ) * (z + n) = π * z + n * π by ring, sin_add_nat_mul_pi', hodd.neg_one_pow]
    ring
  have htrig := trig_identity n h z
  unfold Kh Rh Φh
  rw [hexp, hsin, hA, hA', div_eq_mul_inv (2 * Complex.sin (π * (z - h) / ω₂ n) * G.γ (z - h)),
    div_eq_mul_inv (2 * Complex.sin (π * (z - h) / ω₁ n) * G.γ (z - h)), hBinv, hB'inv,
    show (π : ℂ) * (-z) / ω₂ n = -(π * z / ω₂ n) by ring,
    show (π : ℂ) * (-z) / ω₁ n = -(π * z / ω₁ n) by ring, Complex.sin_neg, Complex.sin_neg]
  field_simp
  linear_combination (-4 * G.γ (-z) * G.γ (z - h)) * htrig

/-! ### Residues of the kernel -/

/-- The residue of `π / sin(π z)` at an integer `a` is `(-1)^a`. -/
lemma tendsto_pi_div_sin (a : ℕ) :
    Tendsto (fun z : ℂ => (z - a) * (π / Complex.sin (π * z))) (𝓝[≠] (a : ℂ)) (𝓝 ((-1) ^ a)) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (π * (-1) ^ a) (a : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) π (a : ℂ) := by
      simpa using (hasDerivAt_id (a : ℂ)).const_mul (π : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * a) * π) (a : ℂ) :=
      (Complex.hasDerivAt_sin ((π : ℂ) * a)).comp (a : ℂ) h1
    rw [show (π : ℂ) * a = a * π by ring, cos_nat_mul_pi'] at h2
    convert h2 using 1; ring
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : (π : ℂ) * (-1) ^ a ≠ 0 := mul_ne_zero hπ (pow_ne_zero _ (by norm_num))
  have hs' : Tendsto (fun z : ℂ => Complex.sin (π * z) / (z - a)) (𝓝[≠] (a : ℂ))
      (𝓝 (π * (-1) ^ a)) := by
    have hfa : Complex.sin ((π : ℂ) * a) = 0 := by
      rw [show (π : ℂ) * a = a * π by ring]; exact Complex.sin_nat_mul_pi a
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [slope, vsub_eq_sub, smul_eq_mul, hfa, sub_zero]
    rw [div_eq_inv_mul]
  have := (hs'.inv₀ hne).const_mul (π : ℂ)
  rw [show (π : ℂ) * ((π : ℂ) * (-1) ^ a)⁻¹ = (-1) ^ a by
    field_simp; rw [← pow_mul, mul_comm, pow_mul]; norm_num] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [inv_div]; ring

include hn in
/-- `R_h` is continuous at every integer `a`. -/
lemma Rh_continuousAt_int (h : ℕ) (a : ℤ) : ContinuousAt (Rh n G h) (a : ℂ) := by
  have hp1 : (ω₂ n : ℂ) + ((a : ℂ) - h) ∉ poleSet (ω₁ n) (ω₂ n) := by
    have := ω₂_add_int_not_pole n hn (a - h); push_cast at this; exact this
  have hp2 : (ω₂ n : ℂ) + (a : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := ω₂_add_int_not_pole n hn a
  have hne : G.γ ((ω₂ n : ℂ) + (a : ℂ)) ≠ 0 := ω₂_add_int_ne_zero n hn G a
  unfold Rh
  refine ContinuousAt.div ?_ ?_ hne
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + (z - h)) (G.continuousAt _ hp1)
      (by fun_prop)
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + z) (G.continuousAt _ hp2)
      (by fun_prop)

include hn in
/-- Step 1: the residue of `K_h` at an integer `a`. -/
theorem Kh_residue_int (h : ℕ) (θ : ℝ) (a : ℕ) :
    HasResidue (Kh n G h θ) a ((-1) ^ a * Complex.exp (-I * θ * a) * Rh n G h a) := by
  have h1 := tendsto_pi_div_sin a
  have h2 : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * Rh n G h z) (𝓝[≠] (a : ℂ))
      (𝓝 (Complex.exp (-I * θ * a) * Rh n G h a)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have := Rh_continuousAt_int n hn G h a
    push_cast at this
    exact ((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul this
  unfold HasResidue
  have := h1.mul h2
  rw [← mul_assoc] at this
  refine this.congr' ?_
  filter_upwards with z
  unfold Kh; ring

/-- The residue of `Φ_h` at a pole `p` of `γ(z - h)` which is not a pole of `γ(-z)`. -/
theorem Φh_residue (h : ℕ) (θ : ℝ) (p : ℂ) (hp : p - h ∈ poleSet (ω₁ n) (ω₂ n))
    (hp' : -p ∉ poleSet (ω₁ n) (ω₂ n)) :
    HasResidue (Φh n G h θ) p (Complex.exp (-I * θ * p) * G.γ (-p) * G.residue (p - h)) := by
  have h1 : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * G.γ (-z)) (𝓝[≠] p)
      (𝓝 (Complex.exp (-I * θ * p) * G.γ (-p))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul
      (ContinuousAt.comp (f := fun z : ℂ => -z) (G.continuousAt _ hp') (by fun_prop))
  have h2 : Tendsto (fun z : ℂ => ((z - h) - (p - h)) * G.γ (z - h)) (𝓝[≠] p)
      (𝓝 (G.residue (p - h))) := by
    have hmap := tendsto_punctured_of_injective (continuous_sub_right (h : ℂ))
      (sub_left_injective) p
    exact (G.hasResidue (p - h) hp).comp hmap
  unfold HasResidue
  refine (h1.mul h2).congr' ?_
  filter_upwards with z
  unfold Φh; ring

/-- Step 3: the residue of `K_h` at a crossed pole, from the difference identity. -/
theorem Kh_residue_of_shift (h : ℕ) (θ : ℝ) (p ρ : ℂ)
    (hev : ∀ᶠ z in 𝓝[≠] p, Kh n G h θ (z + n) - Kh n G h θ z
      = -4 * π * Complex.sin (π * h / ω₁ n) * Φh n G h θ z)
    (hc : ContinuousAt (fun z => Kh n G h θ (z + n)) p)
    (hΦ : HasResidue (Φh n G h θ) p ρ) :
    HasResidue (Kh n G h θ) p (4 * π * Complex.sin (π * h / ω₁ n) * ρ) := by
  have h1 : Tendsto (fun z : ℂ => (z - p) * Kh n G h θ (z + n)) (𝓝[≠] p) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => (z - p) * Kh n G h θ (z + n)) (𝓝 p)
        (𝓝 ((p - p) * Kh n G h θ (p + n))) :=
      ((continuous_id.sub continuous_const).continuousAt).mul hc
    simp only [sub_self, zero_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have h2 := (hΦ.const_mul (4 * π * Complex.sin (π * h / ω₁ n)))
  unfold HasResidue
  have := h1.add h2
  simp only [zero_add] at this
  refine this.congr' ?_
  filter_upwards [hev] with z hz
  have : Kh n G h θ z = Kh n G h θ (z + n) + 4 * π * Complex.sin (π * h / ω₁ n) * Φh n G h θ z := by
    linear_combination -hz
  rw [this]; ring

/-! ### Decay along vertical lines (Step 4) -/

omit hn G in
/-- `|sin w| ≥ e^{|Im w|} / 4` when `|Im w| ≥ 1`. -/
lemma norm_sin_ge (w : ℂ) (hw : 1 ≤ |w.im|) : Real.exp |w.im| / 4 ≤ ‖Complex.sin w‖ := by
  have h2 : 2 * Complex.sin w = (Complex.exp (-w * I) - Complex.exp (w * I)) * I := Complex.two_sin w
  have hn : ‖(2 : ℂ) * Complex.sin w‖ = 2 * ‖Complex.sin w‖ := by
    rw [norm_mul]; norm_num
  have hI : ‖(Complex.exp (-w * I) - Complex.exp (w * I)) * I‖
      = ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hlow : |‖Complex.exp (-w * I)‖ - ‖Complex.exp (w * I)‖|
      ≤ ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := abs_norm_sub_norm_le _ _
  rw [Complex.norm_exp, Complex.norm_exp] at hlow
  have hre1 : (-w * I).re = w.im := by simp
  have hre2 : (w * I).re = -w.im := by simp
  rw [hre1, hre2] at hlow
  have key : Real.exp |w.im| / 2 ≤ |Real.exp w.im - Real.exp (-w.im)| := by
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
    have hexp1 : Real.exp 1 ≤ Real.exp |w.im| := Real.exp_le_exp.2 hw
    have hpos : 0 < Real.exp |w.im| := Real.exp_pos _
    have hinv : Real.exp (-|w.im|) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
      linarith
    have hone : 1 ≤ Real.exp |w.im| := by
      have := Real.exp_le_exp.2 (le_of_lt (lt_of_lt_of_le zero_lt_one hw) : (0 : ℝ) ≤ |w.im|)
      simpa using this
    rcases le_total 0 w.im with h0 | h0
    · rw [abs_of_nonneg h0] at *
      rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 (by linarith : -w.im ≤ w.im)])]
      linarith
    · rw [abs_of_nonpos h0] at *
      simp only [neg_neg] at hinv
      rw [abs_of_nonpos (by linarith [Real.exp_le_exp.2 (by linarith : w.im ≤ -w.im)])]
      linarith
  have := calc Real.exp |w.im| / 2 ≤ |Real.exp w.im - Real.exp (-w.im)| := key
    _ ≤ ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := hlow
    _ = ‖(2 : ℂ) * Complex.sin w‖ := by rw [h2, hI]
    _ = 2 * ‖Complex.sin w‖ := hn
  linarith

/-- Step 4: exponential decay of `K_h` on vertical lines, uniformly on a closed strip. -/
theorem Kh_bound (h : ℕ) (θ : ℝ) (hθ : |θ| ≤ π) (a b : ℝ) :
    ∃ M T : ℝ, 0 < T ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
      ‖Kh n G h θ z‖ ≤ M * Real.exp (-(π * h / (ω₁ n * ω₂ n)) * |z.im|) := by
  obtain ⟨C, T, hT, hC⟩ := G.ratio_bound (-h) (a + ω₂ n) (b + ω₂ n)
  refine ⟨4 * π * C, max T 1, lt_max_of_lt_left hT, ?_⟩
  intro z hza hzb hzT
  have hT' : T ≤ |z.im| := le_trans (le_max_left _ _) hzT
  have h1' : 1 ≤ |z.im| := le_trans (le_max_right _ _) hzT
  have him : z.im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at h1'; linarith
  -- the ratio
  set z' : ℂ := (ω₂ n : ℂ) + z with hz'
  have hz'im : z'.im = z.im := by simp [hz']
  have hz're : z'.re = ω₂ n + z.re := by simp [hz']
  have hp1 : z' ∉ poleSet (ω₁ n) (ω₂ n) := not_mem_poleSet_of_im_ne_zero (by rw [hz'im]; exact him)
  have hp2 : z' + ((-h : ℝ) : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) :=
    not_mem_poleSet_of_im_ne_zero (by simp [hz'im, him])
  have hz'0 : G.γ z' ≠ 0 :=
    G.ne_zero _ hp1 (not_mem_zeroSet_of_im_ne_zero (by rw [hz'im]; exact him))
  have hratio := hC z' (by rw [hz're]; linarith) (by rw [hz're]; linarith) (by rw [hz'im]; exact hT')
    hp1 hp2
  rw [hz'im] at hratio
  have hRh : ‖Rh n G h z‖ ≤ C * Real.exp (π * (-h) * |z.im| / (ω₁ n * ω₂ n)) := by
    unfold Rh
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hz'0)]
    have : (ω₂ n : ℂ) + (z - h) = z' + ((-h : ℝ) : ℂ) := by rw [hz']; push_cast; ring
    rw [this]
    exact hratio
  -- the exponential and the sine
  have hexp : ‖Complex.exp (-I * θ * z)‖ ≤ Real.exp (π * |z.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (-I * θ * z).re = θ * z.im := by simp
    rw [this]
    calc θ * z.im ≤ |θ * z.im| := le_abs_self _
      _ = |θ| * |z.im| := abs_mul _ _
      _ ≤ π * |z.im| := by gcongr
  have hsin : Real.exp (π * |z.im|) / 4 ≤ ‖Complex.sin (π * z)‖ := by
    have hpi := Real.pi_gt_three
    have := norm_sin_ge ((π : ℂ) * z) (by
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith)
    simpa [abs_mul, abs_of_pos Real.pi_pos] using this
  have hsin0 : Complex.sin (π * z) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsin
    have := Real.exp_pos (π * |z.im|); linarith
  -- assembly
  unfold Kh
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have := hratio
    have : C * Real.exp (π * (-h) * |z.im| / (ω₁ n * ω₂ n)) * ‖G.γ z'‖ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (Real.exp_pos _)) (norm_pos_iff.2 hz'0)
    linarith [norm_nonneg (G.γ (z' + ((-h : ℝ) : ℂ)))]
  have hE : Real.exp (π * (-h) * |z.im| / (ω₁ n * ω₂ n))
      = Real.exp (-(π * h / (ω₁ n * ω₂ n)) * |z.im|) := by congr 1; ring
  rw [hE] at hRh
  have hpos4 : 0 < Real.exp (π * |z.im|) / 4 := by positivity
  calc π * ‖Complex.exp (-I * θ * z)‖ / ‖Complex.sin (π * z)‖ * ‖Rh n G h z‖
      ≤ π * Real.exp (π * |z.im|) / (Real.exp (π * |z.im|) / 4)
        * (C * Real.exp (-(π * h / (ω₁ n * ω₂ n)) * |z.im|)) := by
        gcongr
    _ = 4 * π * C * Real.exp (-(π * h / (ω₁ n * ω₂ n)) * |z.im|) := by
        field_simp
        try ring

/-! ### Real points of the form `q₁ + q₂ ω₂` -/

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₂ > 0` is not a pole. -/
lemma not_pole_of_pos_coeff (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n) (hq : 0 < q₂) :
    (x : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, -, h2⟩ := pole_coeff n hn q₁ q₂ x hx hmem
  have : (0 : ℚ) ≤ ((r + s : ℕ) : ℚ) := by positivity
  linarith

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₁ > 0` is not a pole. -/
lemma not_pole_of_pos_const (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n) (hq : 0 < q₁) :
    (x : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, h1, -⟩ := pole_coeff n hn q₁ q₂ x hx hmem
  have : (0 : ℚ) ≤ (r * n : ℚ) := by positivity
  linarith

include hn in
/-- A real point `q₁ + q₂ ω₂` with `-n < q₁ < 0` is not a pole. -/
lemma not_pole_of_const_mem_Ioo (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n) (hq1 : -(n : ℚ) < q₁)
    (hq2 : q₁ < 0) : (x : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, h1, -⟩ := pole_coeff n hn q₁ q₂ x hx hmem
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp at h1; linarith
  · have : (1 : ℚ) ≤ r := by exact_mod_cast hr
    have : (n : ℚ) ≤ r * n := by nlinarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
    linarith

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₂ = 0`, `q₁ ≠ 0` is not a pole. -/
lemma not_pole_of_zero_coeff (q₁ : ℚ) (x : ℝ) (hx : x = q₁) (hq : q₁ ≠ 0) :
    (x : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, h1, h2⟩ := pole_coeff n hn q₁ 0 x (by rw [hx]; simp) hmem
  have : r + s = 0 := by
    have : ((r + s : ℕ) : ℚ) = 0 := by linarith
    exact_mod_cast this
  have hr : r = 0 := by omega
  subst hr
  simp at h1
  exact hq h1

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₂ < 2` is not a zero. -/
lemma not_zero_of_coeff_lt (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n) (hq : q₂ < 2) :
    (x : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, -, h2⟩ := zero_coeff n hn q₁ q₂ x hx hmem
  have : (2 : ℚ) ≤ ((r + s + 2 : ℕ) : ℚ) := by
    push_cast; linarith [(Nat.cast_nonneg r : (0:ℚ) ≤ r), (Nat.cast_nonneg s : (0:ℚ) ≤ s)]
  linarith

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₂ = 2`, `q₁ < n` is not a zero. -/
lemma not_zero_of_coeff_two (q₁ : ℚ) (x : ℝ) (hx : x = q₁ + 2 * ω₂ n) (hq : q₁ < n) :
    (x : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  intro hmem
  obtain ⟨r, s, h1, h2⟩ := zero_coeff n hn q₁ 2 x hx hmem
  have hrs : r + s = 0 := by
    have : ((r + s + 2 : ℕ) : ℚ) = 2 := h2.symm
    push_cast at this
    have : ((r + s : ℕ) : ℚ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hr : r = 0 := by omega
  subst hr
  simp at h1
  linarith

include hn in
/-- A real point `q₁ + q₂ ω₂` with `q₂ ≠ 0` is not an integer. -/
lemma ne_int_of_coeff_ne_zero (q₁ q₂ : ℚ) (x : ℝ) (hx : x = q₁ + q₂ * ω₂ n) (hq : q₂ ≠ 0)
    (m : ℤ) : x ≠ m := by
  intro hxm
  have h1 : x - m = ((q₁ - m : ℚ) : ℝ) + q₂ * ω₂ n := by rw [hx]; push_cast; ring
  have := indep n hn (q₁ - m) q₂ (by rw [← h1, hxm, sub_self])
  exact hq this.2

omit hn G in
/-- `sin (π z) ≠ 0` when `z` is not an integer. -/
lemma sin_pi_ne_zero_of_not_int (z : ℂ) (hz : ∀ m : ℤ, z ≠ m) : Complex.sin (π * z) ≠ 0 := by
  intro h0
  rw [Complex.sin_eq_zero_iff] at h0
  obtain ⟨m, hm⟩ := h0
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply hz m
  apply mul_left_cancel₀ hπ
  rw [hm]; ring

/-! ### Continuity and differentiability of the kernel -/

omit hn in
lemma Rh_continuousAt (h : ℕ) (w : ℂ) (hp1 : (ω₂ n : ℂ) + (w - h) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0) :
    ContinuousAt (Rh n G h) w := by
  unfold Rh
  refine ContinuousAt.div ?_ ?_ hne
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + (z - h)) (G.continuousAt _ hp1)
      (by fun_prop)
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + z) (G.continuousAt _ hp2)
      (by fun_prop)

omit hn in
lemma Rh_differentiableAt (h : ℕ) (w : ℂ) (hp1 : (ω₂ n : ℂ) + (w - h) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0) :
    DifferentiableAt ℂ (Rh n G h) w := by
  unfold Rh
  refine DifferentiableAt.div ?_ ?_ hne
  · exact (G.differentiableAt _ hp1).comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + (z - h)) w)
  · exact (G.differentiableAt _ hp2).comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + z) w)

omit hn in
lemma Kh_differentiableAt (h : ℕ) (θ : ℝ) (w : ℂ)
    (hp1 : (ω₂ n : ℂ) + (w - h) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0)
    (hsin : Complex.sin (π * w) ≠ 0) : DifferentiableAt ℂ (Kh n G h θ) w := by
  unfold Kh
  refine DifferentiableAt.mul (DifferentiableAt.div ?_ ?_ hsin) (Rh_differentiableAt n G h w hp1 hp2 hne)
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => (π : ℂ) * Complex.exp (-I * θ * z)).differentiableAt
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.sin (π * z)).differentiableAt

omit hn in
lemma Kh_shift_continuousAt (h : ℕ) (θ : ℝ) (w : ℂ)
    (hp1 : (ω₂ n : ℂ) + ((w + n) - h) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + (w + n) ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + (w + n)) ≠ 0)
    (hsin : Complex.sin (π * (w + n)) ≠ 0) :
    ContinuousAt (fun z => Kh n G h θ (z + n)) w := by
  have hR := (Rh_continuousAt n G h (w + n) hp1 hp2 hne)
  have hR' : ContinuousAt (fun z : ℂ => Rh n G h (z + n)) w :=
    ContinuousAt.comp (f := fun z : ℂ => z + n) hR (by fun_prop)
  simp only [Kh]
  refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ hsin) hR'
  · exact (by fun_prop : Continuous fun z : ℂ => (π : ℂ) * Complex.exp (-I * θ * (z + n))).continuousAt
  · exact (by fun_prop : Continuous fun z : ℂ => Complex.sin (π * (z + n))).continuousAt

omit hn G in
/-- The zeros of `sin (π z)` are isolated. -/
lemma eventually_sin_ne_zero (p : ℂ) : ∀ᶠ z in 𝓝[≠] p, Complex.sin (π * z) ≠ 0 := by
  have hdiff : Differentiable ℂ (fun z : ℂ => Complex.sin (π * z)) := by fun_prop
  have han : AnalyticAt ℂ (fun z : ℂ => Complex.sin (π * z)) p := hdiff.analyticAt p
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exfalso
    have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) π p := by
      simpa using (hasDerivAt_id p).const_mul (π : ℂ)
    have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * p) * π) p :=
      (Complex.hasDerivAt_sin _).comp p h1
    have h0' : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝 p] (fun z => Complex.sin (π * z)) := by
      filter_upwards [h0] with z hz; exact hz.symm
    have hd0 : HasDerivAt (fun _ : ℂ => (0 : ℂ)) (Complex.cos (π * p) * π) p :=
      hd.congr_of_eventuallyEq h0'
    have hu := hd0.unique (hasDerivAt_const p (0 : ℂ))
    have hs : Complex.sin (π * p) = 0 := h0.self_of_nhds
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : Complex.cos (π * p) = 0 := by
      rcases mul_eq_zero.1 hu with h | h
      · exact h
      · exact absurd h hπ
    have := Complex.sin_sq_add_cos_sq (π * p)
    rw [hs, hc] at this; norm_num at this
  · exact h0

omit hn in
/-- The difference identity holds on a punctured neighbourhood of every point. -/
lemma Kh_shift_eventually (hodd : Odd n) (h : ℕ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -(-1) ^ h) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, Kh n G h θ (z + n) - Kh n G h θ z
      = -4 * π * Complex.sin (π * h / ω₁ n) * Φh n G h θ z := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have e1 := (tendsto_punctured_of_injective (continuous_sub_right (h : ℂ)) sub_left_injective
    p).eventually (eventually_not_mem_poleSet hω₁ hω₂ (p - h))
  have e2 := (tendsto_punctured_of_injective continuous_neg neg_injective p).eventually
    (eventually_not_mem_poleSet hω₁ hω₂ (-p))
  have e3 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) p).eventually (eventually_not_mem_poleSet hω₁ hω₂ ((ω₂ n : ℂ) + p))
  have e4 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) p).eventually (eventually_not_mem_zeroSet hω₁ hω₂ ((ω₂ n : ℂ) + p))
  have e5 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) p).eventually (eventually_not_mem_poleSet hω₁ hω₂ ((ω₁ n : ℂ) + p))
  have e6 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) p).eventually (eventually_not_mem_zeroSet hω₁ hω₂ ((ω₁ n : ℂ) + p))
  have e7 := eventually_sin_ne_zero p
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with z h1 h2 h3 h4 h5 h6 h7
  exact Kh_shift n G hodd h θ hθ z h1 h2 h3 h4 h5 h6 h7

/-! ### The frequency `θ = π v / n` -/

omit G in
include hn in
/-- `e^{-iθn} = (-1)^{h-1}` for a principal frequency. -/
lemma theta_period (hodd : Odd n) (h : ℕ) (hh1 : 1 ≤ h) (k v : ℤ)
    (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (h - 1))) :
    Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * n) = -(-1) ^ h := by
  obtain ⟨m, hm⟩ := hv
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hv' : (v : ℂ) = 2 * k + n * h' + 2 * n * m := by
    have : v = 2 * k + n * h' + 2 * n * m := by push_cast at hm; linarith
    rw [this]; push_cast; ring
  push_cast
  rw [show -I * (π * v / n) * n = -I * π * v by field_simp]
  have e1 : -I * π * (v : ℂ) = ((-k - n * m : ℤ) : ℂ) * (2 * π * I)
      + ((n * h' : ℕ) : ℂ) * (-(π * I)) := by rw [hv']; push_cast; ring
  rw [e1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_nat_mul,
    Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, pow_mul, hodd.neg_one_pow, pow_succ]
  ring

omit G in
include hn in
/-- `e^{-iθa} = e^{-2πika/n} (-1)^{a(h-1)}` for a principal frequency and a natural `a`. -/
lemma theta_sample (h : ℕ) (hh1 : 1 ≤ h) (k v : ℤ)
    (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (h - 1))) (a : ℕ) :
    Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * a)
      = Complex.exp (-(2 * π * I * k * a / n)) * (-1) ^ (a * (h - 1)) := by
  obtain ⟨m, hm⟩ := hv
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hv' : (v : ℂ) = 2 * k + n * h' + 2 * n * m := by
    have : v = 2 * k + n * h' + 2 * n * m := by push_cast at hm; linarith
    rw [this]; push_cast; ring
  simp only [Nat.add_sub_cancel]
  push_cast
  have e1 : -I * (π * v / n) * (a : ℂ) = -(2 * π * I * k * a / n)
      + (((a * h' : ℕ) : ℂ) * (-(π * I)) + ((-(a * m) : ℤ) : ℂ) * (2 * π * I)) := by
    rw [hv']; push_cast; field_simp; ring
  rw [e1, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_nat_mul, show Complex.exp (-(π * I)) = -1 by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num]

omit G in
include hn in
lemma theta_abs_le (v : ℤ) (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n) : |π * v / n| ≤ π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn0, div_le_iff₀ hn0]
  have : |(v : ℝ)| ≤ n := by
    rw [abs_le]; constructor <;> exact_mod_cast (by assumption)
  nlinarith [Real.pi_pos]

/-! ### The choice of `ε` and the position of the poles -/

omit G in
lemma eps_exists (h : ℕ) :
    ∃ (ε : ℝ) (L : ℕ), 0 < ε ∧ ε < 1 ∧ (∀ ℓ : ℕ, ℓ ≤ L → -ε < h - ℓ * ω₂ n) ∧
      (∀ ℓ : ℕ, L + 1 ≤ ℓ → h - ℓ * ω₂ n < -ε) := by
  have hω := ω₂_pos n
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌊(h : ℝ) / ω₂ n⌋₊ := ⟨_, rfl⟩
  have hL1 : (L : ℝ) * ω₂ n ≤ h := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ h / ω₂ n)
    rw [← hL] at this; rwa [le_div_iff₀ hω] at this
  have hL2 : (h : ℝ) < (L + 1) * ω₂ n := by
    have := Nat.lt_floor_add_one ((h : ℝ) / ω₂ n)
    rw [← hL] at this; rwa [div_lt_iff₀ hω] at this
  have hmin1 : 0 < min (1 / 2) (((L + 1) * ω₂ n - h) / 2) := lt_min (by norm_num) (by linarith)
  have hmin2 : min (1 / 2) (((L + 1) * ω₂ n - h) / 2) ≤ ((L + 1) * ω₂ n - h) / 2 := min_le_right _ _
  have hmin3 : min (1 / 2) (((L + 1) * ω₂ n - h) / 2) ≤ 1 / 2 := min_le_left _ _
  refine ⟨min (1 / 2) (((L + 1) * ω₂ n - h) / 2), L, hmin1, by linarith, ?_, ?_⟩
  · intro ℓ hℓ
    have hℓ' : (ℓ : ℝ) ≤ L := by exact_mod_cast hℓ
    have : (ℓ : ℝ) * ω₂ n ≤ L * ω₂ n := by gcongr
    linarith
  · intro ℓ hℓ
    have hℓ' : ((L + 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have : ((L + 1 : ℕ) : ℝ) * ω₂ n ≤ ℓ * ω₂ n := by gcongr
    push_cast at this
    linarith

omit G in
include hn in
/-- No left pole `h - r ω₁ - s ω₂` lies on the line `Re z = -ε`. -/
lemma left_pole_ne (h : ℕ) (hh2 : h ≤ n - 1) (ε : ℝ) (L : ℕ) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < h - ℓ * ω₂ n) (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → h - ℓ * ω₂ n < -ε)
    (r s : ℕ) : (h : ℝ) - r * ω₁ n - s * ω₂ n ≠ -ε := by
  intro heq
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.cast_zero, zero_mul, sub_zero] at heq
    rcases le_or_gt s L with hs | hs
    · have := hP1 s hs; linarith
    · have := hP2 s hs; linarith
  · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (0 : ℝ) ≤ s * ω₂ n := mul_nonneg (Nat.cast_nonneg s) (ω₂_pos n).le
    have h3 := ω₁_eq n
    have h4 : (h : ℝ) ≤ n - 1 := by
      have : (h : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hh2
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
    have h5 : ω₁ n ≤ r * ω₁ n := by nlinarith [ω₁_pos n]
    have h6 := one_lt_ω₂ n
    linarith

omit G in
include hn in
/-- Left poles with `r ≥ 1` lie to the left of the line. -/
lemma left_pole_lt (h : ℕ) (hh2 : h ≤ n - 1) (ε : ℝ) (hε1 : ε < 1) (r s : ℕ) (hr : 1 ≤ r) :
    (h : ℝ) - r * ω₁ n - s * ω₂ n < -ε := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (0 : ℝ) ≤ s * ω₂ n := mul_nonneg (Nat.cast_nonneg s) (ω₂_pos n).le
  have h3 := ω₁_eq n
  have h4 : (h : ℝ) ≤ n - 1 := by
    have : (h : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hh2
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have h5 : ω₁ n ≤ r * ω₁ n := by nlinarith [ω₁_pos n]
  have h6 := one_lt_ω₂ n
  linarith

omit G in
include hn in
/-- The conditions of the difference identity hold on the line `Re z = -ε`. -/
lemma line_conditions (h : ℕ) (hh2 : h ≤ n - 1) (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < h - ℓ * ω₂ n) (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → h - ℓ * ω₂ n < -ε)
    (t : ℝ) :
    (((-ε : ℝ) : ℂ) + t * I) - h ∉ poleSet (ω₁ n) (ω₂ n) ∧
    -(((-ε : ℝ) : ℂ) + t * I) ∉ poleSet (ω₁ n) (ω₂ n) ∧
    (ω₂ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ poleSet (ω₁ n) (ω₂ n) ∧
    (ω₂ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ zeroSet (ω₁ n) (ω₂ n) ∧
    (ω₁ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ poleSet (ω₁ n) (ω₂ n) ∧
    (ω₁ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ zeroSet (ω₁ n) (ω₂ n) ∧
    Complex.sin (π * (((-ε : ℝ) : ℂ) + t * I)) ≠ 0 := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have h6 := one_lt_ω₂ n
  have h7 := n_lt_ω₁ n
  have h8 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r, s, hrs⟩
    have hre := congrArg Complex.re hrs
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, natCast_re, neg_re, natCast_im, sub_self, add_zero] at hre
    exact left_pole_ne n hn h hh2 ε L hε1 hP1 hP2 r s (by linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · apply sin_pi_ne_zero_of_not_int
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      intCast_re, zero_add] at hre
    have h1 : (-1 : ℝ) < m := by linarith
    have h2 : (m : ℝ) < 0 := by linarith
    have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (0 : ℤ) := by exact_mod_cast h2
    omega

/-! ### Step 1: the residues at the integers and the finite Fourier sum -/

section main
variable [NeZero n] (hodd : Odd n)

lemma stdAddChar_eq (k : ℤ) (a : ZMod n) :
    ZMod.stdAddChar (-(a * (k : ZMod n))) = Complex.exp (-(2 * π * I * k * a.val / n)) := by
  have := ZMod.stdAddChar_coe (N := n) (-(a.val * k))
  rw [show ((-(a.val * k : ℤ) : ℤ) : ZMod n) = -(a * (k : ZMod n)) by
    push_cast; rw [ZMod.natCast_zmod_val]] at this
  rw [this]; congr 1; push_cast; ring

lemma sign_collapse (h : ℕ) (hh1 : 1 ≤ h) (a : ℕ) :
    (-1 : ℂ) ^ a * (-1) ^ (a * (h - 1)) * (-1) ^ (h * (a + 1)) = (-1) ^ h := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← pow_add, ← pow_add,
    show a + a * h' + (h' + 1) * (a + 1) = 2 * (a + a * h') + (h' + 1) by ring, pow_add, pow_mul]
  norm_num

/-- Step 1: the sum of the residues of `K_h` at `0, …, n-1`. -/
theorem residue_sum_int (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (k v : ℤ)
    (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (h - 1))) :
    ∑ a : ZMod n, (-1) ^ a.val * Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * a.val) * Rh n G h a.val
      = (-1) ^ h * Real.sqrt (d n) * F n G h *
        (∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n))) * (toCoeffData n hn G hodd).B a h
          + ω₂ n * Complex.exp (-(2 * π * I * k * h / n))) := by
  have hd0 := sqrt_d_ne_zero n
  have hFh := F_nat_ne_zero n hn G h
  have hterm : ∀ a : ZMod n,
      (-1) ^ a.val * Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * a.val) * Rh n G h a.val
      = (-1) ^ h * Real.sqrt (d n) * F n G h * (ZMod.stdAddChar (-(a * (k : ZMod n)))
          * ((toCoeffData n hn G hodd).B a h + ω₂ n * (if a.val = h then 1 else 0))) := by
    intro a
    have hav : a.val ≤ n - 1 := by have := ZMod.val_lt a; omega
    have hs := sample_rule n hn G hodd h hh1 hh2 a.val hav
    rw [ZMod.natCast_zmod_val] at hs
    have hm : (-1 : ℂ) ^ (h * (a.val + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hm2 : ((-1 : ℂ) ^ (h * (a.val + 1))) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hR : Rh n G h a.val = ((toCoeffData n hn G hodd).B a h
        + ω₂ n * (if a.val = h then 1 else 0)) * (Real.sqrt (d n) * F n G h)
        * (-1) ^ (h * (a.val + 1)) := by
      rw [hs]; field_simp; linear_combination (-(Rh n G h a.val)) * hm2
    rw [hR, theta_sample n hn h hh1 k v hv a.val, stdAddChar_eq n k a]
    have hsgn := sign_collapse h hh1 a.val
    linear_combination (Complex.exp (-(2 * π * I * k * a.val / n))
      * (((toCoeffData n hn G hodd).B a h + ω₂ n * (if a.val = h then 1 else 0))
        * (Real.sqrt (d n) * F n G h))) * hsgn
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (h : ZMod n)]
  · rw [val_natCast' n h hh2, if_pos rfl, mul_one, stdAddChar_eq n k, val_natCast' n h hh2]
    ring
  · intro a _ ha
    have : a.val ≠ h := by
      intro e; apply ha; rw [← ZMod.natCast_zmod_val a, e]
    simp [this]
  · intro habs; exact absurd (Finset.mem_univ _) habs

/-! ### Step 6: the two-gamma integral with the crossed poles -/

omit hn G in
/-- The crossed poles `p_ℓ = h - ℓ ω₂`. -/
noncomputable def pl (h ℓ : ℕ) : ℂ := (h : ℂ) - ℓ * ω₂ n

omit hn in
/-- The residues of `Φ_h` at the crossed poles. -/
noncomputable def ρΦ (h : ℕ) (θ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-I * θ * w) * G.γ (-w) * G.residue (w - h)

omit hn G in
lemma pl_injective (h : ℕ) : Function.Injective (pl n h) := by
  intro x y hxy
  have hω : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have : (x : ℂ) * ω₂ n = y * ω₂ n := by unfold pl at hxy; linear_combination -hxy
  exact_mod_cast mul_right_cancel₀ hω this

include hn in
lemma pl_ne_nat (h ℓ a : ℕ) : pl n h (ℓ + 1) ≠ (a : ℂ) := by
  have := ne_int_of_coeff_ne_zero n hn h (-(ℓ + 1 : ℚ)) ((h : ℝ) - (ℓ + 1) * ω₂ n)
    (by push_cast; ring) (by push_cast; linarith) a
  intro heq
  apply this
  have h2 : (((h : ℝ) - (ℓ + 1) * ω₂ n : ℝ) : ℂ) = (a : ℂ) := by
    rw [← heq]; unfold pl; push_cast; ring
  have h3 : (h : ℝ) - (ℓ + 1) * ω₂ n = (a : ℝ) := by exact_mod_cast h2
  rw [h3]; norm_cast

include hn in
/-- Step 6: the two-gamma integral along `Re z = -ε` with the crossed poles `p_0, …, p_L`. -/
theorem two_gamma_applied (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (v : ℤ)
    (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n) (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < h - ℓ * ω₂ n) (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → h - ℓ * ω₂ n < -ε) :
    lineIntegral (Φh n G h (π * v / n)) (-ε)
      + 2 * π * I * ∑ ℓ ∈ Finset.range (L + 1), ρΦ n G h (π * v / n) (pl n h ℓ)
      = I * Real.sqrt (ω₁ n * ω₂ n) * Complex.exp (-I * h * ((π * v / n : ℝ) : ℂ) / 2)
        * G.γ (((ω₁ n + ω₂ n + h) / 2 - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ))
        * G.γ (((ω₁ n + ω₂ n + h) / 2 + (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) * G.γ (-h) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩ : ω₁ n * ω₂ n = ω₁ n + ω₂ n := ω₁_mul_ω₂ n
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast hΩ
  have hω₁C : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast hω₁.ne'
  have hω₂C : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast hω₂.ne'
  have hvr : (v : ℝ) ≤ n := by exact_mod_cast hv2
  have hvl : -(n : ℝ) ≤ v := by exact_mod_cast hv1
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hbound1 : (ω₁ n + ω₂ n) * v / (2 * n) ≤ (ω₁ n + ω₂ n) / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hbound2 : -((ω₁ n + ω₂ n) / 2) ≤ (ω₁ n + ω₂ n) * v / (2 * n) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- the two-gamma integrand is `Φ_h`
  have hΦeq : (fun z : ℂ => Complex.exp (π * I * z * (2 * ((((ω₁ n + ω₂ n + h) / 2
      - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ) + 0 + (-(h : ℂ)) - ω₁ n - ω₂ n) / (ω₁ n * ω₂ n))
      * G.γ (-(h : ℂ) + z) * G.γ (0 - z)) = Φh n G h (π * v / n) := by
    funext z
    unfold Φh
    have e : Complex.exp (π * I * z * (2 * ((((ω₁ n + ω₂ n + h) / 2
        - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ) + 0 + (-(h : ℂ)) - ω₁ n - ω₂ n) / (ω₁ n * ω₂ n))
        = Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * z) := by
      congr 1
      push_cast
      field_simp
      linear_combination (z * (v : ℂ)) * hΩC
    rw [e, show (0 : ℂ) - z = -z by ring, show -(h : ℂ) + z = z - h by ring]; ring
  -- no pinch
  have hpinch : ∀ r s r' s' : ℕ,
      -(-(h : ℂ)) - r * ω₁ n - s * ω₂ n ≠ 0 + r' * ω₁ n + s' * ω₂ n := by
    intro r s r' s' heq
    have hre := congrArg Complex.re heq
    simp only [neg_neg, sub_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero, zero_re, zero_add] at hre
    have := (lattice n hn h (r + r') (s + s') (by push_cast; linarith)).2.2
    omega
  -- the line avoids the left poles
  have hline : ∀ r s : ℕ, (-(-(h : ℂ)) - r * ω₁ n - s * ω₂ n).re ≠ -ε := by
    intro r s
    simp only [neg_neg, sub_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
      sub_zero]
    exact left_pole_ne n hn h hh2 ε L hε1 hP1 hP2 r s
  -- the crossed poles
  have hS : ∀ w, w ∈ (Finset.range (L + 1)).image (pl n h) ↔
      (∃ r s : ℕ, w = -(-(h : ℂ)) - r * ω₁ n - s * ω₂ n) ∧ -ε < w.re := by
    intro w; constructor
    · intro hw
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hw
      refine ⟨⟨0, ℓ, by simp [pl]⟩, ?_⟩
      have := hP1 ℓ (by have := Finset.mem_range.1 hℓ; omega)
      simp only [pl, sub_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
        sub_zero]
      exact this
    · rintro ⟨⟨r, s, rfl⟩, hre⟩
      simp only [neg_neg, sub_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im,
        mul_zero, sub_zero] at hre
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rcases le_or_gt s L with hs | hs
        · refine Finset.mem_image.2 ⟨s, Finset.mem_range.2 (by omega), ?_⟩
          simp [pl]
        · exfalso; have := hP2 s hs; simp only [Nat.cast_zero, zero_mul, sub_zero] at hre; linarith
      · exfalso; have := left_pole_lt n hn h hh2 ε hε1 r s hr; linarith
  -- the residues at the crossed poles
  have hres : ∀ w ∈ (Finset.range (L + 1)).image (pl n h),
      HasResidue (fun z : ℂ => Complex.exp (π * I * z * (2 * ((((ω₁ n + ω₂ n + h) / 2
        - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ) + 0 + (-(h : ℂ)) - ω₁ n - ω₂ n) / (ω₁ n * ω₂ n))
        * G.γ (-(h : ℂ) + z) * G.γ (0 - z)) w (ρΦ n G h (π * v / n) w) := by
    rw [hΦeq]
    intro w hw
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hw
    apply Φh_residue
    · exact ⟨0, ℓ, by simp [pl]⟩
    · rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
      · have := int_not_pole n hn (-h) (by omega)
        simp only [pl, Nat.cast_zero, zero_mul, sub_zero]
        push_cast at this; exact this
      · have := not_pole_of_pos_coeff n hn (-h) ℓ (-(h : ℝ) + ℓ * ω₂ n) (by push_cast; ring)
          (by positivity)
        convert this using 1; simp only [pl]; push_cast; ring
  obtain ⟨-, hE⟩ := G.two_gamma (-(h : ℂ)) 0 _ (-ε) _ (ρΦ n G h (π * v / n))
    (by simp only [ofReal_re]; linarith) (by simp only [sub_re, add_re, ofReal_re, zero_re,
      neg_re, natCast_re, sub_zero, sub_neg_eq_add]; linarith)
    (by simp only [zero_re]; linarith) hpinch hline hS hres
  rw [hΦeq, Finset.sum_image (fun x _ y _ hxy => pl_injective n h hxy)] at hE
  -- simplify the right side
  have e2 : Complex.exp (π * I / (2 * ω₁ n * ω₂ n) * (0 - -(h : ℂ)) * (2 * ((((ω₁ n + ω₂ n + h) / 2
      - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ) + 0 + (-(h : ℂ)) - ω₁ n - ω₂ n))
      = Complex.exp (-I * h * ((π * v / n : ℝ) : ℂ) / 2) := by
    congr 1
    push_cast
    field_simp
    linear_combination ((h : ℂ) * v) * hΩC
  have e3 : (ω₁ n : ℂ) + ω₂ n - 0 - -(h : ℂ) - ((((ω₁ n + ω₂ n + h) / 2
      - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ)
      = ((((ω₁ n + ω₂ n + h) / 2 + (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) : ℂ) := by
    push_cast; ring
  have e4 : -(h : ℂ) + 0 = -h := by ring
  rw [e2, e3, e4] at hE
  exact hE

/-! ### Step 5: the residue theorem on the strip -/

include hn hodd in
/-- Step 5: the strip identity for `K_h`, with the residues at the integers and at the crossed
poles `p_1, …, p_L`. -/
theorem strip_applied (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (θ : ℝ) (hθabs : |θ| ≤ π)
    (hθn : Complex.exp (-I * θ * n) = -(-1) ^ h) (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < h - ℓ * ω₂ n) (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → h - ℓ * ω₂ n < -ε) :
    MeasureTheory.Integrable (fun t : ℝ => Kh n G h θ (((-ε : ℝ) : ℂ) + t * I)) ∧
    MeasureTheory.Integrable (fun t : ℝ => Kh n G h θ (((n - ε : ℝ) : ℂ) + t * I)) ∧
    lineIntegral (Kh n G h θ) (n - ε) - lineIntegral (Kh n G h θ) (-ε)
      = 2 * π * I * (∑ a : ZMod n, (-1) ^ a.val * Complex.exp (-I * θ * a.val) * Rh n G h a.val
          + 4 * π * Complex.sin (π * h / ω₁ n) * ∑ ℓ ∈ Finset.range L, ρΦ n G h θ (pl n h (ℓ + 1))) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhn : (h : ℝ) ≤ n - 1 := by
    have : (h : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hh2
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  -- the finite sets of poles
  set Sint : Finset ℂ := Finset.univ.image (fun a : ZMod n => ((a.val : ℕ) : ℂ)) with hSint
  set Scross : Finset ℂ := (Finset.range L).image (fun ℓ => pl n h (ℓ + 1)) with hScross
  have hval_inj : Function.Injective (fun a : ZMod n => ((a.val : ℕ) : ℂ)) :=
    fun a b hab => ZMod.val_injective n (Nat.cast_injective (R := ℂ) (by simpa using hab))
  have hcross_inj : Function.Injective (fun ℓ : ℕ => pl n h (ℓ + 1)) :=
    fun x y hxy => by have := pl_injective n h hxy; omega
  have hdisj : Disjoint Sint Scross := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨ℓ, -, hℓ⟩ := Finset.mem_image.1 hp'
    exact pl_ne_nat n hn h ℓ a.val hℓ
  -- the residue function
  set c : ℂ := 4 * π * Complex.sin (π * h / ω₁ n) with hc
  set ρK : ℂ → ℂ := fun w => if w ∈ Sint then Complex.cos (π * w) * Complex.exp (-I * θ * w)
    * Rh n G h w else c * ρΦ n G h θ w with hρK
  -- residues
  have hres : ∀ p ∈ Sint ∪ Scross, HasResidue (Kh n G h θ) p (ρK p) := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
      have : ρK ((a.val : ℕ) : ℂ) = (-1) ^ a.val * Complex.exp (-I * θ * a.val) * Rh n G h a.val := by
        simp only [hρK, if_pos hp]
        rw [show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi']
      rw [this]
      exact Kh_residue_int n hn G h θ a.val
    · obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.1 hp
      have hnot : pl n h (ℓ + 1) ∉ Sint := fun hmem => Finset.disjoint_left.1 hdisj hmem hp
      have : ρK (pl n h (ℓ + 1)) = c * ρΦ n G h θ (pl n h (ℓ + 1)) := by
        simp only [hρK, if_neg hnot]
      rw [this, hc]
      apply Kh_residue_of_shift n G h θ _ _ (Kh_shift_eventually n G hodd h θ hθn _)
      · -- continuity of `K_h(z + n)` at `p_{ℓ+1}`
        apply Kh_shift_continuousAt
        · have := not_pole_of_pos_const n hn n (-ℓ) ((n : ℝ) + (-ℓ : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n by omega))
          convert this using 1; simp only [pl]; push_cast; ring
        · have := not_pole_of_pos_const n hn (n + h) (-ℓ) ((n + h : ℝ) + (-ℓ : ℚ) * ω₂ n)
            (by push_cast; ring) (by exact_mod_cast (show 0 < n + h by omega))
          convert this using 1; simp only [pl]; push_cast; ring
        · apply G.ne_zero
          · have := not_pole_of_pos_const n hn (n + h) (-ℓ) ((n + h : ℝ) + (-ℓ : ℚ) * ω₂ n)
              (by push_cast; ring) (by exact_mod_cast (show 0 < n + h by omega))
            convert this using 1; simp only [pl]; push_cast; ring
          · have := not_zero_of_coeff_lt n hn (n + h) (-ℓ) ((n + h : ℝ) + (-ℓ : ℚ) * ω₂ n)
              (by push_cast; ring) (by linarith [(Nat.cast_nonneg ℓ : (0 : ℚ) ≤ ℓ)])
            convert this using 1; simp only [pl]; push_cast; ring
        · apply sin_pi_ne_zero_of_not_int
          intro m hm
          have := ne_int_of_coeff_ne_zero n hn (h + n) (-(ℓ + 1 : ℚ))
            ((h : ℝ) + n - (ℓ + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
          apply this
          have h2 : ((((h : ℝ) + n - (ℓ + 1) * ω₂ n) : ℝ) : ℂ) = ((m : ℤ) : ℂ) := by
            rw [← hm]; simp only [pl]; push_cast; ring
          exact_mod_cast h2
      · apply Φh_residue
        · exact ⟨0, ℓ + 1, by simp [pl]⟩
        · have := not_pole_of_pos_coeff n hn (-h) (ℓ + 1) (-(h : ℝ) + (ℓ + 1) * ω₂ n)
            (by push_cast; ring) (by positivity)
          convert this using 1; simp only [pl]; push_cast; ring
  -- the poles are interior
  obtain ⟨M, T, hT, hM⟩ := Kh_bound n G h θ hθabs (-ε) (n - ε)
  have hSpos : ∀ p ∈ Sint ∪ Scross, -ε < p.re ∧ p.re < n - ε ∧ |p.im| < T := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
      have h1 : (a.val : ℝ) ≤ n - 1 := by
        have : (a.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show a.val ≤ n - 1 by
          have := ZMod.val_lt a; omega)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
      have h2 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
      simp only [natCast_re, natCast_im, abs_zero]
      exact ⟨by linarith, by linarith, hT⟩
    · obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hp
      have hℓL : ℓ + 1 ≤ L := by have := Finset.mem_range.1 hℓ; omega
      have := hP1 (ℓ + 1) hℓL
      have hre : (pl n h (ℓ + 1)).re = h - (ℓ + 1) * ω₂ n := by simp [pl]
      have him : (pl n h (ℓ + 1)).im = 0 := by simp [pl]
      rw [hre, him, abs_zero]
      push_cast at this
      have h3 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
      refine ⟨this, ?_, hT⟩
      nlinarith
  -- differentiability off the poles
  have hd : ∀ ζ : ℂ, -ε ≤ ζ.re → ζ.re ≤ n - ε → ζ ∉ Sint ∪ Scross →
      DifferentiableAt ℂ (Kh n G h θ) ζ := by
    intro ζ hζ1 hζ2 hζS
    have hζint : ζ ∉ Sint := fun hmem => hζS (Finset.mem_union.2 (Or.inl hmem))
    have hζcross : ζ ∉ Scross := fun hmem => hζS (Finset.mem_union.2 (Or.inr hmem))
    apply Kh_differentiableAt
    · -- `ω₂ + ζ - h` is not a pole
      rintro ⟨r, s, hrs⟩
      have hζ : ζ = (h : ℂ) - r * ω₁ n - (s + 1) * ω₂ n := by linear_combination hrs
      have hre : ζ.re = h - r * ω₁ n - (s + 1) * ω₂ n := by
        rw [hζ]; simp
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rcases le_or_gt (s + 1) L with hs | hs
        · apply hζcross
          refine Finset.mem_image.2 ⟨s, Finset.mem_range.2 (by omega), ?_⟩
          rw [hζ]; simp [pl]
        · have := hP2 (s + 1) (by omega)
          simp only [Nat.cast_zero, zero_mul, sub_zero] at hre
          push_cast at this hre
          linarith
      · have := left_pole_lt n hn h hh2 ε hε1 r (s + 1) hr
        push_cast at this hre
        linarith
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · exact G.ne_zero _ (HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith))
        (HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith))
    · apply sin_pi_ne_zero_of_not_int
      intro m hm
      apply hζint
      have hre : ζ.re = m := by rw [hm]; simp
      have h1 : (0 : ℤ) ≤ m := by
        have : (-1 : ℝ) < m := by linarith
        have : (-1 : ℤ) < m := by exact_mod_cast this
        omega
      have h2 : m ≤ (n : ℤ) - 1 := by
        have : (m : ℝ) < n := by linarith
        have : m < (n : ℤ) := by exact_mod_cast this
        omega
      refine Finset.mem_image.2 ⟨((m.toNat : ℕ) : ZMod n), Finset.mem_univ _, ?_⟩
      rw [val_natCast' n _ (by omega), hm]
      have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h1
      exact_mod_cast this
  have hc0 : 0 < π * h / (ω₁ n * ω₂ n) := by positivity
  obtain ⟨hint0, hint1, hEq⟩ := strip_residues (Kh n G h θ) (-ε) (n - ε) (by linarith)
    (Sint ∪ Scross) T hT hSpos ρK hres hd M _ hc0 hM
  refine ⟨hint0, hint1, ?_⟩
  rw [hEq]
  congr 1
  rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => hval_inj hxy),
    Finset.sum_image (fun x _ y _ hxy => hcross_inj hxy), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    have hmem : ((a.val : ℕ) : ℂ) ∈ Sint := Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    simp only [hρK, if_pos hmem]
    rw [show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi']
  · apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hmem : pl n h (ℓ + 1) ∈ Scross := Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩
    have hnot : pl n h (ℓ + 1) ∉ Sint := fun h' => Finset.disjoint_left.1 hdisj h' hmem
    simp only [hρK, if_neg hnot, hc]

/-! ### Step 7: the column Fourier formula -/

/-- Proposition 4.1, stated for the finite Fourier sum of the column `h` of `B`. -/
theorem column_fourier_sum (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (k v : ℤ)
    (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (h - 1))) (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n) :
    ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n))) * (toCoeffData n hn G hodd).B a h
      = -(ω₂ n : ℂ) * Complex.exp (-I * h * ((π * v / n : ℝ) : ℂ) / 2)
        * G.γ (((ω₁ n + ω₂ n + h) / 2 - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ))
        * G.γ (((ω₁ n + ω₂ n + h) / 2 + (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd0 := sqrt_d_ne_zero n
  have hFh := F_nat_ne_zero n hn G h
  -- the frequency
  have hθn := theta_period n hn hodd h hh1 k v hv
  have hθabs := theta_abs_le n hn v hv1 hv2
  -- the strip
  obtain ⟨ε, L, hε0, hε1, hP1, hP2⟩ := eps_exists n h
  obtain ⟨hint0, hint1, hE1⟩ := strip_applied n hn G hodd h hh1 hh2 (π * v / n) hθabs hθn ε L
    hε0 hε1 hP1 hP2
  have hE3 := two_gamma_applied n hn G h hh1 hh2 v hv1 hv2 ε L hε0 hε1 hP1 hP2
  have hE4 := residue_sum_int n hn G hodd h hh1 hh2 k v hv
  -- the line identity (Step 2 on the line)
  have hline : ∀ t : ℝ, Kh n G h (π * v / n) (((n - ε : ℝ) : ℂ) + t * I)
      - Kh n G h (π * v / n) (((-ε : ℝ) : ℂ) + t * I)
      = -4 * π * Complex.sin (π * h / ω₁ n) * Φh n G h (π * v / n) (((-ε : ℝ) : ℂ) + t * I) := by
    intro t
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := line_conditions n hn h hh2 ε L hε0 hε1 hP1 hP2 t
    have := Kh_shift n G hodd h (π * v / n) hθn _ c1 c2 c3 c4 c5 c6 c7
    rw [show ((n - ε : ℝ) : ℂ) + t * I = (((-ε : ℝ) : ℂ) + t * I) + n by push_cast; ring]
    exact this
  have hE2 : lineIntegral (Kh n G h (π * v / n)) (n - ε) - lineIntegral (Kh n G h (π * v / n)) (-ε)
      = -4 * π * Complex.sin (π * h / ω₁ n) * lineIntegral (Φh n G h (π * v / n)) (-ε) := by
    unfold lineIntegral
    rw [← MeasureTheory.integral_sub (hint1.mul_const I) (hint0.mul_const I),
      ← MeasureTheory.integral_const_mul]
    congr 1
    funext t
    rw [← sub_mul, hline t]; ring
  -- the residue at `p_0 = h` and the value `2 sin(πh/ω₁) γ(-h) = (-1)^h F(h)`
  have hρ0 : ρΦ n G h (π * v / n) (pl n h 0)
      = Complex.exp (-(2 * π * I * k * h / n)) * G.γ (-h) * (Real.sqrt (ω₁ n * ω₂ n) / (2 * π)) := by
    unfold ρΦ pl
    simp only [Nat.cast_zero, zero_mul, sub_zero, sub_self, G.residue_zero_eq]
    have := theta_sample n hn h hh1 k v hv h
    rw [this, Nat.even_mul_pred_self h |>.neg_one_pow, mul_one]
    try (push_cast; ring)
  have hsin := two_sin_mul_γ_neg n hn G h (by omega)
  push_cast at hsin
  rw [zpow_natCast] at hsin
  have hsqrt : (Real.sqrt (ω₁ n * ω₂ n) : ℂ) = ω₂ n * Real.sqrt (d n) := by
    rw [sqrt_Ω]; push_cast; ring
  have hρ0' : 2 * π * ρΦ n G h (π * v / n) (pl n h 0)
      = Complex.exp (-(2 * π * I * k * h / n)) * G.γ (-h) * (ω₂ n * Real.sqrt (d n)) := by
    rw [hρ0, hsqrt]; field_simp
  -- assemble
  rw [Finset.sum_range_succ'] at hE3
  set U := ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n))) * (toCoeffData n hn G hodd).B a h
    with hU
  set Sres := ∑ a : ZMod n, (-1) ^ a.val * Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * a.val)
    * Rh n G h a.val with hSres
  set Scross := ∑ ℓ ∈ Finset.range L, ρΦ n G h (π * v / n) (pl n h (ℓ + 1)) with hScross
  set LΦ := lineIntegral (Φh n G h (π * v / n)) (-ε) with hLΦ
  set E := Complex.exp (-I * h * ((π * v / n : ℝ) : ℂ) / 2) with hE
  set Γ := G.γ (((ω₁ n + ω₂ n + h) / 2 - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ))
    * G.γ (((ω₁ n + ω₂ n + h) / 2 + (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) with hΓ
  set s := Complex.sin (π * h / ω₁ n) with hs
  have key : 2 * π * I * Sres = -(4 * π * s) * I * Real.sqrt (ω₁ n * ω₂ n) * E * Γ * G.γ (-h)
      + 2 * π * I * (4 * π * s) * ρΦ n G h (π * v / n) (pl n h 0) := by
    linear_combination -hE1 + hE2 - (4 * π * s) * hE3
  rw [hE4, hsqrt] at key
  have hne : (-1 : ℂ) ^ h * Real.sqrt (d n) * F n G h * (2 * π * I) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hd0) hFh)
    exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
  apply mul_left_cancel₀ hne
  linear_combination key + (4 * π * s * I) * hρ0'
    - (2 * π * I * ω₂ n * Real.sqrt (d n) * (E * Γ - Complex.exp (-(2 * π * I * k * h / n)))) * hsin

end main

end Concrete
end HaagerupIzumi
