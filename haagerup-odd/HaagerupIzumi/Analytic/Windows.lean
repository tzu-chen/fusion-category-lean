module

public import HaagerupIzumi.Analytic.Contour

@[expose] public section

/-!
# The interpolating function `t_p` on all windows

Lemma 3.9 of the expanded proof for integer labels `p` and integer sample
points `a`, in the cases needed for the product transforms (Section 6) and
the negative-column transform (Lemma 8.1):

* `tz_pos`: `1 ≤ p ≤ n-1`, `0 ≤ a ≤ n-1`: `t_p(a) = u_p(a) + ω₂ 1_{a=p}` (Step 1);
* `tz_neg_nonneg`: `-n < p < 0`, `0 ≤ a ≤ n-1`: `t_p(a) = u_p(a)` (Step 2);
* `tz_neg_neg`: `-n < p < 0`, `-n < a < 0`: `t_p(a) = u_p(a) + ω₂ 1_{a=p}` (Step 3).
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

/-- `R_p(z) = γ(ω₂ + z - p)/γ(ω₂ + z)` for an integer label `p`. -/
noncomputable def Rz (p : ℤ) (z : ℂ) : ℂ := G.γ ((ω₂ n : ℂ) + (z - p)) / G.γ ((ω₂ n : ℂ) + z)

omit hn in
lemma Rz_natCast (p : ℕ) (z : ℂ) : Rz n G (p : ℤ) z = Rh n G p z := by
  simp [Rz, Rh]

omit hn in
lemma Rz_eq_F (p : ℤ) (z : ℂ) : Rz n G p z = F n G z / F n G (z - p) := by
  rw [Rz, F_def, F_def, inv_div_inv]

/-- The interpolating function `t_p(a)` of (3.14), at integer points. -/
noncomputable def tz (p a : ℤ) : ℂ :=
  (-1 : ℂ) ^ (p * (a + 1)) / (Real.sqrt (d n) * F n G p) * Rz n G p a

/-! ### Parity bookkeeping -/

omit n hn G in
lemma neg_one_zpow_congr (a b : ℤ) (h : (a : ZMod 2) = (b : ZMod 2)) :
    (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
  have hdvd : (2 : ℤ) ∣ a - b := by
    have : ((a - b : ℤ) : ZMod 2) = 0 := by push_cast; rw [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 2).1 this
  obtain ⟨k, hk⟩ := hdvd
  have : a = b + 2 * k := by omega
  rw [this, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

omit hn G in
lemma natCast_zmod2_of_odd (hodd : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨m, hm⟩ := hodd
  rw [hm]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring

/-! ### The three cases of Lemma 3.9 -/

section
variable [NeZero n] (hodd : Odd n)

/-- Lemma 3.9, Step 1, in the `tz` notation. -/
theorem tz_pos (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ n - 1) (a : ℕ) (ha : a ≤ n - 1) :
    tz n G p a = (toCoeffData n hn G hodd).B (a : ZMod n) (p : ZMod n)
      + (ω₂ n : ℂ) * (if a = p then 1 else 0) := by
  rw [sample_rule n hn G hodd p hp1 hp2 a ha, tz]
  rw [show ((p : ℤ) * ((a : ℤ) + 1)) = ((p * (a + 1) : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  push_cast
  rw [Rz_natCast]

/-- Lemma 3.9, Step 2: negative label, sample points `0 ≤ a ≤ n-1`; no correction. -/
theorem tz_neg_nonneg (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (a : ℕ) (ha : a ≤ n - 1) :
    tz n G (-(h : ℤ)) a = (toCoeffData n hn G hodd).B (a : ZMod n) (-(h : ZMod n)) := by
  have hd0 := sqrt_d_ne_zero n
  have hn2 := natCast_zmod2_of_odd n hodd
  -- the positive representative `p' = n - h`
  obtain ⟨p', hp'⟩ : ∃ p', p' = n - h := ⟨_, rfl⟩
  have hp'1 : 1 ≤ p' := by omega
  have hp'2 : p' ≤ n - 1 := by omega
  have hcast : (-(h : ZMod n)) = (p' : ZMod n) := by
    rw [hp', Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [hcast]
  have hpos := tz_pos n hn G hodd p' hp'1 hp'2 a ha
  have hFh := F_int_ne_zero n hn G (-h)
  have hFp' := F_nat_ne_zero n hn G p'
  -- `F(p') = (-1)^(1-h) F(-h)`
  have hFp'eq : F n G p' = (-1) ^ ((-(h : ℤ)) + 1) * F n G (-(h : ℤ)) := by
    have := F_int_add_n n hn G (-h) (by omega)
    rw [show (((-(h : ℤ)) : ℤ) : ℂ) + (n : ℂ) = (p' : ℂ) by
      rw [hp']; push_cast [Nat.cast_sub (by omega : h ≤ n)]; ring] at this
    push_cast at this ⊢
    exact this
  by_cases hap : a = p'
  · -- the diagonal point: both sides equal `-1`
    subst hap
    rw [(toCoeffData n hn G hodd).B_diag (natCast_ne_zero' n a hp'1 hp'2), tz, Rz_eq_F]
    rw [show ((a : ℤ) : ℂ) - ((-(h : ℤ) : ℤ) : ℂ) = (n : ℂ) by
      rw [hp']; push_cast [Nat.cast_sub (by omega : h ≤ n)]; ring, F_n n hn G]
    push_cast
    rw [hFp'eq]
    have hsign : (-1 : ℂ) ^ (-(h : ℤ) * ((a : ℤ) + 1)) * (-1) ^ (-(h : ℤ) + 1) = -1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      rw [neg_one_zpow_congr _ 1 (by
        rw [hp'] at *
        push_cast [Nat.cast_sub (by omega : h ≤ n)]
        rw [hn2]
        generalize (h : ZMod 2) = x
        revert x; decide), zpow_one]
    have hz1 : (-1 : ℂ) ^ (-(h : ℤ) + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hz2 : (-1 : ℂ) ^ (-(h : ℤ) * ((a : ℤ) + 1)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    push_cast at hsign hFh hFp'eq ⊢
    field_simp
    linear_combination hsign
  · -- off the diagonal: `t_{-h}(a) = t_{p'}(a) = u_{p'}(a)`
    rw [if_neg hap, mul_zero, add_zero] at hpos
    rw [← hpos, tz, tz, Rz_eq_F, Rz_eq_F]
    have hFa := F_nat_ne_zero n hn G a
    have hne : (a : ℤ) - p' ≠ 0 := by omega
    have hshift := F_int_add_n n hn G ((a : ℤ) - p') hne
    rw [show (((a : ℤ) - p' : ℤ) : ℂ) + (n : ℂ) = (a : ℂ) - ((-(h : ℤ) : ℤ) : ℂ) by
      rw [hp']; push_cast [Nat.cast_sub (by omega : h ≤ n)]; ring] at hshift
    have hF1 := F_int_ne_zero n hn G ((a : ℤ) - p')
    have hz1 : (-1 : ℂ) ^ (-(h : ℤ) + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hz2 : (-1 : ℂ) ^ ((a : ℤ) - p' + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    push_cast at hshift hF1 hFp'eq hFh ⊢
    rw [hshift, hFp'eq]
    have hsign : (-1 : ℂ) ^ ((p' : ℤ) * ((a : ℤ) + 1)) * (-1) ^ ((a : ℤ) - p' + 1)
        = (-1) ^ (-(h : ℤ) * ((a : ℤ) + 1)) * (-1) ^ (-(h : ℤ) + 1) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      apply neg_one_zpow_congr
      rw [hp']
      push_cast [Nat.cast_sub (by omega : h ≤ n)]
      rw [hn2]
      generalize (h : ZMod 2) = x
      generalize (a : ZMod 2) = y
      revert x y; decide
    field_simp
    linear_combination (-1 : ℂ) * hsign

include hn hodd in
/-- Lemma 3.9, Step 3 (periodicity): `t_p(a + n) = t_p(a)` for `a ≠ 0`, `a ≠ p`. -/
theorem tz_add_n (p a : ℤ) (ha : a ≠ 0) (hap : a - p ≠ 0) : tz n G p (a + n) = tz n G p a := by
  have hn2 := natCast_zmod2_of_odd n hodd
  have hd0 := sqrt_d_ne_zero n
  have hFp := F_int_ne_zero n hn G p
  have hFa := F_int_ne_zero n hn G a
  have hFap := F_int_ne_zero n hn G (a - p)
  have h1 := F_int_add_n n hn G a ha
  have h2 := F_int_add_n n hn G (a - p) hap
  have hz1 : (-1 : ℂ) ^ (a + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hz2 : (-1 : ℂ) ^ (a - p + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [tz, tz, Rz_eq_F, Rz_eq_F]
  rw [show ((a + n : ℤ) : ℂ) = (a : ℂ) + n by push_cast; ring,
    show (a : ℂ) + n - p = ((a - p : ℤ) : ℂ) + n by push_cast; ring, h1, h2]
  push_cast at hFap hFa hFp ⊢
  have hS1 : (-1 : ℂ) ^ (p * (a + n + 1)) = (-1) ^ (p * (a + 1)) * (-1) ^ p := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply neg_one_zpow_congr
    push_cast
    rw [hn2]
    generalize (p : ZMod 2) = x
    generalize (a : ZMod 2) = y
    revert x y; decide
  have hS3 : (-1 : ℂ) ^ (a - p + 1) = (-1) ^ (a + 1) * (-1) ^ p := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply neg_one_zpow_congr
    push_cast
    generalize (p : ZMod 2) = x
    generalize (a : ZMod 2) = y
    revert x y; decide
  have hsq : ((-1 : ℂ) ^ p) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    exact Even.neg_one_zpow ⟨p, by ring⟩
  rw [hS1, hS3]
  field_simp
  try linear_combination ((-1 : ℂ) ^ (p * (a + 1)) * (-1) ^ (a + 1)) * hsq

/-- Lemma 3.9, Step 3: negative label and negative sample point. -/
theorem tz_neg_neg (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ n - 1) :
    tz n G (-(h : ℤ)) (-(a : ℤ)) = (toCoeffData n hn G hodd).B (-(a : ZMod n)) (-(h : ZMod n))
      + (ω₂ n : ℂ) * (if a = h then 1 else 0) := by
  have hd0 := sqrt_d_ne_zero n
  by_cases hah : a = h
  · -- the diagonal point: `t_{-h}(-h) = 1/d = -1 + ω₂`
    subst hah
    have hne : (-(a : ZMod n)) ≠ 0 := by
      intro h0; apply natCast_ne_zero' n a ha1 ha2; exact neg_eq_zero.1 h0
    rw [(toCoeffData n hn G hodd).B_diag hne, if_pos rfl, mul_one, tz, Rz_eq_F]
    rw [show ((-(a : ℤ) : ℤ) : ℂ) - ((-(a : ℤ) : ℤ) : ℂ) = 0 by ring, F_zero n hn G]
    have hev : Even (-(a : ℤ) * (-(a : ℤ) + 1)) := Int.even_mul_succ_self _
    rw [hev.neg_one_zpow]
    have hsq := sqrt_d_sq n
    have hω : (ω₂ n : ℂ) = 1 + ((d n : ℂ))⁻¹ := by unfold ω₂; push_cast; ring
    have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
    have hF := F_int_ne_zero n hn G (-a)
    push_cast at hF ⊢
    rw [hω]
    field_simp
    linear_combination (-1 : ℂ) * hsq
  · -- off the diagonal: shift the sample point by `n`
    have hshift := tz_add_n n hn G hodd (-(h : ℤ)) (-(a : ℤ)) (by omega) (by omega)
    rw [show (-(a : ℤ) + n) = ((n - a : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : a ≤ n)]; ring]
      at hshift
    rw [← hshift, tz_neg_nonneg n hn G hodd h hh1 hh2 (n - a) (by omega), if_neg hah, mul_zero,
      add_zero]
    congr 2
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring

end

end Concrete
end HaagerupIzumi
