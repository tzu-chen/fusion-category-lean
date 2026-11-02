module

public import HaagerupIzumi.Analytic.Contour
public import HaagerupIzumi.Residuals
public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# The Fourier transform of a column and the quadratic identities

Section 4 of the expanded proof. The column Fourier formula (4.3) is the
analytic input `column_fourier`; from it we derive the reciprocal Fourier
products (Lemma 4.3) and the quadratic identities (Proposition 4.4).
-/

open Complex Real Filter Topology ZMod Finset
open scoped ComplexConjugate

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n)) (hodd : Odd n)

/-- The concrete coefficient data, abbreviated. -/
noncomputable abbrev D : CoeffData n ℂ := toCoeffData n hn G hodd

section
variable [NeZero n]

/-- The finite Fourier transform of the column `p` of `B`. -/
noncomputable def uhat (p k : ZMod n) : ℂ := dft (fun a => (D n hn G hodd).B a p) k

lemma uhat_def (p k : ZMod n) :
    uhat n hn G hodd p k = ∑ a, stdAddChar (-(a * k)) * (D n hn G hodd).B a p := by
  rw [uhat, dft_apply]; simp only [smul_eq_mul]

/-- The column Fourier formula (4.3). Here `v` is any integer with `v ≡ 2k + n(h - 1)`
modulo `2n` and `-n ≤ v ≤ n`, so that `θ = π v / n` is a principal frequency. -/
theorem column_fourier (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (k v : ℤ)
    (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (h - 1))) (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n) :
    uhat n hn G hodd (h : ZMod n) (k : ZMod n)
      = -(ω₂ n : ℂ) * Complex.exp (-I * h * (π * v / n) / 2)
        * G.γ (((ω₁ n + ω₂ n + h) / 2 - (ω₁ n + ω₂ n) * v / (2 * n) : ℝ))
        * G.γ (((ω₁ n + ω₂ n + h) / 2 + (ω₁ n + ω₂ n) * v / (2 * n) : ℝ)) := by
  rw [uhat_def]
  have := column_fourier_sum n hn G hodd h hh1 hh2 k v hv hv1 hv2
  push_cast at this ⊢
  exact this

/-! ### Reductions -/

/-- The entries of `B` are real. -/
lemma B_conj (a b : ZMod n) : conj ((D n hn G hodd).B a b) = (D n hn G hodd).B a b := by
  have hW := W_conj n hn G hodd
  simp only [D, toCoeffData, CoeffData.B]
  split_ifs
  · simp only [CoeffData.τ_def, map_add, map_neg, map_one, map_sub, Complex.conj_ofReal]
  · simp
  · rw [map_div₀, map_mul, hW, hW, hW]

/-- Conjugation symmetry of the column transform. -/
lemma uhat_neg (p k : ZMod n) : uhat n hn G hodd p (-k) = conj (uhat n hn G hodd p k) := by
  rw [uhat_def, uhat_def, map_sum]
  apply sum_congr rfl
  intro a _
  rw [map_mul, B_conj, ← AddChar.map_neg_eq_conj]
  congr 2; ring

/-- The reflection symmetry `û_p (k) = χ(-(p k)) û_p (-k)` for `p ≠ 0`. -/
lemma uhat_reflect {p : ZMod n} (hp : p ≠ 0) (k : ZMod n) :
    uhat n hn G hodd p k = stdAddChar (-(p * k)) * uhat n hn G hodd p (-k) := by
  rw [uhat_def, uhat_def, mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft p) _ _ (fun a => ?_)
  rw [Equiv.subLeft_apply]
  have := (D n hn G hodd).u_symm hp a
  rw [CoeffData.u_def, CoeffData.u_def] at this
  rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2; ring

/-- The exponential `χ(-(k h))` written with the standard character. -/
lemma rhs_char (k h : ℤ) :
    stdAddChar (-((k : ZMod n) * (h : ZMod n))) = Complex.exp (-(2 * π * I * k * h / n)) := by
  have := stdAddChar_coe (N := n) (-(k * h))
  push_cast at this
  rw [this]; congr 1; push_cast; ring

end

/-! ### The core computation: `h` odd, `0 ≤ k ≤ (n - 1)/2` -/

section core
variable [NeZero n]

/-- Lemma 4.3 in the reduced situation. -/
theorem uhat_mul_uhat_core (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (hhodd : Odd h)
    (k : ℕ) (hk : 2 * k ≤ n - 1) :
    uhat n hn G hodd (h : ZMod n) (k : ZMod n) * uhat n hn G hodd ((n - h : ℕ) : ZMod n) (-(k : ZMod n))
      = (ω₂ n : ℂ) ^ 2 * stdAddChar (-((k : ZMod n) * (h : ZMod n))) := by
  -- basic real-number facts
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hω₁C : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast hω₁.ne'
  have hω₂C : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast hω₂.ne'
  have hΩ := ω₁_eq n
  have hquad := ω₂_quad n
  -- `n - h = 2 j`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n - h = 2 * j := by
    obtain ⟨a, ha⟩ := hodd; obtain ⟨b, hb⟩ := hhodd
    exact ⟨a - b, by omega⟩
  have hhn : (h : ℝ) = n - 2 * j := by
    have : h + 2 * j = n := by omega
    have := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at this; linarith
  have hj1 : 1 ≤ j := by omega
  -- the two applications of the column formula
  have H1 := column_fourier n hn G hodd h hh1 hh2 k (2 * k)
    ⟨-(((h - 1) / 2 : ℕ) : ℤ), by
      obtain ⟨b, hb⟩ := hhodd
      have : (h - 1) / 2 = b := by omega
      rw [this]; push_cast; rw [hb]; push_cast; ring⟩
    (by omega) (by omega)
  have H2 := column_fourier n hn G hodd (n - h) (by omega) (by omega) (-(k : ℤ)) (n - 2 * k)
    ⟨1 - (j : ℤ), by
      have e2 : ((n - h : ℕ) : ℤ) = 2 * j := by rw [hj]; push_cast; ring
      rw [e2]; ring⟩
    (by omega) (by omega)
  rw [show ((n - h : ℕ) : ZMod n) = -(h : ZMod n) by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring,
    show ((n - h : ℕ) : ℂ) = 2 * j by rw [hj]; push_cast; ring,
    show ((n - h : ℕ) : ℝ) = 2 * j by rw [hj]; push_cast; ring] at H2
  rw [show ((n - h : ℕ) : ZMod n) = -(h : ZMod n) by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring]
  -- the real quantities
  set Ω : ℝ := ω₁ n + ω₂ n with hΩdef
  set lam : ℝ := Ω * k / n with hlam
  set xm : ℝ := (Ω + h) / 2 - lam with hxm
  set xp : ℝ := (Ω + h) / 2 + lam with hxp
  set y1 : ℝ := Ω + j - lam with hy1
  set y2 : ℝ := j + lam with hy2
  set w : ℝ := xp - ω₁ n with hw
  clear_value w y2 y1 xp xm lam Ω
  have e1 : ((Ω + h) / 2 - Ω * ((2 * k : ℤ) : ℝ) / (2 * n) : ℝ) = xm := by
    rw [hxm, hlam]; push_cast; field_simp; try ring
  have e2 : ((Ω + h) / 2 + Ω * ((2 * k : ℤ) : ℝ) / (2 * n) : ℝ) = xp := by
    rw [hxp, hlam]; push_cast; field_simp; try ring
  have e3 : ((Ω + 2 * j) / 2 - Ω * ((n - 2 * k : ℤ) : ℝ) / (2 * n) : ℝ) = y2 := by
    rw [hy2, hlam]; push_cast; field_simp; try ring
  have e4 : ((Ω + 2 * j) / 2 + Ω * ((n - 2 * k : ℤ) : ℝ) / (2 * n) : ℝ) = y1 := by
    rw [hy1, hlam]; push_cast; field_simp; try ring
  rw [e1, e2] at H1
  rw [e3, e4] at H2
  -- rational-coefficient forms
  have hΩ2 : Ω = n + 2 * ω₂ n := by rw [hΩdef, hΩ]; ring
  have hlam' : lam = k + (2 * k / n) * ω₂ n := by
    rw [hlam, hΩ2]; field_simp; try ring
  have hw' : w = ((k - j : ℚ) : ℝ) + ((2 * k / n : ℚ) : ℝ) * ω₂ n := by
    rw [hw, hxp, hlam', hhn, hΩ2]
    try rw [hΩ]
    try push_cast
    try field_simp
    try ring
  have hxm' : xm = (((n + h) / 2 - k : ℚ) : ℝ) + ((1 - 2 * k / n : ℚ) : ℝ) * ω₂ n := by
    rw [hxm, hlam', hΩ2]; push_cast; field_simp; ring
  have hxm2 : ω₂ n + xm = (((n + h) / 2 - k : ℚ) : ℝ) + ((2 - 2 * k / n : ℚ) : ℝ) * ω₂ n := by
    rw [hxm']; push_cast; ring
  have hkn : (2 * k : ℚ) / n < 1 := by
    rw [div_lt_one (by exact_mod_cast hn0)]
    have : (2 * k : ℚ) ≤ n - 1 := by exact_mod_cast (by omega : 2 * k ≤ n - 1)
    linarith
  have hkn0 : (0 : ℚ) ≤ 2 * k / n := by positivity
  -- domain facts
  have w_pole : (w : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      apply not_pole_of_zero_coeff n hn ((0 : ℚ) - j) w
      · rw [hw']; push_cast; ring
      · have : (1 : ℚ) ≤ j := by exact_mod_cast hj1
        linarith
    · exact not_pole_of_pos_coeff n hn _ _ w hw' (by positivity)
  have w_zero : (w : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) :=
    not_zero_of_coeff_lt n hn _ _ w hw' (by linarith)
  have xm_pole : (xm : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) :=
    not_pole_of_pos_coeff n hn _ _ xm hxm' (by linarith)
  have xm_zero : (xm : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) :=
    not_zero_of_coeff_lt n hn _ _ xm hxm' (by linarith)
  have xm2_pole : ((ω₂ n + xm : ℝ) : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) :=
    not_pole_of_pos_coeff n hn _ _ _ hxm2 (by linarith)
  have xm2_zero : ((ω₂ n + xm : ℝ) : ℂ) ∉ zeroSet (ω₁ n) (ω₂ n) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      apply not_zero_of_coeff_two n hn ((n + h : ℚ) / 2 - 0) _
      · rw [hxm2]; push_cast; ring
      · have : (h : ℚ) < n := by exact_mod_cast (by omega : h < n)
        linarith
    · exact not_zero_of_coeff_lt n hn _ _ _ hxm2 (by
        have : (0 : ℚ) < 2 * k / n := by positivity
        linarith)
  -- the pairings
  have P1 : G.γ xp * G.γ y1 = 2 * Complex.sin (π * w / ω₂ n) := by
    have hs := G.shift₁ w w_pole
    have hr := G.reflect w w_pole w_zero
    have exp_ : (w : ℂ) + ω₁ n = xp := by rw [hw]; push_cast; ring
    have ey : ((ω₁ n : ℂ) + ω₂ n - w) = y1 := by
      rw [hw, hxp, hy1, hhn, hΩdef, hΩ]; push_cast; ring
    rw [exp_] at hs
    rw [ey] at hr
    rw [hs]
    calc 2 * Complex.sin (π * w / ω₂ n) * G.γ w * G.γ y1
        = 2 * Complex.sin (π * w / ω₂ n) * (G.γ w * G.γ y1) := by ring
      _ = 2 * Complex.sin (π * w / ω₂ n) := by rw [hr, mul_one]
  have P2 : G.γ xm * G.γ y2 = (2 * Complex.sin (π * xm / ω₁ n))⁻¹ := by
    have hs := G.shift₂ xm xm_pole
    have hr := G.reflect _ xm2_pole xm2_zero
    have ey : ((ω₁ n : ℂ) + ω₂ n - ((ω₂ n + xm : ℝ) : ℂ)) = y2 := by
      rw [hxm, hy2, hhn, hΩdef, hΩ]; push_cast; ring
    rw [ey] at hr
    have hγ : G.γ xm ≠ 0 := G.ne_zero _ xm_pole xm_zero
    have hsne : Complex.sin (π * xm / ω₁ n) ≠ 0 := by
      intro h0
      rw [show ((ω₂ n + xm : ℝ) : ℂ) = xm + ω₂ n by push_cast; ring, hs, h0] at hr
      simp at hr
    rw [show ((ω₂ n + xm : ℝ) : ℂ) = xm + ω₂ n by push_cast; ring, hs] at hr
    field_simp
    linear_combination hr
  -- the sine ratio: `w / ω₂ + xm / ω₁ = k + 1 - j`
  have hA_real : w / ω₂ n + xm / ω₁ n = k + 1 - j := by
    rw [hw', hxm', hΩ]; push_cast; rw [hhn]
    have hnω : (n : ℝ) + ω₂ n ≠ 0 := by linarith
    field_simp
    linear_combination (-2 * (n : ℝ)) * ((k : ℝ) - j) * hquad
  have hB0 : 0 < xm / ω₁ n := by
    apply div_pos _ hω₁
    rw [hxm']; push_cast
    have h1 : (1 : ℝ) ≤ n - j - k := by
      have : (2 * j : ℝ) ≤ n - 1 := by
        have : 2 * j ≤ n - 1 := by omega
        exact_mod_cast this
      have : (2 * k : ℝ) ≤ n - 1 := by exact_mod_cast hk
      linarith
    have h2 : (0 : ℝ) < 1 - 2 * k / n := by
      rw [sub_pos, div_lt_one hn0]
      have : (2 * k : ℝ) ≤ n - 1 := by exact_mod_cast hk
      linarith
    have h3 : (0 : ℝ) < (1 - 2 * k / n) * ω₂ n := mul_pos h2 hω₂
    rw [hhn]; linarith
  have hB1 : xm / ω₁ n < 1 := by
    rw [div_lt_one hω₁, hxm', hΩ]; push_cast
    have : (0 : ℝ) ≤ 2 * k / n * ω₂ n := by positivity
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have : (0 : ℝ) ≤ k := by positivity
    rw [hhn]; nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = xm / ω₁ n := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = k + 1 - j := ⟨_, rfl⟩
  have hsinB : Complex.sin (π * xm / ω₁ n) ≠ 0 := by
    have : Complex.sin (π * xm / ω₁ n) = ((Real.sin (π * B) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sin, hB]; push_cast; ring_nf
    rw [this]
    have hpos : 0 < Real.sin (π * B) :=
      Real.sin_pos_of_pos_of_lt_pi (by rw [hB]; exact mul_pos Real.pi_pos hB0)
        (by rw [hB]; exact mul_lt_of_lt_one_right Real.pi_pos hB1)
    exact_mod_cast hpos.ne'
  have hsinA : Complex.sin (π * w / ω₂ n) = -((-1 : ℂ) ^ N) * Complex.sin (π * xm / ω₁ n) := by
    have hA : (π : ℂ) * w / ω₂ n = N * π - π * xm / ω₁ n := by
      have := hA_real
      have h' : (w / ω₂ n : ℝ) = (N : ℝ) - xm / ω₁ n := by
        rw [hN]; push_cast; linear_combination hA_real
      have hC : ((w : ℂ) / ω₂ n) = (N : ℂ) - (xm : ℂ) / ω₁ n := by exact_mod_cast h'
      rw [show (π : ℂ) * w / ω₂ n = π * (w / ω₂ n) by ring, hC]; ring
    have hc : Complex.cos ((N : ℂ) * π) = (-1 : ℂ) ^ N := by
      rw [show ((N : ℂ) * π) = (((N * π : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
        Real.cos_int_mul_pi]
      push_cast; ring
    rw [hA, Complex.sin_sub, Complex.sin_int_mul_pi, hc]; ring
  -- the exponentials
  set E1 := Complex.exp (-I * h * (π * ((2 * k : ℤ) : ℂ) / n) / 2) with hE1
  set E2 := Complex.exp (-I * (2 * j : ℂ) * (π * ((n - 2 * k : ℤ) : ℂ) / n) / 2) with hE2
  have hexp : E1 * E2 = Complex.exp (-(2 * π * I * k * h / n)) * ((-1 : ℂ) ^ k * (-1) ^ j) := by
    rw [hE1, hE2, ← Complex.exp_add]
    have h1 : Complex.exp ((k : ℂ) * (π * I)) = (-1) ^ k := by
      rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    have h2 : Complex.exp ((j : ℂ) * (-(π * I))) = (-1) ^ j := by
      rw [Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [← h1, ← h2, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hhC : (h : ℂ) = n - 2 * j := by exact_mod_cast hhn
    rw [hhC]; push_cast
    field_simp
    ring
  -- assembly
  have hkC : (((k : ℤ) : ZMod n)) = ((k : ℕ) : ZMod n) := Int.cast_natCast k
  have hhC' : (((h : ℤ) : ZMod n)) = ((h : ℕ) : ZMod n) := Int.cast_natCast h
  have hrhs := rhs_char n (k : ℤ) (h : ℤ)
  rw [hkC, hhC'] at hrhs
  push_cast at hrhs
  have hk2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hj2 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsign : (-1 : ℂ) ^ N = (-1) ^ k * (-1) * (-1) ^ j := by
    have h1 : (-1 : ℂ) ^ N * (-1) ^ j = (-1) ^ k * (-1) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        show N + (j : ℤ) = ((k + 1 : ℕ) : ℤ) by rw [hN]; push_cast; ring, zpow_natCast, pow_succ]
    calc (-1 : ℂ) ^ N = (-1) ^ N * (-1) ^ j * (-1) ^ j := by rw [mul_assoc, ← sq, hj2, mul_one]
      _ = _ := by rw [h1]
  simp only [Int.cast_natCast, Int.cast_neg] at H1 H2
  rw [H1, H2, hrhs]
  trans (ω₂ n : ℂ) ^ 2 * (E1 * E2) * ((G.γ xp * G.γ y1) * (G.γ xm * G.γ y2))
  · ring
  rw [hexp, P1, P2, hsinA, hsign]
  field_simp
  linear_combination ((-1 : ℂ) ^ j) ^ 2 * hk2 + hj2

/-- Lemma 4.3: the reciprocal Fourier products. -/
theorem uhat_mul_uhat (h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ n - 1) (k : ZMod n) :
    uhat n hn G hodd (h : ZMod n) k * uhat n hn G hodd ((n - h : ℕ) : ZMod n) (-k)
      = (ω₂ n : ℂ) ^ 2 * stdAddChar (-(k * (h : ZMod n))) := by
  -- Step B: `h` odd, arbitrary `k`, via conjugation
  have stepB : ∀ h : ℕ, 1 ≤ h → h ≤ n - 1 → Odd h → ∀ k : ZMod n,
      uhat n hn G hodd (h : ZMod n) k * uhat n hn G hodd ((n - h : ℕ) : ZMod n) (-k)
        = (ω₂ n : ℂ) ^ 2 * stdAddChar (-(k * (h : ZMod n))) := by
    intro h hh1 hh2 hho k
    by_cases hk : 2 * k.val ≤ n - 1
    · have := uhat_mul_uhat_core n hn G hodd h hh1 hh2 hho k.val hk
      rwa [ZMod.natCast_zmod_val] at this
    · push_neg at hk
      have hk' : 2 * (n - k.val) ≤ n - 1 := by
        have := ZMod.val_lt k
        obtain ⟨m, hm⟩ := hodd
        omega
      have this := uhat_mul_uhat_core n hn G hodd h hh1 hh2 hho (n - k.val) hk'
      have hcast : ((n - k.val : ℕ) : ZMod n) = -k := by
        rw [Nat.cast_sub (ZMod.val_lt k).le, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
      rw [hcast, neg_neg] at this
      have hc := congrArg conj this
      have e1 : conj (uhat n hn G hodd (h : ZMod n) (-k)) = uhat n hn G hodd (h : ZMod n) k := by
        rw [uhat_neg, Complex.conj_conj]
      have e2 : conj (uhat n hn G hodd ((n - h : ℕ) : ZMod n) k)
          = uhat n hn G hodd ((n - h : ℕ) : ZMod n) (-k) := (uhat_neg n hn G hodd _ _).symm
      rw [map_mul, e1, e2, map_mul, map_pow, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj] at hc
      rw [hc]
      congr 2; ring
  rcases Nat.even_or_odd h with he | ho
  · have hh1' : 1 ≤ n - h := by omega
    have hh2' : n - h ≤ n - 1 := by omega
    have ho' : Odd (n - h) := Nat.Odd.sub_even (by omega) hodd he
    have := stepB (n - h) hh1' hh2' ho' (-k)
    rw [show n - (n - h) = h by omega, neg_neg] at this
    rw [mul_comm, this]
    congr 2
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  · exact stepB h hh1 hh2 ho k

end core

/-! ### The quadratic identities -/

section quadratics
variable [NeZero n]

/-- The `h = 0` case of the quadratic identity, from the axis values. -/
lemma Q_h_zero (g : ZMod n) : (D n hn G hodd).Q g 0 = 0 := by
  set E := D n hn G hodd
  have hτ := E.τ_ne_zero
  have hδ := E.δ_ne_zero
  rw [CoeffData.Q_def]
  simp only [CoeffData.A_axis_left, CoeffData.A_axis_right, if_true]
  have : ∀ m : ZMod n, ((if m + g = 0 then (1 : ℂ) else 0) - E.τ⁻¹) * ((if m = 0 then 1 else 0) - E.τ⁻¹)
      = (if m = -g then (if m = 0 then (1 : ℂ) else 0) else 0)
        - E.τ⁻¹ * (if m = -g then 1 else 0) - E.τ⁻¹ * (if m = 0 then 1 else 0) + E.τ⁻¹ ^ 2 := by
    intro m
    have e : (m + g = 0) ↔ (m = -g) := add_eq_zero_iff_eq_neg
    simp only [e]
    split_ifs <;> ring
  simp only [this, sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, ← mul_sum,
    sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hn' := E.n_eq
  rw [hn']
  by_cases hg : g = 0
  · subst hg
    simp only [neg_zero, if_true]
    field_simp
    rw [CoeffData.τ_def]; ring
  · rw [if_neg (fun e => hg (by simpa using e)), if_neg hg]
    field_simp
    rw [CoeffData.τ_def]; ring

/-- Proposition 4.4: the quadratic identities hold for the concrete data. -/
theorem Q_eq_zero (g h : ZMod n) : (D n hn G hodd).Q g h = 0 := by
  by_cases hh : h = 0
  · subst hh; exact Q_h_zero n hn G hodd g
  have hτ := (D n hn G hodd).τ_ne_zero
  -- the sum `s g = ∑ a, B (g + a) h * B h a` has constant Fourier transform `τ^2`
  set s : ZMod n → ℂ := fun g => ∑ a, (D n hn G hodd).B (g + a) h * (D n hn G hodd).B h a with hs
  have hFs : ∀ k, dft s k = uhat n hn G hodd h k * uhat n hn G hodd (-h) k := by
    intro k
    have step1 : dft s k = ∑ a, (∑ g, stdAddChar (-(g * k)) * (D n hn G hodd).B (g + a) h)
        * (D n hn G hodd).B h a := by
      rw [dft_apply]
      simp only [smul_eq_mul, hs, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro a _
      rw [sum_mul]
      apply sum_congr rfl; intro g _; ring
    have step2 : ∀ a, ∑ g, stdAddChar (-(g * k)) * (D n hn G hodd).B (g + a) h
        = stdAddChar (a * k) * ∑ x, stdAddChar (-(x * k)) * (D n hn G hodd).B x h := by
      intro a
      rw [mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun g => ?_)
      rw [Equiv.coe_addRight, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2; ring
    have step3 : ∑ a, stdAddChar (a * k) * (D n hn G hodd).B h a
        = ∑ b, stdAddChar (-(b * k)) * (D n hn G hodd).B b (-h) := by
      refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun a => ?_)
      rw [Equiv.neg_apply, (D n hn G hodd).B_eq_u_neg hh a, CoeffData.u_def]
      congr 2; ring
    rw [step1]
    simp only [step2]
    rw [uhat_def, uhat_def, ← step3, mul_sum]
    apply sum_congr rfl; intro a _; ring
  have hconst : ∀ k, dft s k = (D n hn G hodd).τ ^ 2 := by
    intro k
    rw [hFs, uhat_reflect n hn G hodd (neg_ne_zero.mpr hh) k]
    have hnh : ((n - h.val : ℕ) : ZMod n) = -h := by
      rw [Nat.cast_sub (ZMod.val_lt h).le, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
    have hv1 : 1 ≤ h.val := Nat.one_le_iff_ne_zero.mpr (fun e => hh ((ZMod.val_eq_zero h).mp e))
    have hv2 : h.val ≤ n - 1 := by have := ZMod.val_lt h; omega
    have key := uhat_mul_uhat n hn G hodd h.val hv1 hv2 k
    rw [hnh, ZMod.natCast_zmod_val] at key
    rw [mul_comm (stdAddChar _), ← mul_assoc, key, mul_assoc, ← AddChar.map_add_eq_mul]
    rw [show -(k * h) + -(-h * k) = 0 by ring, AddChar.map_zero_eq_one, mul_one]
    have : (D n hn G hodd).τ = -(ω₂ n : ℂ) := by
      show ((δ n : ℝ) : ℂ) - 1 = _
      have := τ_eq n
      exact_mod_cast this
    rw [this]; ring
  -- Fourier inversion: `s = τ^2 • δ₀`
  have hs0 : s = fun g => (D n hn G hodd).τ ^ 2 * (if g = 0 then 1 else 0) := by
    have h1 : dft s = dft (fun g => (D n hn G hodd).τ ^ 2 * (if g = 0 then (1 : ℂ) else 0)) := by
      funext k
      rw [hconst, dft_apply]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true,
        zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul]
    exact (dft (N := n)).injective h1
  -- conclude
  have := congrFun hs0 g
  simp only [hs] at this
  rw [CoeffData.Q_def, if_neg hh, mul_zero, add_zero]
  have hsum : ∑ m, (D n hn G hodd).A (m + g) h * (D n hn G hodd).A h m
      = (D n hn G hodd).τ⁻¹ ^ 2 * ∑ a, (D n hn G hodd).B (g + a) h * (D n hn G hodd).B h a := by
    rw [mul_sum]; apply sum_congr rfl; intro m _
    rw [CoeffData.A_def, CoeffData.A_def, add_comm m g]; ring
  rw [hsum, this]
  field_simp
  ring

end quadratics

end Concrete
end HaagerupIzumi
