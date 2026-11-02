module

import all Mathlib.Data.Complex.Basic

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic
public import HaagerupIzumi.Analytic.GammaHolomorphic
public import HaagerupIzumi.Analytic.GammaShift

/-!
# Finite-product continuation from the hyperbolic-gamma strip

The smaller period is `b`, with `0 < b ≤ a`. Each complex argument is moved
to the half-open strip `b ≤ re z < 2b`, where the original strip function is
defined and nonzero. The continuation is an explicit finite product or
quotient. This file proves the elementary representative and denominator
facts independently of the construction of the strip function.

`StripData` keeps the remaining analytic input explicit. Defining `extension`
alone does not assert that it is holomorphic across the floor boundaries.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped ComplexConjugate

namespace HaagerupIzumi.GammaContinuation

/-- The multiplier in the shift by the smaller period. -/
def factor (a : ℝ) (z : ℂ) : ℂ := 2 * Complex.sin (Real.pi * z / a)

/-- The product of the first `m` shift multipliers starting at `z`. -/
def shiftProduct (a b : ℝ) (z : ℂ) (m : ℕ) : ℂ :=
  ∏ j ∈ Finset.range m, factor a (z + (j : ℂ) * b)

@[simp] lemma shiftProduct_zero (a b : ℝ) (z : ℂ) : shiftProduct a b z 0 = 1 := by
  simp [shiftProduct]

lemma shiftProduct_succ (a b : ℝ) (z : ℂ) (m : ℕ) :
    shiftProduct a b z (m + 1) = shiftProduct a b z m * factor a (z + (m : ℂ) * b) := by
  simp only [shiftProduct, Finset.prod_range_succ]

lemma shiftProduct_add (a b : ℝ) (z : ℂ) (m n : ℕ) :
    shiftProduct a b z (m + n) =
      shiftProduct a b z m * shiftProduct a b (z + (m : ℂ) * b) n := by
  unfold shiftProduct
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  push_cast
  ring

lemma shiftProduct_succ_left (a b : ℝ) (z : ℂ) (m : ℕ) :
    shiftProduct a b z (m + 1) = factor a z * shiftProduct a b (z + b) m := by
  rw [Nat.add_comm m 1, shiftProduct_add]
  simp [shiftProduct]

lemma differentiable_shiftProduct (a b : ℝ) (m : ℕ) :
    Differentiable ℂ (fun z => shiftProduct a b z m) := by
  unfold shiftProduct
  apply Differentiable.fun_finsetProd
  intro j _
  unfold factor
  fun_prop

/-- The number of signed shifts from the canonical representative to `z`. -/
def shiftIndex (b : ℝ) (z : ℂ) : ℤ := ⌊z.re / b⌋ - 1

/-- The canonical representative in the half-open strip `[b,2b)`. -/
def representative (b : ℝ) (z : ℂ) : ℂ := z - (shiftIndex b z : ℂ) * b

lemma representative_re (b : ℝ) (z : ℂ) :
    (representative b z).re = z.re - (shiftIndex b z : ℝ) * b := by
  simp [representative]

lemma representative_add_index (b : ℝ) (z : ℂ) :
    representative b z + (shiftIndex b z : ℂ) * b = z := by
  simp [representative]

lemma representative_bounds {b : ℝ} (hb : 0 < b) (z : ℂ) :
    b ≤ (representative b z).re ∧ (representative b z).re < 2 * b := by
  have hlo := (le_div_iff₀ hb).mp (Int.floor_le (z.re / b))
  have hhi := (div_lt_iff₀ hb).mp (Int.lt_floor_add_one (z.re / b))
  rw [representative_re]
  simp only [shiftIndex, Int.cast_sub, Int.cast_one]
  constructor <;> nlinarith

lemma representative_mem_strip {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (z : ℂ) :
    0 < (representative b z).re ∧ (representative b z).re < a + b := by
  obtain ⟨hlo, hhi⟩ := representative_bounds hb z
  constructor <;> linarith

lemma shiftIndex_add_int_mul {b : ℝ} (hb : b ≠ 0) (z : ℂ) (m : ℤ) :
    shiftIndex b (z + (m : ℂ) * b) = shiftIndex b z + m := by
  have hre : (z + (m : ℂ) * b).re / b = z.re / b + (m : ℝ) := by
    simp only [add_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
      mul_zero, sub_zero]
    field_simp
  unfold shiftIndex
  rw [hre, Int.floor_add_intCast]
  ring

lemma representative_add_int_mul {b : ℝ} (hb : b ≠ 0) (z : ℂ) (m : ℤ) :
    representative b (z + (m : ℂ) * b) = representative b z := by
  simp only [representative, shiftIndex_add_int_mul hb, Int.cast_add]
  ring

/-- The negative period semigroup; this is the pole-set formula. -/
def poleLattice (a b : ℝ) : Set ℂ :=
  {z | ∃ r s : ℕ, z = -((r : ℂ) * a + (s : ℂ) * b)}

/-- The positive translated period semigroup; this is the zero-set formula. -/
def zeroLattice (a b : ℝ) : Set ℂ :=
  {z | ∃ r s : ℕ, z = (a : ℂ) + b + (r : ℂ) * a + (s : ℂ) * b}

lemma not_mem_poleLattice_of_re_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : 0 < z.re) : z ∉ poleLattice a b := by
  rintro ⟨r, s, heq⟩
  have hre : z.re = -((r : ℝ) * a + (s : ℝ) * b) := by rw [heq]; simp
  have hnonneg : 0 ≤ (r : ℝ) * a + (s : ℝ) * b := by positivity
  linarith

lemma factor_eq_zero_iff {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    factor a z = 0 ↔ ∃ k : ℤ, z = (k : ℂ) * a := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · intro hz
    have hsin : Complex.sin (Real.pi * z / a) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
    refine ⟨k, ?_⟩
    calc
      z = (Real.pi * z / a) * (a / Real.pi) := by field_simp
      _ = ((k : ℂ) * Real.pi) * (a / Real.pi) := by rw [hk]
      _ = (k : ℂ) * a := by field_simp
  · rintro ⟨k, rfl⟩
    have harg : Real.pi * ((k : ℂ) * a) / a = (k : ℂ) * Real.pi := by
      field_simp
    have hsin := Complex.sin_eq_zero_iff.mpr ⟨k, harg⟩
    simp only [factor, hsin, mul_zero]

/-- A vanishing descending factor strictly below `a` identifies an actual
pole, rather than an artificial singularity of the finite quotient. -/
lemma mem_poleLattice_of_factor_eq_zero {a b : ℝ} (ha : 0 < a) (z : ℂ) (j : ℕ)
    (hre : (z + (j : ℂ) * b).re < a) (hz : factor a (z + (j : ℂ) * b) = 0) :
    z ∈ poleLattice a b := by
  obtain ⟨k, hk⟩ := (factor_eq_zero_iff ha.ne' _).mp hz
  have hkr : (k : ℝ) * a < a := by simpa [hk] using hre
  have hk0 : k ≤ 0 := by
    by_contra h
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith
  have hcast : ((-k).toNat : ℂ) = -(k : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg (neg_nonneg.mpr hk0))
  refine ⟨(-k).toNat, j, ?_⟩
  rw [hcast]
  linear_combination hk

/-- Non-poles have nonzero descending products whenever all factors lie
strictly below `a` in real part. -/
lemma shiftProduct_ne_zero_of_re_lt {a b : ℝ} (ha : 0 < a) (z : ℂ) (m : ℕ)
    (hz : z ∉ poleLattice a b)
    (hre : ∀ j < m, (z + (j : ℂ) * b).re < a) :
    shiftProduct a b z m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hfactor
  exact hz (mem_poleLattice_of_factor_eq_zero ha z j (hre j (Finset.mem_range.mp hj)) hfactor)

lemma factor_ne_zero_on_strip {a : ℝ} (ha : 0 < a) (z : ℂ)
    (hz₀ : 0 < z.re) (hz₁ : z.re < a) : factor a z ≠ 0 := by
  intro hf
  have hpole := mem_poleLattice_of_factor_eq_zero (b := a) ha z 0
    (by simpa using hz₁) (by simpa using hf)
  exact not_mem_poleLattice_of_re_pos ha ha hz₀ hpole

/-- The denominator used by continuation to the left never vanishes away
from the genuine pole lattice. -/
lemma descendingProduct_ne_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hk : shiftIndex b z < 0) (hz : z ∉ poleLattice a b) :
    shiftProduct a b z (-shiftIndex b z).toNat ≠ 0 := by
  apply shiftProduct_ne_zero_of_re_lt (lt_of_lt_of_le hb hba) z _ hz
  intro j hj
  have hm : (((-shiftIndex b z).toNat : ℕ) : ℝ) = -(shiftIndex b z : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -shiftIndex b z))
  have hj' : (j : ℝ) + 1 ≤ ((-shiftIndex b z).toNat : ℕ) := by
    exact_mod_cast (show j + 1 ≤ (-shiftIndex b z).toNat by omega)
  have hjb := mul_le_mul_of_nonneg_right hj' hb.le
  have hupper := (representative_bounds hb z).2
  rw [representative_re] at hupper
  rw [hm] at hjb
  simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
    mul_zero, sub_zero]
  nlinarith

/-- A vanishing factor on an upward path from the positive strip produces
one of the prescribed zeros at its final argument. -/
lemma mem_zeroLattice_of_factor_eq_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (w : ℂ) (m j : ℕ) (hw : 0 < w.re) (hj : j < m)
    (hfactor : factor a (w + (j : ℂ) * b) = 0) :
    w + (m : ℂ) * b ∈ zeroLattice a b := by
  obtain ⟨k, hk⟩ := (factor_eq_zero_iff ha.ne' _).mp hfactor
  have hwj : 0 < (w + (j : ℂ) * b).re := by
    simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
      mul_zero, sub_zero]
    positivity
  have hkr : 0 < (k : ℝ) * a := by simpa [hk] using hwj
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
    nlinarith
  have hcast : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ k - 1))
  have hm : (m : ℂ) = (j : ℂ) + 1 + ((m - j - 1 : ℕ) : ℂ) := by
    exact_mod_cast (show m = j + 1 + (m - j - 1) by omega)
  refine ⟨(k - 1).toNat, m - j - 1, ?_⟩
  rw [hcast, hm]
  linear_combination hk

lemma shiftProduct_ne_zero_of_not_mem_zeroLattice {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (w : ℂ) (m : ℕ) (hw : 0 < w.re)
    (hz : w + (m : ℂ) * b ∉ zeroLattice a b) : shiftProduct a b w m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hfactor
  exact hz (mem_zeroLattice_of_factor_eq_zero ha hb w m j hw
    (Finset.mem_range.mp hj) hfactor)

/-- Input for the continuation construction, proved separately from the
regularized integral. The shift hypothesis is only on the overlap of strips. -/
structure StripData (a b : ℝ) where
  gamma : ℂ → ℂ
  smaller_pos : 0 < b
  smaller_le : b ≤ a
  differentiableOn : DifferentiableOn ℂ gamma {z | 0 < z.re ∧ z.re < a + b}
  ne_zero : ∀ z, 0 < z.re → z.re < a + b → gamma z ≠ 0
  shift : ∀ z, 0 < z.re → z.re < a → gamma (z + b) = factor a z * gamma z

namespace StripData

variable {a b : ℝ} (G : StripData a b)

lemma iterated_shift (z : ℂ) (m : ℕ) (hz : 0 < z.re)
    (hend : (z + (m : ℂ) * b).re < a + b) :
    G.gamma (z + (m : ℂ) * b) = shiftProduct a b z m * G.gamma z := by
  revert hend
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hend
    have hb := G.smaller_pos
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hwpos : 0 < (z + (m : ℂ) * b).re := by
      simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
        mul_zero, sub_zero]
      positivity
    have hwlt : (z + (m : ℂ) * b).re < a := by
      simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
        mul_zero, sub_zero, Nat.cast_add, Nat.cast_one, one_re] at hend ⊢
      nlinarith
    have heq : z + ((m + 1 : ℕ) : ℂ) * b = (z + (m : ℂ) * b) + b := by
      push_cast
      ring
    rw [heq, G.shift _ hwpos hwlt, ih (by linarith), shiftProduct_succ]
    ring

/-- The concrete total extension; values at poles use total field division. -/
def extension (z : ℂ) : ℂ :=
  if 0 ≤ shiftIndex b z then
    G.gamma (representative b z) *
      shiftProduct a b (representative b z) (shiftIndex b z).toNat
  else
    G.gamma (representative b z) /
      shiftProduct a b z (-shiftIndex b z).toNat

lemma representative_ne_zero (z : ℂ) : G.gamma (representative b z) ≠ 0 := by
  obtain ⟨hlo, hhi⟩ := representative_mem_strip G.smaller_pos G.smaller_le z
  exact G.ne_zero _ hlo hhi

lemma extension_ne_zero_of_index_neg (z : ℂ) (hk : shiftIndex b z < 0)
    (hz : z ∉ poleLattice a b) : G.extension z ≠ 0 := by
  rw [extension, if_neg (by omega)]
  exact div_ne_zero (G.representative_ne_zero z)
    (descendingProduct_ne_zero G.smaller_pos G.smaller_le z hk hz)

/-- The finite quotient and product agree with the original strip function
where that function was defined. -/
lemma extension_eq_on_strip (z : ℂ) (hz₀ : 0 < z.re) (hz₁ : z.re < a + b) :
    G.extension z = G.gamma z := by
  obtain ⟨hrep₀, hrep₁⟩ := representative_mem_strip G.smaller_pos G.smaller_le z
  by_cases hk : 0 ≤ shiftIndex b z
  · have hcast : ((shiftIndex b z).toNat : ℂ) = (shiftIndex b z : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hk)
    have hrep : representative b z + ((shiftIndex b z).toNat : ℂ) * b = z := by
      rw [hcast]
      exact representative_add_index b z
    have heq := G.iterated_shift (representative b z) (shiftIndex b z).toNat hrep₀
      (by simpa only [hrep] using hz₁)
    rw [hrep] at heq
    rw [extension, if_pos hk]
    simpa only [mul_comm] using heq.symm
  · have hk' : shiftIndex b z < 0 := by omega
    have hcast : ((-shiftIndex b z).toNat : ℂ) = -(shiftIndex b z : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -shiftIndex b z))
    have hrep : z + ((-shiftIndex b z).toNat : ℂ) * b = representative b z := by
      rw [hcast]
      unfold representative
      ring
    have heq := G.iterated_shift z (-shiftIndex b z).toNat hz₀
      (by simpa only [hrep] using hrep₁)
    rw [hrep] at heq
    have hpole := not_mem_poleLattice_of_re_pos
      (lt_of_lt_of_le G.smaller_pos G.smaller_le) G.smaller_pos hz₀
    have hden := descendingProduct_ne_zero G.smaller_pos G.smaller_le z hk' hpole
    rw [extension, if_neg hk]
    apply (div_eq_iff hden).mpr
    simpa only [mul_comm] using heq

/-- Outside the prescribed poles and zeros, the explicit continuation is
nonzero. This statement requires no unproved analytic continuation principle. -/
lemma extension_ne_zero (z : ℂ) (hpole : z ∉ poleLattice a b)
    (hzero : z ∉ zeroLattice a b) : G.extension z ≠ 0 := by
  by_cases hk : 0 ≤ shiftIndex b z
  · have hcast : ((shiftIndex b z).toNat : ℂ) = (shiftIndex b z : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hk)
    have hrep : representative b z + ((shiftIndex b z).toNat : ℂ) * b = z := by
      rw [hcast]
      exact representative_add_index b z
    rw [extension, if_pos hk]
    apply mul_ne_zero (G.representative_ne_zero z)
    apply shiftProduct_ne_zero_of_not_mem_zeroLattice
      (lt_of_lt_of_le G.smaller_pos G.smaller_le) G.smaller_pos
    · exact (representative_mem_strip G.smaller_pos G.smaller_le z).1
    · simpa only [hrep] using hzero
  · exact G.extension_ne_zero_of_index_neg z (by omega) hpole

/-! ## Fixed-index charts and gluing across floor boundaries -/

/-- A fixed-index chart has no floor operation in its argument. -/
def chart (k : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ k then
    G.gamma (z - (k : ℂ) * b) * shiftProduct a b (z - (k : ℂ) * b) k.toNat
  else
    G.gamma (z - (k : ℂ) * b) / shiftProduct a b z (-k).toNat

lemma extension_eq_chart (z : ℂ) : G.extension z = G.chart (shiftIndex b z) z := rfl

lemma chart_nat (m : ℕ) (z : ℂ) :
    G.chart (m : ℤ) z =
      G.gamma (z - (m : ℂ) * b) * shiftProduct a b (z - (m : ℂ) * b) m := by
  simp [chart]

lemma chart_neg_nat (m : ℕ) (z : ℂ) :
    G.chart (-(m : ℤ)) z = G.gamma (z + (m : ℂ) * b) / shiftProduct a b z m := by
  by_cases hm : m = 0
  · subst m
    simp [chart]
  · have hn : ¬0 ≤ -(m : ℤ) := by omega
    rw [chart, if_neg hn]
    simp

lemma chart_nat_succ (m : ℕ) (z : ℂ)
    (hlo : 0 < (z - ((m + 1 : ℕ) : ℂ) * b).re)
    (hhi : (z - ((m + 1 : ℕ) : ℂ) * b).re < a) :
    G.chart (m : ℤ) z = G.chart ((m + 1 : ℕ) : ℤ) z := by
  have hbase : z - (m : ℂ) * b = (z - ((m + 1 : ℕ) : ℂ) * b) + b := by
    push_cast
    ring
  rw [G.chart_nat, G.chart_nat, hbase, G.shift _ hlo hhi, shiftProduct_succ_left]
  ring

lemma chart_neg_nat_succ (m : ℕ) (z : ℂ)
    (hlo : 0 < (z + (m : ℂ) * b).re) (hhi : (z + (m : ℂ) * b).re < a) :
    G.chart (-((m + 1 : ℕ) : ℤ)) z = G.chart (-(m : ℤ)) z := by
  have hbase : z + ((m + 1 : ℕ) : ℂ) * b = (z + (m : ℂ) * b) + b := by
    push_cast
    ring
  have hf := factor_ne_zero_on_strip (lt_of_lt_of_le G.smaller_pos G.smaller_le)
    (z + (m : ℂ) * b) hlo hhi
  rw [G.chart_neg_nat, G.chart_neg_nat, hbase, G.shift _ hlo hhi, shiftProduct_succ]
  rw [mul_comm (factor a (z + (m : ℂ) * b)), mul_div_mul_right _ _ hf]

lemma chart_adjacent (k : ℤ) (z : ℂ)
    (hlo : 0 < (z - (k : ℂ) * b).re) (hhi : (z - (k : ℂ) * b).re < a) :
    G.chart (k - 1) z = G.chart k z := by
  by_cases hk : 0 < k
  · let m := (k - 1).toNat
    have hm : (m : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have hk' : k = ((m + 1 : ℕ) : ℤ) := by omega
    have hkc : ((m + 1 : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast hk'.symm
    rw [← hm, hk']
    exact G.chart_nat_succ m z (by simpa only [hkc] using hlo) (by simpa only [hkc] using hhi)
  · let m := (-k).toNat
    have hm : (m : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hk' : k = -(m : ℤ) := by omega
    have hk1 : k - 1 = -((m + 1 : ℕ) : ℤ) := by omega
    have hmc : (m : ℂ) = -(k : ℂ) := by exact_mod_cast hm
    have hbase : z + (m : ℂ) * b = z - (k : ℂ) * b := by rw [hmc]; ring
    rw [hk1, hk']
    exact G.chart_neg_nat_succ m z (by simpa only [hbase] using hlo)
      (by simpa only [hbase] using hhi)

/-- Within a strip of width `2b`, only two adjacent canonical indices occur. -/
lemma index_eq_or_sub_one (hb : 0 < b) (k : ℤ) (z : ℂ)
    (hlo : 0 < (z - (k : ℂ) * b).re) (hhi : (z - (k : ℂ) * b).re < 2 * b) :
    shiftIndex b z = k ∨ shiftIndex b z = k - 1 := by
  simp only [sub_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
    mul_zero, sub_zero] at hlo hhi
  have hlow : (k : ℝ) ≤ z.re / b := (le_div_iff₀ hb).mpr (by linarith)
  have hhigh : z.re / b < (k : ℝ) + 2 := (div_lt_iff₀ hb).mpr (by nlinarith)
  have hfloor₀ : k ≤ ⌊z.re / b⌋ := Int.le_floor.mpr hlow
  have hfloor₁ : ⌊z.re / b⌋ < k + 2 := Int.floor_lt.mpr (by simpa using hhigh)
  unfold shiftIndex
  omega

lemma extension_eq_chart_of_bounds (k : ℤ) (z : ℂ)
    (hlo : 0 < (z - (k : ℂ) * b).re) (hhi : (z - (k : ℂ) * b).re < 2 * b) :
    G.extension z = G.chart k z := by
  rw [G.extension_eq_chart]
  obtain h | h := index_eq_or_sub_one G.smaller_pos k z hlo hhi
  · rw [h]
  · rw [h]
    apply G.chart_adjacent k z hlo
    have hfloor : ⌊z.re / b⌋ = k := by unfold shiftIndex at h; omega
    have hu := Int.lt_floor_add_one (z.re / b)
    rw [hfloor] at hu
    have hu' := (div_lt_iff₀ G.smaller_pos).mp hu
    simp only [sub_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
      mul_zero, sub_zero]
    have hba := G.smaller_le
    linarith

lemma differentiableAt_gamma (z : ℂ) (hz₀ : 0 < z.re) (hz₁ : z.re < a + b) :
    DifferentiableAt ℂ G.gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < a + b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  exact G.differentiableOn.differentiableAt (hopen.mem_nhds ⟨hz₀, hz₁⟩)

lemma differentiableAt_chart_index (z : ℂ) (hpole : z ∉ poleLattice a b) :
    DifferentiableAt ℂ (G.chart (shiftIndex b z)) z := by
  obtain ⟨hlo, hhi⟩ := representative_mem_strip G.smaller_pos G.smaller_le z
  have hpoint : DifferentiableAt ℂ G.gamma (z - (shiftIndex b z : ℂ) * b) :=
    G.differentiableAt_gamma _ hlo hhi
  have haffine : DifferentiableAt ℂ
      (fun w : ℂ => w - (shiftIndex b z : ℂ) * b) z :=
    differentiableAt_id.sub_const _
  have hgamma : DifferentiableAt ℂ
      (fun w : ℂ => G.gamma (w - (shiftIndex b z : ℂ) * b)) z := by
    simpa only [Function.comp_def] using hpoint.comp z haffine
  by_cases hk : 0 ≤ shiftIndex b z
  · have hchart : G.chart (shiftIndex b z) = fun w =>
        G.gamma (w - (shiftIndex b z : ℂ) * b) *
          shiftProduct a b (w - (shiftIndex b z : ℂ) * b) (shiftIndex b z).toNat := by
      funext w
      simp only [chart, if_pos hk]
    rw [hchart]
    convert! hgamma.mul
      ((differentiable_shiftProduct a b (shiftIndex b z).toNat _).comp z haffine) using 1
  · have hchart : G.chart (shiftIndex b z) = fun w =>
        G.gamma (w - (shiftIndex b z : ℂ) * b) /
          shiftProduct a b w (-shiftIndex b z).toNat := by
      funext w
      simp only [chart, if_neg hk]
    rw [hchart]
    exact hgamma.div (differentiable_shiftProduct a b (-shiftIndex b z).toNat z)
      (descendingProduct_ne_zero G.smaller_pos G.smaller_le z (by omega) hpole)

/-- The finite-product extension is holomorphic away from its pole lattice,
including at the boundaries where the floor used to choose a representative
changes. The proof uses neighboring fixed-index charts. -/
lemma differentiableAt_extension (z : ℂ) (hpole : z ∉ poleLattice a b) :
    DifferentiableAt ℂ G.extension z := by
  apply (G.differentiableAt_chart_index z hpole).congr_of_eventuallyEq
  have hbase : Continuous (fun w : ℂ => (w - (shiftIndex b z : ℂ) * b).re) :=
    Complex.continuous_re.comp (continuous_id.sub continuous_const)
  have hlo : 0 < (z - (shiftIndex b z : ℂ) * b).re :=
    (representative_mem_strip G.smaller_pos G.smaller_le z).1
  have hhi : (z - (shiftIndex b z : ℂ) * b).re < 2 * b :=
    (representative_bounds G.smaller_pos z).2
  filter_upwards [(isOpen_lt continuous_const hbase).mem_nhds hlo,
    (isOpen_lt hbase continuous_const).mem_nhds hhi] with w hw₀ hw₁
  exact G.extension_eq_chart_of_bounds (shiftIndex b z) w hw₀ hw₁

lemma differentiableOn_extension : DifferentiableOn ℂ G.extension (poleLattice a b)ᶜ := by
  intro z hz
  exact (G.differentiableAt_extension z hz).differentiableWithinAt

/-- The germ used to compute the residue at the origin is exactly the
fixed-index `-1` chart of the global extension. -/
lemma extension_eq_origin_germ (z : ℂ) (hlo : -b < z.re) (hhi : z.re < b) :
    G.extension z = G.gamma (z + b) / factor a z := by
  have heq := G.extension_eq_chart_of_bounds (-1) z
    (by simp; linarith) (by simp; linarith)
  simpa [chart, shiftProduct] using heq

end StripData

lemma factor_conj (a : ℝ) (z : ℂ) : factor a (conj z) = conj (factor a z) := by
  norm_num [factor, map_div₀, ← Complex.sin_conj, Complex.conj_ofNat]

lemma shiftProduct_conj (a b : ℝ) (z : ℂ) (m : ℕ) :
    shiftProduct a b (conj z) m = conj (shiftProduct a b z m) := by
  simp only [shiftProduct, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  have heq : conj (z + (j : ℂ) * b) = conj z + (j : ℂ) * b := by simp
  rw [← heq, factor_conj]

lemma representative_conj (b : ℝ) (z : ℂ) :
    representative b (conj z) = conj (representative b z) := by
  simp [representative, shiftIndex]

lemma StripData.extension_conj {a b : ℝ} (G : StripData a b)
    (hc : ∀ z, G.gamma (conj z) = conj (G.gamma z)) (z : ℂ) :
    G.extension (conj z) = conj (G.extension z) := by
  have hi : shiftIndex b (conj z) = shiftIndex b z := by simp [shiftIndex]
  simp only [StripData.extension, hi, representative_conj]
  split_ifs with h
  · rw [hc, shiftProduct_conj, map_mul]
  · rw [hc, shiftProduct_conj, map_div₀]

/-- The analytic input is supplied by the actual regularized gamma integral,
not by a hypothetical gamma interface. -/
def integralStripData (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) : StripData a b where
  gamma := GammaIntegral.gamma a b
  smaller_pos := hb
  smaller_le := hba
  differentiableOn := GammaIntegral.differentiableOn_gamma (lt_of_lt_of_le hb hba) hb
  ne_zero := fun z _ _ => GammaIntegral.gamma_ne_zero a b z
  shift := by
    intro z hz₀ hz₁
    simpa only [factor, mul_div_assoc] using
      GammaIntegral.gamma_shift₂_strip a b z (lt_of_lt_of_le hb hba) hb hz₀ hz₁

/-- The explicitly continued hyperbolic gamma function, for ordered positive
periods. Its construction contains no assumed special-function identities. -/
def gamma (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) : ℂ → ℂ :=
  (integralStripData a b hb hba).extension

lemma gamma_eq_on_strip (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz₀ : 0 < z.re) (hz₁ : z.re < a + b) :
    gamma a b hb hba z = GammaIntegral.gamma a b z :=
  (integralStripData a b hb hba).extension_eq_on_strip z hz₀ hz₁

lemma gamma_differentiableAt (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz : z ∉ poleLattice a b) : DifferentiableAt ℂ (gamma a b hb hba) z :=
  (integralStripData a b hb hba).differentiableAt_extension z hz

lemma gamma_conj (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ) :
    gamma a b hb hba (conj z) = conj (gamma a b hb hba z) :=
  (integralStripData a b hb hba).extension_conj (GammaIntegral.gamma_conj a b) z

lemma gamma_real_axis (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (x : ℝ) :
    (gamma a b hb hba x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using (gamma_conj a b hb hba x).symm

lemma gamma_real_pos (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (x : ℝ)
    (hx₀ : 0 < x) (hx₁ : x < a + b) :
    0 < (gamma a b hb hba x).re ∧ (gamma a b hb hba x).im = 0 := by
  rw [gamma_eq_on_strip a b hb hba x hx₀ hx₁]
  exact GammaIntegral.gamma_real_pos a b x

end HaagerupIzumi.GammaContinuation
