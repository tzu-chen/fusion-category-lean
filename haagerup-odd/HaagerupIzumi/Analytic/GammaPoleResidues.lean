module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaResidueZero
public import HaagerupIzumi.Analytic.GammaIdentities
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Simple poles of the explicit hyperbolic gamma function

The residue at zero propagates backwards through the two shift equations.
An irrational period ratio makes every denominator in this recursion nonzero.
The resulting residues are explicit and nonzero at every point of the pole
lattice.
-/

@[expose] public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace HaagerupIzumi

lemma HasResidue.congr_eventually {f g : ℂ → ℂ} {p ρ : ℂ}
    (hf : HasResidue f p ρ) (hfg : f =ᶠ[𝓝[≠] p] g) : HasResidue g p ρ := by
  apply hf.congr'
  exact hfg.mono fun z hz => congrArg ((z - p) * ·) hz

/-- A shift equation transports a simple-pole residue backwards whenever
its multiplier is continuous and nonzero at the new pole. -/
lemma HasResidue.backward_shift {f m : ℂ → ℂ} {p c ρ : ℂ}
    (hf : HasResidue f (p + c) ρ) (hm : ContinuousAt m p) (hm₀ : m p ≠ 0)
    (hshift : ∀ᶠ z in 𝓝[≠] p, f (z + c) = m z * f z) :
    HasResidue f p (ρ / m p) := by
  have ht : Tendsto (fun z : ℂ => z + c) (𝓝[≠] p) (𝓝[≠] (p + c)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_id.add_const c).tendsto p).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z + c ≠ p + c
      exact fun heq => hz (add_right_cancel heq)
  have hlim := hf.comp ht
  have hdiv := hlim.div (hm.tendsto.mono_left nhdsWithin_le_nhds) hm₀
  apply hdiv.congr'
  filter_upwards [hshift, nhdsWithin_le_nhds (hm.eventually_ne hm₀)] with z hz hmz
  simp only [Function.comp_def, Pi.div_apply, add_sub_add_right_eq_sub, hz]
  field_simp

namespace GammaContinuation

/-- The residue of the actual global continuation at the origin. -/
theorem gamma_residue_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    HasResidue (gamma a b hb hba) 0
      ((Real.sqrt (a * b) : ℂ) / (2 * Real.pi)) := by
  apply (GammaIntegral.hasResidue_originGerm a b (lt_of_lt_of_le hb hba) hb).congr_eventually
  have hopen : IsOpen {z : ℂ | -b < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hzero : (0 : ℂ) ∈ {z : ℂ | -b < z.re ∧ z.re < b} := by
    simp only [Set.mem_ofPred_eq, Complex.zero_re]
    exact ⟨neg_lt_zero.mpr hb, hb⟩
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hzero)] with z hz
  have he := (integralStripData a b hb hba).extension_eq_origin_germ z hz.1 hz.2
  simpa only [gamma, integralStripData, GammaIntegral.originGerm, factor,
    mul_div_assoc] using he.symm

lemma factor_ne_zero_of_irrational_coordinate {a x : ℝ} (ha : a ≠ 0)
    (hx : Irrational (x / a)) : factor a (x : ℂ) ≠ 0 := by
  intro hf
  obtain ⟨k, hk⟩ := (factor_eq_zero_iff ha (x : ℂ)).mp hf
  have hreal : x = (k : ℝ) * a := by
    simpa only [Complex.ofReal_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_im, zero_mul, sub_zero] using congrArg Complex.re hk
  exact hx.ne_int k ((div_eq_iff ha).mpr hreal)

lemma factor_ne_zero_first_pole (a b : ℝ) (hb : 0 < b)
    (hirr : Irrational (a / b)) (r : ℕ) (hr : r ≠ 0) :
    factor b (-((r : ℂ) * a)) ≠ 0 := by
  have hi : Irrational ((-((r : ℝ) * a)) / b) := by
    convert (hirr.natCast_mul hr).neg using 1
    ring
  convert factor_ne_zero_of_irrational_coordinate hb.ne' hi using 1
  push_cast
  rfl

lemma factor_ne_zero_second_pole (a b : ℝ) (ha : 0 < a)
    (hirr : Irrational (a / b)) (r s : ℕ) (hs : s ≠ 0) :
    factor a (-((r : ℂ) * a + (s : ℂ) * b)) ≠ 0 := by
  have hi : Irrational (b / a) := by simpa only [inv_div] using hirr.inv
  have hi' : Irrational ((-((r : ℝ) * a + (s : ℝ) * b)) / a) := by
    convert ((hi.natCast_mul hs).natCast_add r).neg using 1
    field_simp
  convert factor_ne_zero_of_irrational_coordinate ha.ne' hi' using 1
  push_cast
  rfl

/-- Residues along the first-period ray, computed by backward shifts. -/
def firstPoleResidue (a b : ℝ) : ℕ → ℂ
  | 0 => (Real.sqrt (a * b) : ℂ) / (2 * Real.pi)
  | r + 1 => firstPoleResidue a b r / factor b (-(((r + 1 : ℕ) : ℂ) * a))

/-- The residue at `-r*a-s*b`, computed by first taking `r` backward
first-period shifts and then `s` backward second-period shifts. -/
def poleResidue (a b : ℝ) (r : ℕ) : ℕ → ℂ
  | 0 => firstPoleResidue a b r
  | s + 1 => poleResidue a b r s /
      factor a (-((r : ℂ) * a + ((s + 1 : ℕ) : ℂ) * b))

lemma firstPoleResidue_ne_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r : ℕ) : firstPoleResidue a b r ≠ 0 := by
  induction r with
  | zero =>
    apply div_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
        (mul_pos (lt_of_lt_of_le hb hba) hb)).ne'
    · exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  | succ r ih =>
    exact div_ne_zero ih (factor_ne_zero_first_pole a b hb hirr (r + 1) (by omega))

lemma poleResidue_ne_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s : ℕ) : poleResidue a b r s ≠ 0 := by
  induction s with
  | zero => exact firstPoleResidue_ne_zero a b hb hba hirr r
  | succ s ih =>
    exact div_ne_zero ih (factor_ne_zero_second_pole a b (lt_of_lt_of_le hb hba)
      hirr r (s + 1) (by omega))

lemma gamma_hasResidue_first_pole (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r : ℕ) :
    HasResidue (gamma a b hb hba) (-((r : ℂ) * a)) (firstPoleResidue a b r) := by
  induction r with
  | zero => simpa only [Nat.cast_zero, zero_mul, neg_zero, firstPoleResidue]
      using gamma_residue_zero a b hb hba
  | succ r ih =>
    have hp : -(((r + 1 : ℕ) : ℂ) * a) + a = -((r : ℂ) * a) := by push_cast; ring
    have hprev : HasResidue (gamma a b hb hba)
        (-(((r + 1 : ℕ) : ℂ) * a) + a) (firstPoleResidue a b r) := by rw [hp]; exact ih
    apply hprev.backward_shift (differentiable_factor b _).continuousAt
      (factor_ne_zero_first_pole a b hb hirr (r + 1) (by omega))
    filter_upwards [eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb
      (-(((r + 1 : ℕ) : ℂ) * a))] with z hz
    exact gamma_shift₁ a b hb hba z hz

/-- Every prescribed pole is simple, with its recursively computed residue. -/
theorem gamma_hasResidue_pole (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s : ℕ) :
    HasResidue (gamma a b hb hba) (-((r : ℂ) * a + (s : ℂ) * b))
      (poleResidue a b r s) := by
  induction s with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero, poleResidue]
      using gamma_hasResidue_first_pole a b hb hba hirr r
  | succ s ih =>
    have hp : -((r : ℂ) * a + ((s + 1 : ℕ) : ℂ) * b) + b =
        -((r : ℂ) * a + (s : ℂ) * b) := by push_cast; ring
    have hprev : HasResidue (gamma a b hb hba)
        (-((r : ℂ) * a + ((s + 1 : ℕ) : ℂ) * b) + b) (poleResidue a b r s) := by
      rw [hp]
      exact ih
    apply hprev.backward_shift (differentiable_factor a _).continuousAt
      (factor_ne_zero_second_pole a b (lt_of_lt_of_le hb hba) hirr r (s + 1) (by omega))
    filter_upwards [eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb
      (-((r : ℂ) * a + ((s + 1 : ℕ) : ℂ) * b))] with z hz
    exact gamma_shift₂ a b hb hba z hz

theorem gamma_has_nonzero_residue (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (p : ℂ) (hp : p ∈ poleLattice a b) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ HasResidue (gamma a b hb hba) p ρ := by
  obtain ⟨r, s, rfl⟩ := hp
  exact ⟨poleResidue a b r s, poleResidue_ne_zero a b hb hba hirr r s,
    gamma_hasResidue_pole a b hb hba hirr r s⟩

end GammaContinuation
end HaagerupIzumi
