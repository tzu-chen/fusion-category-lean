module

public import HaagerupIzumi.Analytic.GammaPeriodUniqueness
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
import all Mathlib.Data.Complex.Basic

/-!
# Local periods on a strip

A holomorphic function on a strip wider than each of two incommensurable
periods is constant if both local shift equations hold. Periodic gluing
extends the function to the plane before applying density.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology

namespace HaagerupIzumi.GammaPeriodUniqueness

def strip (W : ℝ) : Set ℂ := {z | 0 < z.re ∧ z.re < W}

lemma isOpen_strip (W : ℝ) : IsOpen (strip W) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma eq_nat_translate {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b)
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z)
    (n : ℕ) (z : ℂ) (hz : z ∈ strip W)
    (hn : z + (n : ℂ) * b ∈ strip W) : f (z + (n : ℂ) * b) = f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hre : (z + ((n + 1 : ℕ) : ℂ) * b).re = z.re + (n : ℝ) * b + b := by
      push_cast
      simp
      ring
    have hmid : z + (n : ℂ) * b ∈ strip W := by
      constructor
      · simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
          mul_zero, sub_zero]
        exact add_pos_of_pos_of_nonneg hz.1 (mul_nonneg (Nat.cast_nonneg n) hb.le)
      · have hh := hn.2
        rw [hre] at hh
        simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
          mul_zero, sub_zero]
        linarith
    have heq : z + ((n + 1 : ℕ) : ℂ) * b = (z + (n : ℂ) * b) + b := by
      push_cast
      ring
    rw [heq, hshift _ hmid (heq ▸ hn), ih hmid]

lemma eq_int_translate {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b)
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z)
    (k : ℤ) (z : ℂ) (hz : z ∈ strip W)
    (hk : z + (k : ℂ) * b ∈ strip W) : f (z + (k : ℂ) * b) = f z := by
  cases k with
  | ofNat n => exact eq_nat_translate hb hshift n z hz hk
  | negSucc n =>
    have heq : z + (Int.negSucc n : ℂ) * b + ((n + 1 : ℕ) : ℂ) * b = z := by
      push_cast
      ring
    have hh := eq_nat_translate hb hshift (n + 1)
      (z + (Int.negSucc n : ℂ) * b) hk (heq.symm ▸ hz)
    rw [heq] at hh
    exact hh.symm

lemma exists_strip_translate {b W : ℝ} (hb : 0 < b) (hbW : b < W) (z : ℂ) :
    ∃ k : ℤ, z - (k : ℂ) * b ∈ strip W := by
  let c : ℝ := (W - b) / 2
  let k : ℤ := ⌊(z.re - c) / b⌋
  have hlo := (le_div_iff₀ hb).mp (Int.floor_le ((z.re - c) / b))
  have hhi := (div_lt_iff₀ hb).mp (Int.lt_floor_add_one ((z.re - c) / b))
  refine ⟨k, ?_, ?_⟩
  all_goals
    simp only [sub_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
      mul_zero, sub_zero]
    dsimp [k, c] at *
    nlinarith

def stripExtension {b W : ℝ} (hb : 0 < b) (hbW : b < W) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (z - ((exists_strip_translate hb hbW z).choose : ℂ) * b)

lemma stripExtension_eq_chart {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b) (hbW : b < W)
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z)
    (z : ℂ) (k : ℤ) (hk : z - (k : ℂ) * b ∈ strip W) :
    stripExtension hb hbW f z = f (z - (k : ℂ) * b) := by
  let j := (exists_strip_translate hb hbW z).choose
  have hj : z - (j : ℂ) * b ∈ strip W := (exists_strip_translate hb hbW z).choose_spec
  have heq : (z - (k : ℂ) * b) + ((k - j : ℤ) : ℂ) * b = z - (j : ℂ) * b := by
    push_cast
    ring
  have hh := eq_int_translate hb hshift (k - j) (z - (k : ℂ) * b) hk (heq.symm ▸ hj)
  rw [heq] at hh
  exact hh

lemma stripExtension_eq {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b) (hbW : b < W)
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z)
    {z : ℂ} (hz : z ∈ strip W) : stripExtension hb hbW f z = f z := by
  simpa using stripExtension_eq_chart hb hbW hshift z 0 (by simpa using hz)

lemma differentiable_stripExtension {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b) (hbW : b < W)
    (hf : DifferentiableOn ℂ f (strip W))
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z) :
    Differentiable ℂ (stripExtension hb hbW f) := by
  intro z
  obtain ⟨k, hk⟩ := exists_strip_translate hb hbW z
  have hd := (hf.differentiableAt ((isOpen_strip W).mem_nhds hk)).comp z
    (differentiableAt_id.sub_const ((k : ℂ) * b))
  apply hd.congr_of_eventuallyEq
  have hevent : ∀ᶠ w in 𝓝 z, w - (k : ℂ) * b ∈ strip W :=
    (continuous_id.sub continuous_const).continuousAt.eventually
      ((isOpen_strip W).mem_nhds hk)
  filter_upwards [hevent] with w hw
  exact stripExtension_eq_chart hb hbW hshift w k hw

lemma periodic_stripExtension {f : ℂ → ℂ} {b W : ℝ} (hb : 0 < b) (hbW : b < W)
    (hshift : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z) :
    Function.Periodic (stripExtension hb hbW f) (b : ℂ) := by
  intro z
  obtain ⟨k, hk⟩ := exists_strip_translate hb hbW z
  have heq : z + b - ((k + 1 : ℤ) : ℂ) * b = z - (k : ℂ) * b := by
    push_cast
    ring
  rw [stripExtension_eq_chart hb hbW hshift z k hk,
    stripExtension_eq_chart hb hbW hshift (z + b) (k + 1) (heq.symm ▸ hk), heq]

lemma differentiable_eq_const_of_two_real_periods {f : ℂ → ℂ} {a b : ℝ}
    (hf : Differentiable ℂ f) (ha : Function.Periodic f (a : ℂ))
    (hb : Function.Periodic f (b : ℂ)) (hirr : Irrational (a / b)) :
    ∀ z : ℂ, f z = f 0 := by
  suffices hzero : ∀ z : ℂ, deriv f z = 0 from
    fun z => is_const_of_deriv_eq_zero hf hzero z 0
  intro z
  let g : ℝ → ℂ := fun t => f (z + (t : ℂ))
  have hg : Continuous g := hf.continuous.comp (by fun_prop)
  have hp (c : ℝ) (hc : Function.Periodic f (c : ℂ)) : Function.Periodic g c := by
    intro x
    unfold g
    rw [Complex.ofReal_add, ← add_assoc]
    exact hc (z + (x : ℂ))
  have hconst := continuous_eq_const_of_two_periods hg (hp a ha) (hp b hb) hirr
  have hfd : HasDerivAt f (deriv f z) (z + id (0 : ℂ)) := by
    simpa using (hf z).hasDerivAt
  have hd : HasDerivAt g (deriv f z) 0 := by
    convert! (hfd.comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_add z)).comp_ofReal using 1
    simp
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (g 0))

/-- Local incommensurable periods suffice when the strip is wider than each
individual period. No boundedness assumption on the function is needed. -/
theorem eq_of_local_periods {f : ℂ → ℂ} {a b W : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haW : a < W) (hbW : b < W)
    (hirr : Irrational (a / b)) (hf : DifferentiableOn ℂ f (strip W))
    (hshiftA : ∀ z : ℂ, z ∈ strip W → z + a ∈ strip W → f (z + a) = f z)
    (hshiftB : ∀ z : ℂ, z ∈ strip W → z + b ∈ strip W → f (z + b) = f z)
    {z w : ℂ} (hz : z ∈ strip W) (hw : w ∈ strip W) : f z = f w := by
  let F := stripExtension hb hbW f
  have hF : Differentiable ℂ F := differentiable_stripExtension hb hbW hf hshiftB
  have hFB : Function.Periodic F (b : ℂ) := periodic_stripExtension hb hbW hshiftB
  have hFA : Function.Periodic F (a : ℂ) := by
    have hshiftF : Differentiable ℂ (fun z : ℂ => F (z + a)) :=
      hF.comp (differentiable_id.add_const _)
    have hidentity : (fun z : ℂ => F (z + a)) = F := by
      apply (hshiftF.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        (hF.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := ((W - a) / 2 : ℝ))
      have hmid : (((W - a) / 2 : ℝ) : ℂ) ∈ strip (W - a) := by
        constructor <;> simp only [ofReal_re] <;> linarith
      filter_upwards [(isOpen_strip (W - a)).mem_nhds hmid] with u hu
      have huW : u ∈ strip W := ⟨hu.1, by linarith [hu.2]⟩
      have huaW : u + a ∈ strip W := by
        constructor <;> simp only [add_re, ofReal_re] <;> linarith [hu.1, hu.2]
      change stripExtension hb hbW f (u + a) = stripExtension hb hbW f u
      rw [stripExtension_eq hb hbW hshiftB huaW, stripExtension_eq hb hbW hshiftB huW]
      exact hshiftA u huW huaW
    exact fun u => congrFun hidentity u
  have hc := differentiable_eq_const_of_two_real_periods hF hFA hFB hirr
  have heq := (hc z).trans (hc w).symm
  simpa only [F, stripExtension_eq hb hbW hshiftB hz,
    stripExtension_eq hb hbW hshiftB hw] using heq

def horizontalStrip (S : ℝ) : Set ℂ := {z | |z.im| < S}

lemma isOpen_horizontalStrip (S : ℝ) : IsOpen (horizontalStrip S) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

theorem eq_of_local_imaginary_periods {f : ℂ → ℂ} {a b S : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haS : a < 2 * S) (hbS : b < 2 * S)
    (hirr : Irrational (a / b)) (hf : DifferentiableOn ℂ f (horizontalStrip S))
    (hshiftA : ∀ z : ℂ, z ∈ horizontalStrip S → z + a * I ∈ horizontalStrip S →
      f (z + a * I) = f z)
    (hshiftB : ∀ z : ℂ, z ∈ horizontalStrip S → z + b * I ∈ horizontalStrip S →
      f (z + b * I) = f z)
    {z w : ℂ} (hz : z ∈ horizontalStrip S) (hw : w ∈ horizontalStrip S) : f z = f w := by
  let g : ℂ → ℂ := fun u => f ((u - S) * I)
  have hmem {u : ℂ} (hu : u ∈ strip (2 * S)) : (u - S) * I ∈ horizontalStrip S := by
    change |((u - S) * I).im| < S
    simp only [mul_im, sub_re, ofReal_re, I_im, mul_one, sub_im, ofReal_im,
      sub_zero, I_re, mul_zero, add_zero]
    apply abs_lt.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hg : DifferentiableOn ℂ g (strip (2 * S)) := by
    intro u hu
    exact ((hf.differentiableAt ((isOpen_horizontalStrip S).mem_nhds (hmem hu))).comp u
      ((differentiableAt_id.sub_const (S : ℂ)).mul_const I)).differentiableWithinAt
  have hp (c : ℝ) (hc : ∀ u : ℂ, u ∈ horizontalStrip S →
      u + c * I ∈ horizontalStrip S → f (u + c * I) = f u) :
      ∀ u : ℂ, u ∈ strip (2 * S) → u + c ∈ strip (2 * S) → g (u + c) = g u := by
    intro u hu huc
    have heq : (u + c - S) * I = (u - S) * I + c * I := by ring
    unfold g
    rw [heq]
    exact hc _ (hmem hu) (heq ▸ hmem huc)
  have hinv (u : ℂ) : ((S : ℂ) - u * I - S) * I = u := by
    calc
      _ = -u * (I * I) := by ring
      _ = u := by rw [I_mul_I]; ring
  have hback {u : ℂ} (hu : u ∈ horizontalStrip S) : (S : ℂ) - u * I ∈ strip (2 * S) := by
    change |u.im| < S at hu
    have habs := abs_lt.mp hu
    constructor <;> simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, I_im,
      mul_one, zero_sub, sub_neg_eq_add] <;> linarith [habs.1, habs.2]
  have heq := eq_of_local_periods ha hb haS hbS hirr hg (hp a hshiftA) (hp b hshiftB)
    (hback hz) (hback hw)
  simpa only [g, hinv] using heq

end HaagerupIzumi.GammaPeriodUniqueness
