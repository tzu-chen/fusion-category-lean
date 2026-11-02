module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaContinuation
public import HaagerupIzumi.Analytic.HypGamma
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Global identities for the explicitly continued hyperbolic gamma function

The finite-product construction is holomorphic off a closed countable pole
lattice. The analytic identity principle therefore transports the two strip
shifts and reflection to their full domains. No hypothetical gamma object is
used: the only imported interface results are elementary lattice topology.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped ComplexConjugate

namespace HaagerupIzumi.GammaContinuation

lemma poleLattice_inter_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (M : ℝ) :
    (poleLattice a b ∩ Metric.closedBall 0 M).Finite :=
  HypGamma.poleSet_inter_finite ha hb M

lemma poleLattice_isClosed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsClosed (poleLattice a b) :=
  HypGamma.poleSet_isClosed ha hb

lemma eventually_not_mem_poleLattice {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ poleLattice a b :=
  eventually_not_mem_poleSet ha hb p

lemma poleLattice_countable (a b : ℝ) : (poleLattice a b).Countable := by
  apply (Set.countable_range (fun p : ℕ × ℕ => -((p.1 : ℂ) * a + (p.2 : ℂ) * b))).mono
  rintro z ⟨r, s, rfl⟩
  exact ⟨(r, s), rfl⟩

lemma zeroLattice_countable (a b : ℝ) : (zeroLattice a b).Countable := by
  apply (Set.countable_range
    (fun p : ℕ × ℕ => (a : ℂ) + b + (p.1 : ℂ) * a + (p.2 : ℂ) * b)).mono
  rintro z ⟨r, s, rfl⟩
  exact ⟨(r, s), rfl⟩

lemma mem_zeroLattice_iff (a b : ℝ) (z : ℂ) :
    z ∈ zeroLattice a b ↔ (a : ℂ) + b - z ∈ poleLattice a b :=
  mem_zeroSet_iff z

lemma zeroLattice_isClosed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsClosed (zeroLattice a b) := by
  have heq : zeroLattice a b = (fun z : ℂ => (a : ℂ) + b - z) ⁻¹' poleLattice a b := by
    ext z
    exact mem_zeroLattice_iff a b z
  rw [heq]
  exact (poleLattice_isClosed ha hb).preimage (continuous_const.sub continuous_id)

lemma not_mem_zeroLattice_of_re_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : z.re < a + b) : z ∉ zeroLattice a b :=
  HypGamma.not_mem_zeroSet_of_re_lt ha hb hz

lemma not_mem_poleLattice_add_first {a b : ℝ} {z : ℂ} (hz : z ∉ poleLattice a b) :
    z + a ∉ poleLattice a b := by
  rintro ⟨r, s, h⟩
  apply hz
  refine ⟨r + 1, s, ?_⟩
  push_cast
  linear_combination h

lemma not_mem_poleLattice_add_second {a b : ℝ} {z : ℂ} (hz : z ∉ poleLattice a b) :
    z + b ∉ poleLattice a b := by
  rintro ⟨r, s, h⟩
  apply hz
  refine ⟨r, s + 1, ?_⟩
  push_cast
  linear_combination h

/-- A strip identity extends over the complement of a closed countable subset
of the complex plane, provided both sides are holomorphic there. -/
lemma eqOn_compl_of_eq_on_strip {S : Set ℂ} (hclosed : IsClosed S)
    (hcount : S.Countable) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Sᶜ) (hg : DifferentiableOn ℂ g Sᶜ)
    (c : ℝ) (hc : 0 < c) (hmid : ((c / 2 : ℝ) : ℂ) ∉ S)
    (heq : ∀ z : ℂ, 0 < z.re → z.re < c → f z = g z) : Set.EqOn f g Sᶜ := by
  apply (hf.analyticOnNhd hclosed.isOpen_compl).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hclosed.isOpen_compl)
    (Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ)
      (by simp only [Complex.rank_real_complex]; norm_num) hcount).isPreconnected hmid
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < c} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  filter_upwards [hopen.mem_nhds (show ((c / 2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < c}
    from by simp only [Set.mem_ofPred_eq, ofReal_re]; constructor <;> linarith)] with z hz
  exact heq z hz.1 hz.2

lemma differentiable_factor (a : ℝ) : Differentiable ℂ (factor a) := by
  unfold factor
  fun_prop

/-- The first real-period shift now holds everywhere away from the poles. -/
lemma gamma_shift₁ (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz : z ∉ poleLattice a b) :
    gamma a b hb hba (z + a) = factor b z * gamma a b hb hba z := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hf : DifferentiableOn ℂ (fun w => gamma a b hb hba (w + a)) (poleLattice a b)ᶜ := by
    intro w hw
    exact ((gamma_differentiableAt a b hb hba (w + a)
      (not_mem_poleLattice_add_first hw)).comp w
      (differentiableAt_id.add_const (a : ℂ))).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w => factor b w * gamma a b hb hba w)
      (poleLattice a b)ᶜ := by
    intro w hw
    exact ((differentiable_factor b w).mul
      (gamma_differentiableAt a b hb hba w hw)).differentiableWithinAt
  apply eqOn_compl_of_eq_on_strip (poleLattice_isClosed ha hb) (poleLattice_countable a b)
    hf hg b hb (not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)) ?_ hz
  intro w hw₀ hw₁
  rw [gamma_eq_on_strip a b hb hba w hw₀ (by linarith),
    gamma_eq_on_strip a b hb hba (w + a) (by simp; linarith) (by simp; linarith)]
  simpa only [factor, mul_div_assoc] using
    GammaIntegral.gamma_shift₁_strip a b w ha hb hw₀ hw₁

/-- The second real-period shift now holds everywhere away from the poles. -/
lemma gamma_shift₂ (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz : z ∉ poleLattice a b) :
    gamma a b hb hba (z + b) = factor a z * gamma a b hb hba z := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hf : DifferentiableOn ℂ (fun w => gamma a b hb hba (w + b)) (poleLattice a b)ᶜ := by
    intro w hw
    exact ((gamma_differentiableAt a b hb hba (w + b)
      (not_mem_poleLattice_add_second hw)).comp w
      (differentiableAt_id.add_const (b : ℂ))).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w => factor a w * gamma a b hb hba w)
      (poleLattice a b)ᶜ := by
    intro w hw
    exact ((differentiable_factor a w).mul
      (gamma_differentiableAt a b hb hba w hw)).differentiableWithinAt
  apply eqOn_compl_of_eq_on_strip (poleLattice_isClosed ha hb) (poleLattice_countable a b)
    hf hg a ha (not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)) ?_ hz
  intro w hw₀ hw₁
  rw [gamma_eq_on_strip a b hb hba w hw₀ (by linarith),
    gamma_eq_on_strip a b hb hba (w + b) (by simp; linarith) (by simp; linarith)]
  simpa only [factor, mul_div_assoc] using
    GammaIntegral.gamma_shift₂_strip a b w ha hb hw₀ hw₁

/-- Reflection on its natural domain: both a point and its reflection avoid
poles exactly when the point avoids the pole and zero lattices. -/
lemma gamma_reflection (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hp : z ∉ poleLattice a b) (hz : z ∉ zeroLattice a b) :
    gamma a b hb hba z * gamma a b hb hba ((a : ℂ) + b - z) = 1 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hf : DifferentiableOn ℂ
      (fun w => gamma a b hb hba w * gamma a b hb hba ((a : ℂ) + b - w))
      (poleLattice a b ∪ zeroLattice a b)ᶜ := by
    intro w hw
    have hw' : w ∉ poleLattice a b ∧ w ∉ zeroLattice a b := by simpa using hw
    have hr : (a : ℂ) + b - w ∉ poleLattice a b := by
      rw [← mem_zeroLattice_iff]
      exact hw'.2
    exact ((gamma_differentiableAt a b hb hba w hw'.1).mul
      ((gamma_differentiableAt a b hb hba _ hr).comp w
        ((differentiableAt_const ((a : ℂ) + b)).sub differentiableAt_id))).differentiableWithinAt
  have hmid : (((a + b) / 2 : ℝ) : ℂ) ∉ poleLattice a b ∪ zeroLattice a b := by
    simp only [Set.mem_union, not_or]
    exact ⟨not_mem_poleLattice_of_re_pos ha hb (by simp; linarith),
      not_mem_zeroLattice_of_re_lt ha hb (by simp; linarith)⟩
  apply eqOn_compl_of_eq_on_strip
    ((poleLattice_isClosed ha hb).union (zeroLattice_isClosed ha hb))
    ((poleLattice_countable a b).union (zeroLattice_countable a b))
    hf (differentiableOn_const 1) (a + b) (by linarith) hmid ?_ (by simpa using And.intro hp hz)
  intro w hw₀ hw₁
  rw [gamma_eq_on_strip a b hb hba w hw₀ hw₁,
    gamma_eq_on_strip a b hb hba ((a : ℂ) + b - w)
      (by simp; linarith) (by simp; linarith)]
  exact GammaIntegral.gamma_reflection a b w

/-- Every prescribed zero is attained by the explicit continuation. -/
lemma gamma_eq_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz : z ∈ zeroLattice a b) : gamma a b hb hba z = 0 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hbase : gamma a b hb hba ((a : ℂ) + b) = 0 := by
    rw [gamma_shift₂ a b hb hba a (not_mem_poleLattice_of_re_pos ha hb ha)]
    have hfactor : factor a a = 0 := by
      rw [factor_eq_zero_iff (ne_of_gt ha)]
      exact ⟨1, by simp⟩
    rw [hfactor, zero_mul]
  have hfirst : ∀ r : ℕ, gamma a b hb hba ((a : ℂ) + b + (r : ℂ) * a) = 0 := by
    intro r
    induction r with
    | zero => simpa using hbase
    | succ r ih =>
      have heq : (a : ℂ) + b + ((r + 1 : ℕ) : ℂ) * a = ((a : ℂ) + b + (r : ℂ) * a) + a := by
        push_cast
        ring
      rw [heq, gamma_shift₁ a b hb hba _
        (not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)), ih, mul_zero]
  obtain ⟨r, s, rfl⟩ := hz
  induction s with
  | zero => simpa using hfirst r
  | succ s ih =>
    have heq : (a : ℂ) + b + (r : ℂ) * a + ((s + 1 : ℕ) : ℂ) * b =
        ((a : ℂ) + b + (r : ℂ) * a + (s : ℂ) * b) + b := by
      push_cast
      ring
    rw [heq, gamma_shift₂ a b hb hba _
      (not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)), ih, mul_zero]

lemma gamma_ne_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hp : z ∉ poleLattice a b) (hz : z ∉ zeroLattice a b) :
    gamma a b hb hba z ≠ 0 :=
  (integralStripData a b hb hba).extension_ne_zero z hp hz

end HaagerupIzumi.GammaContinuation
