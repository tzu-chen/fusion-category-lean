module

public import HaagerupIzumi.Analytic.GammaIdentities
public import HaagerupIzumi.Analytic.ConvexMinusCountable
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import all Mathlib.Data.Complex.Basic

/-!
# A one-complex-parameter domain for the Euler transformation

Scaling the four parameters preserves convergence on an open convex set.
The two no-pinch conditions remove only a closed countable set of scaling
parameters, so the remaining domain is connected.
-/

@[expose] public section
noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaContinuation

def eulerScaleDomain (a b : ℝ) (r y : ℂ) : Set ℂ :=
  {t | |(t * r).re| + |(t * y).re| < (a + b) / 2}

lemma eulerScaleDomain_isOpen (a b : ℝ) (r y : ℂ) : IsOpen (eulerScaleDomain a b r y) :=
  isOpen_lt (by fun_prop) continuous_const

lemma eulerScaleDomain_convex (a b : ℝ) (r y : ℂ) : Convex ℝ (eulerScaleDomain a b r y) := by
  intro t ht u hu α β hα hβ hαβ
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simpa only [hα0, hβ1, zero_smul, one_smul, zero_add] using hu
  have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hlin (c : ℂ) : ((α • t + β • u) * c).re = α * (t * c).re + β * (u * c).re := by
    simp only [add_mul, smul_mul_assoc, add_re, smul_re, smul_eq_mul]
  change |((α • t + β • u) * r).re| + |((α • t + β • u) * y).re| < (a + b) / 2
  rw [hlin r, hlin y]
  have hr := abs_add_le (α * (t * r).re) (β * (u * r).re)
  have hy := abs_add_le (α * (t * y).re) (β * (u * y).re)
  simp only [abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ] at hr hy
  calc
    _ ≤ α * (|(t * r).re| + |(t * y).re|) + β * (|(u * r).re| + |(u * y).re|) := by linarith
    _ < α * ((a + b) / 2) + β * ((a + b) / 2) :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left ht hαpos) (mul_le_mul_of_nonneg_left hu.le hβ)
    _ = _ := by rw [← add_mul, hαβ, one_mul]

lemma zero_mem_eulerScaleDomain {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r y : ℂ) :
    0 ∈ eulerScaleDomain a b r y := by
  simp only [eulerScaleDomain, mem_ofPred_eq, zero_mul, zero_re, abs_zero, zero_add]
  positivity

lemma mem_eulerScaleDomain_iff (a b : ℝ) (r y t : ℂ) :
    t ∈ eulerScaleDomain a b r y ↔ K4Conv a b (t * r) (t * y) ∧ K4Conv a b (-(t * r)) (t * y) := by
  simp only [eulerScaleDomain, mem_ofPred_eq, K4Conv, neg_re]
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (t * r).re, neg_le_abs (t * r).re]
  · rintro ⟨h₁, h₂⟩
    rcases le_total 0 (t * r).re with hr | hr
    · rw [abs_of_nonneg hr]
      linarith
    · rw [abs_of_nonpos hr]
      linarith

lemma one_mem_eulerScaleDomain_iff (a b : ℝ) (r y : ℂ) :
    1 ∈ eulerScaleDomain a b r y ↔ K4Conv a b r y ∧ K4Conv a b (-r) y := by
  simpa only [one_mul] using mem_eulerScaleDomain_iff a b r y 1

def scalePoleSet (a b : ℝ) (c : ℂ) : Set ℂ :=
  {t | ((a + b : ℝ) : ℂ) / 2 + t * c ∈ poleLattice a b}

def eulerScaleForbidden (a b : ℝ) (r s x : ℂ) : Set ℂ :=
  scalePoleSet a b (r + s) ∪ scalePoleSet a b (r - s) ∪
  scalePoleSet a b (r + x) ∪ scalePoleSet a b (r - x) ∪
  scalePoleSet a b (-r + s) ∪ scalePoleSet a b (-r - s) ∪
  scalePoleSet a b (-r + x) ∪ scalePoleSet a b (-r - x)

lemma scalePoleSet_isClosed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
    IsClosed (scalePoleSet a b c) :=
  (poleLattice_isClosed ha hb).preimage (by fun_prop)

lemma zero_not_mem_scalePoleSet {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
    0 ∉ scalePoleSet a b c := by
  change ((a + b : ℝ) : ℂ) / 2 + 0 * c ∉ poleLattice a b
  apply not_mem_poleLattice_of_re_pos ha hb
  simp only [zero_mul, add_zero, div_ofNat_re, ofReal_re]
  positivity

lemma scalePoleSet_countable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
    (scalePoleSet a b c).Countable := by
  by_cases hc : c = 0
  · have heq : scalePoleSet a b c = ∅ := by
      ext t
      simp only [scalePoleSet, mem_ofPred_eq, hc, mul_zero, add_zero, mem_empty_iff_false,
        iff_false]
      exact not_mem_poleLattice_of_re_pos ha hb (by simp; positivity)
    rw [heq]
    exact countable_empty
  · apply (poleLattice_countable a b).preimage
    intro t u heq
    exact mul_right_cancel₀ hc (add_left_cancel heq)

lemma eulerScaleForbidden_isClosed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x : ℂ) :
    IsClosed (eulerScaleForbidden a b r s x) := by
  unfold eulerScaleForbidden
  repeat' first | apply IsClosed.union | exact scalePoleSet_isClosed ha hb _

lemma eulerScaleForbidden_countable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x : ℂ) :
    (eulerScaleForbidden a b r s x).Countable := by
  unfold eulerScaleForbidden
  repeat' first | apply Set.Countable.union | exact scalePoleSet_countable ha hb _

lemma zero_not_mem_eulerScaleForbidden {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x : ℂ) :
    0 ∉ eulerScaleForbidden a b r s x := by
  simp only [eulerScaleForbidden, mem_union, not_or]
  repeat' constructor
  all_goals exact zero_not_mem_scalePoleSet ha hb _

lemma k4NoPinch_scale_iff (a b : ℝ) (r s x t : ℂ) :
    K4NoPinch a b (t * r) (t * s) (t * x) ↔
      t ∉ scalePoleSet a b (r + s) ∧ t ∉ scalePoleSet a b (r - s) ∧
      t ∉ scalePoleSet a b (r - x) ∧ t ∉ scalePoleSet a b (r + x) := by
  have h₁ : 2 * k4U a b (t * r) (t * s) = ((a + b : ℝ) : ℂ) / 2 + t * (r + s) := by
    unfold k4U
    ring
  have h₂ : 2 * k4V a b (t * r) (t * s) = ((a + b : ℝ) : ℂ) / 2 + t * (r - s) := by
    unfold k4V
    ring
  have h₃ : k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) - t * x =
      ((a + b : ℝ) : ℂ) / 2 + t * (r - x) := by unfold k4U k4V; ring
  have h₄ : k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) + t * x =
      ((a + b : ℝ) : ℂ) / 2 + t * (r + x) := by unfold k4U k4V; ring
  simp only [K4NoPinch, h₁, h₂, h₃, h₄, scalePoleSet, mem_ofPred_eq]
  rfl

lemma not_mem_eulerScaleForbidden_iff (a b : ℝ) (r s x t : ℂ) :
    t ∉ eulerScaleForbidden a b r s x ↔
      K4NoPinch a b (t * r) (t * s) (t * x) ∧
      K4NoPinch a b (-(t * r)) (t * s) (t * x) := by
  rw [show -(t * r) = t * (-r) by ring, k4NoPinch_scale_iff, k4NoPinch_scale_iff]
  simp only [eulerScaleForbidden, mem_union]
  tauto

lemma one_not_mem_eulerScaleForbidden_iff (a b : ℝ) (r s x : ℂ) :
    1 ∉ eulerScaleForbidden a b r s x ↔ K4NoPinch a b r s x ∧ K4NoPinch a b (-r) s x := by
  simpa only [one_mul] using not_mem_eulerScaleForbidden_iff a b r s x 1

theorem eulerScaleRegular_isConnected {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x y : ℂ) :
    IsConnected (eulerScaleDomain a b r y \ eulerScaleForbidden a b r s x) := by
  apply isConnected_diff_countable_of_convex (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two)
    (eulerScaleDomain_convex a b r y) (eulerScaleDomain_isOpen a b r y)
    ⟨0, zero_mem_eulerScaleDomain ha hb r y⟩ (eulerScaleForbidden_countable ha hb r s x)

lemma eulerScaleRegular_isOpen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x y : ℂ) :
    IsOpen (eulerScaleDomain a b r y \ eulerScaleForbidden a b r s x) :=
  (eulerScaleDomain_isOpen a b r y).sdiff (eulerScaleForbidden_isClosed ha hb r s x)

lemma analyticAt_gamma_off_poles {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    {z : ℂ} (hz : z ∉ poleLattice a b) : AnalyticAt ℂ (gamma a b hb hba) z := by
  have hd : DifferentiableOn ℂ (gamma a b hb hba) (poleLattice a b)ᶜ :=
    fun w hw => (gamma_differentiableAt a b hb hba w hw).differentiableWithinAt
  exact hd.analyticOnNhd (poleLattice_isClosed (hb.trans_le hba) hb).isOpen_compl z hz

lemma analyticAt_scaleGamma_of_not_mem {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (r v : ℂ) {t : ℂ} (hp : t ∉ scalePoleSet a b (r + v))
    (hm : t ∉ scalePoleSet a b (r - v)) :
    AnalyticAt ℂ (fun u => Γr (gamma a b hb hba) a b (u * r) (u * v)) t := by
  have h₁ := (analyticAt_gamma_off_poles hb hba hp).comp
    (f := fun u : ℂ => ((a + b : ℝ) : ℂ) / 2 + u * (r + v)) (x := t)
    (show AnalyticAt ℂ (fun u : ℂ => ((a + b : ℝ) : ℂ) / 2 + u * (r + v)) t by fun_prop)
  have h₂ := (analyticAt_gamma_off_poles hb hba hm).comp
    (f := fun u : ℂ => ((a + b : ℝ) : ℂ) / 2 + u * (r - v)) (x := t)
    (show AnalyticAt ℂ (fun u : ℂ => ((a + b : ℝ) : ℂ) / 2 + u * (r - v)) t by fun_prop)
  have heq : (fun u => Γr (gamma a b hb hba) a b (u * r) (u * v)) =
      (fun u => gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + u * (r + v)) *
        gamma a b hb hba (((a + b : ℝ) : ℂ) / 2 + u * (r - v))) := by
    funext u
    unfold Γr
    congr 1 <;> congr 1 <;> ring
  rw [heq]
  exact h₁.mul h₂

lemma analyticAt_eulerScaleGamma_s {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) {t : ℂ} (ht : t ∉ eulerScaleForbidden a b r s x) :
    AnalyticAt ℂ (fun u => Γr (gamma a b hb hba) a b (u * r) (u * s)) t := by
  have h := (k4NoPinch_scale_iff a b r s x t).mp
    ((not_mem_eulerScaleForbidden_iff a b r s x t).mp ht).1
  exact analyticAt_scaleGamma_of_not_mem hb hba r s h.1 h.2.1

lemma analyticAt_eulerScaleGamma_x {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) {t : ℂ} (ht : t ∉ eulerScaleForbidden a b r s x) :
    AnalyticAt ℂ (fun u => Γr (gamma a b hb hba) a b (u * r) (u * x)) t := by
  have h := (k4NoPinch_scale_iff a b r s x t).mp
    ((not_mem_eulerScaleForbidden_iff a b r s x t).mp ht).1
  exact analyticAt_scaleGamma_of_not_mem hb hba r x h.2.2.2 h.2.2.1

lemma analyticAt_eulerScaleGamma_y {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (r y : ℂ) {t : ℂ} (ht : t ∈ eulerScaleDomain a b r y) :
    AnalyticAt ℂ (fun u => Γr (gamma a b hb hba) a b (u * r) (u * y)) t := by
  apply analyticAt_scaleGamma_of_not_mem hb hba r y
  all_goals
    apply not_mem_poleLattice_of_re_pos (hb.trans_le hba) hb
    simp only [mul_add, mul_sub, add_re, sub_re, div_ofNat_re, ofReal_re]
    change |(t * r).re| + |(t * y).re| < (a + b) / 2 at ht
    linarith [neg_le_abs (t * r).re, neg_le_abs (t * y).re, le_abs_self (t * y).re]

end HaagerupIzumi.GammaContinuation
