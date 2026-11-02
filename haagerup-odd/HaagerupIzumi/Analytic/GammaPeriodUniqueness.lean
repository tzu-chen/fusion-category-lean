module

public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Data.Complex.Basic

/-!
# Uniqueness from two incommensurable periods

The Fourier-integral evaluation uses two shift equations. After dividing by
the explicit candidate, their ratio is periodic with two incommensurable
periods. Density and continuity remove the periodic variable; holomorphy
then forces constancy in the other direction too.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace HaagerupIzumi.GammaPeriodUniqueness

lemma continuous_eq_const_of_two_periods {f : ℝ → ℂ} {a b : ℝ}
    (hf : Continuous f) (ha : Function.Periodic f a) (hb : Function.Periodic f b)
    (hirr : Irrational (a / b)) : f = fun _ => f 0 := by
  let P : AddSubgroup ℝ :=
    { carrier := {t | Function.Periodic f t}
      zero_mem' := by intro x; simp
      add_mem' := fun h₁ h₂ => h₁.add_period h₂
      neg_mem' := fun h => h.neg }
  have hP : AddSubgroup.closure {a, b} ≤ P := by
    rw [AddSubgroup.closure_le, pair_subset_iff]
    exact ⟨ha, hb⟩
  apply Continuous.ext_on (dense_addSubgroupClosure_pair_iff.mpr hirr) hf continuous_const
  intro t ht
  have hp : Function.Periodic f t := hP ht
  simpa using hp 0

lemma vertical_eq_of_two_periods {f : ℂ → ℂ} {a b : ℝ}
    (hf : Continuous f) (ha : Function.Periodic f ((a : ℂ) * I))
    (hb : Function.Periodic f ((b : ℂ) * I)) (hirr : Irrational (a / b))
    (z : ℂ) (t : ℝ) : f (z + (t : ℂ) * I) = f z := by
  let g : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hp (c : ℝ) (hc : Function.Periodic f ((c : ℂ) * I)) : Function.Periodic g c := by
    intro x
    unfold g
    rw [Complex.ofReal_add, add_mul, ← add_assoc]
    exact hc (z + (x : ℂ) * I)
  have hconst := continuous_eq_const_of_two_periods hg (hp a ha) (hp b hb) hirr
  have hh := congrFun hconst t
  simpa [g] using hh

/-- An entire function with two incommensurable imaginary periods is constant. -/
theorem differentiable_eq_const_of_two_periods {f : ℂ → ℂ} {a b : ℝ}
    (hf : Differentiable ℂ f) (ha : Function.Periodic f ((a : ℂ) * I))
    (hb : Function.Periodic f ((b : ℂ) * I)) (hirr : Irrational (a / b)) :
    ∀ z : ℂ, f z = f 0 := by
  suffices hzero : ∀ z : ℂ, deriv f z = 0 from
    fun z => is_const_of_deriv_eq_zero hf hzero z 0
  intro z
  have hg : HasDerivAt (fun w : ℂ => z + w * I) I 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).mul_const I).const_add z using 1
    simp
  have hz : HasDerivAt f (deriv f z) (z + (0 : ℂ) * I) := by
    simpa using (hf z).hasDerivAt
  have hd := (hz.comp (0 : ℂ) hg).comp_ofReal
  have hfun : (fun t : ℝ => f (z + (t : ℂ) * I)) = fun _ => f z := by
    funext t
    exact vertical_eq_of_two_periods hf.continuous ha hb hirr z t
  change HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * I)) (deriv f z * I) 0 at hd
  rw [hfun] at hd
  have hzero := hd.unique (hasDerivAt_const (0 : ℝ) (f z))
  exact (mul_eq_zero.mp hzero).resolve_right I_ne_zero

end HaagerupIzumi.GammaPeriodUniqueness
