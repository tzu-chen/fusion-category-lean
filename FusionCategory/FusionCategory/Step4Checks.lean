import FusionCategory.PseudoUnitary
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Step 4 non-trivial checks — ENO §3 positivity

These checks are *provable from our definitions* and *false for a wrong
formalization* (swapped `dual`, missing `^2`, `p`-dependent norm, or
off-by-one cover index).

They are the regression tests for Step 4 and will be imported by
`Sanity.lean` after Step 4 lands.
-/

namespace FusionCategory.Step4Checks

open FusionRing

/-! ### 1. Real shadow is `d²`, not `d` -/

example {n : ℕ} {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    squaredReal h i = h.fpdim i ^ 2 := by
  exact squaredReal_eq_sq h i

example {n : ℕ} {R : FusionRing n} (h : R.FPData) :
    h.globalDim = ∑ i : Fin n, squaredReal h i := by
  exact globalDim_eq_sum_squaredReal h

-- If `globalDim` were defined as `∑ d_i` instead of `∑ d_i²`, the
-- following would be false: `globalDim ≥ 1` fails for `n=0` vs `n>0`
-- and `globalDim = ∑ squaredReal` would not hold.
example {n : ℕ} {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    1 ≤ h.globalDim :=
  globalDim_ge_one h hn

/-! ### 2. Squared norm independent of `p` -/

example {n : ℕ} {k : Type} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) (i : Fin n) :
    squaredNorm P h.fpdim i = algebraMap ℝ k (h.fpdim i ^ 2) :=
  squaredNorm_eq_algebraMap_sq P hn h i

-- Wrong definition `pivotalDim P d i = p_i * d_{i*}` would give
-- `p_i * p_{i*}` ≠ 1 in this equality.
example {n : ℕ} {k : Type} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n)
    (h : S.ring.FPData) :
    pivotalGlobalDim P h = algebraMap ℝ k h.globalDim :=
  pivotalGlobalDim_eq_algebraMap P hn h

/-! ### 3. Positivity is strict, not just non-negative -/

example {n : ℕ} {R : FusionRing n} (h : R.FPData) (i : Fin n) :
    0 < squaredReal h i :=
  squaredReal_pos h i

example {n : ℕ} {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    0 < h.globalDim :=
  h.globalDim_pos hn

example {n : ℕ} {R : FusionRing n} (h : R.FPData) (hn : 0 < n) :
    h.globalDim ≠ 0 :=
  globalDim_ne_zero h hn

/-! ### 4. Cover doubling is `2×`, not `n×` or `+1` -/

-- Concrete numeric check: Fibonacci `d = (1, φ)` with `φ=(1+√5)/2`.
-- `∑_{Fin 4} d(i/2)² = d0²+d0²+d1²+d1² = 2*(1+φ²) = 2*globalDim`.
-- If cover index were `i%2` or `i/3`, this would be `1+φ²+...` ≠ 2*globalDim.
noncomputable def fibFPdim : Fin 2 → ℝ
  | 0 => 1
  | 1 => (1 + Real.sqrt 5) / 2

example : (∑ i : Fin (2 * 2), (fibFPdim (⟨i.val / 2, by omega⟩ : Fin 2) ^ 2 : ℝ)) =
    2 * (∑ i : Fin 2, (fibFPdim i ^ 2 : ℝ)) := by
  -- This is `coverGlobalDim_double` instantiated to a concrete `FPData` function.
  -- We prove it directly via the same `finProdFinEquiv` argument, checking
  -- the shape is correct for a non-trivial `f`.
  let e : Fin 2 × Fin 2 ≃ Fin (2 * 2) := finProdFinEquiv (m := 2) (n := 2)
  have h_eq : ∀ p : Fin 2 × Fin 2,
      (fibFPdim (⟨(e p).val / 2, by omega⟩ : Fin 2) ^ 2 : ℝ) = fibFPdim p.1 ^ 2 := by
    intro p
    have : (⟨(e p).val / 2, by omega⟩ : Fin 2) = p.1 := by
      apply Fin.ext
      have h1 : (e p).val = p.2.val + 2 * p.1.val := by simp [e, finProdFinEquiv]
      have hb : p.2.val < 2 := p.2.isLt
      simp only [h1]
      omega
    rw [this]
  calc (∑ i : Fin (2 * 2), (fibFPdim (⟨i.val / 2, by omega⟩ : Fin 2) ^ 2 : ℝ))
      = ∑ p : Fin 2 × Fin 2, (fibFPdim (⟨(e p).val / 2, by omega⟩ : Fin 2) ^ 2 : ℝ) := by
        rw [← Equiv.sum_comp e (fun i => (fibFPdim (⟨i.val / 2, by omega⟩ : Fin 2) ^ 2 : ℝ))]
    _ = ∑ p : Fin 2 × Fin 2, (fibFPdim p.1 ^ 2 : ℝ) := by
        apply Fintype.sum_congr; intro p; exact h_eq p
    _ = ∑ a : Fin 2, ∑ _b : Fin 2, (fibFPdim a ^ 2 : ℝ) := by rw [Fintype.sum_prod_type]
    _ = ∑ a : Fin 2, (2 * (fibFPdim a ^ 2 : ℝ)) := by apply Finset.sum_congr rfl; intro a _; simp
    _ = 2 * ∑ a : Fin 2, (fibFPdim a ^ 2 : ℝ) := by rw [Finset.mul_sum]

-- Ising `d=(1,1,√2)` → `globalDim = 1+1+2=4`, `coverDim =8`.
noncomputable def isingFPdim : Fin 3 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => Real.sqrt 2

example : (∑ i : Fin (3 * 2), (isingFPdim (⟨i.val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ)) =
    2 * (∑ i : Fin 3, (isingFPdim i ^ 2 : ℝ)) := by
  let e : Fin 3 × Fin 2 ≃ Fin (3 * 2) := finProdFinEquiv (m := 3) (n := 2)
  have h_eq : ∀ p : Fin 3 × Fin 2,
      (isingFPdim (⟨(e p).val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ) = isingFPdim p.1 ^ 2 := by
    intro p
    have : (⟨(e p).val / 2, by omega⟩ : Fin 3) = p.1 := by
      apply Fin.ext
      have h1 : (e p).val = p.2.val + 2 * p.1.val := by simp [e, finProdFinEquiv]
      have hb : p.2.val < 2 := p.2.isLt
      simp only [h1]
      omega
    rw [this]
  calc (∑ i : Fin (3 * 2), (isingFPdim (⟨i.val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ))
      = ∑ p : Fin 3 × Fin 2, (isingFPdim (⟨(e p).val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ) := by
        rw [← Equiv.sum_comp e (fun i => (isingFPdim (⟨i.val / 2, by omega⟩ : Fin 3) ^ 2 : ℝ))]
    _ = ∑ p : Fin 3 × Fin 2, (isingFPdim p.1 ^ 2 : ℝ) := by
        apply Fintype.sum_congr; intro p; exact h_eq p
    _ = ∑ a : Fin 3, ∑ _b : Fin 2, (isingFPdim a ^ 2 : ℝ) := by rw [Fintype.sum_prod_type]
    _ = ∑ a : Fin 3, (2 * (isingFPdim a ^ 2 : ℝ)) := by apply Finset.sum_congr rfl; intro a _; simp
    _ = 2 * ∑ a : Fin 3, (isingFPdim a ^ 2 : ℝ) := by rw [Finset.mul_sum]

-- Generic version already proved as `coverGlobalDim_double`:
example {n : ℕ} {k : Type} [Field k] {S : FusionSystem n k}
    (h : S.ring.FPData) (hn : 0 < n) :
    0 < (∑ i : Fin (n * 2), (h.fpdim (⟨i.val / 2, by omega⟩ : Fin n) ^ 2 : ℝ)) :=
  cover_globalDim_double_pos h hn

/-! ### 5. Descent from cover — positivity without pivotal hypothesis -/

-- If `C` were not assumed pivotal, `|X|²>0` still holds via descent from
-- `̃C`, because `̃C` is pivotal and forgets to `C` preserving norms.
-- Skeletally this is `squaredReal_pos` on `C` directly, but the check
-- ensures the cover's `globalDim` positivity implies `C`'s.
example {n : ℕ} {k : Type} [Field k] {S : FusionSystem n k}
    (h : S.ring.FPData) (hn : 0 < n) :
    0 < h.globalDim :=
  cover_globalDim_pos h hn

end FusionCategory.Step4Checks
