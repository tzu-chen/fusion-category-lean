module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Cyclic Haagerup–Izumi coefficient data

This file formalizes Section 3 of the expanded proof
(`hi_infinitude_expanded.tex`) in an abstract form: the only facts about the
coefficients `W a` that the algebraic parts of the proof use are

* `W 0 = -1`,
* `W a * W (-a) = δ` for `a ≠ 0` (the reciprocal products),
* every `W a` is nonzero,
* `δ ^ 2 = n * δ + 1`.

We package these as a structure `CoeffData`, define the matrices `B` and
`A = B / τ` with `τ = δ - 1`, and prove the uniform formula, the order-three
and transpose-like symmetries, the axis values, and the linear
Evans–Gannon identities.
-/

open Finset

namespace HaagerupIzumi

/-- Abstract coefficient data for the cyclic Haagerup–Izumi construction on
`ZMod n` over a field `K`. -/
structure CoeffData (n : ℕ) (K : Type*) [Field K] where
  /-- the noninvertible categorical dimension -/
  δ : K
  /-- the coefficients -/
  W : ZMod n → K
  hδ : δ ^ 2 = n * δ + 1
  hW0 : W 0 = -1
  hWne : ∀ a, W a ≠ 0
  hrec : ∀ a, a ≠ 0 → W a * W (-a) = δ

namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K)

/-- The normalization `τ = δ - 1`. -/
def τ : K := D.δ - 1

lemma τ_def : D.τ = D.δ - 1 := rfl

lemma δ_ne_zero : D.δ ≠ 0 := by
  intro h
  have := D.hδ
  rw [h] at this
  norm_num at this

lemma τ_ne_zero [CharZero K] [NeZero n] : D.τ ≠ 0 := by
  intro h
  have h1 : D.δ = 1 := by rw [τ_def] at h; linear_combination h
  have h2 := D.hδ
  rw [h1] at h2
  have h3 : (n : K) = 0 := by linear_combination -h2
  exact NeZero.ne n (Nat.cast_eq_zero.mp h3)

/-- `n = δ - δ⁻¹`. -/
lemma n_eq : (n : K) = D.δ - D.δ⁻¹ := by
  have := D.hδ
  field_simp [D.δ_ne_zero]
  linear_combination -this

/-- The reciprocal product with the exceptional value at `0`. -/
lemma rec_all (a : ZMod n) : D.W a * D.W (-a) = D.δ - if a = 0 then D.τ else 0 := by
  by_cases h : a = 0
  · subst h; simp [D.hW0, τ_def]
  · simp [h, D.hrec a h]

/-- The coefficient matrix `B`. -/
def B (a b : ZMod n) : K :=
  if b = 0 then -1 + (if a = 0 then D.τ else 0) else D.W a * D.W (b - a) / D.W b

/-- The reconstruction matrix `A = B / τ`. -/
def A (a b : ZMod n) : K := D.B a b / D.τ

lemma A_def (a b : ZMod n) : D.A a b = D.B a b / D.τ := rfl

lemma B_eq_τ_mul_A [CharZero K] [NeZero n] (a b : ZMod n) : D.B a b = D.τ * D.A a b := by
  rw [A_def]; field_simp [D.τ_ne_zero]

/-- The uniform formula (3.13) for `B`. -/
theorem B_uniform (a b : ZMod n) :
    D.B a b = D.δ⁻¹ * D.W a * D.W (b - a) * D.W (-b)
      + D.τ ^ 2 * D.δ⁻¹ * (if a = 0 ∧ b = 0 then 1 else 0) := by
  unfold B
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl, if_pos rfl, if_pos ⟨rfl, rfl⟩, sub_zero, neg_zero, D.hW0]
      field_simp [D.δ_ne_zero]
      rw [τ_def]; ring
    · have hcond : ¬ (a = 0 ∧ (0 : ZMod n) = 0) := fun h => ha h.1
      rw [if_pos rfl, if_neg ha, add_zero, if_neg hcond, mul_zero, add_zero, zero_sub, neg_zero,
        D.hW0, mul_assoc D.δ⁻¹, D.hrec a ha, inv_mul_cancel₀ D.δ_ne_zero, one_mul]
  · have hcond : ¬ (a = 0 ∧ b = 0) := fun h => hb h.2
    rw [if_neg hb, if_neg hcond, mul_zero, add_zero, div_eq_iff (D.hWne b)]
    have : D.δ⁻¹ * D.W a * D.W (b - a) * D.W (-b) * D.W b
        = D.W a * D.W (b - a) * (D.δ⁻¹ * (D.W b * D.W (-b))) := by ring
    rw [this, D.hrec b hb, inv_mul_cancel₀ D.δ_ne_zero, mul_one]

/-- Order-three symmetry, first form: `B a b = B (b - a) (-a)`. -/
theorem B_rot (a b : ZMod n) : D.B a b = D.B (b - a) (-a) := by
  rw [B_uniform, B_uniform]
  have h1 : -a - (b - a) = -b := by ring
  rw [h1, neg_neg]
  by_cases ha : a = 0
  · subst ha
    simp only [sub_zero, neg_zero, true_and, and_true]
    ring
  · have hne : ¬ (b - a = 0 ∧ -a = 0) := fun h => ha (neg_eq_zero.mp h.2)
    have hne' : ¬ (a = 0 ∧ b = 0) := fun h => ha h.1
    rw [if_neg hne, if_neg hne']
    ring

/-- Order-three symmetry, second form: `B a b = B (-b) (a - b)`. -/
theorem B_rot' (a b : ZMod n) : D.B a b = D.B (-b) (a - b) := by
  have := D.B_rot (-b) (a - b)
  rw [this]
  congr 1 <;> ring

/-- Transpose-like symmetry: `B (-g) l = B (-l) g`. -/
theorem B_transpose (g l : ZMod n) : D.B (-g) l = D.B (-l) g := by
  rw [B_uniform, B_uniform]
  have h1 : l - -g = g - -l := by ring
  have h2 : (-g = 0 ∧ l = 0) ↔ (-l = 0 ∧ g = 0) := by
    simp only [neg_eq_zero]; exact and_comm
  rw [h1]
  simp only [h2]
  ring

/-! ### Axis values -/

lemma B_zero_zero : D.B 0 0 = D.δ - 2 := by
  simp [B, τ_def]; ring

lemma B_zero_left {b : ZMod n} (hb : b ≠ 0) : D.B 0 b = -1 := by
  simp [B, hb, D.hW0, D.hWne b]

lemma B_zero_right {a : ZMod n} (ha : a ≠ 0) : D.B a 0 = -1 := by
  simp [B, ha]

lemma B_diag {a : ZMod n} (ha : a ≠ 0) : D.B a a = -1 := by
  simp [B, ha, D.hW0, D.hWne a]

lemma B_axis_left (b : ZMod n) : D.B 0 b = -1 + if b = 0 then D.τ else 0 := by
  by_cases hb : b = 0
  · subst hb; rw [B_zero_zero]; simp [τ_def]; ring
  · simp [D.B_zero_left hb, hb]

lemma B_axis_right (a : ZMod n) : D.B a 0 = -1 + if a = 0 then D.τ else 0 := by
  simp [B]

/-! ### Linear identities -/

theorem A_rot (a b : ZMod n) : D.A a b = D.A (b - a) (-a) := by
  rw [A_def, A_def, ← B_rot]

theorem A_rot' (a b : ZMod n) : D.A a b = D.A (-b) (a - b) := by
  rw [A_def, A_def, ← B_rot']

section linear
variable [CharZero K] [NeZero n]

theorem A_axis_right (a : ZMod n) : D.A a 0 = (if a = 0 then 1 else 0) - D.τ⁻¹ := by
  rw [A_def, B_axis_right]
  have := D.τ_ne_zero
  split_ifs <;> field_simp <;> ring

theorem A_axis_left (a : ZMod n) : D.A 0 a = (if a = 0 then 1 else 0) - D.τ⁻¹ := by
  rw [A_def, B_axis_left]
  have := D.τ_ne_zero
  split_ifs <;> field_simp <;> ring

/-- The sum identity `∑ a, A a 0 = -δ⁻¹`. -/
theorem sum_A_axis : ∑ a : ZMod n, D.A a 0 = -D.δ⁻¹ := by
  simp only [A_axis_right, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, sum_const,
    card_univ, ZMod.card, nsmul_eq_mul]
  have hτ := D.τ_ne_zero
  have hδ := D.δ_ne_zero
  have := D.hδ
  rw [τ_def] at hτ ⊢
  field_simp
  linear_combination this

end linear

/-! ### Columns -/

/-- The column `u p = B (·, p)`. -/
def u (p a : ZMod n) : K := D.B a p

lemma u_def (p a : ZMod n) : D.u p a = D.B a p := rfl

lemma u_ne_zero {p : ZMod n} (hp : p ≠ 0) (a : ZMod n) : D.u p a ≠ 0 := by
  simp only [u, B, hp, if_false]
  exact div_ne_zero (mul_ne_zero (D.hWne _) (D.hWne _)) (D.hWne _)

lemma u_eq {p : ZMod n} (hp : p ≠ 0) (a : ZMod n) :
    D.u p a = D.W a * D.W (p - a) / D.W p := by
  simp [u, B, hp]

/-- Column symmetry `u p a = u p (p - a)`. -/
theorem u_symm {p : ZMod n} (hp : p ≠ 0) (a : ZMod n) : D.u p a = D.u p (p - a) := by
  rw [u_eq D hp, u_eq D hp, sub_sub_cancel, mul_comm]

/-- Rows as shifted columns: `B p a = u (-p) (a - p)` for `p ≠ 0`. -/
theorem B_eq_u_sub (p a : ZMod n) : D.B p a = D.u (-p) (a - p) := by
  rw [u_def, B_rot]

/-- Rows as reflected columns: `B p a = u (-p) (-a)` for `p ≠ 0`. -/
theorem B_eq_u_neg {p : ZMod n} (hp : p ≠ 0) (a : ZMod n) : D.B p a = D.u (-p) (-a) := by
  rw [B_eq_u_sub, u_symm D (neg_ne_zero.mpr hp)]
  congr 1; ring

end CoeffData

end HaagerupIzumi
