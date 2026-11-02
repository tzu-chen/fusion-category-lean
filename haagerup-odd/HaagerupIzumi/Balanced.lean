module

public import HaagerupIzumi.Factorization
public import HaagerupIzumi.Boundary

@[expose] public section

/-!
# The quantity `δ^2 S - τ P` for balanced pairs with a zero cross sum

Steps A3 and A4 of Lemma 5.4 in the expanded proof, in the normalized
position `a 0 + c 0 = 0`:

* `SP_fullmatch`: if `c j = -a j` for all `j` and the `a j` are distinct,
  then `δ^2 S - τ P = τ^3 δ^3`;
* `SP_collision`: if `a 0 + c 0 = 0`, the pair is balanced, and
  `a 1 + c 1 ≠ 0`, `a 2 + c 1 ≠ 0`, then `δ^2 S - τ P = 0` (using `Q = 0`).
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n] [CharZero K]

/-- A full match with distinct rows. -/
theorem SP_fullmatch (a : Fin 3 → ZMod n) (h01 : a 0 ≠ a 1) (h02 : a 0 ≠ a 2)
    (h12 : a 1 ≠ a 2) :
    D.δ ^ 2 * D.S a (fun j => -a j) - D.τ * D.P a (fun j => -a j) = D.τ ^ 3 * D.δ ^ 3 := by
  have hτ := D.τ_ne_zero
  have hδ := D.δ_ne_zero
  -- the sum
  have hS : D.S a (fun j => -a j)
      = (-D.τ) ^ 3 * ∑ m : ZMod n, ((if m = -a 0 then (1 : K) else 0) - D.δ / D.τ)
          * ((if m = -a 1 then 1 else 0) - D.δ / D.τ) * ((if m = -a 2 then 1 else 0) - D.δ / D.τ) := by
    rw [S_def, mul_sum]
    apply sum_congr rfl; intro m _
    have hq : ∀ x : ZMod n, D.W (m + x) * D.W (-x - m) = D.δ - D.τ * (if m = -x then 1 else 0) := by
      intro x
      rw [show -x - m = -(m + x) by ring, rec_all]
      have : (m + x = 0) ↔ (m = -x) := add_eq_zero_iff_eq_neg
      simp only [this]
      split_ifs <;> ring
    have hf : ∀ y : K, D.δ - D.τ * y = -D.τ * (y - D.δ / D.τ) := by
      intro y; field_simp; ring
    calc D.W (m + a 0) * D.W (m + a 1) * D.W (m + a 2)
          * (D.W (-a 0 - m) * D.W (-a 1 - m) * D.W (-a 2 - m))
        = (D.W (m + a 0) * D.W (-a 0 - m)) * (D.W (m + a 1) * D.W (-a 1 - m))
          * (D.W (m + a 2) * D.W (-a 2 - m)) := by ring
      _ = _ := by rw [hq, hq, hq, hf, hf, hf]; ring
  rw [hS, sum_three_ind]
  have i01 : ¬ (-a 0 = -a 1) := fun e => h01 (neg_inj.mp e)
  have i02 : ¬ (-a 0 = -a 2) := fun e => h02 (neg_inj.mp e)
  have i12 : ¬ (-a 1 = -a 2) := fun e => h12 (neg_inj.mp e)
  rw [if_neg i01, if_neg i02, if_neg i12]
  -- the product
  have hP : D.P a (fun j => -a j) = -D.δ ^ 3 := by
    rw [P_def]
    simp only [add_neg_cancel, D.hW0]
    have r1 := D.hrec (a 0 - a 1) (sub_ne_zero.mpr h01)
    have r2 := D.hrec (a 0 - a 2) (sub_ne_zero.mpr h02)
    have r3 := D.hrec (a 1 - a 2) (sub_ne_zero.mpr h12)
    rw [show a 0 + -a 1 = a 0 - a 1 by ring, show a 0 + -a 2 = a 0 - a 2 by ring,
      show a 1 + -a 0 = -(a 0 - a 1) by ring, show a 1 + -a 2 = a 1 - a 2 by ring,
      show a 2 + -a 0 = -(a 0 - a 2) by ring, show a 2 + -a 1 = -(a 1 - a 2) by ring]
    linear_combination (-(D.W (a 0 - a 2) * D.W (-(a 0 - a 2)))
        * (D.W (a 1 - a 2) * D.W (-(a 1 - a 2)))) * r1
      - (D.δ * (D.W (a 1 - a 2) * D.W (-(a 1 - a 2)))) * r2 - (D.δ ^ 2) * r3
  have hδτ : D.δ = D.τ + 1 := by rw [τ_def]; ring
  have hτ1 : D.τ + 1 ≠ 0 := by rw [← hδτ]; exact hδ
  rw [hP, D.n_eq, hδτ]
  simp only [mul_zero, add_zero, zero_add, sub_zero]
  field_simp
  ring

/-- A zero cross sum without a full match, in the normalized position. -/
theorem SP_collision (hQ : ∀ g h, D.Q g h = 0) (a c : Fin 3 → ZMod n)
    (hbal : a 0 + a 1 + a 2 + c 0 + c 1 + c 2 = 0) (h00 : a 0 + c 0 = 0)
    (hH : a 1 + c 1 ≠ 0) (hV : a 2 + c 1 ≠ 0) :
    D.δ ^ 2 * D.S a c - D.τ * D.P a c = 0 := by
  have hδ := D.δ_ne_zero
  set H := a 1 + c 1 with hHdef
  set V := a 2 + c 1 with hVdef
  have hc0 : c 0 = -a 0 := by linear_combination h00
  have hc2 : c 2 = -a 1 - a 2 - c 1 := by linear_combination hbal - h00
  -- the four-factor sum vanishes
  have hΦ : ∑ m : ZMod n, D.W (m + a 1) * D.W (m + a 2) * D.W (c 1 - m) * D.W (c 2 - m) = 0 := by
    have step1 : ∑ m : ZMod n, D.W (m + a 1) * D.W (m + a 2) * D.W (c 1 - m) * D.W (c 2 - m)
        = ∑ x : ZMod n, D.W (x - V) * D.W (x - H) * D.W (H - (x - V)) * D.W (-x) := by
      refine Fintype.sum_equiv (Equiv.subRight (c 2)) _ _ (fun m => ?_)
      simp only [Equiv.subRight_apply]
      have i1 : m - c 2 - V = m + a 1 := by rw [hVdef, hc2]; ring
      have i2 : m - c 2 - H = m + a 2 := by rw [hHdef, hc2]; ring
      have i3 : H - (m - c 2 - V) = c 1 - m := by rw [hHdef, hVdef, hc2]; ring
      have i4 : -(m - c 2) = c 2 - m := by ring
      rw [i3, i4, i1, i2]
    have step2 : ∀ x : ZMod n, D.W (x - V) * D.W (x - H) * D.W (H - (x - V)) * D.W (-x)
        = D.δ * (D.B (x + -V) H * D.B H x) := by
      intro x
      rw [B_uniform, B_uniform, if_neg (fun e => hH e.2), if_neg (fun e => hH e.1)]
      have := D.hrec H hH
      rw [show x + -V = x - V by ring]
      field_simp
      linear_combination (-(D.W (x - V) * D.W (x - H) * D.W (H - (x - V)) * D.W (-x))) * this
    rw [step1]
    simp only [step2]
    rw [← mul_sum, sum_B_quadratic, hQ, if_neg hH, if_neg (neg_ne_zero.mpr hV)]
    ring
  -- the six-factor sum
  have hS : D.S a c = -D.τ * (D.W (-a 0 + a 1) * D.W (-a 0 + a 2)
      * D.W (c 1 - -a 0) * D.W (c 2 - -a 0)) := by
    rw [S_def]
    have hq : ∀ m : ZMod n, D.W (m + a 0) * D.W (c 0 - m)
        = D.δ - D.τ * (if m = -a 0 then 1 else 0) := by
      intro m
      rw [hc0, show -a 0 - m = -(m + a 0) by ring, rec_all]
      have : (m + a 0 = 0) ↔ (m = -a 0) := add_eq_zero_iff_eq_neg
      simp only [this]
      split_ifs <;> ring
    have : ∀ m : ZMod n, D.W (m + a 0) * D.W (m + a 1) * D.W (m + a 2)
        * (D.W (c 0 - m) * D.W (c 1 - m) * D.W (c 2 - m))
        = D.δ * (D.W (m + a 1) * D.W (m + a 2) * D.W (c 1 - m) * D.W (c 2 - m))
          - D.τ * (if m = -a 0 then D.W (m + a 1) * D.W (m + a 2) * D.W (c 1 - m) * D.W (c 2 - m)
            else 0) := by
      intro m
      have e := hq m
      rw [show D.W (m + a 0) * D.W (m + a 1) * D.W (m + a 2)
          * (D.W (c 0 - m) * D.W (c 1 - m) * D.W (c 2 - m))
          = (D.W (m + a 0) * D.W (c 0 - m))
            * (D.W (m + a 1) * D.W (m + a 2) * D.W (c 1 - m) * D.W (c 2 - m)) by ring, e]
      split_ifs <;> ring
    simp only [this, sum_sub_distrib, ← mul_sum, hΦ, mul_zero, zero_sub, sum_ite_eq', mem_univ,
      if_true]
    rw [neg_mul]
  -- the nine-factor product
  have hP : D.P a c = -D.δ ^ 2 * (D.W (-a 0 + a 1) * D.W (-a 0 + a 2)
      * D.W (c 1 - -a 0) * D.W (c 2 - -a 0)) := by
    rw [P_def, h00, D.hW0]
    have e1 : a 2 + c 2 = -H := by rw [hHdef]; linear_combination hbal - h00
    have e2 : a 1 + c 2 = -V := by rw [hVdef]; linear_combination hbal - h00
    rw [e1, e2, show a 1 + c 0 = -a 0 + a 1 by rw [hc0]; ring,
      show a 2 + c 0 = -a 0 + a 2 by rw [hc0]; ring,
      show a 0 + c 1 = c 1 - -a 0 by ring, show a 0 + c 2 = c 2 - -a 0 by ring]
    have r1 := D.hrec H hH
    have r2 := D.hrec V hV
    linear_combination (-(D.W (c 1 - -a 0) * D.W (c 2 - -a 0) * D.W (-a 0 + a 1)
      * D.W (-a 0 + a 2)) * (D.W V * D.W (-V))) * r1
      - (D.δ * (D.W (c 1 - -a 0) * D.W (c 2 - -a 0) * D.W (-a 0 + a 1) * D.W (-a 0 + a 2))) * r2
  rw [hS, hP]; ring

end CoeffData
end HaagerupIzumi
