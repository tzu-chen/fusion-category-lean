module

public import HaagerupIzumi.Residuals

@[expose] public section

/-!
# The boundary cubics

Part B of Lemma 5.4 in the expanded proof: the cubic residual vanishes when
`g = 0`, `h = 0`, or `g + h = 0`, assuming the quadratic residual vanishes.
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n] [CharZero K]

lemma A_zero_zero : D.A 0 0 = 1 - D.τ⁻¹ := by
  rw [A_axis_right]; simp

lemma A_diag {a : ZMod n} (ha : a ≠ 0) : D.A a a = -D.τ⁻¹ := by
  rw [A_def, B_diag D ha]; ring

lemma A_zero_left {b : ZMod n} (hb : b ≠ 0) : D.A 0 b = -D.τ⁻¹ := by
  rw [A_axis_left, if_neg hb]; ring

lemma A_zero_right {a : ZMod n} (ha : a ≠ 0) : D.A a 0 = -D.τ⁻¹ := by
  rw [A_axis_right, if_neg ha]; ring

/-- The uniform formula for `A` without corrections. -/
lemma A_uniform_of {a b : ZMod n} (hab : ¬ (a = 0 ∧ b = 0)) :
    D.A a b = D.τ⁻¹ * D.δ⁻¹ * (D.W a * D.W (b - a) * D.W (-b)) := by
  rw [A_def, B_uniform, if_neg hab]; ring

/-- A shifted quadratic sum: `∑ m, A m h * A h (m + l) = [l = 0]` for `h ≠ 0`. -/
lemma sum_A_shift (hQ : ∀ g h, D.Q g h = 0) {h : ZMod n} (hh : h ≠ 0) (l : ZMod n) :
    ∑ m, D.A m h * D.A h (m + l) = if l = 0 then 1 else 0 := by
  have := hQ (-l) h
  rw [Q_def, if_neg hh, mul_zero, add_zero, sub_eq_zero] at this
  simp only [neg_eq_zero] at this
  rw [← this]
  refine Fintype.sum_equiv (Equiv.addRight l) _ _ (fun m => ?_)
  rw [Equiv.coe_addRight, show m + l + -l = m by ring]

/-- A shifted quadratic sum of the other kind:
`∑ m, A g (m + k) * A (-g) (m + l) = [k = g + l]` for `g ≠ 0`. -/
lemma sum_A_shift' (hQ : ∀ g h, D.Q g h = 0) {g : ZMod n} (hg : g ≠ 0) (k l : ZMod n) :
    ∑ m, D.A g (m + k) * D.A (-g) (m + l) = if k = g + l then 1 else 0 := by
  have := hQ (l + g - k) g
  rw [Q_def, if_neg hg, mul_zero, add_zero, sub_eq_zero] at this
  have e : (l + g - k = 0) ↔ (k = g + l) := by
    rw [sub_eq_zero, eq_comm, add_comm l g]
  simp only [e] at this
  rw [← this]
  -- reindex `x = m + k` and rotate `A (-g) (m + l) = A (m + l + g) g`
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ (fun m => ?_)
  rw [Equiv.coe_addRight, A_rot D (-g) (m + l), neg_neg,
    show m + l - -g = m + k + (l + g - k) by ring, mul_comm]

/-- Case `g = 0`, `h ≠ 0`. -/
theorem C_g_zero (hQ : ∀ g h, D.Q g h = 0) {h : ZMod n} (hh : h ≠ 0) (k l : ZMod n) :
    D.C 0 h k l = 0 := by
  rw [C_def, if_neg (fun e => hh e.2), mul_zero, add_zero]
  simp only [zero_add]
  have hexp : ∀ m, D.A m h * D.A 0 (m + k) * D.A h (m + l)
      = (if m = -k then D.A m h * D.A h (m + l) else 0)
        - D.τ⁻¹ * (D.A m h * D.A h (m + l)) := by
    intro m
    rw [A_axis_left]
    by_cases hm : m = -k
    · subst hm; simp; ring
    · have : m + k ≠ 0 := fun e => hm (eq_neg_of_add_eq_zero_left e)
      simp [this, hm]; ring
  simp only [hexp, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, ← mul_sum,
    sum_A_shift D hQ hh]
  by_cases hl : l = 0
  · subst hl
    rw [if_pos rfl, mul_one]
    simp only [add_zero, zero_add]
    rw [A_two_products D hh, A_axis_left, A_axis_right]
    have hc := D.δ_c_sq
    by_cases hk : k = 0
    · subst hk; simp [hh]; ring
    · by_cases hk' : -k = h
      · rw [if_pos (Or.inr hk'), if_neg hk]
        have : h + k = 0 := by rw [← hk']; ring
        rw [if_pos this]; ring
      · have h1 : ¬ (-k = 0 ∨ -k = h) := by
          rintro (e | e)
          · exact hk (neg_eq_zero.mp e)
          · exact hk' e
        have h2 : h + k ≠ 0 := fun e => hk' (by linear_combination -e)
        rw [if_neg h1, if_neg hk, if_neg h2]
        linear_combination hc
  · rw [if_neg hl, mul_zero, sub_zero]
    -- both products are uncorrected
    have e1 : D.A (-k) h * D.A h (-k + l)
        = D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W (-k) * D.W (h + k) * D.W (-h))
          * (D.W h * D.W (l - k - h) * D.W (k - l)) := by
      rw [A_uniform_of D (fun e => hh e.2), A_uniform_of D (fun e => hh e.1)]
      rw [show h - -k = h + k by ring, show -k + l - h = l - k - h by ring,
        show -(-k + l) = k - l by ring]
      ring
    have e2 : D.A l k * D.A (h + k) l
        = D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W l * D.W (k - l) * D.W (-k))
          * (D.W (h + k) * D.W (l - h - k) * D.W (-l)) := by
      rw [A_uniform_of D (fun e => hl e.1), A_uniform_of D (fun e => hl e.2)]
      ring
    rw [e1, e2, show l - k - h = l - h - k by ring]
    have r1 := D.hrec h hh
    have r2 := D.hrec l hl
    linear_combination (D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W (-k) * D.W (h + k)
      * D.W (l - h - k) * D.W (k - l))) * (r1 - r2)

/-- Case `h = 0`, `g ≠ 0`. -/
theorem C_h_zero (hQ : ∀ g h, D.Q g h = 0) {g : ZMod n} (hg : g ≠ 0) (k l : ZMod n) :
    D.C g 0 k l = 0 := by
  rw [C_swap]; exact C_g_zero D hQ hg l k

/-- Case `h = -g`, `g ≠ 0`. -/
theorem C_h_neg (hQ : ∀ g h, D.Q g h = 0) {g : ZMod n} (hg : g ≠ 0) (k l : ZMod n) :
    D.C g (-g) k l = 0 := by
  rw [C_def, if_neg (fun e => hg e.1), mul_zero, add_zero, add_neg_cancel,
    show -g + k = k - g by ring]
  have hexp : ∀ m, D.A m 0 * D.A g (m + k) * D.A (-g) (m + l)
      = (if m = 0 then D.A g (m + k) * D.A (-g) (m + l) else 0)
        - D.τ⁻¹ * (D.A g (m + k) * D.A (-g) (m + l)) := by
    intro m
    rw [A_axis_right]
    by_cases hm : m = 0
    · subst hm; simp; ring
    · simp [hm]; ring
  simp only [hexp, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, ← mul_sum,
    sum_A_shift' D hQ hg, zero_add]
  by_cases hk : k = g + l
  · subst hk
    rw [if_pos rfl, mul_one, A_rot D (-g) l, neg_neg, show l - -g = g + l by ring,
      mul_comm (D.A g (g + l)), A_two_products D hg (g + l), show g + l - g = l by ring]
    have hc := D.δ_c_sq
    by_cases hl : l = 0
    · subst hl
      rw [add_zero, if_pos (Or.inr rfl), A_diag D hg, A_zero_zero]; ring
    · by_cases hl' : g + l = 0
      · rw [if_pos (Or.inl hl'), hl', A_zero_zero, A_diag D hl]; ring
      · rw [if_neg (by rintro (e | e); exact hl' e; exact hl (by linear_combination e)),
          A_diag D hl', A_diag D hl]
        linear_combination hc
  · rw [if_neg hk, mul_zero, sub_zero]
    have hne : k - g - l ≠ 0 := fun e => hk (by linear_combination e)
    have e1 : D.A g k * D.A (-g) l
        = D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W g * D.W (k - g) * D.W (-k))
          * (D.W (-g) * D.W (l + g) * D.W (-l)) := by
      rw [A_uniform_of D (fun e => hg e.1), A_uniform_of D (fun e => hg (neg_eq_zero.mp e.1))]
      rw [show l - -g = l + g by ring]; ring
    have e2 : D.A (g + l) k * D.A (k - g) l
        = D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W (g + l) * D.W (k - g - l) * D.W (-k))
          * (D.W (k - g) * D.W (-(k - g - l)) * D.W (-l)) := by
      rw [A_uniform_of D (fun e => hk (by rw [e.2, e.1])),
        A_uniform_of D (fun e => hk (by rw [e.2, add_zero, ← sub_eq_zero, e.1]))]
      rw [show k - (g + l) = k - g - l by ring, show l - (k - g) = -(k - g - l) by ring]
      ring
    rw [e1, e2, show l + g = g + l by ring]
    have r1 := D.hrec g hg
    have r2 := D.hrec (k - g - l) hne
    linear_combination (D.τ⁻¹ ^ 2 * D.δ⁻¹ ^ 2 * (D.W (k - g) * D.W (-k)
      * D.W (g + l) * D.W (-l))) * (r1 - r2)

/-- Sums of products of three shifted indicators. -/
lemma sum_three_ind (a b d : ZMod n) (c : K) :
    ∑ m : ZMod n, ((if m = a then (1 : K) else 0) - c) * ((if m = b then 1 else 0) - c)
        * ((if m = d then 1 else 0) - c)
      = (if a = b then (1 : K) else 0) * (if a = d then 1 else 0)
        - c * ((if a = b then 1 else 0) + (if a = d then 1 else 0) + (if b = d then 1 else 0))
        + 3 * c ^ 2 - n * c ^ 3 := by
  have h : ∀ m : ZMod n, ((if m = a then (1 : K) else 0) - c) * ((if m = b then 1 else 0) - c)
        * ((if m = d then 1 else 0) - c)
      = (if m = a then (1 : K) else 0) * (if m = b then 1 else 0) * (if m = d then 1 else 0)
        - c * ((if m = a then (1 : K) else 0) * (if m = b then 1 else 0)
          + (if m = a then (1 : K) else 0) * (if m = d then 1 else 0)
          + (if m = b then (1 : K) else 0) * (if m = d then 1 else 0))
        + c ^ 2 * ((if m = a then (1 : K) else 0) + (if m = b then 1 else 0)
          + (if m = d then 1 else 0)) - c ^ 3 := fun m => by ring
  simp only [h, sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  ring

/-- Case `g = h = 0`. -/
theorem C_zero_zero (k l : ZMod n) : D.C 0 0 k l = 0 := by
  rw [C_def, if_pos ⟨rfl, rfl⟩, mul_one]
  simp only [zero_add, A_axis_left, A_axis_right]
  have e1 : ∀ m : ZMod n, (m + k = 0) ↔ (m = -k) := fun m => by rw [add_eq_zero_iff_eq_neg]
  have e2 : ∀ m : ZMod n, (m + l = 0) ↔ (m = -l) := fun m => by rw [add_eq_zero_iff_eq_neg]
  simp only [e1, e2]
  rw [sum_three_ind]
  simp only [zero_eq_neg, neg_inj]
  have hn := D.n_eq
  have hτ := D.τ_ne_zero
  have hδ := D.δ_ne_zero
  have hδτ : D.δ = D.τ + 1 := by rw [τ_def]; ring
  have hτ1 : D.τ + 1 ≠ 0 := by rw [← hδτ]; exact hδ
  by_cases hk : k = 0
  · by_cases hl : l = 0
    · subst hk; subst hl
      rw [A_zero_zero]
      simp only [if_true]
      rw [hn, hδτ]; field_simp; ring
    · subst hk
      have hl' : (0 : ZMod n) ≠ l := Ne.symm hl
      rw [A_zero_right D hl, A_zero_left D hl]
      simp only [if_true, hl, hl', if_false]
      rw [hn, hδτ]; field_simp; ring
  · by_cases hl : l = 0
    · subst hl
      have hk' : (0 : ZMod n) ≠ k := Ne.symm hk
      rw [A_zero_left D hk, A_zero_right D hk]
      simp only [if_true, hk, hk', if_false]
      rw [hn, hδτ]; field_simp; ring
    · by_cases hkl : k = l
      · subst hkl
        rw [A_diag D hk]
        simp only [if_true, hk, if_false]
        rw [hn, hδτ]; field_simp; ring
      · rw [A_two_products D hk l,
          if_neg (show ¬ (l = 0 ∨ l = k) from fun e => e.elim (fun e => hl e) (fun e => hkl e.symm))]
        simp only [hk, hl, hkl, if_false]
        rw [hn, hδτ]; field_simp; ring

end CoeffData
end HaagerupIzumi
