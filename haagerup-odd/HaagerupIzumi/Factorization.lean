module

public import HaagerupIzumi.Residuals

@[expose] public section

/-!
# Balanced triples and the factorization of the cubic residual

Section 5.2 of the expanded proof: the pair of triples attached to a cubic
index quadruple, the cross sums, the quantities `S` and `P`, and the
factorization `𝒞 = W(-g-h) W g W h / δ^5 * (δ^2 S - τ P)` for nondegenerate
pairs.
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n]

/-- The row triple `a = (0, k - g, l - h)`. -/
def aTrip (g h k l : ZMod n) : Fin 3 → ZMod n := ![0, k - g, l - h]

/-- The column triple `c = (g + h, -k, -l)`. -/
def cTrip (g h k l : ZMod n) : Fin 3 → ZMod n := ![g + h, -k, -l]

/-- A pair of triples is nondegenerate when all nine cross sums are nonzero. -/
def Nondeg (a c : Fin 3 → ZMod n) : Prop := ∀ i j, a i + c j ≠ 0

/-- The six-factor sum `S`. -/
def S (a c : Fin 3 → ZMod n) : K :=
  ∑ m, (∏ i, D.W (m + a i)) * (∏ j, D.W (c j - m))

/-- The nine-factor product `P`. -/
def P (a c : Fin 3 → ZMod n) : K := ∏ i, ∏ j, D.W (a i + c j)

lemma S_def (a c : Fin 3 → ZMod n) :
    D.S a c = ∑ m, (D.W (m + a 0) * D.W (m + a 1) * D.W (m + a 2))
      * (D.W (c 0 - m) * D.W (c 1 - m) * D.W (c 2 - m)) := by
  simp only [S, Fin.prod_univ_three]

omit [NeZero n] in
lemma P_def (a c : Fin 3 → ZMod n) :
    D.P a c = (D.W (a 0 + c 0) * D.W (a 0 + c 1) * D.W (a 0 + c 2))
      * (D.W (a 1 + c 0) * D.W (a 1 + c 1) * D.W (a 1 + c 2))
      * (D.W (a 2 + c 0) * D.W (a 2 + c 1) * D.W (a 2 + c 2)) := by
  simp only [P, Fin.prod_univ_three]

/-- `S` is invariant under permuting the row triple. -/
theorem S_perm_left (a c : Fin 3 → ZMod n) (σ : Equiv.Perm (Fin 3)) :
    D.S (a ∘ σ) c = D.S a c := by
  unfold S
  apply sum_congr rfl; intro m _
  congr 1
  exact Equiv.prod_comp σ (fun i => D.W (m + a i))

/-- `S` is invariant under permuting the column triple. -/
theorem S_perm_right (a c : Fin 3 → ZMod n) (σ : Equiv.Perm (Fin 3)) :
    D.S a (c ∘ σ) = D.S a c := by
  unfold S
  apply sum_congr rfl; intro m _
  congr 1
  exact Equiv.prod_comp σ (fun j => D.W (c j - m))

/-- `S` is invariant under translation. -/
theorem S_translate (a c : Fin 3 → ZMod n) (t : ZMod n) :
    D.S (fun i => a i - t) (fun j => c j + t) = D.S a c := by
  unfold S
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ (fun m => ?_)
  simp only [Equiv.subRight_apply]
  congr 1
  · apply prod_congr rfl; intro i _; congr 1; ring
  · apply prod_congr rfl; intro j _; congr 1; ring

theorem P_perm_left (a c : Fin 3 → ZMod n) (σ : Equiv.Perm (Fin 3)) :
    D.P (a ∘ σ) c = D.P a c := by
  unfold P
  exact Equiv.prod_comp σ (fun i => ∏ j, D.W (a i + c j))

theorem P_perm_right (a c : Fin 3 → ZMod n) (σ : Equiv.Perm (Fin 3)) :
    D.P a (c ∘ σ) = D.P a c := by
  unfold P
  apply prod_congr rfl; intro i _
  exact Equiv.prod_comp σ (fun j => D.W (a i + c j))

theorem P_translate (a c : Fin 3 → ZMod n) (t : ZMod n) :
    D.P (fun i => a i - t) (fun j => c j + t) = D.P a c := by
  unfold P
  apply prod_congr rfl; intro i _; apply prod_congr rfl; intro j _
  congr 1; ring

/-- The cross sums of the pair attached to `(g, h, k, l)`. -/
lemma cross_sums (g h k l : ZMod n) :
    aTrip g h k l 0 + cTrip g h k l 0 = g + h ∧
    aTrip g h k l 0 + cTrip g h k l 1 = -k ∧
    aTrip g h k l 0 + cTrip g h k l 2 = -l ∧
    aTrip g h k l 1 + cTrip g h k l 0 = h + k ∧
    aTrip g h k l 1 + cTrip g h k l 1 = -g ∧
    aTrip g h k l 1 + cTrip g h k l 2 = k - g - l ∧
    aTrip g h k l 2 + cTrip g h k l 0 = g + l ∧
    aTrip g h k l 2 + cTrip g h k l 1 = l - h - k ∧
    aTrip g h k l 2 + cTrip g h k l 2 = -h := by
  simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

section factor
variable [CharZero K]

/-- The factorization (5.7) for nondegenerate pairs. -/
theorem Cs_factor {g h k l : ZMod n} (hnd : Nondeg (aTrip g h k l) (cTrip g h k l)) :
    D.Cs g h k l = D.W (-(g + h)) * D.W g * D.W h / D.δ ^ 5
      * (D.δ ^ 2 * D.S (aTrip g h k l) (cTrip g h k l)
        - D.τ * D.P (aTrip g h k l) (cTrip g h k l)) := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := cross_sums g h k l
  have hgh : g + h ≠ 0 := x00 ▸ hnd 0 0
  have hk : k ≠ 0 := fun e => hnd 0 1 (by rw [x01, e, neg_zero])
  have hl : l ≠ 0 := fun e => hnd 0 2 (by rw [x02, e, neg_zero])
  have hhk : h + k ≠ 0 := x10 ▸ hnd 1 0
  have hg : g ≠ 0 := fun e => hnd 1 1 (by rw [x11, e, neg_zero])
  have hgl : g + l ≠ 0 := x20 ▸ hnd 2 0
  have hh : h ≠ 0 := fun e => hnd 2 2 (by rw [x22, e, neg_zero])
  have hδ := D.δ_ne_zero
  -- the uniform formula without corrections
  have hB : ∀ a b : ZMod n, ¬ (a = 0 ∧ b = 0) →
      D.B a b = D.δ⁻¹ * D.W a * D.W (b - a) * D.W (-b) := by
    intro a b hab; rw [B_uniform, if_neg hab]; ring
  rw [Cs_eq_B, if_neg (fun e => hg e.1), mul_zero, add_zero]
  -- the sum
  have hsum : ∑ m, D.B m (g + h) * D.B g (m + k) * D.B h (m + l)
      = D.δ⁻¹ ^ 3 * (D.W (-(g + h)) * D.W g * D.W h) * D.S (aTrip g h k l) (cTrip g h k l) := by
    rw [S_def, mul_sum]
    apply sum_congr rfl; intro m _
    rw [hB m (g + h) (fun e => hgh e.2), hB g (m + k) (fun e => hg e.1),
      hB h (m + l) (fun e => hh e.1)]
    simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [show m + k - g = m + (k - g) by ring, show m + l - h = m + (l - h) by ring,
      show -(m + k) = -k - m by ring, show -(m + l) = -l - m by ring, add_zero]
    ring
  -- the product
  have hprod : D.B (g + l) k * D.B (h + k) l
      = D.δ⁻¹ ^ 2 * (D.W (g + l) * D.W (k - g - l) * D.W (-k))
        * (D.W (h + k) * D.W (l - h - k) * D.W (-l)) := by
    rw [hB (g + l) k (fun e => hgl e.1), hB (h + k) l (fun e => hhk e.1)]
    rw [show k - (g + l) = k - g - l by ring, show l - (h + k) = l - h - k by ring]
    ring
  have hP : D.P (aTrip g h k l) (cTrip g h k l)
      = (D.W (g + h) * D.W (-g) * D.W (-h))
        * ((D.W (g + l) * D.W (k - g - l) * D.W (-k))
          * (D.W (h + k) * D.W (l - h - k) * D.W (-l))) := by
    rw [P_def, x00, x01, x02, x10, x11, x12, x20, x21, x22]; ring
  have key : D.W (-(g + h)) * D.W g * D.W h * (D.W (g + h) * D.W (-g) * D.W (-h)) = D.δ ^ 3 := by
    have e1 := D.hrec g hg
    have e2 := D.hrec h hh
    have e3 := D.hrec (g + h) hgh
    linear_combination (D.W g * D.W (-g) * D.W h * D.W (-h)) * e3
      + (D.δ * D.W h * D.W (-h)) * e1 + (D.δ ^ 2) * e2
  rw [hsum, hprod, hP]
  have hinv : D.δ⁻¹ * D.δ = 1 := inv_mul_cancel₀ hδ
  field_simp
  linear_combination (D.τ * ((D.W (g + l) * D.W (k - g - l) * D.W (-k))
    * (D.W (h + k) * D.W (l - h - k) * D.W (-l)))) * key

/-- The factorization with corrections (5.8), valid whenever `g, h, g + h ≠ 0`. -/
theorem Cs_factor' {g h k l : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0) :
    D.Cs g h k l = D.W (-(g + h)) * D.W g * D.W h / D.δ ^ 5
      * (D.δ ^ 2 * D.S (aTrip g h k l) (cTrip g h k l)
        - D.τ * D.P (aTrip g h k l) (cTrip g h k l)
        - D.τ ^ 3 * D.δ ^ 3 * ((if g + l = 0 ∧ k = 0 then 1 else 0)
          + (if h + k = 0 ∧ l = 0 then 1 else 0))) := by
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := cross_sums g h k l
  have hδ := D.δ_ne_zero
  have hB : ∀ a b : ZMod n, ¬ (a = 0 ∧ b = 0) →
      D.B a b = D.δ⁻¹ * D.W a * D.W (b - a) * D.W (-b) := by
    intro a b hab; rw [B_uniform, if_neg hab]; ring
  rw [Cs_eq_B, if_neg (fun e => hg e.1), mul_zero, add_zero]
  have hsum : ∑ m, D.B m (g + h) * D.B g (m + k) * D.B h (m + l)
      = D.δ⁻¹ ^ 3 * (D.W (-(g + h)) * D.W g * D.W h) * D.S (aTrip g h k l) (cTrip g h k l) := by
    rw [S_def, mul_sum]
    apply sum_congr rfl; intro m _
    rw [hB m (g + h) (fun e => hgh e.2), hB g (m + k) (fun e => hg e.1),
      hB h (m + l) (fun e => hh e.1)]
    simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [show m + k - g = m + (k - g) by ring, show m + l - h = m + (l - h) by ring,
      show -(m + k) = -k - m by ring, show -(m + l) = -l - m by ring, add_zero]
    ring
  set X₁ := D.W (g + l) * D.W (k - g - l) * D.W (-k) with hX₁
  set X₂ := D.W (h + k) * D.W (l - h - k) * D.W (-l) with hX₂
  set W3 := D.W g * D.W h * D.W (-(g + h)) with hW3
  have hprod : D.B (g + l) k * D.B (h + k) l
      = D.δ⁻¹ ^ 2 * X₁ * X₂ + D.τ ^ 2 * D.δ⁻¹ ^ 2 * W3
        * ((if g + l = 0 ∧ k = 0 then 1 else 0) + (if h + k = 0 ∧ l = 0 then 1 else 0)) := by
    rw [B_uniform, B_uniform, show k - (g + l) = k - g - l by ring,
      show l - (h + k) = l - h - k by ring]
    by_cases c1 : g + l = 0 ∧ k = 0
    · obtain ⟨e1, e2⟩ := c1
      have hl : l = -g := eq_neg_of_add_eq_zero_right e1
      subst e2; subst hl
      have c2 : ¬ (h + 0 = 0 ∧ -g = 0) := fun e => hh (by simpa using e.1)
      rw [if_pos ⟨e1, rfl⟩, if_neg c2]
      rw [hX₁, hX₂, hW3]
      simp only [add_zero, neg_neg, neg_zero, sub_zero, e1]
      rw [show -g - h = -(g + h) by ring]
      ring
    · by_cases c2 : h + k = 0 ∧ l = 0
      · obtain ⟨e1, e2⟩ := c2
        have hk : k = -h := eq_neg_of_add_eq_zero_right e1
        subst e2; subst hk
        rw [if_neg c1, if_pos ⟨e1, rfl⟩]
        rw [hX₁, hX₂, hW3]
        simp only [add_zero, neg_neg, neg_zero, sub_zero, zero_sub, e1]
        rw [show -h - g = -(g + h) by ring]
        ring
      · rw [if_neg c1, if_neg c2]
        rw [hX₁, hX₂]; ring
  have hP : D.P (aTrip g h k l) (cTrip g h k l)
      = (D.W (g + h) * D.W (-g) * D.W (-h)) * (X₁ * X₂) := by
    rw [P_def, x00, x01, x02, x10, x11, x12, x20, x21, x22, hX₁, hX₂]; ring
  have key : D.W (-(g + h)) * D.W g * D.W h * (D.W (g + h) * D.W (-g) * D.W (-h)) = D.δ ^ 3 := by
    have e1 := D.hrec g hg
    have e2 := D.hrec h hh
    have e3 := D.hrec (g + h) hgh
    linear_combination (D.W g * D.W (-g) * D.W h * D.W (-h)) * e3
      + (D.δ * D.W h * D.W (-h)) * e1 + (D.δ ^ 2) * e2
  rw [hsum, hprod, hP]
  rw [hW3]
  field_simp
  linear_combination (D.τ * (X₁ * X₂)) * key

end factor

end CoeffData
end HaagerupIzumi
