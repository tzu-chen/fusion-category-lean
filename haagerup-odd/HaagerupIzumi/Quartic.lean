module

public import HaagerupIzumi.Residuals

@[expose] public section

/-!
# The quartic residual is a contraction of the cubic residual

Lemma 10.1 of the expanded proof: for any matrix with the order-three
symmetry, the Evans–Gannon quartic residual `Kq` is a linear combination of
cubic residuals `C` and one quadratic residual `Q`. Hence `Q = C = 0`
implies the quartic equations.
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n]

/-- The quartic residual of Evans–Gannon, Eq. (4.10) with `ω = 1`. -/
def Kq (g h i k : ZMod n) : K :=
  ∑ l, ∑ m, D.A l m * D.A (l + g) h * D.A (h + m) (l + i) * D.A i (k + m)
    - D.A (h - g) (i - g) * (if g = k then 1 else 0)
    + D.δ⁻¹ * (if h = 0 then 1 else 0) * D.A i k
    + D.δ⁻¹ * D.A g h * (if i = 0 then 1 else 0)

/-- The contraction identity (10.1). -/
theorem Kq_eq (g h i k : ZMod n) :
    D.Kq g h i k = ∑ m, D.A i (k + m) * D.C (-h) (h + m) (g - h) i
      + D.A (i - h) (g - h) * D.Q (g - k) i := by
  have hC : ∀ m, D.C (-h) (h + m) (g - h) i
      = ∑ l, D.A l m * D.A (l + g) h * D.A (h + m) (l + i)
        - D.A (i - h) (g - h) * D.A (m + g) i
        + D.δ⁻¹ * (if h = 0 ∧ m = 0 then 1 else 0) := by
    intro m
    rw [C_def]
    have e1 : -h + (h + m) = m := by ring
    have e2 : -h + i = i - h := by ring
    have e3 : h + m + (g - h) = m + g := by ring
    have e4 : (-h = 0 ∧ h + m = 0) ↔ (h = 0 ∧ m = 0) := by
      constructor
      · rintro ⟨h1, h2⟩
        rw [neg_eq_zero] at h1
        subst h1
        simpa using h2
      · rintro ⟨h1, h2⟩
        subst h1; subst h2; simp
    rw [e1, e2, e3]
    simp only [e4]
    congr 2
    apply sum_congr rfl; intro l _
    have : D.A (-h) (l + (g - h)) = D.A (l + g) h := by
      rw [A_rot' D (l + g) h]; congr 1; ring
    rw [this]
  have hQ : D.Q (g - k) i = ∑ m, D.A i (k + m) * D.A (m + g) i
      - (if g = k then 1 else 0) + D.δ⁻¹ * (if i = 0 then 1 else 0) := by
    rw [Q_def]
    have : ∑ m, D.A (m + (g - k)) i * D.A i m = ∑ m, D.A i (k + m) * D.A (m + g) i := by
      refine (Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun m => ?_)).symm
      rw [Equiv.coe_addLeft, show k + m + (g - k) = m + g by ring]; ring
    rw [this]
    simp only [sub_eq_zero]
  have hS1 : ∑ m, D.A i (k + m) * (∑ l, D.A l m * D.A (l + g) h * D.A (h + m) (l + i))
      = ∑ l, ∑ m, D.A l m * D.A (l + g) h * D.A (h + m) (l + i) * D.A i (k + m) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro l _; apply sum_congr rfl; intro m _; ring
  have hS2 : ∑ m, D.A i (k + m) * (D.δ⁻¹ * (if h = 0 ∧ m = 0 then (1 : K) else 0))
      = D.δ⁻¹ * (if h = 0 then 1 else 0) * D.A i k := by
    by_cases hh : h = 0
    · subst hh
      simp only [true_and, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
      ring_nf
    · simp [hh]
  have hS3 : ∑ m, D.A i (k + m) * (D.A (i - h) (g - h) * D.A (m + g) i)
      = D.A (i - h) (g - h) * ∑ m, D.A i (k + m) * D.A (m + g) i := by
    rw [mul_sum]; apply sum_congr rfl; intro m _; ring
  have hf : D.A (i - h) (g - h) = D.A (h - g) (i - g) := by
    rw [A_rot D (h - g) (i - g)]; congr 1 <;> ring
  have hi : D.A (h - g) (i - g) * (if i = 0 then (1 : K) else 0)
      = D.A g h * (if i = 0 then 1 else 0) := by
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl, mul_one, mul_one, A_rot D (h - g) (0 - g), A_rot' D g h]
      congr 1 <;> ring
    · simp [hi0]
  rw [Kq]
  simp only [hC, hQ]
  simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
  rw [hS1, hS2, hS3, hf]
  linear_combination -D.δ⁻¹ * hi

/-- If all quadratic and cubic residuals vanish, so do the quartic ones. -/
theorem Kq_eq_zero (hQ : ∀ g h, D.Q g h = 0) (hC : ∀ g h k l, D.C g h k l = 0)
    (g h i k : ZMod n) : D.Kq g h i k = 0 := by
  rw [Kq_eq]; simp [hQ, hC]

end CoeffData
end HaagerupIzumi
