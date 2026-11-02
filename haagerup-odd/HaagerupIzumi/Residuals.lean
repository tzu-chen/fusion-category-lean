module

public import HaagerupIzumi.Coefficients

@[expose] public section

/-!
# The quadratic and cubic residuals

Section 5.1 of the expanded proof: the residuals `Q`, `C` and `𝒞 = τ^3 C`,
their expression through `B`, the swap symmetry of `C`, and the two-product
lemma (5.9).
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n]

/-- The quadratic residual (5.1). -/
def Q (g h : ZMod n) : K :=
  ∑ m, D.A (m + g) h * D.A h m - (if g = 0 then 1 else 0) + D.δ⁻¹ * (if h = 0 then 1 else 0)

/-- The cubic residual (5.2). -/
def C (g h k l : ZMod n) : K :=
  ∑ m, D.A m (g + h) * D.A g (m + k) * D.A h (m + l)
    - D.A (g + l) k * D.A (h + k) l + D.δ⁻¹ * (if g = 0 ∧ h = 0 then 1 else 0)

/-- The rescaled cubic residual `𝒞 = τ^3 C` (5.3). -/
def Cs (g h k l : ZMod n) : K := D.τ ^ 3 * D.C g h k l

lemma Q_def (g h : ZMod n) : D.Q g h =
    ∑ m, D.A (m + g) h * D.A h m - (if g = 0 then 1 else 0) + D.δ⁻¹ * (if h = 0 then 1 else 0) :=
  rfl

lemma C_def (g h k l : ZMod n) : D.C g h k l =
    ∑ m, D.A m (g + h) * D.A g (m + k) * D.A h (m + l)
      - D.A (g + l) k * D.A (h + k) l + D.δ⁻¹ * (if g = 0 ∧ h = 0 then 1 else 0) := rfl

/-- The swap symmetry `C g h k l = C h g l k`. -/
theorem C_swap (g h k l : ZMod n) : D.C g h k l = D.C h g l k := by
  have h1 : ∑ m, D.A m (g + h) * D.A g (m + k) * D.A h (m + l)
      = ∑ m, D.A m (h + g) * D.A h (m + l) * D.A g (m + k) := by
    apply sum_congr rfl; intro m _; rw [add_comm h g]; ring
  have h2 : (if g = 0 ∧ h = 0 then (1 : K) else 0) = if h = 0 ∧ g = 0 then 1 else 0 := by
    simp only [and_comm]
  rw [C_def, C_def, h1, h2]; ring

section charzero
variable [CharZero K]

/-- The rescaled residual in terms of `B` (5.4). -/
theorem Cs_eq_B (g h k l : ZMod n) : D.Cs g h k l =
    ∑ m, D.B m (g + h) * D.B g (m + k) * D.B h (m + l)
      - D.τ * (D.B (g + l) k * D.B (h + k) l)
      + D.τ ^ 3 * D.δ⁻¹ * (if g = 0 ∧ h = 0 then 1 else 0) := by
  rw [Cs, C_def]
  simp only [B_eq_τ_mul_A]
  rw [mul_add, mul_sub, mul_sum]
  congr 1
  · congr 1
    · apply sum_congr rfl; intro m _; ring
    · ring
  · ring

/-- The quadratic sum in `B`-form: `∑ m, B (m+g) h * B h m = τ^2 * (Q g h + [g=0] - δ⁻¹ [h=0])`. -/
theorem sum_B_quadratic (g h : ZMod n) :
    ∑ m, D.B (m + g) h * D.B h m
      = D.τ ^ 2 * (D.Q g h + (if g = 0 then 1 else 0) - D.δ⁻¹ * (if h = 0 then 1 else 0)) := by
  have : D.Q g h + (if g = 0 then 1 else 0) - D.δ⁻¹ * (if h = 0 then 1 else 0)
      = ∑ m, D.A (m + g) h * D.A h m := by rw [Q_def]; ring
  rw [this, mul_sum]
  apply sum_congr rfl; intro m _
  rw [B_eq_τ_mul_A, B_eq_τ_mul_A]; ring

end charzero

omit [NeZero n] in
/-- The two-product lemma, `B`-form: for `h ≠ 0`,
`B u h * B h u = 1` if `u ∈ {0, h}` and `= δ` otherwise. -/
theorem B_two_products {h : ZMod n} (hh : h ≠ 0) (u : ZMod n) :
    D.B u h * D.B h u = if u = 0 ∨ u = h then 1 else D.δ := by
  by_cases hu0 : u = 0
  · subst hu0
    rw [D.B_zero_left hh, D.B_zero_right hh]; simp
  · by_cases huh : u = h
    · subst huh
      rw [D.B_diag hh]; simp
    · have hne : ¬ (u = 0 ∨ u = h) := by tauto
      rw [if_neg hne]
      have h1 : D.B u h = D.W u * D.W (h - u) / D.W h := by simp [B, hh]
      have h2 : D.B h u = D.W h * D.W (u - h) / D.W u := by simp [B, hu0]
      rw [h1, h2]
      have h3 : D.W (h - u) * D.W (u - h) = D.δ := by
        have := D.hrec (h - u) (sub_ne_zero.mpr (Ne.symm huh))
        rwa [neg_sub] at this
      field_simp [D.hWne u, D.hWne h]
      linear_combination h3

omit [NeZero n] in
/-- The two-product lemma, `A`-form (5.9): with `c = τ⁻¹`,
`A u h * A h u = c^2` if `u ∈ {0,h}` and `δ c^2` otherwise. -/
theorem A_two_products [CharZero K] {h : ZMod n} (hh : h ≠ 0) (u : ZMod n) :
    D.A u h * D.A h u = if u = 0 ∨ u = h then D.τ⁻¹ ^ 2 else D.δ * D.τ⁻¹ ^ 2 := by
  have := D.B_two_products hh u
  rw [A_def, A_def, div_mul_div_comm, this]
  split_ifs <;> ring

/-- The identity `δ c^2 - c = c^2` for `c = τ⁻¹`. -/
theorem δ_c_sq [CharZero K] : D.δ * D.τ⁻¹ ^ 2 - D.τ⁻¹ = D.τ⁻¹ ^ 2 := by
  have := D.τ_ne_zero
  field_simp
  rw [τ_def]; ring

end CoeffData
end HaagerupIzumi
