/-
WP2 round 1, member m3, direction D4 (supporting piece for the unitors).

The unit object `𝟙 = X₀` of the design note and the two object-level unit
identities: `(𝟙 ⊗ X).m c = X.m c` and `(X ⊗ 𝟙).m c = X.m c`.  These are the
multiplicity-level form of the note's "`𝟙 ⊗ X` is canonically `X` blockwise"
(`left_unit : N 0 a c = δ_{ac}`); the block equivalence and the unitors
themselves are the triangle direction's, but the object-level identities are
here.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconTensor

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- The unit object `X₀` of the reconstruction: multiplicity `1` at the label
`0` (which exists only when `n > 0`). -/
def unitObj (hn : 0 < n) : FusionMat n k where
  m j := if j = ⟨0, hn⟩ then 1 else 0
  blk j := Fin (if j = ⟨0, hn⟩ then 1 else 0)
  fintype_blk _ := inferInstance
  decidableEq_blk _ := inferInstance
  card_blk _ := by simp

theorem unitObj_m_zero (hn : 0 < n) : (unitObj (k := k) hn).m ⟨0, hn⟩ = 1 := by
  simp [unitObj]

theorem unitObj_m_ne (hn : 0 < n) {j : Fin n} (hj : j ≠ ⟨0, hn⟩) :
    (unitObj (k := k) hn).m j = 0 := by
  simp [unitObj, hj]

/-- `𝟙 ⊗ X` has the multiplicity vector of `X`: the design note's
"`𝟙 ⊗ X` is canonically `X` blockwise", at the level of multiplicities. -/
theorem unitObj_tensor_m (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    (tensorObj S (unitObj hn) X).m c = X.m c := by
  rw [tensorObj_m]
  have key : ∀ a : Fin n,
      (∑ b : Fin n, S.ring.N a b c * (unitObj (k := k) hn).m a * X.m b)
        = (if a = ⟨0, hn⟩ then (1 : ℕ) else 0) * X.m c := by
    intro a
    by_cases ha : a = ⟨0, hn⟩
    · subst ha
      simp only [unitObj_m_zero hn, mul_one, one_mul, if_true]
      rw [Finset.sum_eq_single c]
      · rw [S.ring.left_unit hn c c]
        simp
      · intro b _ hb
        rw [S.ring.left_unit hn b c, if_neg hb]
        simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg ha, zero_mul]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [unitObj_m_ne hn ha]
      simp
  rw [Finset.sum_congr rfl fun a _ => key a]
  rw [Finset.sum_eq_single (⟨0, hn⟩)]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `X ⊗ 𝟙` has the multiplicity vector of `X`. -/
theorem tensor_unitObj_m (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    (tensorObj S X (unitObj hn)).m c = X.m c := by
  rw [tensorObj_m]
  have key : ∀ a : Fin n,
      (∑ b : Fin n, S.ring.N a b c * X.m a * (unitObj (k := k) hn).m b)
        = S.ring.N a ⟨0, hn⟩ c * X.m a := by
    intro a
    rw [Finset.sum_eq_single (⟨0, hn⟩)]
    · rw [unitObj_m_zero hn, mul_one]
    · intro b _ hb
      rw [unitObj_m_ne hn hb]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => key a]
  rw [Finset.sum_eq_single c]
  · rw [S.ring.right_unit hn c c]
    simp
  · intro a _ ha
    rw [S.ring.right_unit hn a c, if_neg ha, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end FusionCategory
