import FusionCategory.System

open FusionCategory

universe u

namespace CoherenceCheck

variable {n : ℕ} {k : Type u} [Field k]

/-- WP1 Task 1.3, option (ii): the law with the `F`-factors retained, exactly as
displayed in the proposal (`J^e_ab * J^d_ec * F = J^f_bc * J^d_af * F`). -/
def Retained (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    S.J a b e * S.J e c d * S.F a b c d e f
      = S.J b c f * S.J a f d * S.F a b c d e f

/-- WP1 Task 1.3, option (i): the F-free law qualified by an explicit nonzero
side condition `hF` on the associator entry. -/
def Qualified (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d → S.F a b c d e f ≠ 0 →
    S.J a b e * S.J e c d = S.J b c f * S.J a f d

/-- Option (i) implies option (ii) (multiply by the entry; no hypothesis). -/
theorem retained_of_qualified (S : FusionSystem n k) (h : Qualified S) : Retained S := by
  intro a b c d e f h1 h2 h3 h4
  by_cases hF : S.F a b c d e f = 0
  · rw [hF, mul_zero, mul_zero]
  · rw [h a b c d e f h1 h2 h3 h4 hF]

/-- Option (ii) implies option (i) (`hF` is the cancellation licence). -/
theorem qualified_of_retained (S : FusionSystem n k) (h : Retained S) : Qualified S := by
  intro a b c d e f h1 h2 h3 h4 hF
  have hh := h a b c d e f h1 h2 h3 h4
  exact mul_right_cancel₀ hF hh

/-- The library's `J_coherent` --- restated in the retained-`F` form (decision 2 of
the delegation batch, WP1 Task 1.3) --- IS option (ii), definitionally: the field's
body is `Retained`'s. -/
theorem retained_of_coherent (S : FusionSystem n k) : Retained S :=
  fun a b c d e f h1 h2 h3 h4 => S.J_coherent a b c d e f h1 h2 h3 h4

/-- And option (i) (the F-free law, qualified by `hF`) follows from the field under
the nonzero side condition --- as it must: the restatement is a weakening of the old
F-free field, which is exactly what the review required. -/
theorem qualified_of_coherent (S : FusionSystem n k) : Qualified S :=
  qualified_of_retained S (retained_of_coherent S)

#print axioms CoherenceCheck.retained_of_qualified
#print axioms CoherenceCheck.qualified_of_retained

end CoherenceCheck
