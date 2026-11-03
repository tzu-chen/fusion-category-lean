/-
WP2 round 1, member m3, direction D4: the entrywise formula for `tensorHom`.

This is the design note's tensor entry, with the correction recorded in
`NoteFormula.lean`: block-diagonal in the LABEL, and inside the block the full
Kronecker product of the two blocks, with the channel coordinate acting as an
identity (`Fin (N p.1 p.2 c)` is a subsingleton by `mult_free`, so the `δ` on
the channel is the identity matrix there).

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

/-- The entry of `f ⊗ g` in the `c`-block at equal labels: the channel acts as
an identity and the block is the Kronecker product of the two blocks. -/
theorem tensorHom_apply {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n)
    (ν : Fin (S.ring.N p.1 p.2 c)) (x : X.blk p.1) (y : Y.blk p.2)
    (ν' : Fin (S.ring.N p.1 p.2 c)) (x' : X'.blk p.1) (y' : Y'.blk p.2) :
    tensorHom S f g c ⟨p, ν, x, y⟩ ⟨p, ν', x', y'⟩
      = (if ν = ν' then 1 else 0) * (f p.1 x x' * g p.2 y y') := by
  rw [tensorHom, blockDiag_mk]
  simp [tensorHomBlock, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The entry of `f ⊗ g` at differing labels is zero: the tensor is
block-diagonal in the label. -/
theorem tensorHom_apply_ne {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) {p q : Fin n × Fin n} (hpq : p ≠ q)
    (ν : Fin (S.ring.N p.1 p.2 c)) (x : X.blk p.1) (y : Y.blk p.2)
    (ν' : Fin (S.ring.N q.1 q.2 c)) (x' : X'.blk q.1) (y' : Y'.blk q.2) :
    tensorHom S f g c ⟨p, ν, x, y⟩ ⟨q, ν', x', y'⟩ = 0 := by
  rw [tensorHom]
  simp only [blockDiag, dif_neg hpq]

end FusionCategory
