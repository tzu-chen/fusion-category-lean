/-
WP2 round 1, member m3, direction D4: the frozen statements of the associator
package, plus the label-level identities that the entrywise reduction
consumes.

Everything here is a `def`/`Prop` or a restatement of a `FusionSystem` axiom;
nothing is assumed.  The three Props are the targets of the reduction:

* `AssociatorIso`     — what the associator/inverse pair must satisfy;
* `AssociatorNatural` — naturality in the three variables;
* `ObjectAssociativity` — the note's claim that the two triple tensors have the
  same multiplicity vector (a computation with `FusionRing.associativity`).

The label-level inputs are `FusionSystem.Finv_comp` and
`FusionSystem.F_comp_inv`; the reconstruction-level statements are the exact
Σ-index collapse of these (see `report.md` §"Residual").

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconAssoc
import FusionCategory.ReconTensorApply
import FusionCategory.ReconUnit

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- The associator and its inverse are mutually inverse. -/
def AssociatorIso : Prop :=
  (∀ X Y Z : FusionMat n k,
      associatorHom S X Y Z ≫ associatorInv S X Y Z
        = 𝟙 (tensorObj S (tensorObj S X Y) Z))
  ∧ (∀ X Y Z : FusionMat n k,
      associatorInv S X Y Z ≫ associatorHom S X Y Z
        = 𝟙 (tensorObj S X (tensorObj S Y Z)))

/-- The associator is natural in all three variables. -/
def AssociatorNatural : Prop :=
  ∀ (X Y Z X' Y' Z' : FusionMat n k) (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z'
      = associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)

/-- The design note's object-level associativity: `(X⊗Y)⊗Z` and `X⊗(Y⊗Z)` have
the same multiplicity vector.  This is the fusion ring's associativity
(`FusionRing.associativity`) after distributing the products; it is *not*
needed to define the associator (the two block index types are different, and
a matrix between different index types is well formed). -/
def ObjectAssociativity : Prop :=
  ∀ (X Y Z : FusionMat n k) (d : Fin n),
    (tensorObj S (tensorObj S X Y) Z).m d = (tensorObj S X (tensorObj S Y Z)).m d

/-! ## The label-level identities the reduction consumes -/

/-- `α⁻¹ ∘ α = 1` at a label: the (only) `FusionSystem` axiom used by
`AssociatorIso`'s second component after the Σ-collapse. -/
theorem assocIso_label_right {a b c d e' e : Fin n}
    (h1 : 0 < S.ring.N a b e') (h2 : 0 < S.ring.N e' c d)
    (h3 : 0 < S.ring.N a b e) (h4 : 0 < S.ring.N e c d) :
    (∑ f : Fin n, S.Finv a b c d f e' * S.F a b c d e f) = if e' = e then 1 else 0 :=
  S.F_comp_inv a b c d e' e h1 h2 h3 h4

/-- `α ∘ α⁻¹ = 1` at a label: the axiom used by `AssociatorIso`'s first
component after the Σ-collapse. -/
theorem assocIso_label_left {a b c d f' f : Fin n}
    (h1 : 0 < S.ring.N b c f') (h2 : 0 < S.ring.N a f' d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N a f d) :
    (∑ e : Fin n, S.Finv a b c d f' e * S.F a b c d e f) = if f' = f then 1 else 0 :=
  S.Finv_comp a b c d f' f h1 h2 h3 h4

end FusionCategory
