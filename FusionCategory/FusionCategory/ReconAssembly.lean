/-
WP2 round 2, member m4, direction D5 (monoidal assembly), integration with D4.

D4 (member m5) delivered the unitors *and* the triangle (`Unitors.lean`, copied here verbatim
as `M5Unitors.lean`).  This file plugs them into the assembler of `ReconMonoidal.lean`, so the
monoidal structure now depends on exactly **three** open items:

* `AssociatorIso S`     — D2 (frozen statement, `ReconAssocStatements`),
* `AssociatorNatural S` — D2 (frozen statement),
* the pentagon           — D3.

Everything else (the two unitor `Iso` families, their naturalities, the triangle, the tensor,
both whisker identities, the structural `MonoidalCategory` fields, `MonoidalPreadditive`) is
proved.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconMonoidal
import FusionCategory.ReconUnitors

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option warn.classDefReducibility false

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory

variable {n : ℕ} {k : Type u} [Field k]

/-- **The pentagon (D3), in the shape the assembler consumes.**  This is
`MonoidalCategory.pentagon` for the assembled structure, with the associator's `Iso` replaced by
its `hom`; `(associatorIsoOf S hiso _ _ _).hom = associatorHom S _ _ _` definitionally, so a
pentagon proved about `associatorHom` is accepted verbatim. -/
def PentagonShape (S : FusionSystem n k) (hiso : AssociatorIso S) : Prop :=
  ∀ W X Y Z : FusionMat n k,
    tensorHom S (associatorIsoOf S hiso W X Y).hom (𝟙 Z)
        ≫ (associatorIsoOf S hiso W (tensorObj S X Y) Z).hom
        ≫ tensorHom S (𝟙 W) (associatorIsoOf S hiso X Y Z).hom
      = (associatorIsoOf S hiso (tensorObj S W X) Y Z).hom
        ≫ (associatorIsoOf S hiso W X (tensorObj S Y Z)).hom

/-- The pentagon as a statement about the F-symbol block matrix `associatorHom`. -/
def PentagonShapeHom (S : FusionSystem n k) : Prop :=
  ∀ W X Y Z : FusionMat n k,
    tensorHom S (associatorHom S W X Y) (𝟙 Z)
        ≫ associatorHom S W (tensorObj S X Y) Z
        ≫ tensorHom S (𝟙 W) (associatorHom S X Y Z)
      = associatorHom S (tensorObj S W X) Y Z ≫ associatorHom S W X (tensorObj S Y Z)

/-- `PentagonShapeHom` is `PentagonShape`: the associator's `Iso` hom is `associatorHom`
definitionally. -/
theorem pentagonShape_iff (S : FusionSystem n k) (hiso : AssociatorIso S) :
    PentagonShape S hiso ↔ PentagonShapeHom S where
  mp h := h
  mpr h := h

/-- **The monoidal coherence data**, with D4's unitors and triangle plugged in.  The only
inputs are D2's two frozen associator statements and D3's pentagon. -/
noncomputable def monoidalDataOfAssoc (S : FusionSystem n k) (hn : 0 < n)
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso) :
    MonoidalData S hn :=
  monoidalDataOfFrozen S hiso hnat
    (fun X => Units.leftUnitorIso S hn X)
    (fun X => Units.rightUnitorIso S hn X)
    (fun {_ _} f => Units.whiskerLeft_leftUnitor S hn f)
    (fun {_ _} f => Units.whiskerRight_rightUnitor S hn f)
    (fun W X Y Z => pent W X Y Z)
    (fun X Y => Units.triangle S hn X Y)

/-- **The monoidal category**, from D2's two frozen statements and D3's pentagon. -/
noncomputable def monoidalCategoryOfAssoc (S : FusionSystem n k) (hn : 0 < n)
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso) :
    MonoidalCategory (FusionMat n k) :=
  (monoidalDataOfAssoc S hn hiso hnat pent).toMonoidalCategory

/-- The additivity of the tensor for that structure (the bilinearity of `tensorHom`). -/
theorem monoidalPreadditiveOfAssoc (S : FusionSystem n k) (hn : 0 < n)
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso) :
    @MonoidalPreadditive (FusionMat n k) _ _
      (monoidalCategoryOfAssoc S hn hiso hnat pent) :=
  (monoidalDataOfAssoc S hn hiso hnat pent).toMonoidalPreadditive

/-- The assembled associator *is* the F-symbol block matrix: its `hom` is `associatorHom`,
definitionally. -/
theorem monoidalDataOfAssoc_associator_hom (S : FusionSystem n k) (hn : 0 < n)
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso)
    (X Y Z : FusionMat n k) :
    ((monoidalDataOfAssoc S hn hiso hnat pent).associator X Y Z).hom
      = associatorHom S X Y Z := rfl

end FusionCategory
