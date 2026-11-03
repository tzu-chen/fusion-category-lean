/-
WP2 round 2, member m4, direction D5 (monoidal assembly), part (b): the
`MonoidalCategory`/`MonoidalPreadditive` instances for the canonical scaffold, assembled from
the landed tensor (Round 1: `tensorObj`, `tensorHom`, `tensorHom_id`, `tensorHom_comp`) plus
exactly the coherence data that D2 (associator), D3 (pentagon) and D4 (unitors, triangle)
owe.

Design: the assembly is stated as a *structure of data* (`MonoidalData`) whose fields are
exactly the three `Iso` families plus the five coherence equations, and then conversion
lemmas:

* `monoidalDataOfFrozen` — builds the data from the **frozen** Round-1 statements
  `AssociatorIso` and `AssociatorNatural` (so D2's targets plug in with no reshaping), plus a
  unitor `Iso` family with its two naturalities, plus the pentagon and the triangle;
* `MonoidalData.toMonoidalCategory` / `MonoidalData.toMonoidalPreadditive` — the instances.

What is *proved* here, unconditionally, is everything that does not need the F-symbol
calculus: `tensorHom_def`, `id_tensorHom_id`, `tensorHom_comp_tensorHom`, both whisker
identities, and all four `MonoidalPreadditive` fields.  What is *assumed* is exactly the five
coherence equations and the three `Iso` families — i.e. precisely the Round-2 targets of
D2/D3/D4, marked as such.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconMonoidalBilin
import FusionCategory.ReconAssocStatements
import Mathlib.CategoryTheory.Monoidal.Preadditive

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option warn.classDefReducibility false

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## Turning hom/inverse pairs into `Iso`s

The associator is *defined* already (`ReconAssoc.associatorHom`); what is owed is that it is
invertible with inverse `associatorInv`.  These two small constructors are the whole of the
"data" conversion; they are `rfl`-level and are what makes the assembled associator the
system's F-symbol rather than an arbitrary isomorphism. -/

/-- An isomorphism from a hom, an inverse and the two round trips. -/
def isoOfHomInv {C : Type*} [Category C] {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X)
    (hom_inv_id : hom ≫ inv = 𝟙 X) (inv_hom_id : inv ≫ hom = 𝟙 Y) : X ≅ Y where
  hom := hom
  inv := inv
  hom_inv_id := hom_inv_id
  inv_hom_id := inv_hom_id

@[simp] theorem isoOfHomInv_hom {C : Type*} [Category C] {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X)
    (h₁ : hom ≫ inv = 𝟙 X) (h₂ : inv ≫ hom = 𝟙 Y) :
    (isoOfHomInv hom inv h₁ h₂).hom = hom := rfl

/-- **The associator as an isomorphism**, from the frozen `AssociatorIso`.  Its `hom` is the
F-symbol block matrix `associatorHom` *definitionally*, which is what the naturality and
pentagon statements are about. -/
noncomputable def associatorIsoOf (S : FusionSystem n k) (h : AssociatorIso S)
    (X Y Z : FusionMat n k) :
    tensorObj S (tensorObj S X Y) Z ≅ tensorObj S X (tensorObj S Y Z) :=
  isoOfHomInv (associatorHom S X Y Z) (associatorInv S X Y Z) (h.1 X Y Z) (h.2 X Y Z)

@[simp] theorem associatorIsoOf_hom (S : FusionSystem n k) (h : AssociatorIso S)
    (X Y Z : FusionMat n k) :
    (associatorIsoOf S h X Y Z).hom = associatorHom S X Y Z := rfl

@[simp] theorem associatorIsoOf_inv (S : FusionSystem n k) (h : AssociatorIso S)
    (X Y Z : FusionMat n k) :
    (associatorIsoOf S h X Y Z).inv = associatorInv S X Y Z := rfl

/-! ## The data of the monoidal structure -/

/-- **The coherence data the assembly consumes.**

The three `Iso` families are the associator and the two unitors; the five equations are
Mathlib's `MonoidalCategory` coherence fields, stated in the `tensorHom`-primary form that
`MonoidalCategory.ofTensorHom` takes (the first is *literally* the frozen
`AssociatorNatural`). -/
structure MonoidalData (S : FusionSystem n k) (hn : 0 < n) where
  /-- The associator `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. -/
  associator : ∀ X Y Z : FusionMat n k,
    tensorObj S (tensorObj S X Y) Z ≅ tensorObj S X (tensorObj S Y Z)
  /-- The left unitor `𝟙 ⊗ X ≅ X`. -/
  leftUnitor : ∀ X : FusionMat n k, tensorObj S (unitObj hn) X ≅ X
  /-- The right unitor `X ⊗ 𝟙 ≅ X`. -/
  rightUnitor : ∀ X : FusionMat n k, tensorObj S X (unitObj hn) ≅ X
  /-- Naturality of the associator (D2's frozen `AssociatorNatural`). -/
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : FusionMat n k}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    tensorHom S (tensorHom S f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom
      = (associator X₁ X₂ X₃).hom ≫ tensorHom S f₁ (tensorHom S f₂ f₃)
  /-- Naturality of the left unitor (D4). -/
  leftUnitor_naturality : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
    tensorHom S (𝟙 (unitObj hn)) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f
  /-- Naturality of the right unitor (D4). -/
  rightUnitor_naturality : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
    tensorHom S f (𝟙 (unitObj hn)) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f
  /-- The pentagon (D3). -/
  pentagon : ∀ W X Y Z : FusionMat n k,
    tensorHom S (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensorObj S X Y) Z).hom
        ≫ tensorHom S (𝟙 W) (associator X Y Z).hom
      = (associator (tensorObj S W X) Y Z).hom ≫ (associator W X (tensorObj S Y Z)).hom
  /-- The triangle (D4). -/
  triangle : ∀ X Y : FusionMat n k,
    (associator X (unitObj hn) Y).hom ≫ tensorHom S (𝟙 X) (leftUnitor Y).hom
      = tensorHom S (rightUnitor X).hom (𝟙 Y)

namespace MonoidalData

variable {S : FusionSystem n k} {hn : 0 < n}

/-- The `MonoidalCategoryStruct` of the reconstruction: tensor and whiskerings are the landed
ones, the tensor unit is `unitObj`, and the three structural isomorphisms are the data. -/
noncomputable def toStruct (D : MonoidalData S hn) : MonoidalCategoryStruct (FusionMat n k) where
  tensorObj := tensorObj S
  whiskerLeft := fun X {_ _} g => tensorHom S (𝟙 X) g
  whiskerRight := fun {_ _} f Y => tensorHom S f (𝟙 Y)
  tensorHom := tensorHom S
  tensorUnit := unitObj hn
  associator := D.associator
  leftUnitor := D.leftUnitor
  rightUnitor := D.rightUnitor

/-- **The monoidal category instance.**  Built with `MonoidalCategory.ofTensorHom`: every
structural field (`tensorHom_def`, `id_tensorHom_id`, `tensorHom_comp_tensorHom`, the two
whisker identities) is discharged from the landed tensor lemmas, and the five coherence
fields come from the data. -/
noncomputable def toMonoidalCategory (D : MonoidalData S hn) :
    MonoidalCategory (FusionMat n k) := by
  letI : MonoidalCategoryStruct (FusionMat n k) := D.toStruct
  exact @MonoidalCategory.ofTensorHom (FusionMat n k) _ D.toStruct
    (fun X Y => tensorHom_id S X Y)
    (fun X {_ _} f => rfl)
    (fun {_ _} f Y => rfl)
    (fun f₁ f₂ g₁ g₂ => (tensorHom_comp S f₁ g₁ f₂ g₂).symm)
    (fun f₁ f₂ f₃ => D.associator_naturality f₁ f₂ f₃)
    (fun f => D.leftUnitor_naturality f)
    (fun f => D.rightUnitor_naturality f)
    (fun W X Y Z => D.pentagon W X Y Z)
    (fun X Y => D.triangle X Y)

/-- **The additivity of the tensor (Mathlib's `MonoidalPreadditive`).**  All four fields are
the entrywise bilinearity of `tensorHom` proved in `ReconMonoidalBilin.lean`; nothing about
the associator or the unitors enters. -/
theorem toMonoidalPreadditive (D : MonoidalData S hn) :
    @MonoidalPreadditive (FusionMat n k) _ _ D.toMonoidalCategory :=
  @MonoidalPreadditive.mk (FusionMat n k) _ _ D.toMonoidalCategory
    (by intro X Y Z; exact wl_zero S X) (by intro X Y Z; exact wr_zero S X)
    (by intro X Y Z f g; exact wl_add S X f g) (by intro X Y Z f g; exact wr_add S X f g)

end MonoidalData

/-! ## Building the data from the frozen statements -/

/-- Build the monoidal coherence data from the frozen associator statements plus unitor
`Iso`s, their naturalities, the pentagon and the triangle. -/
noncomputable def monoidalDataOfFrozen (S : FusionSystem n k) {hn : 0 < n}
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S)
    (lU : ∀ X : FusionMat n k, tensorObj S (unitObj hn) X ≅ X)
    (rU : ∀ X : FusionMat n k, tensorObj S X (unitObj hn) ≅ X)
    (lU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S (𝟙 (unitObj hn)) f ≫ (lU Y).hom = (lU X).hom ≫ f)
    (rU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S f (𝟙 (unitObj hn)) ≫ (rU Y).hom = (rU X).hom ≫ f)
    (pent : ∀ W X Y Z : FusionMat n k,
      tensorHom S (associatorIsoOf S hiso W X Y).hom (𝟙 Z)
          ≫ (associatorIsoOf S hiso W (tensorObj S X Y) Z).hom
          ≫ tensorHom S (𝟙 W) (associatorIsoOf S hiso X Y Z).hom
        = (associatorIsoOf S hiso (tensorObj S W X) Y Z).hom
          ≫ (associatorIsoOf S hiso W X (tensorObj S Y Z)).hom)
    (tri : ∀ X Y : FusionMat n k,
      (associatorIsoOf S hiso X (unitObj hn) Y).hom ≫ tensorHom S (𝟙 X) (lU Y).hom
        = tensorHom S (rU X).hom (𝟙 Y)) :
    MonoidalData S hn where
  associator := associatorIsoOf S hiso
  leftUnitor := lU
  rightUnitor := rU
  associator_naturality := by
    intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    simpa only [associatorIsoOf_hom] using hnat X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
  leftUnitor_naturality := lU_nat
  rightUnitor_naturality := rU_nat
  pentagon := pent
  triangle := tri

/-- **The assembly, in one statement**: from the frozen associator statements, the unitor
isomorphisms and the pentagon/triangle, the reconstruction's block model carries a monoidal
structure whose tensor is the landed one and whose associator is the F-symbol block matrix. -/
noncomputable def monoidalCategoryOfFrozen (S : FusionSystem n k) {hn : 0 < n}
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S)
    (lU : ∀ X : FusionMat n k, tensorObj S (unitObj hn) X ≅ X)
    (rU : ∀ X : FusionMat n k, tensorObj S X (unitObj hn) ≅ X)
    (lU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S (𝟙 (unitObj hn)) f ≫ (lU Y).hom = (lU X).hom ≫ f)
    (rU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S f (𝟙 (unitObj hn)) ≫ (rU Y).hom = (rU X).hom ≫ f)
    (pent : ∀ W X Y Z : FusionMat n k,
      tensorHom S (associatorIsoOf S hiso W X Y).hom (𝟙 Z)
          ≫ (associatorIsoOf S hiso W (tensorObj S X Y) Z).hom
          ≫ tensorHom S (𝟙 W) (associatorIsoOf S hiso X Y Z).hom
        = (associatorIsoOf S hiso (tensorObj S W X) Y Z).hom
          ≫ (associatorIsoOf S hiso W X (tensorObj S Y Z)).hom)
    (tri : ∀ X Y : FusionMat n k,
      (associatorIsoOf S hiso X (unitObj hn) Y).hom ≫ tensorHom S (𝟙 X) (lU Y).hom
        = tensorHom S (rU X).hom (𝟙 Y)) :
    MonoidalCategory (FusionMat n k) :=
  (monoidalDataOfFrozen S hiso hnat lU rU lU_nat rU_nat pent tri).toMonoidalCategory

/-- The additivity of the tensor for the assembled structure. -/
theorem monoidalPreadditiveOfFrozen (S : FusionSystem n k) {hn : 0 < n}
    (hiso : AssociatorIso S) (hnat : AssociatorNatural S)
    (lU : ∀ X : FusionMat n k, tensorObj S (unitObj hn) X ≅ X)
    (rU : ∀ X : FusionMat n k, tensorObj S X (unitObj hn) ≅ X)
    (lU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S (𝟙 (unitObj hn)) f ≫ (lU Y).hom = (lU X).hom ≫ f)
    (rU_nat : ∀ {X Y : FusionMat n k} (f : X ⟶ Y),
      tensorHom S f (𝟙 (unitObj hn)) ≫ (rU Y).hom = (rU X).hom ≫ f)
    (pent : ∀ W X Y Z : FusionMat n k,
      tensorHom S (associatorIsoOf S hiso W X Y).hom (𝟙 Z)
          ≫ (associatorIsoOf S hiso W (tensorObj S X Y) Z).hom
          ≫ tensorHom S (𝟙 W) (associatorIsoOf S hiso X Y Z).hom
        = (associatorIsoOf S hiso (tensorObj S W X) Y Z).hom
          ≫ (associatorIsoOf S hiso W X (tensorObj S Y Z)).hom)
    (tri : ∀ X Y : FusionMat n k,
      (associatorIsoOf S hiso X (unitObj hn) Y).hom ≫ tensorHom S (𝟙 X) (lU Y).hom
        = tensorHom S (rU X).hom (𝟙 Y)) :
    @MonoidalPreadditive (FusionMat n k) _ _
      (monoidalCategoryOfFrozen S hiso hnat lU rU lU_nat rU_nat pent tri) :=
  (monoidalDataOfFrozen S hiso hnat lU rU lU_nat rU_nat pent tri).toMonoidalPreadditive

end FusionCategory
