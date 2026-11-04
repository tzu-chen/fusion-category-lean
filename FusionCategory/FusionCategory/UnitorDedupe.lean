/-
WP2 round 3, member m7, direction D6 (freeze revision and dedupe), part (b):
the unitor dedupe.

Two independent developments of the unitors of the reconstruction exist:

* `FusionCategory.Units.*` (`FusionCategory/ReconUnitors.lean`, round 2, m5):
  `leftUnitor`, `leftUnitorInv`, `rightUnitor`, `rightUnitorInv`, the four round
  trips, both naturalities, the `Iso`s, and the triangle identity.  It is built
  through the canonical *block equivalence* `leftIdxEquiv`/`rightIdxEquiv`
  (`TensorIdx 𝟙 X c ≃ X.blk c`) and the graph matrix of that equivalence.
* `FusionCategory.FusionMat.leftUnitor`/`rightUnitor`
  (`FusionCategory/ReconRigid.lean`, round 2, m6): the delta matrix at the
  canonical index `unitIdxL`/`unitIdxR`, with `mul_leftUnitor`/`mul_rightUnitor`
  (the absorption lemmas the snake collapse consumes) but *no* inverses and *no*
  naturality.

This file records the dedupe: **`Units` is the home** (it is the only one of the
two carrying the `Iso`s, the inverses and the coherence), and the `FusionMat`
copy is *definitionally determined* by it — the two homs are equal as matrices,
the `Units` inverse is a two-sided inverse of the `FusionMat` hom, and hence the
frozen snake statements are unchanged whether they are written with one or the
other.  Nothing in `ReconRigid`/`ReconSnake` needs to change; a proof of a snake
in the `FusionMat` shape transports verbatim to the `Units` shape (M5's
`MonoidalCategory` consumes `Units`).

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconRigid
import FusionCategory.ReconUnitors
import FusionCategory.ReconSnake

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

namespace UnitorDedupe

/-! ## The two canonical indices agree

`FusionMat.unitIdxL`/`unitIdxR` are written out by hand (`⟨0, …⟩` for the
channel and the unit-block point); `Units.leftIdxEquiv`/`rightIdxEquiv` are
equivalences whose inverse is the same handwritten tuple.  The two agree. -/

/-- The `FusionMat` left canonical index is the inverse block identification of
`Units`. -/
theorem unitIdxL_eq_symm (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k)
    (c : Fin n) (j : X.blk c) :
    FusionMat.unitIdxL S hn X c j = (Units.leftIdxEquiv S hn X c).symm j := by
  rw [Units.leftIdxEquiv_symm_apply]
  rfl

/-- The `FusionMat` right canonical index is the inverse block identification of
`Units`. -/
theorem unitIdxR_eq_symm (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k)
    (c : Fin n) (j : X.blk c) :
    FusionMat.unitIdxR S hn X c j = (Units.rightIdxEquiv S hn X c).symm j := by
  rw [Units.rightIdxEquiv_symm_apply]
  rfl

/-- The block identification sends the `FusionMat` canonical index to the block
index. -/
theorem leftIdxEquiv_unitIdxL (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k)
    (c : Fin n) (j : X.blk c) :
    Units.leftIdxEquiv S hn X c (FusionMat.unitIdxL S hn X c j) = j := by
  rw [unitIdxL_eq_symm, Equiv.apply_symm_apply]

/-- The block identification sends the `FusionMat` canonical index to the block
index. -/
theorem rightIdxEquiv_unitIdxR (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k)
    (c : Fin n) (j : X.blk c) :
    Units.rightIdxEquiv S hn X c (FusionMat.unitIdxR S hn X c j) = j := by
  rw [unitIdxR_eq_symm, Equiv.apply_symm_apply]

/-! ## The unitor homs agree -/

/-- **The dedupe of the left unitor.**  Round 2's two left unitors are the same
morphism: `Units`'s graph matrix of the block equivalence, and `FusionMat`'s
delta matrix at the canonical index. -/
theorem leftUnitor_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    Units.leftUnitor S hn X = FusionMat.leftUnitor S hn X := by
  funext c r j
  simp only [Units.leftUnitor, Units.graphMat, FusionMat.leftUnitor, Matrix.of_apply]
  by_cases h : r = FusionMat.unitIdxL S hn X c j
  · rw [if_pos h, if_pos (by rw [h, leftIdxEquiv_unitIdxL])]
  · rw [if_neg h, if_neg]
    intro hh
    refine h ?_
    rw [unitIdxL_eq_symm, ← hh]
    exact (Equiv.symm_apply_apply (Units.leftIdxEquiv S hn X c) r).symm

/-- **The dedupe of the right unitor.** -/
theorem rightUnitor_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    Units.rightUnitor S hn X = FusionMat.rightUnitor S hn X := by
  funext c r j
  simp only [Units.rightUnitor, Units.graphMat, FusionMat.rightUnitor, Matrix.of_apply]
  by_cases h : r = FusionMat.unitIdxR S hn X c j
  · rw [if_pos h, if_pos (by rw [h, rightIdxEquiv_unitIdxR])]
  · rw [if_neg h, if_neg]
    intro hh
    refine h ?_
    rw [unitIdxR_eq_symm, ← hh]
    exact (Equiv.symm_apply_apply (Units.rightIdxEquiv S hn X c) r).symm

/-! ## The `Units` inverses invert the `FusionMat` homs

`ReconRigid` defines only the homs, so the compatibility on the inverse side is
stated as: `Units`'s inverse is a two-sided inverse of `FusionMat`'s hom.  This
is exactly what a snake proof written against `FusionMat.leftUnitor` needs in
order to compose into `MonoidalCategory`'s `Iso`-valued unitors. -/

theorem leftUnitor_comp_leftUnitorInv (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.leftUnitor S hn X ≫ Units.leftUnitorInv S hn X
      = 𝟙 (tensorObj S (unitObj hn) X) := by
  rw [← leftUnitor_eq]
  exact Units.leftUnitor_comp_inv S hn X

theorem leftUnitorInv_comp_leftUnitor (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    Units.leftUnitorInv S hn X ≫ FusionMat.leftUnitor S hn X = 𝟙 X := by
  rw [← leftUnitor_eq]
  exact Units.leftUnitorInv_comp S hn X

theorem rightUnitor_comp_rightUnitorInv (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.rightUnitor S hn X ≫ Units.rightUnitorInv S hn X
      = 𝟙 (tensorObj S X (unitObj hn)) := by
  rw [← rightUnitor_eq]
  exact Units.rightUnitor_comp_inv S hn X

theorem rightUnitorInv_comp_rightUnitor (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    Units.rightUnitorInv S hn X ≫ FusionMat.rightUnitor S hn X = 𝟙 X := by
  rw [← rightUnitor_eq]
  exact Units.rightUnitorInv_comp S hn X

/-- The home `Iso`'s hom is the `FusionMat` unitor. -/
theorem leftUnitorIso_hom_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    (Units.leftUnitorIso S hn X).hom = FusionMat.leftUnitor S hn X :=
  leftUnitor_eq S hn X

/-- The home `Iso`'s hom is the `FusionMat` unitor. -/
theorem rightUnitorIso_hom_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    (Units.rightUnitorIso S hn X).hom = FusionMat.rightUnitor S hn X :=
  rightUnitor_eq S hn X

/-! ## The snake statements are unchanged by the dedupe

The frozen `FusionMat.SnakeLeft`/`SnakeRight` (`ReconSnake.lean`) are stated with
`FusionMat`'s unitors; `MonoidalData`'s associator/unitor data and the triangle
are stated with `Units`'s.  By the equalities above the two forms of each snake
are *the same proposition*, so a proof in either shape is a proof of the frozen
statement. -/

/-- The left snake with the home (`Units`) unitors. -/
def SnakeLeftUnits (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    whiskerRight S (FusionMat.coev S hn X) X
        ≫ associatorHom S X (FusionMat.dual S X) X
        ≫ whiskerLeft S X (FusionMat.ev S hn X) ≫ Units.rightUnitor S hn X
      = Units.leftUnitor S hn X

/-- The right snake with the home (`Units`) unitors. -/
def SnakeRightUnits (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
        ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
        ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X)
        ≫ Units.leftUnitor S hn (FusionMat.dual S X)
      = Units.rightUnitor S hn (FusionMat.dual S X)

/-- **The frozen left snake is the home-form left snake.** -/
theorem snakeLeft_iff_units (S : FusionSystem n k) :
    FusionMat.SnakeLeft S ↔ SnakeLeftUnits S := by
  constructor
  · intro h hn X
    rw [leftUnitor_eq, rightUnitor_eq]
    exact h hn X
  · intro h hn X
    have h' := h hn X
    rw [leftUnitor_eq, rightUnitor_eq] at h'
    exact h'

/-- **The frozen right snake is the home-form right snake.** -/
theorem snakeRight_iff_units (S : FusionSystem n k) :
    FusionMat.SnakeRight S ↔ SnakeRightUnits S := by
  constructor
  · intro h hn X
    rw [leftUnitor_eq, rightUnitor_eq]
    exact h hn X
  · intro h hn X
    have h' := h hn X
    rw [leftUnitor_eq, rightUnitor_eq] at h'
    exact h'

/-- **The dedupe record**, in one statement: the two developments agree on the
homs, the home's inverse inverts the copy's hom on both sides, and the frozen
snakes are the home-form snakes. -/
theorem unitor_dedupe (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    Units.leftUnitor S hn X = FusionMat.leftUnitor S hn X
  ∧ Units.rightUnitor S hn X = FusionMat.rightUnitor S hn X
  ∧ (FusionMat.leftUnitor S hn X ≫ Units.leftUnitorInv S hn X
      = 𝟙 (tensorObj S (unitObj hn) X))
  ∧ (Units.leftUnitorInv S hn X ≫ FusionMat.leftUnitor S hn X = 𝟙 X)
  ∧ (FusionMat.rightUnitor S hn X ≫ Units.rightUnitorInv S hn X
      = 𝟙 (tensorObj S X (unitObj hn)))
  ∧ (Units.rightUnitorInv S hn X ≫ FusionMat.rightUnitor S hn X = 𝟙 X) :=
  ⟨leftUnitor_eq S hn X, rightUnitor_eq S hn X,
    leftUnitor_comp_leftUnitorInv S hn X, leftUnitorInv_comp_leftUnitor S hn X,
    rightUnitor_comp_rightUnitorInv S hn X, rightUnitorInv_comp_rightUnitor S hn X⟩

/-! ## The frozen snakes are Mathlib's `ExactPairing` triangles

Mathlib's rigidity (`Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`) asks for

  `ExactPairing.evaluation_coevaluation' :
      eta_X ▷ X ≫ (α_ X Y X).hom ≫ X ◁ eps_X = (λ_ X).hom ≫ (ρ_ X).inv`
  `ExactPairing.coevaluation_evaluation' :
      eta_Y ◁ Y ≫ (α_ Y X Y).inv ≫ eps_Y ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv`

(for `Y = X*`; `α_` is `(X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)`, which is the direction of
`associatorHom` here).  The frozen `FusionMat.SnakeLeft`/`SnakeRight` keep one unitor on the
*outside*:

  `A_X ≫ ρ_X = λ_X`  and  `B_X ≫ λ_{X*} = ρ_{X*}`.

The two forms are the same proposition: the conversion is a cancellation of an `Iso`
(`Units.rightUnitorInv_comp`, `Units.leftUnitorInv_comp`), with no `F`-entry, no sum and no
coherence.  This is the shape a rigidity packaging consumes, so it is recorded here with the
frozen statements as the source of truth. -/

/-- Mathlib's `ExactPairing.evaluation_coevaluation'` for the pair `(X, X*)`, written in the
reconstruction's matrix notation. -/
def TriangleLeft (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) : Prop :=
  whiskerRight S (FusionMat.coev S hn X) X ≫ associatorHom S X (FusionMat.dual S X) X
      ≫ whiskerLeft S X (FusionMat.ev S hn X)
    = Units.leftUnitor S hn X ≫ Units.rightUnitorInv S hn X

/-- Mathlib's `ExactPairing.coevaluation_evaluation'` for the pair `(X*, X)`, written in the
reconstruction's matrix notation. -/
def TriangleRight (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) : Prop :=
  whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
      ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
      ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X)
    = Units.rightUnitor S hn (FusionMat.dual S X)
      ≫ Units.leftUnitorInv S hn (FusionMat.dual S X)

/-- The left triangle in the shape the frozen statement uses (all `hn` and `X`). -/
def TriangleLeftAll (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k), TriangleLeft S hn X

/-- The right triangle in the shape the frozen statement uses. -/
def TriangleRightAll (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k), TriangleRight S hn X

/-- **The frozen left snake is Mathlib's `evaluation_coevaluation'` triangle**, pointwise.

The two composites are the same morphism followed by `(ρ_ X)`; the frozen statement keeps that
unitor on the outside, Mathlib's `ExactPairing.evaluation_coevaluation'` puts `(λ_ X)` and
`(ρ_ X)⁻¹` on the other side.  The conversion is the unitors' two-sided inverse, and nothing
else. -/
theorem snakeLeft_triangle_pointwise (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    (whiskerRight S (FusionMat.coev S hn X) X ≫ associatorHom S X (FusionMat.dual S X) X
        ≫ whiskerLeft S X (FusionMat.ev S hn X) ≫ FusionMat.rightUnitor S hn X
      = FusionMat.leftUnitor S hn X)
    ↔ TriangleLeft S hn X := by
  unfold TriangleLeft
  constructor
  · intro h
    have h1 : (whiskerRight S (FusionMat.coev S hn X) X
          ≫ associatorHom S X (FusionMat.dual S X) X
          ≫ whiskerLeft S X (FusionMat.ev S hn X)) ≫ Units.rightUnitor S hn X
        = Units.leftUnitor S hn X := by
      simpa only [Category.assoc, rightUnitor_eq, leftUnitor_eq] using h
    calc whiskerRight S (FusionMat.coev S hn X) X ≫ associatorHom S X (FusionMat.dual S X) X
          ≫ whiskerLeft S X (FusionMat.ev S hn X)
        = ((whiskerRight S (FusionMat.coev S hn X) X
            ≫ associatorHom S X (FusionMat.dual S X) X
            ≫ whiskerLeft S X (FusionMat.ev S hn X))
            ≫ Units.rightUnitor S hn X) ≫ Units.rightUnitorInv S hn X := by
            rw [Category.assoc, Units.rightUnitor_comp_inv, Category.comp_id]
      _ = Units.leftUnitor S hn X ≫ Units.rightUnitorInv S hn X := by rw [h1]
  · intro h
    have h1 : (whiskerRight S (FusionMat.coev S hn X) X
          ≫ associatorHom S X (FusionMat.dual S X) X
          ≫ whiskerLeft S X (FusionMat.ev S hn X)) ≫ Units.rightUnitor S hn X
        = Units.leftUnitor S hn X := by
      rw [h, Category.assoc, Units.rightUnitorInv_comp, Category.comp_id]
    simpa only [Category.assoc, rightUnitor_eq, leftUnitor_eq] using h1

/-- **The frozen right snake is Mathlib's `coevaluation_evaluation'` triangle**, pointwise. -/
theorem snakeRight_triangle_pointwise (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    (whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
        ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
        ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X)
        ≫ FusionMat.leftUnitor S hn (FusionMat.dual S X)
      = FusionMat.rightUnitor S hn (FusionMat.dual S X))
    ↔ TriangleRight S hn X := by
  unfold TriangleRight
  constructor
  · intro h
    have h1 : (whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
          ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
          ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X))
          ≫ Units.leftUnitor S hn (FusionMat.dual S X)
        = Units.rightUnitor S hn (FusionMat.dual S X) := by
      simpa only [Category.assoc, rightUnitor_eq, leftUnitor_eq] using h
    calc whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
          ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
          ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X)
        = ((whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
            ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
            ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X))
            ≫ Units.leftUnitor S hn (FusionMat.dual S X))
            ≫ Units.leftUnitorInv S hn (FusionMat.dual S X) := by
            rw [Category.assoc, Units.leftUnitor_comp_inv, Category.comp_id]
      _ = Units.rightUnitor S hn (FusionMat.dual S X)
            ≫ Units.leftUnitorInv S hn (FusionMat.dual S X) := by rw [h1]
  · intro h
    have h1 : (whiskerLeft S (FusionMat.dual S X) (FusionMat.coev S hn X)
          ≫ associatorInv S (FusionMat.dual S X) X (FusionMat.dual S X)
          ≫ whiskerRight S (FusionMat.ev S hn X) (FusionMat.dual S X))
          ≫ Units.leftUnitor S hn (FusionMat.dual S X)
        = Units.rightUnitor S hn (FusionMat.dual S X) := by
      rw [h, Category.assoc, Units.leftUnitorInv_comp, Category.comp_id]
    simpa only [Category.assoc, rightUnitor_eq, leftUnitor_eq] using h1

/-- **The frozen left snake is Mathlib's `evaluation_coevaluation'` triangle**, in the shape of
the frozen statement (all `hn`, `X`). -/
theorem snakeLeft_iff_triangleLeft (S : FusionSystem n k) :
    FusionMat.SnakeLeft S ↔ TriangleLeftAll S :=
  ⟨fun h hn X => (snakeLeft_triangle_pointwise S hn X).mp (h hn X),
   fun h hn X => (snakeLeft_triangle_pointwise S hn X).mpr (h hn X)⟩

/-- **The frozen right snake is Mathlib's `coevaluation_evaluation'` triangle**, in the shape of
the frozen statement. -/
theorem snakeRight_iff_triangleRight (S : FusionSystem n k) :
    FusionMat.SnakeRight S ↔ TriangleRightAll S :=
  ⟨fun h hn X => (snakeRight_triangle_pointwise S hn X).mp (h hn X),
   fun h hn X => (snakeRight_triangle_pointwise S hn X).mpr (h hn X)⟩

/-! ## The `ReconSnake` copy: the inverses, the `Iso`s and the iso-form snake

`FusionCategory/ReconSnake.lean` (also namespace `FusionMat`) carries a *third* piece of the
same development: the transposed delta matrices `leftUnitorInv`/`rightUnitorInv`, the `Iso`s
`leftUnitorIso`/`rightUnitorIso`, and the **iso-form** snake `SnakeLeftIso`
(`λ⁻¹ ≫ (coev ⊗ 1) ≫ α ≫ (1 ⊗ ev) ≫ ρ = 𝟙`).  It agrees with `Units` on the nose, so the
dedupe closes: the home `Units` inverses are the `ReconSnake` inverses, the home `Iso`s are the
`ReconSnake` `Iso`s, and the iso-form snake is the home-form snake. -/

/-- The `ReconSnake` left inverse is the home left inverse. -/
theorem leftUnitorInv_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.leftUnitorInv S hn X = Units.leftUnitorInv S hn X := by
  funext c j r
  simp only [FusionMat.leftUnitorInv, Matrix.of_apply, Units.leftUnitorInv, Units.graphMatInv]
  by_cases h : r = FusionMat.unitIdxL S hn X c j
  · rw [if_pos h, if_pos (by rw [h, leftIdxEquiv_unitIdxL])]
  · rw [if_neg h, if_neg]
    intro hh
    refine h ?_
    rw [unitIdxL_eq_symm, ← hh]
    exact (Equiv.symm_apply_apply (Units.leftIdxEquiv S hn X c) r).symm

/-- The `ReconSnake` right inverse is the home right inverse. -/
theorem rightUnitorInv_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.rightUnitorInv S hn X = Units.rightUnitorInv S hn X := by
  funext c j r
  simp only [FusionMat.rightUnitorInv, Matrix.of_apply, Units.rightUnitorInv, Units.graphMatInv]
  by_cases h : r = FusionMat.unitIdxR S hn X c j
  · rw [if_pos h, if_pos (by rw [h, rightIdxEquiv_unitIdxR])]
  · rw [if_neg h, if_neg]
    intro hh
    refine h ?_
    rw [unitIdxR_eq_symm, ← hh]
    exact (Equiv.symm_apply_apply (Units.rightIdxEquiv S hn X c) r).symm

/-- The `ReconSnake` left unitor `Iso` is the home `Iso`. -/
theorem leftUnitorIso_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.leftUnitorIso S hn X = Units.leftUnitorIso S hn X :=
  Iso.ext (leftUnitor_eq S hn X).symm

/-- The `ReconSnake` right unitor `Iso` is the home `Iso`. -/
theorem rightUnitorIso_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    FusionMat.rightUnitorIso S hn X = Units.rightUnitorIso S hn X :=
  Iso.ext (rightUnitor_eq S hn X).symm

/-- **The iso-form snake is the home-form snake**: `ReconSnake`'s `SnakeLeftIso`
(`λ⁻¹ ≫ (coev ⊗ 1) ≫ α ≫ (1 ⊗ ev) ≫ ρ = 𝟙`) is the same proposition as the home-form
`SnakeLeftUnits`. -/
theorem snakeLeftIso_iff_units (S : FusionSystem n k) :
    FusionMat.SnakeLeftIso S ↔ SnakeLeftUnits S :=
  (FusionMat.snakeLeft_iff_iso S).symm.trans (snakeLeft_iff_units S)

end UnitorDedupe

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.UnitorDedupe.unitIdxL_eq_symm
#print axioms FusionCategory.UnitorDedupe.unitIdxR_eq_symm
#print axioms FusionCategory.UnitorDedupe.leftIdxEquiv_unitIdxL
#print axioms FusionCategory.UnitorDedupe.rightIdxEquiv_unitIdxR
#print axioms FusionCategory.UnitorDedupe.leftUnitor_eq
#print axioms FusionCategory.UnitorDedupe.rightUnitor_eq
#print axioms FusionCategory.UnitorDedupe.leftUnitor_comp_leftUnitorInv
#print axioms FusionCategory.UnitorDedupe.leftUnitorInv_comp_leftUnitor
#print axioms FusionCategory.UnitorDedupe.rightUnitor_comp_rightUnitorInv
#print axioms FusionCategory.UnitorDedupe.rightUnitorInv_comp_rightUnitor
#print axioms FusionCategory.UnitorDedupe.leftUnitorIso_hom_eq
#print axioms FusionCategory.UnitorDedupe.rightUnitorIso_hom_eq
#print axioms FusionCategory.UnitorDedupe.SnakeLeftUnits
#print axioms FusionCategory.UnitorDedupe.SnakeRightUnits
#print axioms FusionCategory.UnitorDedupe.snakeLeft_iff_units
#print axioms FusionCategory.UnitorDedupe.snakeRight_iff_units
#print axioms FusionCategory.UnitorDedupe.unitor_dedupe
#print axioms FusionCategory.UnitorDedupe.TriangleLeft
#print axioms FusionCategory.UnitorDedupe.TriangleRight
#print axioms FusionCategory.UnitorDedupe.TriangleLeftAll
#print axioms FusionCategory.UnitorDedupe.TriangleRightAll
#print axioms FusionCategory.UnitorDedupe.snakeLeft_triangle_pointwise
#print axioms FusionCategory.UnitorDedupe.snakeRight_triangle_pointwise
#print axioms FusionCategory.UnitorDedupe.snakeLeft_iff_triangleLeft
#print axioms FusionCategory.UnitorDedupe.snakeRight_iff_triangleRight
#print axioms FusionCategory.UnitorDedupe.leftUnitorInv_eq
#print axioms FusionCategory.UnitorDedupe.rightUnitorInv_eq
#print axioms FusionCategory.UnitorDedupe.leftUnitorIso_eq
#print axioms FusionCategory.UnitorDedupe.rightUnitorIso_eq
#print axioms FusionCategory.UnitorDedupe.snakeLeftIso_iff_units
