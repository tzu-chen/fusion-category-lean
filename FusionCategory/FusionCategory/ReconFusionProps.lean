/-
WP2 round 2, member m4, direction D5 (monoidal assembly), part (c): the property fields of
`IsFusionCategory` that the assembly owns.

Two of the four fields of `FusionCategory.IsFusionCategory` (`Statements2.lean` §1) are
*unconditional* on the canonical scaffold and are proved here, with no monoidal structure
assumed at all:

* `hom_finite` — `Hom X Y` is `∀ i, Matrix (X.blk i) (Y.blk i) k`, a finite product of finite
  matrix spaces, so it is finite-dimensional;
* `end_unit` — `End (unitObj hn) ≃+* k`: the endomorphism ring of the unit object is `k`,
  read as the `(0,0)` entry at the unit label.  This is the map the categorical trace of
  Task 2.2 is read through (`WP2.trDualScalar`), so it is the interface D7 consumes.

Both are stated for `FusionCategory.FusionMat` (the canonical block-carrying scaffold), not
the literal `WP2.FusionMat` model.

The third item is the assembly lemma `isFusionCategoryOf`: `IsFusionCategory k (FusionMat n k)`
from the two remaining fields (simples and decomposition — D1's layer) in an abstract
monoidal/rigid/biproduct context, so that once D1–D4 land the predicate follows with no
further work.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconUnit
import FusionCategory.ReconAssocStatements
import FusionCategory.ReconMonoidal
import FusionCategory.Statements2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory CategoryTheory.Limits

variable {n : ℕ} {k : Type u} [Field k]

/-! ## `Hom` is finite-dimensional -/

/-- **`hom_finite`.**  A hom of the reconstruction is a finite tuple of finite matrices. -/
theorem homFiniteDimensional (X Y : FusionMat n k) : FiniteDimensional k (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional k (∀ i, Matrix (X.blk i) (Y.blk i) k))

/-- The same, as an instance (so that `IsFusionCategory.hom_finite` is `inferInstance`). -/
instance instHomFiniteDimensional (X Y : FusionMat n k) : FiniteDimensional k (X ⟶ Y) :=
  homFiniteDimensional X Y

/-! ## `End 𝟙 = k` -/

/-- The unit block is one-dimensional. -/
theorem card_unitObj_blk (hn : 0 < n) :
    Fintype.card ((unitObj (k := k) hn).blk ⟨0, hn⟩) = 1 := by
  show Fintype.card (Fin (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then 1 else 0)) = 1
  simp

/-- The unit block is a singleton. -/
theorem subsingleton_unitObj_blk (hn : 0 < n) :
    Subsingleton ((unitObj (k := k) hn).blk ⟨0, hn⟩) :=
  Fintype.card_le_one_iff_subsingleton.mp (by rw [card_unitObj_blk hn])

/-- A non-unit block of the unit object is empty. -/
theorem card_unitObj_blk_ne (hn : 0 < n) {i : Fin n} (hi : i ≠ ⟨0, hn⟩) :
    Fintype.card ((unitObj (k := k) hn).blk i) = 0 := by
  show Fintype.card (Fin (if i = (⟨0, hn⟩ : Fin n) then 1 else 0)) = 0
  simp [hi]

/-- A non-unit block of the unit object carries only the zero matrix. -/
theorem subsingleton_matrix_unitObj_blk_ne (hn : 0 < n) {i : Fin n} (hi : i ≠ ⟨0, hn⟩) :
    Subsingleton (Matrix ((unitObj (k := k) hn).blk i) ((unitObj (k := k) hn).blk i) k) := by
  have h := card_unitObj_blk_ne (k := k) hn hi
  haveI : IsEmpty ((unitObj (k := k) hn).blk i) := Fintype.card_eq_zero_iff.mp h
  infer_instance

/-- A chosen element of the (one-point) unit block. -/
noncomputable def unitObjPt (hn : 0 < n) : (unitObj (k := k) hn).blk ⟨0, hn⟩ :=
  (Fintype.card_pos_iff.mp (by rw [card_unitObj_blk hn]; norm_num)).some

/-- **`end_unit`.**  The endomorphisms of the unit object are `k`, read as the `(0,0)` entry
at the unit label.  Every other label contributes the zero matrix (its block is empty). -/
noncomputable def endUnitEquiv (hn : 0 < n) :
    End (unitObj (k := k) hn) ≃+* k where
  toFun f := f ⟨0, hn⟩ (unitObjPt hn) (unitObjPt hn)
  invFun a := fun i => if i = ⟨0, hn⟩ then fun _ _ => a else 0
  left_inv f := by
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      ext a b
      haveI := subsingleton_unitObj_blk (k := k) hn
      rw [Subsingleton.elim a (unitObjPt hn), Subsingleton.elim b (unitObjPt hn)]
      simp
    · haveI := subsingleton_matrix_unitObj_blk_ne (k := k) hn hi
      exact Subsingleton.elim _ _
  right_inv a := by
    simp
  map_add' f g := rfl
  map_mul' f g := by
    haveI := subsingleton_unitObj_blk (k := k) hn
    show (g ⟨0, hn⟩ * f ⟨0, hn⟩) (unitObjPt hn) (unitObjPt hn)
      = f ⟨0, hn⟩ (unitObjPt hn) (unitObjPt hn) * g ⟨0, hn⟩ (unitObjPt hn) (unitObjPt hn)
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single (unitObjPt hn) ?_ ?_).trans ?_
    · intro b _ hb
      exact absurd (Subsingleton.elim b (unitObjPt hn)) hb
    · intro h; exact absurd (Finset.mem_univ _) h
    · rw [mul_comm]

@[simp] theorem endUnitEquiv_apply (hn : 0 < n) (f : End (unitObj (k := k) hn)) :
    endUnitEquiv hn f = f ⟨0, hn⟩ (unitObjPt hn) (unitObjPt hn) := rfl

/-! ## The `IsFusionCategory` assembly -/

/-- The tensor unit of the assembled structure is `unitObj hn` — definitionally, so the
`end_unit` field below is an `rfl`-level match. -/
theorem MonoidalData.toStruct_tensorUnit {S : FusionSystem n k} {hn : 0 < n}
    (D : MonoidalData S hn) :
    @MonoidalCategoryStruct.tensorUnit (FusionMat n k) _ D.toStruct = unitObj hn := rfl

/-- The tensor of the assembled structure is the landed tensor. -/
theorem MonoidalData.toStruct_tensorObj {S : FusionSystem n k} {hn : 0 < n}
    (D : MonoidalData S hn) :
    @MonoidalCategoryStruct.tensorObj (FusionMat n k) _ D.toStruct = tensorObj S := rfl

/-- **`end_unit` for the assembled structure**: the unit endomorphism ring is `k`. -/
theorem endUnitEquivOfData {S : FusionSystem n k} {hn : 0 < n} (D : MonoidalData S hn) :
    Nonempty (End (@MonoidalCategoryStruct.tensorUnit (FusionMat n k) _ D.toStruct) ≃+* k) :=
  (MonoidalData.toStruct_tensorUnit D) ▸ ⟨endUnitEquiv hn⟩


/-- **The predicate, assembled.**  In any context where the canonical scaffold carries the
seven Mathlib structures (as instances), `IsFusionCategory k (FusionMat n k)` follows from
the two remaining property fields — finitely many simples (D1) and the decomposition of every
object into simples (D1) — together with the `End 𝟙 = k` of the given monoidal structure.

`hom_finite` is discharged here unconditionally (`homFiniteDimensional`). -/
theorem isFusionCategoryOf
    [MonoidalCategory (FusionMat n k)] [MonoidalPreadditive (FusionMat n k)]
    [RigidCategory (FusionMat n k)] [HasFiniteBiproducts (FusionMat n k)]
    (end_unit : Nonempty (End (𝟙_ (FusionMat n k)) ≃+* k))
    (simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
      ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i))
    (decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
      (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)) :
    IsFusionCategory k (FusionMat n k) where
  hom_finite X Y := homFiniteDimensional X Y
  end_unit := end_unit
  simples_fin := simples_fin
  decomposition := decomposition


/-- **The predicate, assembled with the reconstruction's unit.**  Same as
`isFusionCategoryOf`, but the `End 𝟙 = k` field is discharged from `endUnitEquiv` under the
hypothesis that the tensor unit is the reconstruction's `unitObj hn` (true by `rfl` for the
assembled structure, `MonoidalData.toStruct_tensorUnit`). -/
theorem isFusionCategoryOfUnit {hn : 0 < n}
    [MonoidalCategory (FusionMat n k)] [MonoidalPreadditive (FusionMat n k)]
    [RigidCategory (FusionMat n k)] [HasFiniteBiproducts (FusionMat n k)]
    (hUnit : (𝟙_ (FusionMat n k)) = unitObj hn)
    (simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
      ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i))
    (decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
      (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)) :
    IsFusionCategory k (FusionMat n k) :=
  isFusionCategoryOf (end_unit := hUnit ▸ ⟨endUnitEquiv hn⟩)
    simples_fin decomposition

/-! ## The bridge to the frozen literal model

`Statements2.WP2.FusionMat` is the *literal* model (a multiplicity vector only); the canonical
scaffold `FusionCategory.FusionMat` carries the per-label block types.  `ofM` embeds the
literal model.  The kernel-checked facts below record exactly how far the embedding goes — they
matter because the frozen `WP2.ReconFusion` names the literal model:

* on the image of `ofM` the two hom-types agree *definitionally* (first theorem), so the
  category structure restricts;
* but the tensor leaves the image: `tensorObj` of two `ofM`-objects has the channel-refined Σ
  block type, not `Fin` of the convolution (`tensorObj_ofM_blk`), with the cardinalities
  agreeing (`tensorObj_ofM_card`).  So a monoidal structure on the canonical scaffold does not
  restrict to one on the literal model; the refinement is carried by the block types. -/

section Bridge

/-- On the image of `ofM`, the canonical hom-type and the frozen literal hom-type agree
definitionally. -/
theorem ofM_hom_eq (m m' : Fin n → ℕ) :
    (FusionMat.ofM (k := k) m ⟶ FusionMat.ofM (k := k) m')
      = WP2.Hom (k := k) (⟨m⟩ : WP2.FusionMat n k) ⟨m'⟩ := rfl

/-- The block type of the tensor of two `ofM`-objects is the channel refinement, not a `Fin`. -/
theorem tensorObj_ofM_blk (S : FusionSystem n k) (m m' : Fin n → ℕ) (c : Fin n) :
    (tensorObj S (FusionMat.ofM (k := k) m) (FusionMat.ofM (k := k) m')).blk c
      = Σ p : Fin n × Fin n, Fin (S.ring.N p.1 p.2 c) × Fin (m p.1) × Fin (m' p.2) := rfl

/-- The refinement has the cardinality of the convolution: it is a refinement, not a change of
the multiplicity vector. -/
theorem tensorObj_ofM_card (S : FusionSystem n k) (m m' : Fin n → ℕ) (c : Fin n) :
    Fintype.card (Σ p : Fin n × Fin n, Fin (S.ring.N p.1 p.2 c) × Fin (m p.1) × Fin (m' p.2))
      = ∑ p : Fin n × Fin n, S.ring.N p.1 p.2 c * m p.1 * m' p.2 := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, mul_assoc]

end Bridge

end FusionCategory
