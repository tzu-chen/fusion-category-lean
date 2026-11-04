/-
WP2 round 3, member m7, direction D6 (freeze revision and dedupe), part (a):
the restated reconstruction freeze `ReconFusionCanonical`.

## What is being revised, and why

`Statements2.WP2.ReconFusion` (the Round-1 freeze, `FusionCategory/Statements2.lean`
§2) states the reconstruction theorem about the **literal model**
`WP2.FusionMat n k`, whose objects are bare multiplicity vectors
`m : Fin n → ℕ` and whose morphisms are `WP2.Hom X Y = ∀ i, Matrix (Fin (X.m i))
(Fin (Y.m i)) k`.  Rounds 1–2 built (and Round 3 is proving) the reconstruction on
the **canonical scaffold** `FusionCategory.FusionMat n k` (`Recon.lean`), whose
objects carry the *block index types* as data (`m`, `blk`, `card_blk`), and all of
whose morphism-level results — the tensor `tensorHom`, the associator
`associatorHom`, the unitors, `ev`/`coev`, the snakes, the trace correspondence —
are stated about the block types.

The two models agree at the level of multiplicities (`FusionMat.ofM` embeds the
literal model, `ofM_m`, `ofM_hom_eq`) but **not at the level of blocks**: the
canonical tensor's block at `c` is the channel refinement

  `(ofM m ⊗ ofM m').blk c = Σ p : Fin n × Fin n, Fin (N p.1 p.2 c) × Fin (m p.1) × Fin (m' p.2)`

*definitionally* (`ReconFusionProps.tensorObj_ofM_blk`, re-derived below as
`tensorObj_ofM_blk_shape`), whereas every literal-model object has `Fin`-shaped
blocks (`ofM_blk_shape`).  So `ofM` is **not** a strict monoidal functor on
objects, and a monoidal structure on the literal model cannot be *the* canonical
one: the identification `(X ⊗ Y).blk c ≃ Fin ((X ⊗ Y).m c)` that the literal
model's `Hom`-type forces is an extra, non-canonical choice (an offset
embedding), and along it none of the round's morphism-level proofs transport
definitionally.  That is the recorded Round-2 finding; it is not a refutation of
the literal freeze (nothing here proves it uninhabitable), it is the reason the
freeze cannot be *discharged by* the landed work.

## What the revision says

`ReconFusionCanonical S hn` is the same field list, stated where the blocks live:

* the three object-level identifications of the frozen literal freeze keep their
  **exact shapes** — the tensor's multiplicity is the fusion-ring convolution
  (here as an equality of *objects*, which pins the block types too, so it is
  strictly stronger than the literal `m`-level field: `tensorObj_eq`), the unit is
  the vector supported at the unit label (`tensorUnit_eq`), and the right dual is
  the duality relabelling (`rightDual_m`, verbatim);
* the combinatorial field `fusion : IsFusionCategory k (FusionMat n k)` is
  unchanged in content, now about the scaffold the proofs are about;
* the category/preadditive/linear structures are **not** fields.  On the
  canonical scaffold those are unconditional global instances (Round 1,
  `Recon.lean`); re-quantifying them would only create instance diamonds.

`ReconIsFusionCanonical S hn := Nonempty (ReconFusionCanonical S hn)` is the
revised success criterion.  `reconFusionCanonical_of_residual` reduces it to the
round's remaining obligations, named one by one (`Residual`), and
`toLiteralImageFields` shows the revision *implies* the frozen literal freeze's
three object-level field equations at the image of `ofM` — the revision is a
strengthening of the freeze, not a change of subject.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconFusionProps
import FusionCategory.ReconAssembly
import FusionCategory.ReconAssocIso
import FusionCategory.ReconRigid
import FusionCategory.Statements2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory CategoryTheory.Limits

variable {n : ℕ} {k : Type u} [Field k]

namespace WP2Canon

/-! ## The revised freeze -/

/-- **The restated reconstruction freeze** (revision of `WP2Canon.ReconFusion`, stated on the
canonical scaffold `FusionCategory.FusionMat` where Rounds 1–2 built the reconstruction).

The four instance fields are the structures the round constructs
(`MonoidalCategory` from D2/D3, `MonoidalPreadditive` from Round 1's bilinearity,
`RigidCategory` from D4's snakes, `HasFiniteBiproducts` from D1).  The three
identification fields pin the reconstruction to the fusion system: the tensor as an
equality of *objects* (`tensorObj_eq`, the block-level pin the literal freeze could not
state), the unit object (`tensorUnit_eq`), and the right dual (`rightDual_m`, the frozen
literal shape verbatim).  `fusion` is the `IsFusionCategory` field of the frozen
`ReconFusion`, unchanged in content. -/
class ReconFusionCanonical (S : FusionSystem n k) (hn : 0 < n) where
  /-- The monoidal structure of the reconstruction (D2's associator naturality and D3's
  pentagon enter here, through `monoidalCategoryOfAssoc`). -/
  [mon : MonoidalCategory (FusionMat n k)]
  /-- The additivity of the tensor (Round 1: entrywise bilinearity of `tensorHom`). -/
  [monPre : MonoidalPreadditive (FusionMat n k)]
  /-- The rigidity (D4: `dual`, `ev`, `coev` and the two snakes). -/
  [rig : RigidCategory (FusionMat n k)]
  /-- Finite biproducts (D1's layer). -/
  [biprod : HasFiniteBiproducts (FusionMat n k)]
  /-- **The tensor on objects is the landed `tensorObj`** — an equality of objects, hence
  of multiplicity vectors *and* block index types.  This is the block-level pin that the
  literal freeze (`tensorObj_m` on the bare multiplicity vector) could not state; it
  implies the frozen `m`-level field (`tensorObj_m_eq`, `tensor_m_ofM`). -/
  tensorObj_eq : ∀ X Y : FusionMat n k, X ⊗ Y = FusionCategory.tensorObj S X Y
  /-- **The tensor unit is the landed `unitObj`** (the vector supported at the unit
  label), again as an equality of objects. -/
  tensorUnit_eq : 𝟙_ (FusionMat n k) = FusionCategory.unitObj hn
  /-- **The right dual is the duality-involution relabelling** — the frozen literal
  field `ReconFusion.rightDual_m`, verbatim. -/
  rightDual_m : ∀ (X : FusionMat n k) (c : Fin n),
    (HasRightDual.rightDual X).m c = X.m (S.ring.dual c)
  /-- **D4's success criterion**: the reconstruction is a fusion category in the
  library's sense (the `IsFusionCategory` field of the frozen package). -/
  fusion : IsFusionCategory k (FusionMat n k)

attribute [instance] ReconFusionCanonical.mon ReconFusionCanonical.monPre
  ReconFusionCanonical.rig ReconFusionCanonical.biprod

/-- **The revised success criterion**: the canonical scaffold of `S` carries a
`ReconFusionCanonical` structure.  This is the form of `WP2.ReconIsFusion` that the
round's work can inhabit. -/
def ReconIsFusionCanonical (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  Nonempty (ReconFusionCanonical S hn)

/-! ## The frozen object-level fields, on the canonical scaffold

With the revision's instances and identifications in hand, the frozen literal freeze's
three object-level equations hold in their exact shapes — the only change is that the
objects are the scaffold's (they carry their blocks), so the tensor field is *implied*
rather than assumed. -/

section Consequences

variable {S : FusionSystem n k} {hn : 0 < n}
variable [h : ReconFusionCanonical S hn]

/-- The multiplicity of a tensor is the fusion-ring convolution. -/
theorem tensorObj_m_eq (X Y : FusionMat n k) (c : Fin n) :
    (X ⊗ Y).m c = ∑ a : Fin n, ∑ b : Fin n, S.ring.N a b c * X.m a * Y.m b := by
  rw [h.tensorObj_eq]
  exact tensorObj_m S X Y c

/-- The block index type of a tensor is the channel refinement. -/
theorem tensorObj_blk_eq (X Y : FusionMat n k) (c : Fin n) :
    (X ⊗ Y).blk c = TensorIdx S X Y c := by
  rw [h.tensorObj_eq]

/-- The multiplicity of the tensor unit: the vector supported at the unit label. -/
theorem tensorUnit_m (c : Fin n) :
    (𝟙_ (FusionMat n k)).m c = if c = (⟨0, hn⟩ : Fin n) then 1 else 0 := by
  rw [h.tensorUnit_eq]
  rfl

/-- The frozen literal shape of the unit field (`c.val = 0` instead of `c = ⟨0, hn⟩`). -/
theorem tensorUnit_m_val (c : Fin n) :
    (𝟙_ (FusionMat n k)).m c = if c.val = 0 then 1 else 0 := by
  rw [tensorUnit_m]
  by_cases hc : c.val = 0
  · rw [if_pos hc, if_pos (Fin.ext (by rw [hc]))]
  · rw [if_neg hc, if_neg (fun hh => hc (by rw [hh]))]

/-- The block of the unit object is `Fin`-shaped, as in the literal model. -/
theorem tensorUnit_blk (c : Fin n) :
    (𝟙_ (FusionMat n k)).blk c = Fin (if c.val = 0 then 1 else 0) := by
  rw [h.tensorUnit_eq]
  show Fin (if c = (⟨0, hn⟩ : Fin n) then 1 else 0) = Fin (if c.val = 0 then 1 else 0)
  congr 1
  by_cases hc : c.val = 0
  · rw [if_pos hc, if_pos (Fin.ext (by rw [hc]))]
  · rw [if_neg hc, if_neg (fun hh => hc (by rw [hh]))]

/-- **The frozen literal `tensorObj_m` field, at the image of `ofM`.** -/
theorem tensor_m_ofM (m m' : Fin n → ℕ) (c : Fin n) :
    (FusionMat.ofM (k := k) m ⊗ FusionMat.ofM (k := k) m').m c
      = WP2.tensorMul S.ring (⟨m⟩ : WP2.FusionMat n k) (⟨m'⟩ : WP2.FusionMat n k) c := by
  rw [tensorObj_m_eq]
  rfl

/-- **The frozen literal `rightDual_m` field, at the image of `ofM`.** -/
theorem rightDual_m_ofM (m : Fin n → ℕ) (c : Fin n) :
    (HasRightDual.rightDual (FusionMat.ofM (k := k) m)).m c = m (S.ring.dual c) :=
  h.rightDual_m (FusionMat.ofM (k := k) m) c

/-- The frozen literal `tensorUnit_m` field (its `unitMat` has multiplicity
`if c.val = 0 then 1 else 0`), verbatim. -/
theorem tensorUnit_m_literal (c : Fin n) :
    (𝟙_ (FusionMat n k)).m c = (WP2.unitMat n k).m c := by
  rw [tensorUnit_m_val]
  rfl

/-! ## The finding: the canonical tensor leaves the literal model's image

These two are *definitional* equalities (`rfl`), and together they are the recorded
reason the literal freeze cannot be discharged by the round's work.  They are restated
here so that the citation is self-contained. -/

/-- Literal-model objects have `Fin`-shaped blocks. -/
theorem ofM_blk_shape (m : Fin n → ℕ) (c : Fin n) :
    (FusionMat.ofM (k := k) m).blk c = Fin (m c) := rfl

/-- The canonical tensor of two literal-model objects has the channel-refined Σ-block,
not a `Fin`-block: `ofM` is not a strict monoidal functor on objects. -/
theorem tensorObj_ofM_blk_shape (m m' : Fin n → ℕ) (c : Fin n) :
    (FusionCategory.tensorObj S (FusionMat.ofM (k := k) m) (FusionMat.ofM (k := k) m')).blk c
      = Σ p : Fin n × Fin n, Fin (S.ring.N p.1 p.2 c) × Fin (m p.1) × Fin (m' p.2) := rfl

/-- The same statement for the *tensor of the reconstruction*: by `tensorObj_eq` the
reconstruction's tensor has the Σ-block at the image of `ofM`, while every
`ofM`-object's block is a `Fin`. -/
theorem tensor_blk_shape_ofM (m m' : Fin n → ℕ) (c : Fin n) :
    (FusionMat.ofM (k := k) m ⊗ FusionMat.ofM (k := k) m').blk c
      = Σ p : Fin n × Fin n, Fin (S.ring.N p.1 p.2 c) × Fin (m p.1) × Fin (m' p.2) := by
  rw [tensorObj_blk_eq]
  rfl

end Consequences

/-! ## The scaffold refines the literal model, it does not change it

Two objects with the same multiplicity vector are isomorphic on the canonical scaffold
(the permutation matrix of a block equivalence), so every canonical object is
isomorphic to the literal-model object of its multiplicity vector.  Together with
`tensorObj_ofM_blk_shape` this is the precise form of the finding: the revision changes
*neither* the objects up to isomorphism *nor* the multiplicities — it changes only where
the coherence is proved, namely on the channel-refined blocks. -/

open _root_.FusionCategory.Units in
/-- **`ofM` is essentially surjective**: every canonical object is isomorphic to the
literal-model object of its multiplicity vector. -/
noncomputable def ofMIso (X : FusionMat n k) :
    FusionMat.ofM (k := k) X.m ≅ X where
  hom i := graphMatInv (Fintype.equivFinOfCardEq (X.card_blk i))
  inv i := graphMat (Fintype.equivFinOfCardEq (X.card_blk i))
  hom_inv_id := by
    funext i
    exact graphMatInv_mul_graphMat (Fintype.equivFinOfCardEq (X.card_blk i))
  inv_hom_id := by
    funext i
    exact graphMat_mul_graphMatInv (Fintype.equivFinOfCardEq (X.card_blk i))

/-- The same, in `Nonempty` form (the shape an equivalence of object classes uses). -/
theorem ofM_essentially_surjective (X : FusionMat n k) :
    Nonempty (FusionMat.ofM (k := k) X.m ≅ X) :=
  ⟨ofMIso X⟩

/-! ## The residual obligations, named

Everything the round still owes, as a structure.  `AssociatorIso` is *not* here: it is
proved (`ReconAssocIso.associatorIso`).  Each field is the target of a named direction:
`hnat` (D2), `pent` (D3), `rig` + `hdual` (D4), `biprod` + `simples_fin` +
`decomposition` (D1). -/

/-- The round's remaining obligations for the reconstructed fusion category. -/
structure ReconResidual (S : FusionSystem n k) (hn : 0 < n) where
  /-- D2: naturality of the associator (frozen `AssociatorNatural`). -/
  hnat : AssociatorNatural S
  /-- D3: the pentagon (frozen `PentagonShape`, about `associatorHom`). -/
  pent : PentagonShape S (associatorIso S)
  /-- D4: rigidity, for the assembled monoidal structure. -/
  rig : @RigidCategory (FusionMat n k) _
    (monoidalCategoryOfAssoc S hn (associatorIso S) hnat pent)
  /-- D1: finite biproducts. -/
  biprod : @HasFiniteBiproducts (FusionMat n k) _ _
  /-- D4: the assembled right dual is the duality relabelling (the frozen
  `rightDual_m` shape). -/
  hdual : ∀ (X : FusionMat n k) (c : Fin n),
    (@HasRightDual.rightDual (FusionMat n k) _
      (monoidalCategoryOfAssoc S hn (associatorIso S) hnat pent) X (rig.rightDual X)).m c
      = X.m (S.ring.dual c)
  /-- D1: finitely many simples up to isomorphism. -/
  simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
    ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i)
  /-- D1: every object is a finite biproduct of simples. -/
  decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)

/-! ## Constructing the revision

Two constructors: one from an arbitrary monoidal/rigid/biproduct structure on the
scaffold together with the two `IsFusionCategory` fields D1 owns, and one from the
`Residual` above, which uses the *landed* assembled monoidal structure
(`monoidalCategoryOfAssoc`) and the landed additivity of its tensor. -/

section FromHypotheses

variable [MonoidalCategory (FusionMat n k)] [MonoidalPreadditive (FusionMat n k)]
  [RigidCategory (FusionMat n k)] [HasFiniteBiproducts (FusionMat n k)]

/-- **The revision from an abstract monoidal/rigid/biproduct scaffold.**  The only
inputs are the unit identification (automatic for the assembled structure, see
`MonoidalData.toStruct_tensorUnit`) and D1's two combinatorial fields; `hom_finite` is
discharged by `isFusionCategoryOfUnit`. -/
noncomputable def reconFusionCanonical_ofHypotheses {S : FusionSystem n k} {hn : 0 < n}
    (hUnit : (𝟙_ (FusionMat n k)) = FusionCategory.unitObj hn)
    (htensor : ∀ X Y : FusionMat n k, X ⊗ Y = FusionCategory.tensorObj S X Y)
    (hdual : ∀ (X : FusionMat n k) (c : Fin n),
      (HasRightDual.rightDual X).m c = X.m (S.ring.dual c))
    (simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
      ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i))
    (decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
      (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)) :
    ReconFusionCanonical S hn where
  mon := inferInstance
  monPre := inferInstance
  rig := inferInstance
  biprod := inferInstance
  tensorObj_eq := htensor
  tensorUnit_eq := hUnit
  rightDual_m := hdual
  fusion := isFusionCategoryOfUnit hUnit simples_fin decomposition

end FromHypotheses

/-- **The revision from the round's residual obligations.**  This is the form D5
inhabits: `AssociatorIso` is already proved, the monoidal structure is the landed
`monoidalCategoryOfAssoc`, and the additivity of its tensor is the landed
`monoidalPreadditiveOfAssoc`. -/
noncomputable def reconFusionCanonical_of_residual (S : FusionSystem n k) (hn : 0 < n)
    (R : ReconResidual S hn) : ReconFusionCanonical S hn := by
  letI M : MonoidalCategory (FusionMat n k) :=
    monoidalCategoryOfAssoc S hn (associatorIso S) R.hnat R.pent
  letI P : MonoidalPreadditive (FusionMat n k) :=
    monoidalPreadditiveOfAssoc S hn (associatorIso S) R.hnat R.pent
  letI RG : RigidCategory (FusionMat n k) := R.rig
  letI B : HasFiniteBiproducts (FusionMat n k) := R.biprod
  exact
    { mon := M
      monPre := P
      rig := RG
      biprod := B
      tensorObj_eq := fun X Y => rfl
      tensorUnit_eq := rfl
      rightDual_m := R.hdual
      fusion := isFusionCategoryOfUnit (hn := hn) rfl R.simples_fin R.decomposition }

/-- **The revised success criterion, from the residual obligations.** -/
theorem reconIsFusionCanonical_of_residual (S : FusionSystem n k) (hn : 0 < n)
    (R : ReconResidual S hn) : ReconIsFusionCanonical S hn :=
  ⟨reconFusionCanonical_of_residual S hn R⟩

/-- **The reconstruction is a fusion category, with every instance named.**  This is the
explicit end-to-end form (the `IsFusionCategory` field of the frozen freeze, with the
assembled monoidal structure written out): the only inputs are `ReconResidual`'s, i.e.
D2's `AssociatorNatural`, D3's `PentagonShape`, D4's rigidity, D1's biproducts and two
combinatorial fields. -/
theorem isFusionCategory_of_residual (S : FusionSystem n k) (hn : 0 < n)
    (R : ReconResidual S hn) :
    @IsFusionCategory k _ (FusionMat n k) _ _
      (monoidalCategoryOfAssoc S hn (associatorIso S) R.hnat R.pent) _
      (monoidalPreadditiveOfAssoc S hn (associatorIso S) R.hnat R.pent)
      R.rig R.biprod :=
  (reconFusionCanonical_of_residual S hn R).fusion

/-- The revision's `Residual` field `pent` in the shape D3 proves (`PentagonShapeHom`, about
`associatorHom`) rather than the assembler's `PentagonShape`.  `ReconAssembly.pentagonShape_iff`
is the conversion; landed, nothing assumed. -/
theorem pentagonShape_of_hom {S : FusionSystem n k} (h : PentagonShapeHom S) :
    PentagonShape S (associatorIso S) :=
  (pentagonShape_iff S (associatorIso S)).mpr h

/-- The residual obligations, from D3's own shape of the pentagon. -/
noncomputable def reconResidualOfPentagonHom (S : FusionSystem n k) (hn : 0 < n)
    (hnat : AssociatorNatural S) (pHom : PentagonShapeHom S)
    (rig : @RigidCategory (FusionMat n k) _
      (monoidalCategoryOfAssoc S hn (associatorIso S) hnat (pentagonShape_of_hom pHom)))
    (biprod : @HasFiniteBiproducts (FusionMat n k) _ _)
    (hdual : ∀ (X : FusionMat n k) (c : Fin n),
      (@HasRightDual.rightDual (FusionMat n k) _
        (monoidalCategoryOfAssoc S hn (associatorIso S) hnat (pentagonShape_of_hom pHom))
        X (rig.rightDual X)).m c = X.m (S.ring.dual c))
    (simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
      ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i))
    (decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
      (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)) :
    ReconResidual S hn where
  hnat := hnat
  pent := pentagonShape_of_hom pHom
  rig := rig
  biprod := biprod
  hdual := hdual
  simples_fin := simples_fin
  decomposition := decomposition

/-! ## Discharging the dual obligation from an object-level identification

`ReconResidual.hdual` is the frozen `m`-level shape.  If the assembled right dual *is* the
landed `FusionMat.dual S X` (which is what building `HasRightDual` from an `ExactPairing`
on `dual S X` gives, definitionally), then the `m`-level field is the landed `dual_m`.
This removes the dual from the list of things D5 has to check by hand. -/

section DualFromEq

variable [MonoidalCategory (FusionMat n k)] [RigidCategory (FusionMat n k)]

/-- An object-level identification of the right dual with the landed `dual` gives the
frozen `rightDual_m` field. -/
theorem rightDual_m_of_eq {S : FusionSystem n k}
    (hdual_eq : ∀ X : FusionMat n k, HasRightDual.rightDual X = FusionMat.dual S X) :
    ∀ (X : FusionMat n k) (c : Fin n),
      (HasRightDual.rightDual X).m c = X.m (S.ring.dual c) := by
  intro X c
  rw [hdual_eq X]
  exact FusionMat.dual_m S X c

end DualFromEq

/-! ## The bridge to the frozen literal freeze

`LiteralImageFields` is the frozen `WP2Canon.ReconFusion`'s **object-level field list**,
stated where the canonical model meets the literal one: at the image of `ofM` (for the
tensor and the dual) and at the frozen unit vector (for the unit).  The theorem
`toLiteralImageFields` says the revision implies it, so the revision loses nothing of
the freeze.  The converse (building the revision from the literal freeze) is not
available: the literal freeze says nothing about block index types, and the canonical
tensor's blocks are the channel refinement (`tensorObj_ofM_blk_shape`), so the
literal model's `Fin`-shaped blocks would have to be re-identified by hand. -/

/-- The frozen literal freeze's object-level field equations, at the image of `ofM`. -/
structure LiteralImageFields (S : FusionSystem n k) (hn : 0 < n)
    [MonoidalCategory (FusionMat n k)] [RigidCategory (FusionMat n k)] : Prop where
  /-- The frozen `tensorObj_m`. -/
  tensorObj_m : ∀ (m m' : Fin n → ℕ) (c : Fin n),
    (FusionMat.ofM (k := k) m ⊗ FusionMat.ofM (k := k) m').m c
      = WP2.tensorMul S.ring (⟨m⟩ : WP2.FusionMat n k) (⟨m'⟩ : WP2.FusionMat n k) c
  /-- The frozen `tensorUnit_m`. -/
  tensorUnit_m : ∀ c : Fin n, (𝟙_ (FusionMat n k)).m c = (WP2.unitMat n k).m c
  /-- The frozen `rightDual_m`. -/
  rightDual_m : ∀ (m : Fin n → ℕ) (c : Fin n),
    (HasRightDual.rightDual (FusionMat.ofM (k := k) m)).m c = m (S.ring.dual c)

/-- **The revision implies the frozen object-level freeze, at the image of `ofM`.** -/
theorem toLiteralImageFields {S : FusionSystem n k} {hn : 0 < n}
    [h : ReconFusionCanonical S hn] : LiteralImageFields S hn where
  tensorObj_m := tensor_m_ofM
  tensorUnit_m := tensorUnit_m_literal
  rightDual_m := rightDual_m_ofM

/-- The `IsFusionCategory` field of the revision, exposed (this is the field of the
frozen `ReconFusion` that D4's success criterion names). -/
theorem ReconFusionCanonical.isFusionCategory {S : FusionSystem n k} {hn : 0 < n}
    (h : ReconFusionCanonical S hn) : IsFusionCategory k (FusionMat n k) :=
  h.fusion

/-- The revision's `End 𝟙 = k`, read through the landed `endUnitEquiv` (the interface the
trace correspondence of Task 2.2 consumes). -/
theorem ReconFusionCanonical.endUnitEquiv_nonempty {S : FusionSystem n k} {hn : 0 < n}
    (h : ReconFusionCanonical S hn) : Nonempty (End (𝟙_ (FusionMat n k)) ≃+* k) :=
  h.fusion.end_unit

end WP2Canon

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.WP2Canon.ReconFusionCanonical
#print axioms FusionCategory.WP2Canon.ReconIsFusionCanonical
#print axioms FusionCategory.WP2Canon.tensorObj_m_eq
#print axioms FusionCategory.WP2Canon.tensorObj_blk_eq
#print axioms FusionCategory.WP2Canon.tensorUnit_m
#print axioms FusionCategory.WP2Canon.tensorUnit_m_val
#print axioms FusionCategory.WP2Canon.tensorUnit_blk
#print axioms FusionCategory.WP2Canon.tensor_m_ofM
#print axioms FusionCategory.WP2Canon.rightDual_m_ofM
#print axioms FusionCategory.WP2Canon.tensorUnit_m_literal
#print axioms FusionCategory.WP2Canon.ofM_blk_shape
#print axioms FusionCategory.WP2Canon.tensorObj_ofM_blk_shape
#print axioms FusionCategory.WP2Canon.tensor_blk_shape_ofM
#print axioms FusionCategory.WP2Canon.ofMIso
#print axioms FusionCategory.WP2Canon.ofM_essentially_surjective
#print axioms FusionCategory.WP2Canon.ReconResidual
#print axioms FusionCategory.WP2Canon.reconFusionCanonical_ofHypotheses
#print axioms FusionCategory.WP2Canon.reconFusionCanonical_of_residual
#print axioms FusionCategory.WP2Canon.reconIsFusionCanonical_of_residual
#print axioms FusionCategory.WP2Canon.isFusionCategory_of_residual
#print axioms FusionCategory.WP2Canon.pentagonShape_of_hom
#print axioms FusionCategory.WP2Canon.reconResidualOfPentagonHom
#print axioms FusionCategory.WP2Canon.rightDual_m_of_eq
#print axioms FusionCategory.WP2Canon.LiteralImageFields
#print axioms FusionCategory.WP2Canon.toLiteralImageFields
#print axioms FusionCategory.WP2Canon.ReconFusionCanonical.isFusionCategory
#print axioms FusionCategory.WP2Canon.ReconFusionCanonical.endUnitEquiv_nonempty
