/-
# WP2 round 3, member m5, direction D5 — the assembly completion

This file carries the part of D5 that does *not* wait on the other directions:

* §1 the **unitor dedupe**: the two independent unitor developments agree
  (`Units.leftUnitor` from `ReconUnitors` = `FusionMat.leftUnitor` from `ReconRigid`), hom
  and inverse.  This is what lets the frozen snakes of `ReconSnake` (stated with the
  `FusionMat` matrix unitors) be read in the assembled monoidal structure of
  `ReconAssembly` (whose unitors are the `Units` ones).
* §2 a general monoidal lemma: the two λ-multiplied snake equations are an `ExactPairing`.
* §3 the **rigidity packaging**: `ExactPairing`, `HasRightDual`, `HasLeftDual`,
  `RightRigidCategory`, `LeftRigidCategory`, `RigidCategory` for the assembled structure,
  from the frozen `SnakeLeft`/`SnakeRight`.
* §4 the compatibility lemmas of the assembled instance (whiskerings, tensor unit, tensor,
  duals of simples).
* §5 the canonical-scaffold reconstruction package and its inhabitation, with `D1`–`D4`'s
  items as explicit named hypotheses.

Axiom budget `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconAssembly
import FusionCategory.ReconAssocIso
import FusionCategory.ReconSnake
import FusionCategory.ReconFusionProps
import FusionCategory.Statements2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory CategoryTheory.Limits

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — The unitor dedupe: `Units.*` and `FusionMat.*` agree

`ReconUnitors` builds the unitors as `graphMat` of the canonical block equivalences;
`ReconRigid`/`ReconSnake` build them as delta matrices on the canonical index `unitIdxL`/
`unitIdxR`.  The two are the same matrix: the equivalence sends `unitIdxL j` to `j`. -/

section Dedupe

variable (S : FusionSystem n k)

/-- The equivalence `leftIdxEquiv` sends the canonical index to the block index. -/
theorem Units.leftIdxEquiv_unitIdxL (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : X.blk c) :
    Units.leftIdxEquiv S hn X c (FusionMat.unitIdxL S hn X c j) = j :=
  Units.leftIdxEquiv_apply S hn X c _ _ j

/-- The equivalence `rightIdxEquiv` sends the canonical index to the block index. -/
theorem Units.rightIdxEquiv_unitIdxR (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : X.blk c) :
    Units.rightIdxEquiv S hn X c (FusionMat.unitIdxR S hn X c j) = j :=
  Units.rightIdxEquiv_apply S hn X c _ j _

/-- `leftIdxEquiv r = j` iff `r` is the canonical index of `j`. -/
theorem Units.leftIdxEquiv_eq_iff (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (unitObj hn) X).blk c) (j : X.blk c) :
    Units.leftIdxEquiv S hn X c r = j ↔ r = FusionMat.unitIdxL S hn X c j := by
  constructor
  · intro h
    have h2 : (Units.leftIdxEquiv S hn X c).symm j = FusionMat.unitIdxL S hn X c j := by
      rw [Equiv.symm_apply_eq]
      exact (Units.leftIdxEquiv_unitIdxL S hn X c j).symm
    calc r = (Units.leftIdxEquiv S hn X c).symm (Units.leftIdxEquiv S hn X c r) :=
          (Equiv.symm_apply_apply _ r).symm
      _ = (Units.leftIdxEquiv S hn X c).symm j := by rw [h]
      _ = FusionMat.unitIdxL S hn X c j := h2
  · intro h
    rw [h]
    exact Units.leftIdxEquiv_unitIdxL S hn X c j

/-- `rightIdxEquiv r = j` iff `r` is the canonical index of `j`. -/
theorem Units.rightIdxEquiv_eq_iff (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S X (unitObj hn)).blk c) (j : X.blk c) :
    Units.rightIdxEquiv S hn X c r = j ↔ r = FusionMat.unitIdxR S hn X c j := by
  constructor
  · intro h
    have h2 : (Units.rightIdxEquiv S hn X c).symm j = FusionMat.unitIdxR S hn X c j := by
      rw [Equiv.symm_apply_eq]
      exact (Units.rightIdxEquiv_unitIdxR S hn X c j).symm
    calc r = (Units.rightIdxEquiv S hn X c).symm (Units.rightIdxEquiv S hn X c r) :=
          (Equiv.symm_apply_apply _ r).symm
      _ = (Units.rightIdxEquiv S hn X c).symm j := by rw [h]
      _ = FusionMat.unitIdxR S hn X c j := h2
  · intro h
    rw [h]
    exact Units.rightIdxEquiv_unitIdxR S hn X c j

/-- **The unitor dedupe, left, hom.**  `Units.leftUnitor = FusionMat.leftUnitor`. -/
theorem Units.leftUnitor_eq_matrix (hn : 0 < n) (X : FusionMat n k) :
    Units.leftUnitor S hn X = FusionMat.leftUnitor S hn X := by
  funext c r j
  simp only [Units.leftUnitor, FusionMat.leftUnitor_eq, Units.graphMat]
  by_cases h : r = FusionMat.unitIdxL S hn X c j
  · rw [if_pos h, if_pos ((Units.leftIdxEquiv_eq_iff S hn X c r j).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Units.leftIdxEquiv_eq_iff S hn X c r j).mp hh))]

/-- **The unitor dedupe, right, hom.**  `Units.rightUnitor = FusionMat.rightUnitor`. -/
theorem Units.rightUnitor_eq_matrix (hn : 0 < n) (X : FusionMat n k) :
    Units.rightUnitor S hn X = FusionMat.rightUnitor S hn X := by
  funext c r j
  simp only [Units.rightUnitor, FusionMat.rightUnitor_eq, Units.graphMat]
  by_cases h : r = FusionMat.unitIdxR S hn X c j
  · rw [if_pos h, if_pos ((Units.rightIdxEquiv_eq_iff S hn X c r j).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Units.rightIdxEquiv_eq_iff S hn X c r j).mp hh))]

/-- **The unitor dedupe, left, inverse.** -/
theorem Units.leftUnitorInv_eq_matrix (hn : 0 < n) (X : FusionMat n k) :
    Units.leftUnitorInv S hn X = FusionMat.leftUnitorInv S hn X := by
  funext c j r
  simp only [Units.leftUnitorInv, FusionMat.leftUnitorInv, Units.graphMatInv, Matrix.of_apply]
  by_cases h : r = FusionMat.unitIdxL S hn X c j
  · rw [if_pos h, if_pos ((Units.leftIdxEquiv_eq_iff S hn X c r j).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Units.leftIdxEquiv_eq_iff S hn X c r j).mp hh))]

/-- **The unitor dedupe, right, inverse.** -/
theorem Units.rightUnitorInv_eq_matrix (hn : 0 < n) (X : FusionMat n k) :
    Units.rightUnitorInv S hn X = FusionMat.rightUnitorInv S hn X := by
  funext c j r
  simp only [Units.rightUnitorInv, FusionMat.rightUnitorInv, Units.graphMatInv, Matrix.of_apply]
  by_cases h : r = FusionMat.unitIdxR S hn X c j
  · rw [if_pos h, if_pos ((Units.rightIdxEquiv_eq_iff S hn X c r j).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Units.rightIdxEquiv_eq_iff S hn X c r j).mp hh))]

end Dedupe

/-! ## §2 — The λ-multiplied snakes are an exact pairing

Nothing here is specific to the reconstruction: any monoidal category in which the two
snake composites, *multiplied on the right by the unitors*, are the unitors, has an exact
pairing. -/

section General

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **The λ-multiplied snakes give an exact pairing.**  `h₁` is the left snake
`(η ▷ X) ≫ α ≫ (X ◁ ε) ≫ ρ = λ`; `h₂` is the right snake
`(Y ◁ η) ≫ α⁻¹ ≫ (ε ▷ Y) ≫ λ = ρ`. -/
def exactPairingOfSnake {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (h₁ : η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = (λ_ X).hom)
    (h₂ : Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).hom) :
    ExactPairing X Y where
  coevaluation' := η
  evaluation' := ε
  coevaluation_evaluation' := by
    have h := congrArg (fun t => t ≫ (λ_ Y).inv) h₂
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  evaluation_coevaluation' := by
    have h := congrArg (fun t => t ≫ (ρ_ X).inv) h₁
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

end General


/-! ## §3 — The rigidity packaging on the assembled structure

The frozen snakes of `ReconSnake` are equations between the *scaffold's* matrices; §1 lets us
read them as the snake equations of the assembled monoidal structure, and §2 turns those into
an exact pairing.  Everything after that is bookkeeping: `HasRightDual`, `HasLeftDual` (the
latter from the right dual of `X*` and `dual_dual`), and the three rigidity classes. -/



section Rigid

variable (S : FusionSystem n k) (hn : 0 < n)
  (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso)

/-- The assembled monoidal structure, as an abbreviation. -/
noncomputable abbrev monoOf : MonoidalCategory (FusionMat n k) :=
  monoidalCategoryOfAssoc S hn hiso hnat pent

/-- The additivity of the assembled tensor, as an abbreviation. -/
noncomputable abbrev monPreOf : @MonoidalPreadditive (FusionMat n k) _ _
    (monoOf S hn hiso hnat pent) :=
  monoidalPreadditiveOfAssoc S hn hiso hnat pent

/-- **The left snake, in the assembled structure's own vocabulary.**  The two `show`s are the
unitor dedupe of §1: the assembled structure's `λ`, `ρ` are the `Units` unitors, and §1
identifies those with the `FusionMat` matrix unitors the frozen snake is stated with.  Every
other component (`▷`, `◁`, `α_`) is the scaffold's by `rfl`. -/
theorem snakeLeft_of_frozen (hL : FusionMat.SnakeLeft S) (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    FusionMat.coev S hn X ▷ X ≫ (α_ X (FusionMat.dual S X) X).hom
        ≫ X ◁ FusionMat.ev S hn X ≫ (ρ_ X).hom = (λ_ X).hom := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  have hrho : (ρ_ X).hom = FusionMat.rightUnitor S hn X := by
    show Units.rightUnitor S hn X = FusionMat.rightUnitor S hn X
    exact Units.rightUnitor_eq_matrix S hn X
  have hlam : (λ_ X).hom = FusionMat.leftUnitor S hn X := by
    show Units.leftUnitor S hn X = FusionMat.leftUnitor S hn X
    exact Units.leftUnitor_eq_matrix S hn X
  rw [hrho, hlam]
  exact hL hn X

/-- **The right snake, in the assembled structure's own vocabulary.** -/
theorem snakeRight_of_frozen (hR : FusionMat.SnakeRight S) (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    FusionMat.dual S X ◁ FusionMat.coev S hn X
        ≫ (α_ (FusionMat.dual S X) X (FusionMat.dual S X)).inv
        ≫ FusionMat.ev S hn X ▷ FusionMat.dual S X
        ≫ (λ_ (FusionMat.dual S X)).hom = (ρ_ (FusionMat.dual S X)).hom := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  have hrho : (ρ_ (FusionMat.dual S X)).hom
      = FusionMat.rightUnitor S hn (FusionMat.dual S X) := by
    show Units.rightUnitor S hn (FusionMat.dual S X)
      = FusionMat.rightUnitor S hn (FusionMat.dual S X)
    exact Units.rightUnitor_eq_matrix S hn (FusionMat.dual S X)
  have hlam : (λ_ (FusionMat.dual S X)).hom
      = FusionMat.leftUnitor S hn (FusionMat.dual S X) := by
    show Units.leftUnitor S hn (FusionMat.dual S X)
      = FusionMat.leftUnitor S hn (FusionMat.dual S X)
    exact Units.leftUnitor_eq_matrix S hn (FusionMat.dual S X)
  rw [hrho, hlam]
  exact hR hn X

/-- **The exact pairing `(X, X*)`** from the frozen snakes: coevaluation `coev`, evaluation
`ev`, and the two triangle identities *are* the two snakes, divided by the unitors. -/
noncomputable def pairingOfSnake (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S)
    (X : FusionMat n k) :
    @ExactPairing (FusionMat n k) _ (monoOf S hn hiso hnat pent) X (FusionMat.dual S X) := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  exact exactPairingOfSnake (FusionMat.coev S hn X) (FusionMat.ev S hn X)
    (snakeLeft_of_frozen S hn hiso hnat pent hL X)
    (snakeRight_of_frozen S hn hiso hnat pent hR X)

/-- **`HasRightDual`, with `X* = dual S X`.** -/
noncomputable def hasRightDualOf (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S)
    (X : FusionMat n k) : @HasRightDual (FusionMat n k) _ (monoOf S hn hiso hnat pent) X := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  exact { rightDual := FusionMat.dual S X, exact := pairingOfSnake S hn hiso hnat pent hL hR X }

/-- The right dual of `hasRightDualOf` is the scaffold's dual. -/
theorem hasRightDualOf_rightDual (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S)
    (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    (hasRightDualOf S hn hiso hnat pent hL hR X).rightDual = FusionMat.dual S X := rfl

/-- **`HasLeftDual`**: the left dual of `X` is its right dual, because the duality involution
is an involution on the nose (`dual_dual`), so `(X*, X)` is the pairing of `X*`. -/
noncomputable def hasLeftDualOf (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S)
    (X : FusionMat n k) : @HasLeftDual (FusionMat n k) _ (monoOf S hn hiso hnat pent) X := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  have hEq : ExactPairing (FusionMat.dual S X) (FusionMat.dual S (FusionMat.dual S X))
      = ExactPairing (FusionMat.dual S X) X := by rw [FusionMat.dual_dual]
  exact { leftDual := FusionMat.dual S X,
          exact := hEq ▸ (pairingOfSnake S hn hiso hnat pent hL hR (FusionMat.dual S X)) }

/-- The right rigidity of the assembled structure. -/
noncomputable def rightRigidOf (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S) :
    @RightRigidCategory (FusionMat n k) _ (monoOf S hn hiso hnat pent) := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  exact { rightDual X := hasRightDualOf S hn hiso hnat pent hL hR X }

/-- The left rigidity of the assembled structure. -/
noncomputable def leftRigidOf (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S) :
    @LeftRigidCategory (FusionMat n k) _ (monoOf S hn hiso hnat pent) := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  exact { leftDual X := hasLeftDualOf S hn hiso hnat pent hL hR X }

/-- **`RigidCategory` for the assembled structure**, from the two frozen snakes. -/
noncomputable def rigidOf (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S) :
    @RigidCategory (FusionMat n k) _ (monoOf S hn hiso hnat pent) := by
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
  exact { rightDual X := hasRightDualOf S hn hiso hnat pent hL hR X,
          leftDual X := hasLeftDualOf S hn hiso hnat pent hL hR X }

/-- The right dual of the rigid structure is `dual S X`, on multiplicities. -/
theorem rigidOf_rightDual_m (hL : FusionMat.SnakeLeft S) (hR : FusionMat.SnakeRight S)
    (X : FusionMat n k) (c : Fin n) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    letI : RigidCategory (FusionMat n k) := rigidOf S hn hiso hnat pent hL hR
    (HasRightDual.rightDual X).m c = X.m (S.ring.dual c) := by
  show ((hasRightDualOf S hn hiso hnat pent hL hR X).rightDual).m c = X.m (S.ring.dual c)
  rw [hasRightDualOf_rightDual]
  rfl

end Rigid


/-! ## §4 — The compatibility lemmas of the assembled instance

These are the three conditions the trace correspondence (`ReconTraceCorrespondence`) asks for,
stated as theorems about the *assembled* instance: the whiskerings are the scaffold's
`tensorHom` with an identity, the tensor unit is the scaffold's `unitObj`, and the
coevaluation/evaluation of the packaged pairing are the scaffold's `coev`/`ev` (the
`coevSim`/`evSim` block matrices of the trace file are these at a simple). -/

section Compat

variable (S : FusionSystem n k) (hn : 0 < n)
  (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso)

/-- The assembled left whiskering is `tensorHom` with the identity. -/
theorem toStruct_whiskerLeft (X : FusionMat n k) {Y Y' : FusionMat n k} (g : Y ⟶ Y') :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    X ◁ g = tensorHom S (𝟙 X) g := rfl

/-- The assembled right whiskering is `tensorHom` with the identity. -/
theorem toStruct_whiskerRight {X X' : FusionMat n k} (f : X ⟶ X') (Y : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    f ▷ Y = tensorHom S f (𝟙 Y) := rfl

/-- The assembled tensor on objects is the scaffold's `tensorObj`. -/
theorem toStruct_tensorObj_eq (X Y : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    (X ⊗ Y) = tensorObj S X Y := rfl

/-- The assembled tensor unit is the scaffold's `unitObj`. -/
theorem toStruct_tensorUnit_eq :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    (𝟙_ (FusionMat n k)) = unitObj hn := rfl

/-- The tensor unit *is* the simple `X₀`: `unitObj hn = sim ⟨0, hn⟩` — the compatibility
condition "unit = sim 0" of the trace correspondence, on the canonical scaffold. -/
theorem unitObj_eq_sim_zero : unitObj (k := k) hn = sim (k := k) ⟨0, hn⟩ := rfl

/-- The tensor of two simples carries the fusion coefficient (restated for §5). -/
theorem tensorObj_sim_m_eq (a b c : Fin n) :
    (tensorObj S (sim (k := k) a) (sim (k := k) b)).m c = S.ring.N a b c :=
  tensorObj_sim_m S a b c

/-- **The dual of a simple is the simple at the dual label.** -/
theorem dual_sim (i : Fin n) : FusionMat.dual S (sim (k := k) i) = sim (k := k) (S.ring.dual i) := by
  refine FusionMat.ext_m_blk ?_ ?_
  · funext c
    show (sim (k := k) i).m (S.ring.dual c) = (sim (k := k) (S.ring.dual i)).m c
    simp only [sim]
    by_cases h : c = S.ring.dual i
    · subst h
      rw [S.ring.dual_involutive]
      simp
    · have h' : S.ring.dual c ≠ i := fun hh => h (by
        rw [← hh, S.ring.dual_involutive])
      rw [if_neg h, if_neg h']
  · funext c
    show (sim (k := k) i).blk (S.ring.dual c) = (sim (k := k) (S.ring.dual i)).blk c
    simp only [sim]
    by_cases h : c = S.ring.dual i
    · subst h
      rw [S.ring.dual_involutive]
      simp
    · have h' : S.ring.dual c ≠ i := fun hh => h (by
        rw [← hh, S.ring.dual_involutive])
      rw [if_neg h, if_neg h']

end Compat


/-! ## §5 — The reconstruction package on the canonical scaffold

`Statements2.WP2.ReconFusion` names the *literal* model (multiplicity vectors only).  The
Round-2 finding `tensorObj_ofM_blk` shows the scaffold's tensor leaves the image of `ofM`
(the block type of `X ⊗ Y` is the channel refinement, not a `Fin`), so the reconstruction
theorem must be stated on `FusionCategory.FusionMat`.  This section does that: the package
below is `WP2.ReconFusion`'s canonical counterpart, with the object-level identifications
stated as *equalities on the canonical scaffold* (hence `rfl`-level facts, not transport).

The remaining inputs are packaged as `ClosureInputs`: exactly D2's naturality, D3's pentagon,
D4's two snakes, and D1's two semisimplicity fields plus the finite biproducts. -/

section Closure

variable (S : FusionSystem n k) (hn : 0 < n)

/-- **The remaining inputs of the reconstruction**, one structure so that the gap is a
theorem-shaped object rather than a list of hypotheses. -/
structure ClosureInputs (S : FusionSystem n k) where
  /-- D2: naturality of the associator (the frozen `AssociatorNatural`). -/
  hnat : AssociatorNatural S
  /-- D3: the pentagon, in the `associatorHom` form (`PentagonShapeHom`). -/
  pent : PentagonShapeHom S
  /-- D4: the left snake (the frozen `FusionMat.SnakeLeft`). -/
  snakeLeft : FusionMat.SnakeLeft S
  /-- D4: the right snake (the frozen `FusionMat.SnakeRight`). -/
  snakeRight : FusionMat.SnakeRight S
  /-- D1(d): finite biproducts on the blob model. -/
  [biprod : HasFiniteBiproducts (FusionMat n k)]
  /-- D1(c): finitely many simples up to isomorphism. -/
  simples_fin : ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
    ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i)
  /-- D1(e): every object is a finite biproduct of simples. -/
  decomposition : ∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)

/-- **The canonical reconstruction package**: the vocabulary of `WP2.ReconFusion`, on the
canonical scaffold.  The instance fields are the seven structures; the identification fields
pin them to the system's data; the last field is D4's success criterion. -/
structure ReconFusionCanonical where
  [cat : Category.{u} (FusionMat n k)]
  [pre : Preadditive (FusionMat n k)]
  [mon : MonoidalCategory (FusionMat n k)]
  [lin : Linear k (FusionMat n k)]
  [monPre : MonoidalPreadditive (FusionMat n k)]
  [rig : RigidCategory (FusionMat n k)]
  [biprod : HasFiniteBiproducts (FusionMat n k)]
  /-- The tensor on objects is the fusion-ring convolution. -/
  tensorObj_m : ∀ (X Y : FusionMat n k) (c : Fin n), (X ⊗ Y).m c = tensorMul S X Y c
  /-- The tensor unit is the reconstruction's unit object `X₀`. -/
  tensorUnit_eq : 𝟙_ (FusionMat n k) = unitObj hn
  /-- The right dual is the duality-involution relabelling. -/
  rightDual_m : ∀ (X : FusionMat n k) (c : Fin n),
    (HasRightDual.rightDual X).m c = X.m (S.ring.dual c)
  /-- **D4's success criterion**: the reconstruction is a fusion category in the library's
  sense. -/
  fusion : IsFusionCategory k (FusionMat n k)

/-- **The frozen success criterion, on the canonical scaffold.** -/
def ReconIsFusionCanonical : Prop :=
  Nonempty (ReconFusionCanonical S hn)

/-- The `IsFusionCategory` field of the package, in the usable `@`-form. -/
theorem IsFusionCategory.ofReconFusionCanonical (H : ReconFusionCanonical S hn) :
    @IsFusionCategory k _ (FusionMat n k) H.cat H.pre H.mon H.lin H.monPre H.rig H.biprod :=
  H.fusion

/-- **The reconstruction, assembled.**  From the remaining inputs, the canonical scaffold
carries the seven structures and satisfies `IsFusionCategory`. -/
noncomputable def reconFusionCanonicalOf (I : ClosureInputs S) :
    ReconFusionCanonical S hn := by
  have hiso : AssociatorIso S := associatorIso S
  have pent : PentagonShape S hiso := (pentagonShape_iff S hiso).mpr I.pent
  letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso I.hnat pent
  letI : MonoidalPreadditive (FusionMat n k) := monPreOf S hn hiso I.hnat pent
  letI : RigidCategory (FusionMat n k) := rigidOf S hn hiso I.hnat pent I.snakeLeft I.snakeRight
  letI : HasFiniteBiproducts (FusionMat n k) := I.biprod
  refine { tensorObj_m := ?_, tensorUnit_eq := ?_, rightDual_m := ?_, fusion := ?_ }
  · intro X Y c
    show (tensorObj S X Y).m c = tensorMul S X Y c
    rw [tensorObj_m, tensorMul, Fintype.sum_prod_type]
  · exact toStruct_tensorUnit_eq S hn hiso I.hnat pent
  · intro X c
    exact rigidOf_rightDual_m S hn hiso I.hnat pent I.snakeLeft I.snakeRight X c
  · exact isFusionCategoryOfUnit (hUnit := toStruct_tensorUnit_eq S hn hiso I.hnat pent)
      I.simples_fin I.decomposition

/-- **The canonical reconstruction theorem.**  A `FusionSystem` with `0 < n`, together with
the remaining inputs, reconstructs a fusion category: the `FusionMat` block model carries a
monoidal, rigid, finite-biproduct, `End(1) = k` structure whose simples are the `sim i`. -/
theorem reconIsFusionCanonical (I : ClosureInputs S) :
    ReconIsFusionCanonical S hn :=
  ⟨reconFusionCanonicalOf S hn I⟩

/-- The package also gives the assembled monoidal structure's `End 𝟙 ≃+* k` — the map the
categorical trace of Task 2.2 is read through. -/
theorem endUnitEquivOfCanonical (H : ReconFusionCanonical S hn) :
    Nonempty (End (@MonoidalCategoryStruct.tensorUnit (FusionMat n k) _ H.mon.toMonoidalCategoryStruct)
      ≃+* k) :=
  ⟨H.tensorUnit_eq.symm ▸ endUnitEquiv hn⟩

end Closure


/-! ## §6 — The pairing's coevaluation/evaluation as block matrices

The last of the three compatibility conditions of the trace correspondence: the coefficients of
the packaged exact pairing *are* the scaffold's `coev`/`ev` block matrices. -/

section PairingBlocks

variable (S : FusionSystem n k) (hn : 0 < n)
  (hiso : AssociatorIso S) (hnat : AssociatorNatural S) (pent : PentagonShape S hiso)

/-- The coevaluation of the packaged pairing is the scaffold's `coev`. -/
theorem pairingOfSnake_coevaluation (hL : FusionMat.SnakeLeft S)
    (hR : FusionMat.SnakeRight S) (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    letI : ExactPairing X (FusionMat.dual S X) :=
      pairingOfSnake S hn hiso hnat pent hL hR X
    ExactPairing.coevaluation X (FusionMat.dual S X) = FusionMat.coev S hn X := rfl

/-- The evaluation of the packaged pairing is the scaffold's `ev`. -/
theorem pairingOfSnake_evaluation (hL : FusionMat.SnakeLeft S)
    (hR : FusionMat.SnakeRight S) (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    letI : ExactPairing X (FusionMat.dual S X) :=
      pairingOfSnake S hn hiso hnat pent hL hR X
    ExactPairing.evaluation X (FusionMat.dual S X) = FusionMat.ev S hn X := rfl

/-- The evaluation of the pairing of the dual object `X*` — the evaluation that
`WP2.trDual` uses on the right of the trace composite. -/
theorem pairingOfSnake_evaluation_dual (hL : FusionMat.SnakeLeft S)
    (hR : FusionMat.SnakeRight S) (X : FusionMat n k) :
    letI : MonoidalCategory (FusionMat n k) := monoOf S hn hiso hnat pent
    letI : ExactPairing (FusionMat.dual S X) (FusionMat.dual S (FusionMat.dual S X)) :=
      pairingOfSnake S hn hiso hnat pent hL hR (FusionMat.dual S X)
    ExactPairing.evaluation (FusionMat.dual S X) (FusionMat.dual S (FusionMat.dual S X))
      = FusionMat.ev S hn (FusionMat.dual S X) := rfl

end PairingBlocks

/-! ## §7 — The pairing's coefficients at a simple, entrywise

The trace correspondence of `ReconTraceCorrespondence` computes the trace with the *label-level*
`coevSim`/`evSim` block matrices; `WP2.trDual` uses the exact pairing of §3, whose
coevaluation/evaluation are the scaffold's `coev`/`ev`.  The two agree, and the content is the
following two entry computations (everything in the scaffold's own Σ-coordinates). -/

section Coefficients

variable (S : FusionSystem n k)

/-- The block of the simple at its own label is a subsingleton. -/
theorem subsingleton_sim_blk_self (i : Fin n) : Subsingleton ((sim (k := k) i).blk i) := by
  constructor
  intro a b
  exact Fin.ext (by
    have ha : a.val < 1 := by simpa [sim] using a.isLt
    have hb : b.val < 1 := by simpa [sim] using b.isLt
    omega)

/-- A point of the `i`-simple's block at a label forces that label. -/
theorem eq_of_sim_blk_nonempty {i j : Fin n} (x : (sim (k := k) i).blk j) : j = i := by
  by_contra hne
  have hE : IsEmpty ((sim (k := k) i).blk j) := by
    rw [show (sim (k := k) i).blk j = Fin (if j = i then 1 else 0) from rfl, if_neg hne]
    infer_instance
  exact hE.false x

/-- **The coevaluation of the pairing at a simple, entrywise**: on the unit channel it is the
scalar `S.coev i`, and there is no other channel. -/
theorem coev_sim_apply (hn : 0 < n) (i : Fin n) (c : Fin n)
    (j : (unitObj (k := k) hn).blk c)
    (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : (sim (k := k) i).blk p.1) (t : (FusionMat.dual S (sim (k := k) i)).blk p.2) :
    FusionMat.coev S hn (sim (k := k) i) c j ⟨p, ν, s, t⟩
      = if c = ⟨0, hn⟩ then S.coev i else 0 := by
  by_cases hc : c = ⟨0, hn⟩
  · subst hc
    have hp2 : p.2 = S.ring.dual p.1 := FusionMat.dual_label_of_unit S hn ν
    have hp1 : p.1 = i := eq_of_sim_blk_nonempty s
    have hcond : p.1 = S.ring.dual p.2 := by rw [hp2, hp1, S.ring.dual_involutive]
    haveI : Subsingleton ((sim (k := k) i).blk p.1) := by
      rw [hp1]
      exact subsingleton_sim_blk_self (k := k) i
    have hcoe : FusionMat.coev S hn (sim (k := k) i) ⟨0, hn⟩ j ⟨p, ν, s, t⟩
        = if s = hcond.symm ▸ t then S.coev p.1 else 0 :=
      FusionMat.coev_apply_of_eq (S := S) (hn := hn) (X := sim (k := k) i)
        (c := ⟨0, hn⟩) (h := hcond) (ν := ν) (s := s) (t := t) (j := j)
    rw [hcoe, if_pos (Subsingleton.elim s (hcond.symm ▸ t)), if_pos rfl, hp1]
  · have hE : IsEmpty ((unitObj (k := k) hn).blk c) := by
      rw [show (unitObj (k := k) hn).blk c = Fin (if c = ⟨0, hn⟩ then 1 else 0) from rfl,
        if_neg hc]
      infer_instance
    rw [if_neg hc]
    exact (hE.false j).elim

/-- **The evaluation of the pairing at the dual of a simple, entrywise**: on the unit channel it
is `S.ev i*` (this is the raw entry of `ev` at the object `X*`, before the `dual_dual`
reindexing that `WP2.trDual` performs on the left factor). -/
theorem ev_dual_sim_apply (hn : 0 < n) (i : Fin n) (c : Fin n)
    (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : (FusionMat.dual S (FusionMat.dual S (sim (k := k) i))).blk p.1)
    (t : (FusionMat.dual S (sim (k := k) i)).blk p.2)
    (j : (unitObj (k := k) hn).blk c) :
    FusionMat.ev S hn (FusionMat.dual S (sim (k := k) i)) c ⟨p, ν, s, t⟩ j
      = if c = ⟨0, hn⟩ then S.ev (S.ring.dual i) else 0 := by
  by_cases hc : c = ⟨0, hn⟩
  · subst hc
    have hp2 : p.2 = S.ring.dual p.1 := FusionMat.dual_label_of_unit S hn ν
    have hdd : S.ring.dual (S.ring.dual p.1) = i :=
      eq_of_sim_blk_nonempty (k := k) (i := i) (j := S.ring.dual (S.ring.dual p.1)) s
    have hp1 : p.1 = i := by rw [← S.ring.dual_involutive p.1]; exact hdd
    haveI : Subsingleton ((FusionMat.dual S (sim (k := k) i)).blk (S.ring.dual p.1)) := by
      show Subsingleton ((sim (k := k) i).blk (S.ring.dual (S.ring.dual p.1)))
      rw [hdd]
      exact subsingleton_sim_blk_self (k := k) i
    have hev : FusionMat.ev S hn (FusionMat.dual S (sim (k := k) i)) ⟨0, hn⟩ ⟨p, ν, s, t⟩ j
        = if (show (FusionMat.dual S (sim (k := k) i)).blk (S.ring.dual p.1) from s) = hp2 ▸ t
          then S.ev p.2 else 0 :=
      FusionMat.ev_apply_of_eq (S := S) (hn := hn)
        (X := FusionMat.dual S (sim (k := k) i)) (c := ⟨0, hn⟩) (h := hp2) (ν := ν)
        (s := s) (t := t) (j := j)
    rw [hev, if_pos (Subsingleton.elim _ _), if_pos rfl, hp2, hp1]
  · have hE : IsEmpty ((unitObj (k := k) hn).blk c) := by
      rw [show (unitObj (k := k) hn).blk c = Fin (if c = ⟨0, hn⟩ then 1 else 0) from rfl,
        if_neg hc]
      infer_instance
    rw [if_neg hc]
    exact (hE.false j).elim

end Coefficients

end FusionCategory

/-! ## §8 — Axiom audit -/

open FusionCategory in
#print axioms FusionCategory.Units.leftIdxEquiv_unitIdxL
open FusionCategory in
#print axioms FusionCategory.Units.rightIdxEquiv_unitIdxR
open FusionCategory in
#print axioms FusionCategory.Units.leftIdxEquiv_eq_iff
open FusionCategory in
#print axioms FusionCategory.Units.rightIdxEquiv_eq_iff
open FusionCategory in
#print axioms FusionCategory.Units.leftUnitor_eq_matrix
open FusionCategory in
#print axioms FusionCategory.Units.rightUnitor_eq_matrix
open FusionCategory in
#print axioms FusionCategory.Units.leftUnitorInv_eq_matrix
open FusionCategory in
#print axioms FusionCategory.Units.rightUnitorInv_eq_matrix
open FusionCategory in
#print axioms FusionCategory.exactPairingOfSnake
open FusionCategory in
#print axioms FusionCategory.snakeLeft_of_frozen
open FusionCategory in
#print axioms FusionCategory.snakeRight_of_frozen
open FusionCategory in
#print axioms FusionCategory.pairingOfSnake
open FusionCategory in
#print axioms FusionCategory.pairingOfSnake_coevaluation
open FusionCategory in
#print axioms FusionCategory.pairingOfSnake_evaluation
open FusionCategory in
#print axioms FusionCategory.pairingOfSnake_evaluation_dual
open FusionCategory in
#print axioms FusionCategory.hasRightDualOf
open FusionCategory in
#print axioms FusionCategory.hasRightDualOf_rightDual
open FusionCategory in
#print axioms FusionCategory.hasLeftDualOf
open FusionCategory in
#print axioms FusionCategory.rightRigidOf
open FusionCategory in
#print axioms FusionCategory.leftRigidOf
open FusionCategory in
#print axioms FusionCategory.rigidOf
open FusionCategory in
#print axioms FusionCategory.rigidOf_rightDual_m
open FusionCategory in
#print axioms FusionCategory.toStruct_whiskerLeft
open FusionCategory in
#print axioms FusionCategory.toStruct_whiskerRight
open FusionCategory in
#print axioms FusionCategory.toStruct_tensorObj_eq
open FusionCategory in
#print axioms FusionCategory.toStruct_tensorUnit_eq
open FusionCategory in
#print axioms FusionCategory.unitObj_eq_sim_zero
open FusionCategory in
#print axioms FusionCategory.tensorObj_sim_m_eq
open FusionCategory in
#print axioms FusionCategory.dual_sim
open FusionCategory in
#print axioms FusionCategory.IsFusionCategory.ofReconFusionCanonical
open FusionCategory in
#print axioms FusionCategory.reconFusionCanonicalOf
open FusionCategory in
#print axioms FusionCategory.reconIsFusionCanonical
open FusionCategory in
#print axioms FusionCategory.endUnitEquivOfCanonical
open FusionCategory in
#print axioms FusionCategory.subsingleton_sim_blk_self
open FusionCategory in
#print axioms FusionCategory.eq_of_sim_blk_nonempty
open FusionCategory in
#print axioms FusionCategory.coev_sim_apply
open FusionCategory in
#print axioms FusionCategory.ev_dual_sim_apply
