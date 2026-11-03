import FusionCategory.Statements
import FusionCategory.Prop821CNorm
import FusionCategory.Gauge
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Statements2 — the frozen statements of WP2 (Tasks 2.1–2.3, deliverable D4)

**Statements, definitions and glue only.**  No proposition of WP2 is proved here: the
reconstruction theorem, the pentagon/triangle, the snakes, the three trace-correspondence
statements and the three `derivedJ` targets are recorded as `Prop`-valued definitions or as
fields of a data structure, so that this file elaborates with no `sorry`, no `axiom` and no
proof of any programme statement.  This is the B4 pattern (`Statements.lean`) applied to WP2.

Source of truth: `docs/research-proposal.tex` WP2 (Tasks 2.1–2.3, D4), and
`FusionCategory/docs/wp2-design.md` (which governs where the two differ).

## What is frozen here, and where each proof is owed

* **Task 2.1 — the predicate.**  `FusionCategory.IsFusionCategory`: the named predicate that
  D4's success criterion cites ("the reconstructed category is a `FusionCategory` in the sense
  of the library's own definition").  §1, with the field list argued there.
* **Task 2.1 — the reconstruction target.**  `WP2.FusionMat` (objects), `WP2.Hom` (morphisms),
  the channel-refined index types, and `WP2.ReconFusion S`: the package whose inhabitant *is*
  the statement "the `FusionMat` reconstruction of `S` is a fusion category".  §2.
* **Task 2.2 — the trace correspondence.**  `WP2.trDual` / `WP2.trDualScalar` are the
  frozen *definition site* of the categorical trace (there is no trace API in the pinned
  Mathlib — checked, see the module docs of §3), and the three correspondence statements are
  `TraceOfScalar`, `TraceOfPivotalComponent`, `TraceProduct_eq_kappa`, plus the
  pseudo-unitarity link `TraceGlobalDim_eq_pseudoUnitary`.  §3.
* **Task 2.3 — the `derivedJ` interface.**  The frozen type is B4's
  (`∀ {n}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`), and the three targets are
  `DerivedJ_eq_settledJ` (the bridge to `Prop821CNorm.settledJ`), `DerivedJ_pointed_eq_delta_kappa`
  (the `δ(κ)` validation) and `DerivedJ_gauge_invariant` (gauge covariance).  §4.

  `derivedJ` is a *parameter* of these statements, exactly as in `Statements.lean`: its
  definition is Task 2.3's (D8 of this round) and this file freezes only its type and the
  equations it must satisfy.  In particular nothing here identifies `derivedJ` with the
  carried field `S.J`; the relation is `J_match` and only `J_match`.

The *only* theorems proved in this file are glue (§5): the arity/type checks that show the
frozen interface composes with the landed WP1 API (`Prop821CNorm.mult_of_J_match_settledJ`,
`Gauge.gauge`), and the arithmetic collapse of the general vertex-gauge factor under
dual-invariance (which is *why* the covariance law of §4 is an invariance).  They are marked
"glue" and they prove nothing that WP2 or WP3 owes.

## Three findings recorded (kernel-checked; see §1, §2 and §4 of the section docs)

1. **The design note's `IsFusionCategory` sketch is not compilable as written.**  It puts
   `[rigid : RigidCategory C]` in the field list of a `Prop`-valued class.  `RigidCategory C`
   carries data (`rightDual : ∀ X, HasRightDual X`, and `HasRightDual X` has a field
   `rightDual : C`), so it lives in `Type`, and a `Prop` cannot have it as a field.  The
   predicate therefore takes `RigidCategory C` (and `HasFiniteBiproducts C`) as *instance
   arguments* and keeps the four properties as `Prop`-valued fields.  §1.
2. **The reconstruction target needs `0 < n`.**  At `n = 0` there is no unit label: `FusionMat 0 k`
   has one object and one endomorphism, so `End(1) ≃+* k` is false for a nontrivial `k` and
   `ReconFusion S` is uninhabited.  The frozen statement therefore carries `hn : 0 < n`
   (`ReconIsFusion S hn`), the same gate the `FusionSystem` unit axioms already carry.  §2.
3. **Gauge covariance is invariance, and only on the signature's gauge group.**  The general
   vertex gauge moves the double-dual twist by the dual factor
   `λ_a λ_b λ_{c*} / (λ_c λ_{a*} λ_{b*})` (this is the WP1-round m1 observation recorded in
   `DoubleDual.lean`'s caveat); the gauge group of the corrected signature is the
   *dual-invariant* subgroup (`Gauge.gauge` takes `hlam`, and `Gauge.gauge_ev_dual_iff` shows
   this is exactly the stabiliser of `EvDual`), on which the factor is `1`.  So the covariance
   law to freeze is invariance under `Gauge.gauge`, and `gauge_dual_factor_eq_one` below is
   that collapse in the kernel.  §4.

Axiom budget of every declaration: `[propext, Classical.choice, Quot.sound]` (checked with
`#print axioms` at the end of the file).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace FusionCategory

open CategoryTheory MonoidalCategory CategoryTheory.Limits

/-! ## §1 — Task 2.1: the named predicate `IsFusionCategory`

### The field list, and why

The proposal asks the predicate to package four properties: **monoidal**, **rigid**,
**semisimple**, **`End(1) = k`**.  In the pinned Mathlib two of these are *structures carrying
data*, and the other two are properties:

* monoidal — `MonoidalCategory C`, a structure (tensor, associator, unitors + laws);
* rigid — `RigidCategory C`, a structure (`∀ X, HasRightDual X`, and `HasRightDual X` carries the
  dual *object* `rightDual : C` and an `ExactPairing`);
* semisimple — a property ("every object is a finite biproduct of simples, and there are
  finitely many simples up to iso");
* `End(1) = k` — a property (the existence of a ring isomorphism).

A `Prop` can hold the last two but not the first two.  Since the predicate's *use* is as a
hypothesis in statements (D4: "the reconstruction is a `FusionCategory` in the sense of the
library's own definition") and as a *name* for the four properties together, the form frozen
here is: the data-carrying structures are instance arguments (found by typeclass search, so
`Xᘁ`, `α_`, `⨁` all work downstream with no unpacking), and the property-valued content is the
field list.  This is also what makes the predicate *useful*: from `[IsFusionCategory k C]` a
consumer keeps every instance it already had, and gains semisimplicity and `End(1) = k`.

Deliberately **not** fields, with reasons:

* `MonoidalPreadditive C` — the bilinearity of the whiskerings.  It is part of "a `k`-linear
  monoidal category" as Mathlib packages it (`Linear k C` supplies the `Module` structures, and
  `MonoidalPreadditive` the compatibility); it is an argument, so that the *reconstruction*
  proves it as one of its morphism-level facts rather than assuming it of itself.
* `Nontrivial C` / `0 < n` — a fusion category has `1 ≠ 0`; in the reconstruction this is
  `0 < n`.  Left out: it is derivable from `end_unit` together with `End (𝟙_ C)` being a
  nontrivial ring only if one assumes `1 ≠ 0` in `k`, and `Hom(1,1) ≃+* k` already forces it
  (`k` is a field), so a separate field would be redundant.  Kept out to keep the predicate
  minimal.
* `Skeleton`/`Skeletal` — the *reconstruction* is skeletal by construction (`FusionMat`), and
  requiring it would exclude the honest applications of the predicate.  Not a fusion-category
  axiom in ENO's sense (ENO §2.1 requires finite semisimplicity, not skeletality). -/

/-- **The named predicate of WP2 Task 2.1.**  `C` is a fusion category over `k` when it is a
`k`-linear monoidal category (those as instance arguments), rigid (instance argument, carrying
the duals), with finite biproducts, whose hom-spaces are finite-dimensional, whose unit
endomorphism ring is `k`, with finitely many simple objects up to isomorphism, and every object
a finite biproduct of simples.

D4's success criterion is `[IsFusionCategory k C]` for `C` the `WP2.FusionMat` reconstruction
of a `FusionSystem` (`WP2.ReconFusion.fusion`, §2). -/
class IsFusionCategory (k : Type u) [Field k] (C : Type v) [Category C] [Preadditive C]
    [MonoidalCategory C] [Linear k C] [MonoidalPreadditive C] [RigidCategory C]
    [HasFiniteBiproducts C] : Prop where
  /-- **Finite-dimensional hom-spaces.**  `Hom(X,Y)` is a finite-dimensional `k`-vector space.
  (In the reconstruction this is immediate: a hom is a finite tuple of finite matrices.) -/
  hom_finite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)
  /-- **`End(1) = k`**: the endomorphism ring of the unit object is `k`.  Frozen as a ring
  isomorphism, not just a bijection: the trace correspondence (Task 2.2) reads the categorical
  trace `1 → 1` as a scalar through exactly this map, and multiplication in `End(1)` is what
  makes the trace multiplicative on the nose. -/
  end_unit : Nonempty (End (𝟙_ C) ≃+* k)
  /-- **Finitely many simples up to isomorphism.** -/
  simples_fin : ∃ (N : ℕ) (f : Fin N → C), (∀ i, Simple (f i)) ∧
    ∀ Y : C, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i)
  /-- **Finite semisimplicity**: every object is a finite biproduct of simple objects. -/
  decomposition : ∀ X : C, ∃ (m : ℕ) (f : Fin m → C), (∀ i, Simple (f i)) ∧
    Nonempty (X ≅ ⨁ f)

namespace IsFusionCategory

variable {k : Type u} [Field k] {C : Type v} [Category C] [Preadditive C]
  [MonoidalCategory C] [Linear k C] [MonoidalPreadditive C] [RigidCategory C]
  [HasFiniteBiproducts C]

/-- The `End(1) = k` isomorphism, extracted from the predicate.  Its existence is the field;
this is the usable form (the choice is `Classical.choice`, as everywhere in this library). -/
noncomputable def endUnit (h : IsFusionCategory k C) : End (𝟙_ C) ≃+* k :=
  Classical.choice h.end_unit

/-- The scalar of an endomorphism of the unit object, read through `End(1) = k`.  The
categorical trace of Task 2.2 lands in `End(1)` and is read as a scalar through this map. -/
noncomputable def unitScalar (h : IsFusionCategory k C) (x : End (𝟙_ C)) : k :=
  h.endUnit x

@[simp] theorem unitScalar_apply (h : IsFusionCategory k C) (x : End (𝟙_ C)) :
    h.unitScalar x = h.endUnit x := rfl

end IsFusionCategory

/-! ## §2 — Task 2.1: the reconstruction target

The object and morphism types are the design note's; they are *defined* here because the frozen
statements must be statable before the category structure exists.  The category/preadditive/
monoidal/rigid instances are **not** constructed here (that is D2–D6 of this round): they are
instance fields of `ReconFusion S`, so that "the reconstruction of `S` is a fusion category" is
a single `Prop`, `ReconIsFusion S`.

Naming: everything in this section is under `FusionCategory.WP2`, so that the canonical
`FusionCategory.FusionMat` of the base layer (`ReconBasic.lean`) can be merged with it without
a name clash — the definitions are identical in content (multiplicity vector and per-label block
matrices), and the merge is a `rfl`-level identification. -/

namespace WP2

/-- **Objects of the reconstruction**: multiplicity vectors, i.e. formal finite direct sums
`⨁_i X_i^{⊕ m_i}` of the `n` simples (the design note's `FusionMat`). -/
structure FusionMat (n : ℕ) (k : Type u) [Field k] : Type u where
  /-- The multiplicity of the simple `X_i`. -/
  m : Fin n → ℕ

/-- **Morphisms of the reconstruction**: one block per simple label, `(f i) : k^{m_i × m'_i}`.
Schur's lemma is structural — `Hom(X_i, X_j) = 0` for `i ≠ j` is the absence of off-diagonal
blocks. -/
def Hom {n : ℕ} {k : Type u} [Field k] (X Y : FusionMat n k) : Type u :=
  ∀ i : Fin n, Matrix (Fin (X.m i)) (Fin (Y.m i)) k

/-- The simple `X_i`, as a multiplicity vector. -/
def sim {n : ℕ} {k : Type u} [Field k] (i : Fin n) : FusionMat n k :=
  ⟨fun c => if c = i then 1 else 0⟩

/-- The unit object `1 = X₀`, as a multiplicity vector (written with `c.val = 0` so that it is
defined for `n = 0` too, where there are no labels and the vector is empty). -/
def unitMat (n : ℕ) (k : Type u) [Field k] : FusionMat n k :=
  ⟨fun c => if c.val = 0 then 1 else 0⟩

/-- **The tensor on objects**: the fusion-ring convolution
`(X ⊗ Y).m c = ∑_{a b} N_{ab}^{c} · m_a · m_b`. -/
def tensorMul {n : ℕ} {k : Type u} [Field k] (R : FusionRing n) (X Y : FusionMat n k)
    (c : Fin n) : ℕ :=
  ∑ a : Fin n, ∑ b : Fin n, R.N a b c * X.m a * Y.m b

/-- **The channel-refined index type of the `c`-block of `X ⊗ Y`**: a pair of labels, the
channel `Fin (N a b c)`, and the two block indices.  This is the index type the design note
prescribes for the tensor on morphisms and for the associator; by `chan_subsingleton` the
channel factor is a subsingleton, which is how multiplicity-freeness enters every reduction. -/
def Chan {n : ℕ} {k : Type u} [Field k] (R : FusionRing n) (X Y : FusionMat n k)
    (c : Fin n) : Type :=
  Σ (a : Fin n) (b : Fin n), Fin (R.N a b c) × Fin (X.m a) × Fin (Y.m b)

/-- **Multiplicity-freeness earns its keep**: the channel index set of a block is a
subsingleton, so a channel is unique when it exists and every "sum over the intermediate
channel" in the entrywise reductions collapses to a single term.  (The general fact behind
every `Σ_{e} N a b e · …` collapse in D3–D6.) -/
theorem chan_subsingleton {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (a b c : Fin n) : Subsingleton (Fin (S.ring.N a b c)) :=
  ⟨fun x y => Fin.ext (by
    have hx := x.isLt
    have hy := y.isLt
    have h := S.mult_free a b c
    omega)⟩

/-- The channel factor is either empty or a single point: `Fin (N a b c)` is `Fin 0` or
`Fin 1`.  (Recorded as the dichotomy the entrywise reductions use.) -/
theorem chan_eq_zero_or_one {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (a b c : Fin n) : S.ring.N a b c = 0 ∨ S.ring.N a b c = 1 := by
  have h := S.mult_free a b c
  omega

/-- **The frozen reconstruction package.**  An inhabitant of `ReconFusion S` is: a
category/preadditive/`k`-linear/monoidal/rigid structure on the multiplicity vectors, with
finite biproducts, whose tensor on objects is `S`'s convolution, whose unit is `X₀`, whose right
duals are `m ∘ dual`, and which satisfies `IsFusionCategory`.

The *morphism-level* identifications with `S`'s data (the associator is the `F`-block matrix, the
evaluation/coevaluation are `S.ev`/`S.coev`, the trace of a scalar is `κ`-normalised) are not
fields here: they are the separate frozen statements of §3 and the targets of D3–D7, because
stating them requires the channel-refinement equivalences (D4's `Chan`-bookkeeping), which are
not available before the instances exist.  Recording the object-level identification here pins
the reconstruction to `S` exactly where it can be pinned now. -/
structure ReconFusion {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) where
  [cat : Category.{u} (FusionMat n k)]
  [pre : Preadditive (FusionMat n k)]
  [mon : MonoidalCategory (FusionMat n k)]
  [lin : Linear k (FusionMat n k)]
  [monPre : MonoidalPreadditive (FusionMat n k)]
  [rig : RigidCategory (FusionMat n k)]
  [biprod : HasFiniteBiproducts (FusionMat n k)]
  /-- The tensor on objects is the fusion-ring convolution. -/
  tensorObj_m : ∀ (X Y : FusionMat n k) (c : Fin n), (X ⊗ Y).m c = tensorMul S.ring X Y c
  /-- The tensor unit is the vector supported at the unit label. -/
  tensorUnit_m : ∀ c : Fin n, (𝟙_ (FusionMat n k)).m c = if c.val = 0 then 1 else 0
  /-- The right dual is the duality-involution relabelling. -/
  rightDual_m : ∀ (X : FusionMat n k) (c : Fin n),
    (HasRightDual.rightDual X).m c = X.m (S.ring.dual c)
  /-- **D4's success criterion**: the reconstruction is a fusion category in the library's
  sense. -/
  fusion : IsFusionCategory k (FusionMat n k)

/-- **The frozen theorem statement of WP2 Task 2.1**: the `FusionMat` reconstruction of a
`FusionSystem n k` is a fusion category.  A `Prop` with no proof here; D2–D6 of this round
build the instances, and this is the statement they discharge.

The hypothesis `0 < n` is not decoration.  At `n = 0` there is no unit label, `FusionMat 0 k`
has a single object and a single endomorphism, so `End(1) ≃+* k` is *false* for a nontrivial
field and the frozen statement would be unprovable — the reconstruction target is a statement
about data with at least one simple.  (The same gate appears on `FusionSystem`'s unit axioms,
`F_left_unit`, `snake_left`, `J_unit_left`, … for exactly this reason.) -/
def ReconIsFusion {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  Nonempty (ReconFusion S)

/-! ## §3 — Task 2.2: the categorical trace and the trace correspondence

**There is no trace API in the pinned Mathlib.**  Checked by grep over
`/opt/mathlib/Mathlib/CategoryTheory`: no `leftTrace`, no `rightTrace`, no `trace_*` for rigid
categories.  Task 2.2 therefore *defines* the trace, and this section is its frozen definition
site: `FusionCategory.WP2.trDual` (valued in `End(1)`) and `WP2.trDualScalar` (valued in
`k`, through `IsFusionCategory.endUnit`).

The definition is the classical one for a morphism into the double dual, and it needs no pivotal
structure, no braiding and no linearity — only the two exact pairings `(X, X*)` and
`(X*, X**)`:

  `Tr(f : X ⟶ X**)  :=  η_X ≫ (f ▷ X*) ≫ ε_{X*} : 1 ⟶ 1`,

with `η_X : 1 ⟶ X ⊗ X*` the coevaluation of `ExactPairing X X*` and `ε_{X*} : X** ⊗ X* ⟶ 1` the
evaluation of `ExactPairing X* X**` (Mathlib's `evaluation' : Y ⊗ X ⟶ 1` is exactly this
order).  The two objects meet in the middle without an associator: `f ▷ X*` has type
`X ⊗ X* ⟶ X** ⊗ X*`.

In the reconstruction `X** = X` *on the nose* (`m ∘ dual ∘ dual = m`), so `Tr` applies verbatim
to an endomorphism `f : X ⟶ X` — this is the sense in which Task 2.2's "trace of `p_i : X_i → X_i**`"
and "trace of the scalar `a_i : End(X_i)`" are the same functional, and it is why the frozen
statements below quantify over a single `trSimple`.

### The frozen interface

As in `Statements.lean` for `derivedJ`, the trace is a *parameter* of the frozen statements
(`trSimple`), of B4's shape: `trSimple S i a` is the categorical trace, in the reconstruction of
`S`, of the endomorphism of the simple `X_i` whose block entry is `a ∈ k = End(X_i)`.  D7 of
this round supplies the definition (`WP2.trDualScalar` evaluated in the reconstruction, with
the `End(1) = k` of `IsFusionCategory.endUnit`) and proves the four statements.  The point of
freezing the interface is that the statements are well-posed *now*, and that they are equations
on a function of the datum, not a definition by fiat. -/

/-- The categorical trace of a morphism into the double dual, valued in `End(1)`.
`Tr(f) = η_X ≫ (f ▷ X*) ≫ ε_{X*}`.  This is Task 2.2's `Tr` — its frozen definition site. -/
noncomputable def trDual {C : Type v} [Category C] [MonoidalCategory C] {X : C}
    [HasRightDual X] [HasRightDual (HasRightDual.rightDual X)]
    (f : X ⟶ HasRightDual.rightDual (HasRightDual.rightDual X)) : 𝟙_ C ⟶ 𝟙_ C :=
  ExactPairing.coevaluation X (HasRightDual.rightDual X) ≫
    (f ▷ HasRightDual.rightDual X) ≫
    ExactPairing.evaluation (HasRightDual.rightDual X)
      (HasRightDual.rightDual (HasRightDual.rightDual X))

/-- The categorical trace as a scalar, through the `End(1) = k` identification. -/
noncomputable def trDualScalar {k : Type u} [Field k] {C : Type v} [Category C]
    [Preadditive C] [MonoidalCategory C] (e : End (𝟙_ C) ≃+* k) {X : C}
    [HasRightDual X] [HasRightDual (HasRightDual.rightDual X)]
    (f : X ⟶ HasRightDual.rightDual (HasRightDual.rightDual X)) : k :=
  e (trDual f)

/-- **Task 2.2(b), frozen.**  The categorical trace of the scalar `a` in `End(X_i)` is
`a · coev_i · ev_{i*}` — ENO's `d_i` at `p_i = a` (`Statements.dimENO` is the same expression at
`a = p_i`).  This is the statement that closes the gap between the library's scalars and the
source's dimensions: the right-hand side is ENO's formula, the left-hand side is the trace. -/
def TraceOfScalar {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n k) (i : Fin n) (a : k),
    trSimple S i a = a * S.coev i * S.ev (S.ring.dual i)

/-- **Task 2.2(a), frozen.**  The categorical trace of the pivotal component `p_i : X_i → X_i**`
is `p_i κ_i`, which is the categorical dimension `dim P i` of the simple.  (Both sides are
`End(X_i)`-valued in the reconstruction because `X** = X` on objects; the pivotal component is
the scalar `P.p i`.) -/
def TraceOfPivotalComponent {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n k) (P : PivotalStructure S) (i : Fin n),
    trSimple S i (P.pVal i) = dim P i

/-- **Task 2.2(c), frozen.**  `κ_i κ_{i*} = |X_i|²` in the pseudo-unitarity sense: the product
of the two categorical dimensions (of `X_i` and of `X_{i*}`) is `κ_i κ_{i*}`.  This is the
trace-level form of `PseudoUnitary.dim_mul_dim_dual`; note it is stated with the *traces*, so it
is a statement about the reconstruction's trace functional and not only about the scalars. -/
def TraceProduct_eq_kappa {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n k) (P : PivotalStructure S) (i : Fin n),
    trSimple S i (P.pVal i) * trSimple S (S.ring.dual i) (P.pVal (S.ring.dual i))
      = S.kappa i * S.kappa (S.ring.dual i)

/-- **Task 2.2(c) at `ℂ`, the pseudo-unitarity link.**  Summing the previous statement over the
simples turns it into exactly the pseudo-unitarity equation `dim(C) = FPdim(C)` of
`Statements.IsPseudoUnitaryC`, i.e. `Σ_i κ_i κ_{i*} = FPdim(C)`.  Frozen at `ℂ` because that is
the field of the scalar contract (`Statements.lean` §Task 1.1). -/
def TraceGlobalDim_eq_pseudoUnitary (trC : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → ℂ → ℂ) : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData) (P : PivotalStructure S),
    (∑ i : Fin n, trC S i (P.pVal i) * trC S (S.ring.dual i) (P.pVal (S.ring.dual i)))
        = algebraMap ℝ ℂ hFP.globalDim ↔ IsPseudoUnitaryC S hFP

end WP2

end FusionCategory

#check @FusionCategory.WP2.trDual
#check @FusionCategory.WP2.ReconFusion
#check @FusionCategory.IsFusionCategory

namespace FusionCategory

namespace WP2

/-! ## §4 — Task 2.3: the `derivedJ` interface

`derivedJ` is defined by D8 of this round as the `(k,k)`-entry, in the channel basis, of the
tensorator `X_i** ⊗ X_j** ⟶ (X_i ⊗ X_j)**` of the monoidal structure of the double-dual functor
— a *morphism* of the reconstruction, hence a function of `(F, ev, coev)`.  This section freezes
only its **type** (B4's, `Statements.lean`) and the four equations it must satisfy.  It is a
parameter of every statement below, never a table identified with the carried field `S.J`; the
relation between them is `J_match` and only `J_match` (`Statements.J_match`).

Why the parameter: the false-`J` datum (`Examples/Z2SqFalseJ.lean`: `(Z/2)²` with `J ≡ 1`) carries
every law the signature imposes and refuses to be a derived twist, so `J_match` at an arbitrary
candidate is not a restriction (`Statements.J_match_carried` makes that a `rfl`).  Freezing the
interface separately from the definition keeps the two obligations apart: D8 owes the
*definition* and the *pointed-case theorem*; WP3 owes the four laws and the per-instance
`J_match`. -/

/-- **Pointedness** (used by `DerivedJ_pointed_eq_delta_kappa`): the tensor product of two
simples is a single simple.  With `FusionSystem.mult_free` this is the honest reading of
"pointed" for the skeletal datum — the fusion ring is that of a finite group. -/
def Pointed {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : Prop :=
  ∀ a b : Fin n, ∃! c : Fin n, 0 < S.ring.N a b c

section DerivedJ

/- **The frozen type of `derivedJ`** (B4, `Statements.lean`'s `DerivedTwist` section): a
function of the datum alone.  Written out in full here as the type of the parameter, and
type-checked against `ENO823ExactC` below. -/
variable (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ)

/-- The qualification `J_match` at the derived twist, as used in `ENO823ExactC`'s antecedent. -/
def J_match_at_derivedJ {n : ℕ} (S : FusionSystem n ℂ) : Prop := J_match S (derivedJ S)

/-- **The type check against B4**: `ENO823ExactC` applied to `derivedJ`.  That this definition
elaborates *is* the frozen-type check — `ENO823ExactC`'s first parameter is
`∀ {n}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`, and the `derivedJ` above has exactly that
type, so Task 2.3's eventual definition drops into the frozen target with no coercion. -/
noncomputable def ENO823ExactC_at_derivedJ {n : ℕ} (S : FusionSystem n ℂ)
    (hFP : S.ring.FPData) : Prop := ENO823ExactC derivedJ S hFP

/-- **The frozen target, first form**: B4's exact target at the derived twist, universally over
data.  This is the statement WP3 discharges once `J_match` is proved for the derived twist. -/
noncomputable def FrozenENO823ExactC_at_derivedJ : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData), ENO823ExactC derivedJ S hFP

/-- **Task 2.3 target 1 — the `settledJ` bridge.**  On pseudo-unitary data the derived twist is
the *settled* twist `f_c κ_a κ_b / (κ_c f_a f_b)` of `Prop821CNorm.settledJ`, on every supported
channel.  This is the bridge WP3 consumes: `Prop821CNorm.j_match_settledJ_iff` identifies the
statement with the per-channel law (K) of WP1 Task 1.4, and
`Prop821CNorm.mult_of_J_match_settledJ` turns it into multiplicativity of every pivotal
dimension (WP3's acceptance test (M)).

Pseudo-unitarity is in the hypothesis because the settled twist involves `f = FPdim`, while
`derivedJ` is computed from `(F, ev, coev)`; without pseudo-unitarity the two live on different
scales (the design note: "on pseudo-unitary data, `derivedJ = settledJ` is the expected
theorem").  At `fpdim ≡ 1` — the pointed normalisation — the two frozen targets agree by
`settledJ_eq_delta_kappa_of_fpdim_one` below. -/
def DerivedJ_eq_settledJ : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData), IsPseudoUnitaryC S hFP →
    ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJ S a b c = settledJ S hFP a b c

/-- **Task 2.3 target 2 — the `δ(κ)` validation.**  On *pointed* data the derived twist is
`δ(κ)`: `J^c_{ab} = κ_a κ_b / κ_c` on every supported channel.  This is the kernel version of
what `docs/honest_twist_check.py` does at script level, and it is the case on which the
false-`J` datum `(Z/2)²` with `J ≡ 1` is refuted.  D8 of this round proves it. -/
def DerivedJ_pointed_eq_delta_kappa : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ), Pointed S → ∀ a b c : Fin n, 0 < S.ring.N a b c →
    derivedJ S a b c = S.kappa a * S.kappa b / S.kappa c

/-- **Task 2.3 target 3 — gauge covariance.**  The derived twist is *invariant* under the vertex
gauge of the corrected signature (`Gauge.gauge`: `coev i ↦ λ_i coev i`, `ev i ↦ ev i / λ_i`, all
else fixed, `λ` dual-invariant).

This is the frozen form of the WP1-round m1 finding.  The unnormalised vertex gauge would move
the double-dual twist by the *dual factor* `λ_a λ_b λ_{c*} / (λ_c λ_{a*} λ_{b*})` (recorded in
`DoubleDual.lean`'s caveat); the gauge group of the signature is the dual-invariant subgroup
(`Gauge.gauge` demands `hlam`, and `Gauge.gauge_ev_dual_iff` proves that is exactly the
stabiliser of the Task 1.4 normalisation `EvDual`), on which the factor is `1` by
`gauge_dual_factor_eq_one` below.  Hence invariance — and hence
`J_match S (derivedJ S) ↔ J_match (gauge S λ) (derivedJ (gauge S λ))` (`j_match_gauge_iff`
below), because the gauge leaves the carried field `S.J` alone (`Gauge.gauge` keeps `J`): the
qualification is a statement about the *datum*, not about the choice of evaluations. -/
def DerivedJ_gauge_invariant : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin n),
    0 < S.ring.N a b c → derivedJ (gauge S lam hlam) a b c = derivedJ S a b c

/-- **The interface element WP3's ratio formula needs**: the derived twist does not vanish on a
supported channel.  (`research-proposal.tex` Task 3.2: "its statement includes the nonvanishing of
both components on every supported channel — available because `ψ` is an isomorphism and the
channels are one-dimensional under `mult_free`, not by cancellation".)  Frozen so that WP3 can
state the ratio `ψ_{a,b}/ψ_{b*,a*}` without an extra hypothesis. -/
def DerivedJ_ne_zero : Prop :=
  ∀ {n : ℕ} (S : FusionSystem n ℂ) (a b c : Fin n), 0 < S.ring.N a b c →
    derivedJ S a b c ≠ 0

end DerivedJ

/-! ## §5 — glue

The theorems below are the only proofs in this file.  They are the type-checks and arithmetic
that show the frozen interface is *consistent* and *composes with the landed WP1 API*; none of
them proves a WP2 statement. -/

/-- **The dual factor of the general vertex gauge collapses on dual-invariant gauges.**  The
double-dual twist of a vertex-gauged datum is multiplied by `λ_a λ_b λ_{c*} / (λ_c λ_{a*}
λ_{b*})` (`DoubleDual.lean`'s caveat, the WP1-round m1 observation); for a dual-invariant `λ`
that factor is `1`.  This is *why* the covariance law of `DerivedJ_gauge_invariant` is an
invariance, in the kernel. -/
theorem gauge_dual_factor_eq_one {n : ℕ} {k : Type u} [Field k] (R : FusionRing n)
    (lam : Fin n → k) (h : ∀ i, lam (R.dual i) = lam i) (hne : ∀ i, lam i ≠ 0)
    (a b c : Fin n) :
    lam a * lam b * lam (R.dual c) / (lam c * lam (R.dual a) * lam (R.dual b)) = 1 := by
  rw [h c, h a, h b]
  have ha := hne a
  have hb := hne b
  have hc := hne c
  field_simp

/-- **Consistency of the two frozen `derivedJ` targets.**  At `FPdim ≡ 1` — the pointed
normalisation, where every simple of a pointed fusion category is invertible and hence has
FP-dimension `1` — the settled twist *is* `δ(κ)`, so `DerivedJ_eq_settledJ` and
`DerivedJ_pointed_eq_delta_kappa` do not contradict each other.  A kernel check that the freeze
of §4 is coherent. -/
theorem settledJ_eq_delta_kappa_of_fpdim_one {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    (S : FusionSystem n k) (hFP : S.ring.FPData) (h1 : ∀ i : Fin n, hFP.fpdim i = 1)
    (a b c : Fin n) :
    settledJ S hFP a b c = S.kappa a * S.kappa b / S.kappa c := by
  simp only [settledJ, h1, map_one, one_mul, mul_one]

/-- **Glue: the covariance law makes `J_match` a *gauge-invariant* qualification.**  If the
derived twist is invariant under the signature's vertex gauge (`DerivedJ_gauge_invariant`, which
is what the covariance law of Task 2.3 freezes to — see the finding in §4), then
`J_match S (derivedJ S)` holds of a datum exactly when it holds of any gauge translate of it.  So
the qualification is a statement about the datum and not about the choice of evaluations — the
"so that" clause of D4's success criterion, in the kernel.  (The gauge fixes `S.J` and `S.ring`,
both by `rfl`, which is what makes the transport free.) -/
theorem j_match_gauge_iff {n : ℕ}
    {dJ : ∀ {m : ℕ}, FusionSystem m ℂ → Fin m → Fin m → Fin m → ℂ}
    (h : DerivedJ_gauge_invariant dJ) (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) :
    J_match S (dJ S) ↔ J_match (gauge S lam hlam) (dJ (gauge S lam hlam)) := by
  have hN : ∀ a b c : Fin n, (0 < (gauge S lam hlam).ring.N a b c) ↔ (0 < S.ring.N a b c) :=
    fun _ _ _ => Iff.rfl
  constructor
  · intro hJ a b c hP
    have hstep : dJ (gauge S lam hlam) a b c = dJ S a b c :=
      h S lam hlam a b c ((hN a b c).mpr hP)
    rw [hstep]
    exact hJ a b c hP
  · intro hJ a b c hP
    have hP' : 0 < (gauge S lam hlam).ring.N a b c := (hN a b c).mp hP
    have hstep : dJ (gauge S lam hlam) a b c = dJ S a b c := h S lam hlam a b c hP'
    have h1 : S.J a b c = dJ (gauge S lam hlam) a b c := hJ a b c hP'
    rw [hstep] at h1
    exact h1

/-- **Glue: the frozen trace statements are coherent.**  Statement (b) — the trace of a scalar
is `a · coev_i · ev_{i*}` — implies statement (a) — the trace of the pivotal component is
`p_i κ_i` — using only the Task 1.4 normalisation `ev_{i*} = ev_i`, which the signature now
carries as the field `FusionSystem.ev_dual`.  So D7 needs to prove *(b) only*: (a) then follows,
and it is the proposal's wording (`p_i κ_i`) up to that normalisation. -/
theorem traceOfPivotalComponent_of_traceOfScalar {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) (h : TraceOfScalar trSimple) :
    TraceOfPivotalComponent trSimple := by
  intro n S P i
  show trSimple S i (P.pVal i) = (P.p i : k) * (S.coev i * S.ev i)
  calc trSimple S i (P.pVal i)
      = P.pVal i * S.coev i * S.ev (S.ring.dual i) := h S i (P.pVal i)
    _ = (P.p i : k) * (S.coev i * S.ev i) := by rw [S.ev_dual i]; ring

/-- **Glue: (c) is the pseudo-unitarity equation.**  Summing the frozen statement (c) over the
simples gives exactly `Statements.IsPseudoUnitaryC` — `Σ_i κ_i κ_{i*} = FPdim(C)`, the source's
`dim(C) = FPdim(C)`.  So `TraceGlobalDim_eq_pseudoUnitary` is not an extra assumption: it is (c)
plus the definition of pseudo-unitarity.  This is the kernel form of the design note's "`κ_i κ_{i*}
= |X_i|²` in the sense of Definition `def:pseudo`". -/
theorem traceGlobalDim_iff_pseudoUnitary (trC : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → ℂ → ℂ)
    (h : TraceProduct_eq_kappa trC) : TraceGlobalDim_eq_pseudoUnitary trC := by
  intro n S hFP P
  have hsum : (∑ i : Fin n,
        trC S i (P.pVal i) * trC S (S.ring.dual i) (P.pVal (S.ring.dual i)))
      = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) :=
    Finset.sum_congr rfl fun i _ => h S P i
  rw [hsum]
  exact Iff.rfl

/-- **Glue: (b) *is* ENO's `d_i`.**  Statement (b) at `a = p_i` is literally
`Statements.dimENO`: the right-hand side of the frozen equation is `p_i · coev_i · ev_{i*}`, which
is `dimENO P i` by definition.  This one-liner is the kernel statement that the trace-correspondence
target of Task 2.2 and the source's dimension formula are the same expression — the "gap between
the library's scalars and the source's dimensions" that D4's success criterion calls for. -/
theorem traceOfPivotalComponent_eq_dimENO {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) (h : TraceOfScalar trSimple)
    {n : ℕ} (S : FusionSystem n k) (P : PivotalStructure S) (i : Fin n) :
    trSimple S i (P.pVal i) = dimENO P i :=
  h S i (P.pVal i)

/-- **Glue: (b) implies (c)**, the `κ_i κ_{i*} = |X_i|²` statement at trace level, using
`p_{i*} = p_i⁻¹` (`PivotalStructure.pVal_dual`, which needs `0 < n`) and again `ev_dual`.  So
the three frozen statements of Task 2.2 are not independent obligations: (b) is the one with
content and the other two follow. -/
theorem traceProduct_of_traceOfScalar {k : Type u} [Field k]
    (trSimple : ∀ {n : ℕ}, FusionSystem n k → Fin n → k → k) (h : TraceOfScalar trSimple) :
    TraceProduct_eq_kappa trSimple := by
  intro n S P i
  change trSimple S i (P.pVal i) * trSimple S (S.ring.dual i) (P.pVal (S.ring.dual i))
    = S.kappa i * S.kappa (S.ring.dual i)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact i.elim0
    · exact h0
  have hp : P.pVal i ≠ 0 := P.pVal_ne_zero i
  have h1 : trSimple S i (P.pVal i) = P.pVal i * S.coev i * S.ev i := by
    calc trSimple S i (P.pVal i) = P.pVal i * S.coev i * S.ev (S.ring.dual i) := h S i (P.pVal i)
      _ = P.pVal i * S.coev i * S.ev i := by rw [S.ev_dual i]
  have h2 : trSimple S (S.ring.dual i) (P.pVal (S.ring.dual i))
      = (P.pVal i)⁻¹ * S.coev (S.ring.dual i) * S.ev i := by
    calc trSimple S (S.ring.dual i) (P.pVal (S.ring.dual i))
        = P.pVal (S.ring.dual i) * S.coev (S.ring.dual i) * S.ev (S.ring.dual (S.ring.dual i)) :=
          h S (S.ring.dual i) (P.pVal (S.ring.dual i))
      _ = (P.pVal i)⁻¹ * S.coev (S.ring.dual i) * S.ev i := by
          rw [P.pVal_dual hn i, S.ev_dual (S.ring.dual i), S.ev_dual i]
  rw [h1, h2]
  show (P.p i : k) * S.coev i * S.ev i * ((P.p i : k)⁻¹ * S.coev (S.ring.dual i) * S.ev i)
      = (S.coev i * S.ev i) * (S.coev (S.ring.dual i) * S.ev (S.ring.dual i))
  rw [S.ev_dual i]
  calc (P.p i : k) * S.coev i * S.ev i * ((P.p i : k)⁻¹ * S.coev (S.ring.dual i) * S.ev i)
      = ((P.p i : k) * ((P.p i : k))⁻¹) * (S.coev i * S.ev i)
          * (S.coev (S.ring.dual i) * S.ev i) := by ring
    _ = (S.coev i * S.ev i) * (S.coev (S.ring.dual i) * S.ev i) := by
          rw [mul_inv_cancel₀ hp]; ring

/-- **Glue: the `settledJ` bridge yields `J_match` at the settled twist.**  Pointwise
transitivity of the two equalities.  Together with the landed
`Prop821CNorm.mult_of_J_match_settledJ` this is the chain by which the derived twist reaches
WP1's multiplicativity (recorded as `mult_of_derivedJ_settledJ`). -/
theorem j_match_of_derivedJ_settledJ {n : ℕ} {derivedJ : ∀ {m : ℕ}, FusionSystem m ℂ → Fin m → Fin m → Fin m → ℂ}
    (S : FusionSystem n ℂ) (hFP : S.ring.FPData)
    (h : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJ S a b c = settledJ S hFP a b c)
    (hJ : J_match S (derivedJ S)) : J_match S (settledJ S hFP) :=
  fun a b c hN => (hJ a b c hN).trans (h a b c hN)

/-- **Glue: the derived twist, once matched to the settled one, makes every pivotal dimension
multiplicative on the fusion ring.**  This is WP3's acceptance test (M) as a consequence of the
frozen interface and the landed WP1 theorem `Prop821CNorm.mult_of_J_match_settledJ`; the only
inputs are `J_match` at the derived twist and the bridge `DerivedJ_eq_settledJ`. -/
theorem mult_of_derivedJ_settledJ {n : ℕ}
    {derivedJ : ∀ {m : ℕ}, FusionSystem m ℂ → Fin m → Fin m → Fin m → ℂ}
    (S : FusionSystem n ℂ) (hFP : S.ring.FPData) (hn : 0 < n)
    (h : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJ S a b c = settledJ S hFP a b c)
    (hJ : J_match S (derivedJ S)) (P : PivotalStructure S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c) = dim P a * dim P b :=
  mult_of_J_match_settledJ (S := S) hFP hn
    (fun a b c hN => (hJ a b c hN).trans (h a b c hN)) P

/-! ## §6 — the type checks against B4 -/

-- The frozen type applied in `J_match`, exactly as `Statements.ENO823ExactC` writes it.
#check fun (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) {n : ℕ}
    (S : FusionSystem n ℂ) => J_match S (dJ S)
-- The frozen type applied in B4's exact target.
#check fun (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) {n : ℕ}
    (S : FusionSystem n ℂ) (hFP : S.ring.FPData) => ENO823ExactC dJ S hFP
-- The frozen `Tr`, applied to an endomorphism of a simple in the reconstruction's shape.
#check @trDual

/-! ### The frozen statements unfold by `rfl` (nothing is smuggled into a definition) -/

example (trSimple : ∀ {n : ℕ}, FusionSystem n ℚ → Fin n → ℚ → ℚ) : TraceOfScalar trSimple =
    (∀ {n : ℕ} (S : FusionSystem n ℚ) (i : Fin n) (a : ℚ),
      trSimple S i a = a * S.coev i * S.ev (S.ring.dual i)) := rfl

example (trSimple : ∀ {n : ℕ}, FusionSystem n ℚ → Fin n → ℚ → ℚ) :
    TraceOfPivotalComponent trSimple =
    (∀ {n : ℕ} (S : FusionSystem n ℚ) (P : PivotalStructure S) (i : Fin n),
      trSimple S i (P.pVal i) = dim P i) := rfl

example (trSimple : ∀ {n : ℕ}, FusionSystem n ℚ → Fin n → ℚ → ℚ) :
    TraceProduct_eq_kappa trSimple =
    (∀ {n : ℕ} (S : FusionSystem n ℚ) (P : PivotalStructure S) (i : Fin n),
      trSimple S i (P.pVal i) * trSimple S (S.ring.dual i) (P.pVal (S.ring.dual i))
        = S.kappa i * S.kappa (S.ring.dual i)) := rfl

example (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    DerivedJ_eq_settledJ dJ =
      (∀ {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData), IsPseudoUnitaryC S hFP →
        ∀ a b c : Fin n, 0 < S.ring.N a b c → dJ S a b c = settledJ S hFP a b c) := rfl

example (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    DerivedJ_pointed_eq_delta_kappa dJ =
      (∀ {n : ℕ} (S : FusionSystem n ℂ), Pointed S → ∀ a b c : Fin n, 0 < S.ring.N a b c →
        dJ S a b c = S.kappa a * S.kappa b / S.kappa c) := rfl

example (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    DerivedJ_gauge_invariant dJ =
      (∀ {n : ℕ} (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
        (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin n),
        0 < S.ring.N a b c → dJ (gauge S lam hlam) a b c = dJ S a b c) := rfl

example (dJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) {n : ℕ}
    (S : FusionSystem n ℂ) : J_match_at_derivedJ dJ S = J_match S (dJ S) := rfl

end WP2

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.IsFusionCategory
#print axioms FusionCategory.IsFusionCategory.endUnit
#print axioms FusionCategory.IsFusionCategory.unitScalar
#print axioms FusionCategory.WP2.FusionMat
#print axioms FusionCategory.WP2.Hom
#print axioms FusionCategory.WP2.sim
#print axioms FusionCategory.WP2.unitMat
#print axioms FusionCategory.WP2.tensorMul
#print axioms FusionCategory.WP2.Chan
#print axioms FusionCategory.WP2.chan_subsingleton
#print axioms FusionCategory.WP2.chan_eq_zero_or_one
#print axioms FusionCategory.WP2.ReconFusion
#print axioms FusionCategory.WP2.ReconIsFusion
#print axioms FusionCategory.WP2.trDual
#print axioms FusionCategory.WP2.trDualScalar
#print axioms FusionCategory.WP2.TraceOfScalar
#print axioms FusionCategory.WP2.TraceOfPivotalComponent
#print axioms FusionCategory.WP2.TraceProduct_eq_kappa
#print axioms FusionCategory.WP2.TraceGlobalDim_eq_pseudoUnitary
#print axioms FusionCategory.WP2.J_match_at_derivedJ
#print axioms FusionCategory.WP2.ENO823ExactC_at_derivedJ
#print axioms FusionCategory.WP2.FrozenENO823ExactC_at_derivedJ
#print axioms FusionCategory.WP2.DerivedJ_eq_settledJ
#print axioms FusionCategory.WP2.DerivedJ_pointed_eq_delta_kappa
#print axioms FusionCategory.WP2.DerivedJ_gauge_invariant
#print axioms FusionCategory.WP2.DerivedJ_ne_zero
#print axioms FusionCategory.WP2.Pointed
#print axioms FusionCategory.WP2.gauge_dual_factor_eq_one
#print axioms FusionCategory.WP2.traceOfPivotalComponent_of_traceOfScalar
#print axioms FusionCategory.WP2.traceProduct_of_traceOfScalar
#print axioms FusionCategory.WP2.traceOfPivotalComponent_eq_dimENO
#print axioms FusionCategory.WP2.traceGlobalDim_iff_pseudoUnitary
#print axioms FusionCategory.WP2.settledJ_eq_delta_kappa_of_fpdim_one
#print axioms FusionCategory.WP2.j_match_gauge_iff
#print axioms FusionCategory.WP2.j_match_of_derivedJ_settledJ
#print axioms FusionCategory.WP2.mult_of_derivedJ_settledJ
