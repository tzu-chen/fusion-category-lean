/-
# WP2 round 3, member m1, direction D7 — the derivedJ tensorator

`DerivedJScalar.lean` defines the *scalar* `derivedJGen S a b c` — the `(c,c)`
entry of the tensorator `X_a** ⊗ X_b** ⟶ (X_a ⊗ X_b)**` in the channel basis —
as a ratio of two comparison scalars.  This file builds the **morphism**:

* `doubleDualObj` / `doubleDualMap` / `doubleDualFunctor`: the double-dual
  endofunctor `(−)**` on the reconstruction `FusionMat n k`, identity on objects
  (`doubleDualObj_eq`, from `dual_dual`) and the transport action on morphisms;
* `omegaCoeff`: the coefficient of the tensorator written **from the associator
  alone** — two `F`-entries and two `Finv`-entries, no `ev`, no `coev`, no
  normalisation of the duality data;
* `derivedJGen_eq_omegaCoeff`: the two forms agree, i.e. **the duality
  normalisation cancels out of the tensorator's coefficient**.  This is the
  kernel-checked form of the `J = ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}` derivation:
  the `ev`-factors in numerator and denominator cancel by `ev_dual`;
* `tensorator`: the morphism
  `tensorObj S (dual (dual X)) (dual (dual Y)) ⟶ dual (dual (tensorObj S X Y))`,
  the block matrix whose entry at a doubly-dual source index and the matching
  target index is `derivedJGen S a b c` for the channel `(a,b;c)`, and `0` off
  the matching pattern.  It is *not* the transported identity: the coefficients
  are the datum's, which is the content of the `(−)**` monoidal structure;
* `tensorator_apply_self`, `tensorator_apply_of_ne`: the entry of the tensorator
  on / off its index pattern;
* `tensorator_entry_sim`: **the entry theorem** — at the `(a,b)`-channel of
  `sim a ⊗ sim b` the `(c,c)`-entry of the tensorator is `derivedJGen S a b c`;
  `tensorator_entry_sim_omega` is the same in associator-only form, and
  `tensorator_apply_sim` strengthens it: since the simple blocks are
  subsingletons (§6a), the *whole* component is that scalar;
* `tensorator_entry_sim_pointed`, `channelTwist_diagonal_pointed`: on pointed
  data the entries are the `δ(κ)` gauge matrix `κ_a κ_b / κ_c` (D7's stretch);
* `tensorator_mul_invBlock`, `invBlock_mul_tensorator`: on a channel with
  `derivedJGen ≠ 0` the component is invertible, with the scalar inverse —
  the channel-level form of "`(−)**` is an equivalence";
* `tensorator_eq_naive_comp_channelTwist`: the tensorator is the naive
  `dual_dual` identification followed by the diagonal channel twist, and
  `tensorator_ne_naive_of_coeff_ne_one` says the two differ wherever the
  derived twist is not `1` (witnessed on the honest `(Z/2)²` datum in §10);
* `tensorCoeff_gauge`, `tensorIdxMap_gauge`, `tensorator_entry_sim_gauge`: the
  tensorator is **invariant under the vertex gauge** `ev ↦ ev/λ`,
  `coev ↦ λ·coev` — it is a morphism of the reconstruction and not a function
  of the duality normalisation.

What is *not* claimed here (and why): the tensorator's functoriality
(`μ_{X⊗Y,Z} ∘ (μ_{X,Y} ⊗ id) = μ_{X,Y⊗Z} ∘ α` and unitality as a monoidal
structure on `(−)**`) is the pentagon/triangle of the reconstruction, i.e. it
needs `AssociatorNatural` (D2) and `PentagonShape` (D3) together with the snake
equations (D4); the mate description of the tensorator needs the rigidity
packaging of D5.  This file proves the entry theorem unconditionally, with no
hypothesis beyond the datum, and records the exact residual in the report.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJScalar
import FusionCategory.DerivedJLaws
import FusionCategory.ReconRigid
import FusionCategory.ReconAssoc
import FusionCategory.Examples.Z2SqHonest
import FusionCategory.DerivedJPointed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat

/-! ## §1 — the double-dual endofunctor -/

section Endo

variable (S : FusionSystem n k)

/-- The double dual of an object, `X**`. -/
def doubleDualObj (X : FusionMat n k) : FusionMat n k := dual S (dual S X)

@[simp] theorem doubleDualObj_m (X : FusionMat n k) (c : Fin n) :
    (doubleDualObj S X).m c = X.m (S.ring.dual (S.ring.dual c)) := rfl

@[simp] theorem doubleDualObj_blk (X : FusionMat n k) (c : Fin n) :
    (doubleDualObj S X).blk c = X.blk (S.ring.dual (S.ring.dual c)) := rfl

/-- The double dual is the identity on objects. -/
theorem doubleDualObj_eq (X : FusionMat n k) : doubleDualObj S X = X := dual_dual S X

/-- The action of `(−)**` on morphisms: `f ↦ f`, read at the doubly dual label. -/
def doubleDualMap {X Y : FusionMat n k} (f : X ⟶ Y) :
    doubleDualObj S X ⟶ doubleDualObj S Y :=
  fun c => f (S.ring.dual (S.ring.dual c))

@[simp] theorem doubleDualMap_apply {X Y : FusionMat n k} (f : X ⟶ Y) (c : Fin n)
    (r : X.blk (S.ring.dual (S.ring.dual c))) (q : Y.blk (S.ring.dual (S.ring.dual c))) :
    doubleDualMap S f c r q = f (S.ring.dual (S.ring.dual c)) r q := rfl

theorem doubleDualMap_id (X : FusionMat n k) :
    doubleDualMap S (𝟙 X) = 𝟙 (doubleDualObj S X) := rfl

theorem doubleDualMap_comp {X Y Z : FusionMat n k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    doubleDualMap S (f ≫ g) = doubleDualMap S f ≫ doubleDualMap S g := rfl

/-- **The double-dual endofunctor** on the reconstruction. -/
def doubleDualFunctor : FusionMat n k ⥤ FusionMat n k where
  obj := doubleDualObj S
  map f := doubleDualMap S f
  map_id X := doubleDualMap_id S X
  map_comp f g := doubleDualMap_comp S f g

@[simp] theorem doubleDualFunctor_obj (X : FusionMat n k) :
    (doubleDualFunctor S).obj X = doubleDualObj S X := rfl

/-- The endofunctor is the identity on objects, up to `dual_dual`. -/
theorem doubleDualFunctor_obj_eq (X : FusionMat n k) : (doubleDualFunctor S).obj X = X :=
  doubleDualObj_eq S X

end Endo

/-! ## §2 — the label identity that makes the tensorator well typed

`(−)**` applied to the *label* leaves every fusion coefficient unchanged
(`N i j k = N i** j** k**`, twice `dual_symm`).  This is what identifies the
channel of the source `X** ⊗ Y**` with the channel of the target `(X ⊗ Y)**`. -/

theorem N_doubleDual_eq (S : FusionSystem n k) (i j l : Fin n) :
    S.ring.N (S.ring.dual (S.ring.dual i)) (S.ring.dual (S.ring.dual j))
        (S.ring.dual (S.ring.dual l)) = S.ring.N i j l := by
  have h1 := S.ring.dual_symm i j l
  have h2 := S.ring.dual_symm (S.ring.dual j) (S.ring.dual i) (S.ring.dual l)
  exact (h1.trans h2).symm

theorem N_doubleDual_eq' (S : FusionSystem n k) (i j l : Fin n) :
    S.ring.N i j l = S.ring.N (S.ring.dual (S.ring.dual i))
      (S.ring.dual (S.ring.dual j)) (S.ring.dual (S.ring.dual l)) :=
  (N_doubleDual_eq S i j l).symm

/-! ## §3 — the coefficient from the associator alone -/

/-- **The tensorator's coefficient, associator form.**  `Ω(a,b;c)` is the
comparison `ψ_{a,b}|_c` of `DerivedJScalar`'s derivation with the `ev`-factors
divided out; the tensorator's coefficient is the ratio
`Ω(b*,a*;c*)/Ω(a,b;c)`.

Written with `F` and `Finv` only: no `ev`, no `coev`.  (`Finv` carries the
*matrix inverse* of the associator block, which is why no entrywise reciprocal
appears — see `System.lean`'s docstring.) -/
noncomputable def omegaCoeff (S : FusionSystem n k) (a b c : Fin n) : k :=
  if h : 0 < n then
    (S.F a b (S.ring.dual c) ⟨0, h⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
          (S.ring.dual c) ⟨0, h⟩) /
      (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, h⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, h⟩)
  else 0

@[simp] theorem omegaCoeff_def (S : FusionSystem n k) (a b c : Fin n) :
    omegaCoeff S a b c =
      (if h : 0 < n then
        (S.F a b (S.ring.dual c) ⟨0, h⟩ c (S.ring.dual a) *
            S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
              (S.ring.dual c) ⟨0, h⟩) /
          (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, h⟩ (S.ring.dual c) b *
            S.Finv (S.ring.dual a) a b b c ⟨0, h⟩)
      else 0) := rfl

/-- **The duality normalisation cancels.**  The `ev`-side definition
`derivedJGen` of `DerivedJScalar.lean` and the associator-only form `omegaCoeff`
agree: the four `ev`-factors cancel by `ev_dual`.

No cancellation is made without the explicit nonvanishing hypotheses `hD`
(denominator of `ψ_{a,b}|_c`) and `hN` (numerator of `ψ_{b*,a*}|_{c*}`). -/
theorem derivedJGen_eq_omegaCoeff (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n)
    (hD : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0)
    (hN : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
          (S.ring.dual c) ⟨0, hn⟩ ≠ 0) :
    derivedJGen S a b c = omegaCoeff S a b c := by
  have hcs1 : comparisonScalar S a b c =
      S.ev c / (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ * S.ev a * S.ev b) := by
    rw [comparisonScalar_def, dif_pos hn]
  have hcs2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) =
      S.ev (S.ring.dual c) /
        (S.F (S.ring.dual (S.ring.dual a)) (S.ring.dual (S.ring.dual b))
            (S.ring.dual c) ⟨0, hn⟩ (S.ring.dual (S.ring.dual c)) (S.ring.dual a) *
          S.Finv (S.ring.dual (S.ring.dual b)) (S.ring.dual b) (S.ring.dual a)
            (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩ *
          S.ev (S.ring.dual b) * S.ev (S.ring.dual a)) := by
    rw [comparisonScalar_def, dif_pos hn]
  -- rewrite the doubly dual labels back
  simp only [S.ring.dual_involutive] at hcs2
  rw [derivedJGen_def, hcs1, hcs2, omegaCoeff, dif_pos hn]
  have heva : S.ev a ≠ 0 := S.ev_ne_zero a
  have hevb : S.ev b ≠ 0 := S.ev_ne_zero b
  have hevc : S.ev c ≠ 0 := S.ev_ne_zero c
  rw [S.ev_dual b, S.ev_dual a, S.ev_dual c]
  field_simp
  try ring


/-! ## §4 — the index map underlying the tensorator

The source block of `X** ⊗ Y**` and the target block of `(X ⊗ Y)**` are the
same type up to the double-dual relabelling `(p, ν, x, y) ↦ (p**, ν, x, y)`;
`tensorIdxMap` is that map, written with the transport `N p₁ p₂ c = N p₁** p₂** c**`
of §2.  On labels it is `p ↦ p**`, on the multiplicity indices it is the
identity (they live in the *same* blocks `X.blk (p**)` resp. `Y.blk (p**)` of the
target), and on the channel it is the transport. -/

section Tensorator

variable (S : FusionSystem n k)

/-- The tensorator's index map: a source index of `X** ⊗ Y**` at the block `c`
goes to the index of `(X ⊗ Y)**` at the same block with labels `p ↦ p**`. -/
noncomputable def tensorIdxMap (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    (dual S (dual S (tensorObj S X Y))).blk c :=
  ⟨(S.ring.dual (S.ring.dual r.1.1), S.ring.dual (S.ring.dual r.1.2)),
    (N_doubleDual_eq' S r.1.1 r.1.2 c) ▸ r.2.1, r.2.2.1, r.2.2.2⟩

@[simp] theorem tensorIdxMap_fst (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    (tensorIdxMap S X Y c r).1 = (S.ring.dual (S.ring.dual r.1.1),
      S.ring.dual (S.ring.dual r.1.2)) := rfl

@[simp] theorem tensorIdxMap_fst_fst (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    (tensorIdxMap S X Y c r).1.1 = S.ring.dual (S.ring.dual r.1.1) := rfl

@[simp] theorem tensorIdxMap_fst_snd (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    (tensorIdxMap S X Y c r).1.2 = S.ring.dual (S.ring.dual r.1.2) := rfl

/-! ## §5 — the tensorator -/

/-- The scalar the tensorator carries on the source index `r`: the channel of
`(a,b)` in the block `c`, i.e. `derivedJGen S a b c` read at the source labels.
(The labels of a source index are the *doubly dual* ones; on `sim a` they are
`a**`, so the entry theorem below reads `derivedJGen S a b c`.) -/
noncomputable def tensorCoeff (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) : k :=
  derivedJGen S (S.ring.dual (S.ring.dual r.1.1)) (S.ring.dual (S.ring.dual r.1.2)) c

/-- **The tensorator** `μ_{X,Y} : X** ⊗ Y** ⟶ (X ⊗ Y)**` of the reconstruction,
as a block matrix in the channel basis: the entry is `0` off the double-dual
index pattern `tensorIdxMap`, and `derivedJGen` on it.

This is the matrix formula the direction D7 sanctions in the absence of the
`rightAdjointMate` of D5's rigidity: the entry is the system's own
`derivedJGen`, i.e. `F`, `Finv`, `ev`, `coev` and the fusion ring, never the
carried field `S.J`. -/
noncomputable def tensorator (X Y : FusionMat n k) :
    tensorObj S (dual S (dual S X)) (dual S (dual S Y)) ⟶
      dual S (dual S (tensorObj S X Y)) :=
  fun c => Matrix.of fun r q =>
    if q = tensorIdxMap S X Y c r then tensorCoeff S X Y c r else 0

/-- The entry of the tensorator at the matched index pair. -/
theorem tensorator_apply_self (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorator S X Y c r (tensorIdxMap S X Y c r) = tensorCoeff S X Y c r := by
  simp only [tensorator, Matrix.of_apply, if_true]

/-- The tensorator vanishes off the index pattern. -/
theorem tensorator_apply_of_ne (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c)
    (q : (dual S (dual S (tensorObj S X Y))).blk c)
    (h : q ≠ tensorIdxMap S X Y c r) :
    tensorator S X Y c r q = 0 := by
  simp only [tensorator, Matrix.of_apply, if_neg h]

/-! ## §6 — the entry theorem at the `(a,b)`-channel of `sim a ⊗ sim b` -/

/-- The canonical source index of the `(a,b)`-channel: the label `(a**,b**)`,
the channel `ν` (transported along the trivialised labels) and the unique
multiplicity indices of the two simples. -/
noncomputable def simTensSrc (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c)) :
    (tensorObj S (dual S (dual S (sim a))) (dual S (dual S (sim b)))).blk c :=
  ⟨(S.ring.dual (S.ring.dual a), S.ring.dual (S.ring.dual b)),
    (by rw [S.ring.dual_involutive a, S.ring.dual_involutive b] :
      S.ring.N a b c =
        S.ring.N (S.ring.dual (S.ring.dual a)) (S.ring.dual (S.ring.dual b)) c) ▸ ν,
    ⟨0, by simp [S.ring.dual_involutive]⟩,
    ⟨0, by simp [S.ring.dual_involutive]⟩⟩

/-- The canonical target index: the image of `simTensSrc` under the tensorator's
index map — the `(a,b)`-channel of `(sim a ⊗ sim b)**` at the block `c`. -/
noncomputable def simTensTgt (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c)) :
    (dual S (dual S (tensorObj S (sim a) (sim b)))).blk c :=
  tensorIdxMap S (sim a) (sim b) c (simTensSrc S hn a b c ν)

@[simp] theorem simTensTgt_fst (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c)) :
    (simTensTgt S hn a b c ν).1 =
      (S.ring.dual (S.ring.dual (S.ring.dual (S.ring.dual a))),
        S.ring.dual (S.ring.dual (S.ring.dual (S.ring.dual b)))) := by
  unfold simTensTgt tensorIdxMap simTensSrc
  rfl

/-- The coefficient at the canonical simple source, before the label
trivialisation: it is `derivedJGen` at the doubly dual labels. -/
theorem tensorCoeff_simTensSrc (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c)) :
    tensorCoeff S (sim a) (sim b) c (simTensSrc S hn a b c ν) =
      derivedJGen S (S.ring.dual (S.ring.dual (S.ring.dual (S.ring.dual a))))
        (S.ring.dual (S.ring.dual (S.ring.dual (S.ring.dual b)))) c := by
  unfold tensorCoeff simTensSrc
  rfl

/-- **The entry theorem.**  The `(c,c)`-channel entry of the tensorator at the
`(a,b)`-channel of `sim a ⊗ sim b` **is** `derivedJGen S a b c`: the scalar of
`DerivedJScalar.lean` is realised as the matrix entry of the morphism. -/
theorem tensorator_entry_sim (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c)) :
    tensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν) (simTensTgt S hn a b c ν) =
      derivedJGen S a b c := by
  rw [simTensTgt, tensorator_apply_self, tensorCoeff_simTensSrc]
  simp only [S.ring.dual_involutive]

/-- The same entry, in the associator-only form: the tensorator's coefficient is
`Ω(b*,a*;c*)/Ω(a,b;c)` — computed from `F` and `Finv`, with no dependence on the
duality normalisation `ev`/`coev`.  (Explicit nonvanishing hypotheses, as in
`derivedJGen_eq_omegaCoeff`.) -/
theorem tensorator_entry_sim_omega (hn : 0 < n) (a b c : Fin n) (ν : Fin (S.ring.N a b c))
    (hD : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0)
    (hN : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
          (S.ring.dual c) ⟨0, hn⟩ ≠ 0) :
    tensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν) (simTensTgt S hn a b c ν) =
      omegaCoeff S a b c := by
  rw [tensorator_entry_sim, derivedJGen_eq_omegaCoeff S hn a b c hD hN]

/-- **The entry theorem in general form**: on *any* objects `X`, `Y`, the
tensorator's entry at a matched index pair `(r, tensorIdxMap r)` whose target
labels are `(a,b)` and whose block is `c` is `derivedJGen S a b c` — the channel
scalar depends only on the channel, not on the multiplicity indices. -/
theorem tensorator_apply_labels (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c)
    (a b : Fin n)
    (h1 : (tensorIdxMap S X Y c r).1.1 = a) (h2 : (tensorIdxMap S X Y c r).1.2 = b) :
    tensorator S X Y c r (tensorIdxMap S X Y c r) = derivedJGen S a b c := by
  have hcoeff : tensorCoeff S X Y c r =
      derivedJGen S (tensorIdxMap S X Y c r).1.1 (tensorIdxMap S X Y c r).1.2 c := by
    unfold tensorCoeff tensorIdxMap
    rfl
  rw [tensorator_apply_self, hcoeff, h1, h2]

/-! ## §6a — the simple blocks are subsingletons

`N ≤ 1` (`FusionSystem.mult_free`) makes every block of a tensor of simples a
subsingleton — in particular the blocks of the tensorator's source `X** ⊗ Y**`
and target `(X ⊗ Y)**` at simples.  This is what upgrades the entry theorem from
"the entry at the canonical index" to "the whole component is the scalar
matrix": a component with at most one entry is determined by that entry.
(Useful outside this file: any computation at simples needs it.) -/

/-- The `c`-block of `sim a ⊗ sim b` is a subsingleton. -/
theorem simTensorBlock_subsingleton (a b c : Fin n) :
    Subsingleton ((tensorObj S (sim a) (sim b)).blk c) := by
  have hcard : Fintype.card ((tensorObj S (sim a) (sim b)).blk c) ≤ 1 := by
    rw [(tensorObj S (sim a) (sim b)).card_blk c, tensorObj_sim_m S a b c]
    exact S.mult_free a b c
  exact ⟨Fintype.card_le_one_iff.mp hcard⟩

/-- The `c`-block of `sim a** ⊗ sim b**` is a subsingleton. -/
theorem simDualTensorBlock_subsingleton (a b c : Fin n) :
    Subsingleton ((tensorObj S (dual S (dual S (sim a)))
      (dual S (dual S (sim b)))).blk c) := by
  rw [dual_dual S (sim a), dual_dual S (sim b)]
  exact simTensorBlock_subsingleton S a b c

/-- The `c`-block of `(sim a ⊗ sim b)**` is a subsingleton. -/
theorem simTensorDualBlock_subsingleton (a b c : Fin n) :
    Subsingleton ((dual S (dual S (tensorObj S (sim a) (sim b)))).blk c) := by
  rw [dual_dual S (tensorObj S (sim a) (sim b))]
  exact simTensorBlock_subsingleton S a b c

/-! ## §6b — the pointed gauge matrix

On a pointed datum (`WP2.Pointed`: `a ⊗ b` is a single simple) the derived twist
is `κ_a κ_b / κ_c` (`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed`), so the
tensorator's channel entries are the **δ(κ) gauge matrix**: this is the
morphism-level form of the round-2 scalar theorem, and it is the "stretch" item
of direction D7. -/

/-- **The pointed tensorator entry**: `κ_a κ_b / κ_c`. -/
theorem tensorator_entry_sim_pointed (hn : 0 < n) (hP : WP2.Pointed S) (a b c : Fin n)
    (hN : 0 < S.ring.N a b c) (ν : Fin (S.ring.N a b c)) :
    tensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν) (simTensTgt S hn a b c ν) =
      S.kappa a * S.kappa b / S.kappa c := by
  rw [tensorator_entry_sim, derivedJGen_eq_delta_kappa_of_pointed S hn hP hN]

/-- **The strengthened entry theorem**: at simples the tensorator's *whole*
component is the scalar matrix `derivedJGen S a b c` — the blocks are
subsingletons (`§6a`), so the entry is independent of the index pair.  This is
the form in which the channel basis is used: `(c,c)`-entry at the `(a,b)`-channel
= `derivedJGen S a b c`, for every representative of the channel. -/
theorem tensorator_apply_sim (hn : 0 < n) (a b c : Fin n) (hN : 0 < S.ring.N a b c)
    (r : (tensorObj S (dual S (dual S (sim a))) (dual S (dual S (sim b)))).blk c)
    (q : (dual S (dual S (tensorObj S (sim a) (sim b)))).blk c) :
    tensorator S (sim a) (sim b) c r q = derivedJGen S a b c := by
  haveI := simDualTensorBlock_subsingleton S a b c
  haveI := simTensorDualBlock_subsingleton S a b c
  have hr : r = simTensSrc S hn a b c ⟨0, hN⟩ := Subsingleton.elim _ _
  have hq : q = simTensTgt S hn a b c ⟨0, hN⟩ := Subsingleton.elim _ _
  rw [hr, hq, tensorator_entry_sim]

/-! ## §6c — invertibility on the channels

With `N ≤ 1` and a present channel the simple blocks have **exactly one** element,
so the tensorator's component at the `(a,b)`-channel is a `1 × 1` matrix with
entry `derivedJGen S a b c`.  It is therefore invertible exactly when that scalar
is nonzero, with inverse component the scalar `derivedJGen S a b c`⁻¹.  This is the
channel-level form of "`(−)**` is a monoidal equivalence": the twist is what
makes the comparison invertible, and it is invertible wherever the datum is
honest. -/

/-- The target block `(sim a ⊗ sim b)**` at a present channel has exactly one element. -/
theorem card_simTensorDualBlock (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    Fintype.card ((dual S (dual S (tensorObj S (sim a) (sim b)))).blk c) = 1 := by
  have hm : (dual S (dual S (tensorObj S (sim a) (sim b)))).m c = S.ring.N a b c := by
    rw [dual_m, dual_m, tensorObj_sim_m, S.ring.dual_involutive]
  have hle : Fintype.card ((dual S (dual S (tensorObj S (sim a) (sim b)))).blk c) ≤ 1 := by
    rw [(dual S (dual S (tensorObj S (sim a) (sim b)))).card_blk c, hm]
    exact S.mult_free a b c
  have hpos : 0 < Fintype.card ((dual S (dual S (tensorObj S (sim a) (sim b)))).blk c) := by
    rw [(dual S (dual S (tensorObj S (sim a) (sim b)))).card_blk c, hm]
    exact hN
  omega

/-- The source block `sim a** ⊗ sim b**` at a present channel has exactly one element. -/
theorem card_simDualTensorBlock (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    Fintype.card ((tensorObj S (dual S (dual S (sim a)))
      (dual S (dual S (sim b)))).blk c) = 1 := by
  have h1 : dual S (dual S (sim a)) = sim a := dual_dual S (sim a)
  have h2 : dual S (dual S (sim b)) = sim b := dual_dual S (sim b)
  rw [h1, h2]
  have hm : (tensorObj S (sim a) (sim b)).m c = S.ring.N a b c := tensorObj_sim_m S a b c
  have hle : Fintype.card ((tensorObj S (sim a) (sim b)).blk c) ≤ 1 := by
    rw [(tensorObj S (sim a) (sim b)).card_blk c, hm]
    exact S.mult_free a b c
  have hpos : 0 < Fintype.card ((tensorObj S (sim a) (sim b)).blk c) := by
    rw [(tensorObj S (sim a) (sim b)).card_blk c, hm]
    exact hN
  omega

/-- The candidate inverse component of the tensorator at the `(a,b)`-channel: the
scalar matrix `derivedJGen S a b c`⁻¹. -/
noncomputable def tensoratorInvBlock (a b c : Fin n) :
    Matrix ((dual S (dual S (tensorObj S (sim a) (sim b)))).blk c)
      ((tensorObj S (dual S (dual S (sim a))) (dual S (dual S (sim b)))).blk c) k :=
  Matrix.of fun _ _ => (derivedJGen S a b c)⁻¹

/-- **The tensorator is invertible on a channel with nonzero twist** (`⟶` side). -/
theorem tensorator_mul_invBlock (hn : 0 < n) (a b c : Fin n) (hN : 0 < S.ring.N a b c)
    (hJ : derivedJGen S a b c ≠ 0) :
    tensorator S (sim a) (sim b) c * tensoratorInvBlock S a b c = 1 := by
  haveI := simTensorDualBlock_subsingleton S a b c
  haveI := simDualTensorBlock_subsingleton S a b c
  ext r r'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ m, tensorator S (sim a) (sim b) c r m *
      tensoratorInvBlock S a b c m r' = 1 := by
    intro m
    rw [tensorator_apply_sim S hn a b c hN r m]
    simp only [tensoratorInvBlock, Matrix.of_apply]
    exact mul_inv_cancel₀ hJ
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_const, Finset.card_univ,
    card_simTensorDualBlock S a b c hN, one_smul]
  exact (if_pos (Subsingleton.elim r r')).symm

/-- **The tensorator is invertible on a channel with nonzero twist** (`⟵` side). -/
theorem invBlock_mul_tensorator (hn : 0 < n) (a b c : Fin n) (hN : 0 < S.ring.N a b c)
    (hJ : derivedJGen S a b c ≠ 0) :
    tensoratorInvBlock S a b c * tensorator S (sim a) (sim b) c = 1 := by
  haveI := simTensorDualBlock_subsingleton S a b c
  haveI := simDualTensorBlock_subsingleton S a b c
  ext r r'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ m, tensoratorInvBlock S a b c r m *
      tensorator S (sim a) (sim b) c m r' = 1 := by
    intro m
    rw [tensorator_apply_sim S hn a b c hN m r']
    simp only [tensoratorInvBlock, Matrix.of_apply]
    exact inv_mul_cancel₀ hJ
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_const, Finset.card_univ,
    card_simDualTensorBlock S a b c hN, one_smul]
  exact (if_pos (Subsingleton.elim r r')).symm

/-! ## §7 — the tensorator is the naive identification twisted by the channels

The morhism `X** ⊗ Y** ⟶ (X ⊗ Y)**` is *not* the identification induced by
`dual_dual` (which has coefficient `1` on every channel): it is that
identification followed by the diagonal channel twist whose scalar is
`derivedJGen`.  This is what "`J` is the monoidal structure of `(−)**`" means
in the model, and it is why the tensorator cannot be replaced by `eqToHom`. -/

/-- The naive double-dual identification `X** ⊗ Y** ⟶ (X ⊗ Y)**`: the index
pattern with coefficient `1` (the morphism that the object equality `dual_dual`
induces; it is not monoidal). -/
noncomputable def naiveTensorator (X Y : FusionMat n k) :
    tensorObj S (dual S (dual S X)) (dual S (dual S Y)) ⟶
      dual S (dual S (tensorObj S X Y)) :=
  fun c => Matrix.of fun r q => if q = tensorIdxMap S X Y c r then 1 else 0

/-- The channel twist: the diagonal endomorphism of `(X ⊗ Y)**` whose scalar on
a channel `(a,b;c)` is `derivedJGen S a b c`. -/
noncomputable def channelTwist (X Y : FusionMat n k) :
    dual S (dual S (tensorObj S X Y)) ⟶ dual S (dual S (tensorObj S X Y)) :=
  fun c => Matrix.diagonal fun q => derivedJGen S q.1.1 q.1.2 c

/-- **The channel twist of a pointed datum is the δ(κ) gauge matrix**: its diagonal
entry on a supported channel `(a,b;c)` is `κ_a κ_b / κ_c`. -/
theorem channelTwist_diagonal_pointed (hP : WP2.Pointed S) (X Y : FusionMat n k) (c : Fin n)
    (q : (dual S (dual S (tensorObj S X Y))).blk c) (hN : 0 < S.ring.N q.1.1 q.1.2 c) :
    channelTwist S X Y c q q = S.kappa q.1.1 * S.kappa q.1.2 / S.kappa c := by
  have hn : 0 < n := by have := q.1.1.isLt; omega
  have hdiag : channelTwist S X Y c q q = derivedJGen S q.1.1 q.1.2 c := by
    simp only [channelTwist, Matrix.diagonal_apply, if_true]
  rw [hdiag]
  exact derivedJGen_eq_delta_kappa_of_pointed S hn hP hN

/-- **The factorisation**: `tensorator = naiveTensorator ≫ channelTwist`. -/
theorem tensorator_eq_naive_comp_channelTwist (X Y : FusionMat n k) :
    tensorator S X Y = naiveTensorator S X Y ≫ channelTwist S X Y := by
  funext c
  ext r q
  show (if q = tensorIdxMap S X Y c r then tensorCoeff S X Y c r else 0) =
    ∑ m, (if m = tensorIdxMap S X Y c r then (1 : k) else 0) *
      (if m = q then derivedJGen S m.1.1 m.1.2 c else 0)
  rw [Finset.sum_eq_single (tensorIdxMap S X Y c r)]
  · have hcoeff : tensorCoeff S X Y c r =
        derivedJGen S (tensorIdxMap S X Y c r).1.1 (tensorIdxMap S X Y c r).1.2 c := by
      unfold tensorCoeff tensorIdxMap
      rfl
    rw [if_pos rfl, one_mul, hcoeff]
    by_cases hq : q = tensorIdxMap S X Y c r
    · rw [if_pos hq, if_pos hq.symm]
    · rw [if_neg hq, if_neg (Ne.symm hq)]
  · intro m _ hm
    rw [if_neg hm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The double dual is not strictly monoidal when the derived twist is
non-trivial**: if some channel has `derivedJGen ≠ 1`, the tensorator differs from
the naive identification.  (No datum is needed: this is the exact obstruction,
and `DerivedJLaws`/`DerivedJPointed` supply channels where it fires.) -/
theorem tensorator_ne_naive_of_coeff_ne_one (hn : 0 < n) (a b c : Fin n)
    (ν : Fin (S.ring.N a b c)) (h : derivedJGen S a b c ≠ 1) :
    tensorator S (sim a) (sim b) ≠ naiveTensorator S (sim a) (sim b) := by
  intro heq
  have h1 : tensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν)
      (simTensTgt S hn a b c ν) = derivedJGen S a b c := tensorator_entry_sim S hn a b c ν
  have h2 : naiveTensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν)
      (simTensTgt S hn a b c ν) = 1 := by
    unfold naiveTensorator simTensTgt
    simp only [Matrix.of_apply, if_true]
  rw [heq, h2] at h1
  exact h h1.symm

/-! ## §8 — unitality of the tensorator's entries, from `DerivedJLaws`

The tensorator's entry on a unit channel is `1`: the scalar `derivedJGen` is
normalised at the unit and at the duality channel
(`derivedJGen_unit_left`, `derivedJGen_unit_right`, `derivedJGen_dual` in
`DerivedJLaws`).  Hence the tensorator is unital on channels, as a monoidal
structure on `(−)**` must be. -/

theorem tensorator_entry_sim_unit_left (hn : 0 < n) (b : Fin n)
    (ν : Fin (S.ring.N ⟨0, hn⟩ b b)) :
    tensorator S (sim ⟨0, hn⟩) (sim b) b (simTensSrc S hn ⟨0, hn⟩ b b ν)
      (simTensTgt S hn ⟨0, hn⟩ b b ν) = 1 := by
  rw [tensorator_entry_sim, derivedJGen_unit_left]

theorem tensorator_entry_sim_unit_right (hn : 0 < n) (a : Fin n)
    (ν : Fin (S.ring.N a ⟨0, hn⟩ a)) :
    tensorator S (sim a) (sim ⟨0, hn⟩) a (simTensSrc S hn a ⟨0, hn⟩ a ν)
      (simTensTgt S hn a ⟨0, hn⟩ a ν) = 1 := by
  rw [tensorator_entry_sim, derivedJGen_unit_right]

theorem tensorator_entry_sim_dual (hn : 0 < n) (i : Fin n)
    (ν : Fin (S.ring.N i (S.ring.dual i) ⟨0, hn⟩)) :
    tensorator S (sim i) (sim (S.ring.dual i)) ⟨0, hn⟩
      (simTensSrc S hn i (S.ring.dual i) ⟨0, hn⟩ ν)
      (simTensTgt S hn i (S.ring.dual i) ⟨0, hn⟩ ν) = 1 := by
  rw [tensorator_entry_sim, derivedJGen_dual]

/-! ## §9 — gauge invariance of the tensorator

The vertex gauge `ev ↦ ev/λ`, `coev ↦ λ·coev` (`Gauge.lean`) leaves `F`, `Finv`
and the fusion ring untouched, so it leaves the *index pattern* of the tensorator
untouched, and `derivedJGen` is gauge-invariant.  Hence the tensorator is a
morphism of the reconstruction and not an artefact of the duality
normalisation. -/

theorem tensorCoeff_gauge (X Y : FusionMat n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorCoeff (gauge S lam hlam) X Y c r = tensorCoeff S X Y c r := by
  unfold tensorCoeff
  exact derivedJGen_gauge S lam hlam (S.ring.dual (S.ring.dual r.1.1))
    (S.ring.dual (S.ring.dual r.1.2)) c

theorem tensorIdxMap_gauge (X Y : FusionMat n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorIdxMap (gauge S lam hlam) X Y c r = tensorIdxMap S X Y c r := rfl

/-- **The tensorator's entries are invariant under the vertex gauge**: the gauge
moves `ev`/`coev` but not the associator, so it moves neither the tensorator's
index pattern (`tensorIdxMap_gauge`) nor its coefficient (`tensorCoeff_gauge`).

Stated on the `(a,b)`-channel of `sim a ⊗ sim b`, where the two data have the
same simple objects: the two entries coincide. -/
theorem tensorator_entry_sim_gauge (hn : 0 < n) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin n)
    (ν : Fin (S.ring.N a b c)) :
    tensorator (gauge S lam hlam) (sim a) (sim b) c
        (simTensSrc (gauge S lam hlam) hn a b c ν)
        (simTensTgt (gauge S lam hlam) hn a b c ν) =
      tensorator S (sim a) (sim b) c (simTensSrc S hn a b c ν)
        (simTensTgt S hn a b c ν) := by
  rw [tensorator_entry_sim (gauge S lam hlam) hn a b c ν,
    tensorator_entry_sim S hn a b c ν, derivedJGen_gauge]

end Tensorator

end FusionMat

end FusionCategory

namespace FusionCategory

/-! ## §10 — a concrete datum: the honest `(Z/2)²` twist is not `1`

`Z2SqH.system` (`Examples/Z2SqHonest.lean`, `ω = (-1)^{a₁b₂c₁}`) has
`κ = (1,1,1,-1)`, so on the channel `1 ⊗ 2 ∋ 3` the derived twist is `-1`.  By
`tensorator_ne_naive_of_coeff_ne_one` the tensorator of `(−)**` therefore
**differs from the object-level identification `dual_dual`** on this datum: the
double-dual functor is not strictly monoidal, and the correction is exactly the
derived twist.  (Kernel-checked counterpart of the `docs/*.py` twist batteries;
the number is the one `DerivedJScalar`'s docstring quotes.) -/

namespace Z2SqH

/-- The honest `(Z/2)²` datum is pointed: every `a ⊗ b` has the unique channel
`gadd a b`. -/
theorem pointed : WP2.Pointed system := by
  intro a b
  refine ⟨gadd a b, ?_, ?_⟩
  · show 0 < N a b (gadd a b)
    exact N_pos_iff.mpr rfl
  · intro c hc
    show c = gadd a b
    exact N_pos_iff.mp hc

end Z2SqH

namespace FusionMat

/-- On the honest `(Z/2)²` datum the derived twist on the channel `1 ⊗ 2 ∋ 3` is
`κ 1 * κ 2 / κ 3 = 1 * 1 / (-1) = -1`. -/
theorem derivedJGen_Z2SqH_one_two_three : derivedJGen Z2SqH.system 1 2 3 = -1 := by
  have hN : 0 < Z2SqH.system.ring.N 1 2 3 := by
    show 0 < Z2SqH.N 1 2 3
    rw [Z2SqH.N_pos_iff]
    decide
  rw [derivedJGen_eq_delta_kappa_of_pointed Z2SqH.system (by norm_num) Z2SqH.pointed hN,
    Z2SqH.kappa_one, Z2SqH.kappa_two, Z2SqH.kappa_three]
  norm_num

/-- **The double dual is not strictly monoidal on the honest `(Z/2)²` datum**: the
tensorator on `sim 1 ⊗ sim 2` differs from the naive `dual_dual` identification,
because the channel `1 ⊗ 2 ∋ 3` carries the twist `-1 ≠ 1`. -/
theorem tensorator_ne_naive_Z2SqH :
    tensorator Z2SqH.system (sim 1) (sim 2) ≠ naiveTensorator Z2SqH.system (sim 1) (sim 2) := by
  have hN : 0 < Z2SqH.system.ring.N 1 2 3 := by
    show 0 < Z2SqH.N 1 2 3
    rw [Z2SqH.N_pos_iff]
    decide
  refine tensorator_ne_naive_of_coeff_ne_one Z2SqH.system (by norm_num) 1 2 3 ⟨0, hN⟩ ?_
  rw [derivedJGen_Z2SqH_one_two_three]
  norm_num

/-- The entry statement on the same datum: the tensorator's entry on the channel
`1 ⊗ 2 ∋ 3` is `-1`, while the naive identification's entry there is `1`. -/
theorem tensorator_entry_Z2SqH (ν : Fin (Z2SqH.system.ring.N 1 2 3)) :
    tensorator Z2SqH.system (sim 1) (sim 2) 3
        (simTensSrc Z2SqH.system (by norm_num) 1 2 3 ν)
        (simTensTgt Z2SqH.system (by norm_num) 1 2 3 ν) = -1 := by
  rw [tensorator_entry_sim, derivedJGen_Z2SqH_one_two_three]

end FusionMat

end FusionCategory



/-! ## Axiom audit -/

open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualObj
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualObj_eq
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualMap
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualMap_id
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualMap_comp
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualFunctor
open FusionCategory in
#print axioms FusionCategory.FusionMat.N_doubleDual_eq
open FusionCategory in
#print axioms FusionCategory.FusionMat.omegaCoeff
open FusionCategory in
#print axioms FusionCategory.FusionMat.derivedJGen_eq_omegaCoeff
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorIdxMap
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorCoeff
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_apply_self
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_apply_of_ne
open FusionCategory in
#print axioms FusionCategory.FusionMat.simTensSrc
open FusionCategory in
#print axioms FusionCategory.FusionMat.simTensTgt
open FusionCategory in
#print axioms FusionCategory.FusionMat.simTensTgt_fst
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorCoeff_simTensSrc
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_omega
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_pointed
open FusionCategory in
#print axioms FusionCategory.FusionMat.channelTwist_diagonal_pointed
open FusionCategory in
#print axioms FusionCategory.FusionMat.simTensorBlock_subsingleton
open FusionCategory in
#print axioms FusionCategory.FusionMat.simDualTensorBlock_subsingleton
open FusionCategory in
#print axioms FusionCategory.FusionMat.simTensorDualBlock_subsingleton
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_apply_sim
open FusionCategory in
#print axioms FusionCategory.FusionMat.card_simTensorDualBlock
open FusionCategory in
#print axioms FusionCategory.FusionMat.card_simDualTensorBlock
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensoratorInvBlock
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_mul_invBlock
open FusionCategory in
#print axioms FusionCategory.FusionMat.invBlock_mul_tensorator
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_apply_labels
open FusionCategory in
#print axioms FusionCategory.FusionMat.naiveTensorator
open FusionCategory in
#print axioms FusionCategory.FusionMat.channelTwist
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_eq_naive_comp_channelTwist
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_ne_naive_of_coeff_ne_one
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_unit_left
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_unit_right
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_dual
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorCoeff_gauge
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorIdxMap_gauge

open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_sim_gauge
open FusionCategory in
#print axioms FusionCategory.Z2SqH.pointed
open FusionCategory in
#print axioms FusionCategory.FusionMat.derivedJGen_Z2SqH_one_two_three
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_ne_naive_Z2SqH
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorator_entry_Z2SqH
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualObj_m
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualObj_blk
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualMap_apply
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualFunctor_obj
open FusionCategory in
#print axioms FusionCategory.FusionMat.doubleDualFunctor_obj_eq
open FusionCategory in
#print axioms FusionCategory.FusionMat.N_doubleDual_eq'
open FusionCategory in
#print axioms FusionCategory.FusionMat.omegaCoeff_def
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorIdxMap_fst
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorIdxMap_fst_fst
open FusionCategory in
#print axioms FusionCategory.FusionMat.tensorIdxMap_fst_snd
open FusionCategory in
#print axioms FusionCategory.Z2SqH.pointed
