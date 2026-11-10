/-
# WP3 closure, item 3: the double-dual tensorator is an isomorphism

`DoubleDualTensorator.lean` builds the morphism
`tensorator S X Y : X** ⊗ Y** ⟶ (X ⊗ Y)**` — the block matrix whose entry on the
double-dual index pattern is `derivedJGen` and `0` off it — and proves it is
invertible *on the `(a,b)`-channel of a tensor of two simples* (§6c), where the
blocks are singletons.  This file proves the morphism-level statement: the
tensorator is an isomorphism of the reconstruction for **all** objects `X`, `Y`,
under the single hypothesis that the derived twist does not vanish on supported
channels — which is the honest hypothesis of the whole comparison, and which is
a theorem on pointed data (`DerivedJPointed.derivedJGen_ne_zero_of_pointed`).

What the file adds, in order:

* `finEquivCast`, `ddEquiv`, `fiberEquiv`, `tensorIdxEquiv`: the index map
  `tensorIdxMap` of the tensorator is an **equivalence of block index types**
  (`tensorIdxEquiv_apply`: the equivalence *is* `tensorIdxMap`, on the nose).  The
  double-dual relabelling `p ↦ p**` is an involution of `Fin n × Fin n`
  (`dual_involutive`), the channel coordinate moves by `Fin`-cast along
  `N a b c = N a** b** c**` (`N_doubleDual_eq'`), and the two multiplicity
  coordinates are untouched;
* `tensoratorInv`: the **inverse block matrix** — the transpose of the index
  pattern with reciprocal coefficients;
* `monomial_mul_inv`, `inv_mul_monomial`: the general linear-algebra lemma for a
  monomial matrix with nowhere-zero weights (what makes the block matrix
  invertible without any block having size `1`);
* `tensorator_mul_tensoratorInv`, `tensoratorInv_mul_tensorator`: the two
  composite identities, `tensoratorIso`, `isIso_tensorator`;
* `tensoratorIso_pointed`, `isIso_tensorator_pointed`: the pointed instantiation
  (the hypothesis is discharged, not assumed), and
  `tensoratorInv_entry_sim_pointed`: on pointed data the inverse entry is
  `(κ_a κ_b / κ_c)⁻¹` — the inverse `δ(κ)` gauge matrix, matching the forward
  entry `tensorator_entry_sim_pointed` of `DoubleDualTensorator`; and
  `tensorCoeff_pointed`, `tensorator_apply_pointed`,
  `tensoratorInv_apply_pointed`: the same two entries on *arbitrary* objects
  `X`, `Y` on pointed data — the block matrix *is* the `δ(κ)` gauge matrix;
* `tensoratorInv_entry_sim`, `tensoratorInv_apply_sim`: at simples the inverse is
  the scalar matrix `(derivedJGen S a b c)⁻¹`, hypothesis-free — the inverse
  companion of `tensorator_apply_sim`, and the morphism-level form of
  `tensoratorInvBlock` (§6c of `DoubleDualTensorator`);
* `tensorator_isIso_iff`: **the hypothesis is exact** — the tensorator is
  invertible on every pair of objects if and only if the derived twist does not
  vanish on supported channels.  `TwistNonzero` is therefore not a convenient
  sufficient condition but the exact condition for a double-dual tensorator.

Not claimed: the tensorator's *coherence* (`μ`-associativity and unitality as a
monoidal structure on `(−)**`) — that needs `AssociatorNatural` and the pentagon
shape, as recorded in `DoubleDualTensorator.lean`.  Invertibility, which is what
"`(−)**` is an equivalence rather than a mere endofunctor" needs from the
comparison, is what is proved here.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DoubleDualTensorator
import FusionCategory.DerivedJPointed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §0 — a monomial matrix with nowhere-zero weights is invertible -/

section Monomial

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **A monomial matrix is invertible.**  If every row of a matrix has exactly one
entry `w r`, at the column `e r` of a bijection `e`, and the weights are nonzero,
then the transpose pattern with reciprocal weights is a two-sided inverse. -/
theorem monomial_mul_inv (e : α ≃ β) (w : α → k) (hw : ∀ r, w r ≠ 0) :
    (Matrix.of fun r q => if q = e r then w r else 0) *
      (Matrix.of fun q r => if q = e r then (w r)⁻¹ else 0) = (1 : Matrix α α k) := by
  ext r r'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single (e r)]
  · by_cases hr : r = r'
    · subst hr
      simp [hw r]
    · have hne : e r ≠ e r' := fun h => hr (e.injective h)
      simp [hr, hne]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The other composite** of the monomial matrix and its transpose-with-reciprocals. -/
theorem inv_mul_monomial (e : α ≃ β) (w : α → k) (hw : ∀ r, w r ≠ 0) :
    (Matrix.of fun q r => if q = e r then (w r)⁻¹ else 0) *
      (Matrix.of fun r q => if q = e r then w r else 0) = (1 : Matrix β β k) := by
  ext q q'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm q)]
  · by_cases hq : q' = q
    · subst hq
      simp [hw _, e.apply_symm_apply]
    · have hq' : ¬ q = q' := fun h => hq h.symm
      simp [hq', hq, e.apply_symm_apply]
  · intro b _ hb
    have h : q ≠ e b := by
      intro hc
      exact hb (by rw [hc, e.symm_apply_apply])
    simp [h]
  · intro h; exact absurd (Finset.mem_univ _) h

end Monomial

namespace FusionMat

/-! ## §1 — the index map of the tensorator is a bijection -/

/-- Transport of a `Fin` index along an equality of the numbers, as an equivalence
whose forward map is the transport `▸` itself (so that the composite below is
definitionally the tensorator's own index map). -/
noncomputable def finEquivCast {m : ℕ} (h : n = m) : Fin n ≃ Fin m where
  toFun ν := h ▸ ν
  invFun ν := h.symm ▸ ν
  left_inv ν := by cases h; rfl
  right_inv ν := by cases h; rfl

/-- The double-dual relabelling of a pair of simple labels.  It is an involution
because the fusion ring's `dual` is one. -/
def ddEquiv (S : FusionSystem n k) : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun p := (S.ring.dual (S.ring.dual p.1), S.ring.dual (S.ring.dual p.2))
  invFun p := (S.ring.dual (S.ring.dual p.1), S.ring.dual (S.ring.dual p.2))
  left_inv p := by simp only [S.ring.dual_involutive]
  right_inv p := by simp only [S.ring.dual_involutive]

/-- The fibre relabelling over a label pair: the channel coordinate is cast along
`N a b c = N a** b** c**` (`N_doubleDual_eq'`), the two multiplicity coordinates
are untouched — they live in the *same* blocks of the source and the target. -/
noncomputable def fiberEquiv (S : FusionSystem n k) (X Y : FusionMat n k) (c : Fin n)
    (p : Fin n × Fin n) :
    (Fin (S.ring.N p.1 p.2 c) × X.blk (S.ring.dual (S.ring.dual p.1)) ×
        Y.blk (S.ring.dual (S.ring.dual p.2)))
      ≃ (Fin (S.ring.N (S.ring.dual (S.ring.dual p.1)) (S.ring.dual (S.ring.dual p.2))
            (S.ring.dual (S.ring.dual c))) ×
          X.blk (S.ring.dual (S.ring.dual p.1)) × Y.blk (S.ring.dual (S.ring.dual p.2))) :=
  Equiv.prodCongr (finEquivCast (N_doubleDual_eq' S p.1 p.2 c))
    (Equiv.prodCongr (Equiv.refl _) (Equiv.refl _))

/-- **The index map of the tensorator is a bijection**, in equivalence form: the
source block of `X** ⊗ Y**` at `c` and the target block of `(X ⊗ Y)**` at `c`
differ only by the double-dual relabelling of the simple labels. -/
noncomputable def tensorIdxEquiv (S : FusionSystem n k) (X Y : FusionMat n k) (c : Fin n) :
    (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c ≃
      (dual S (dual S (tensorObj S X Y))).blk c :=
  Equiv.sigmaCongr (ddEquiv S) (fun p => fiberEquiv S X Y c p)

/-- **The equivalence is the tensorator's index map**, definitionally. -/
theorem tensorIdxEquiv_apply (S : FusionSystem n k) (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorIdxEquiv S X Y c r = tensorIdxMap S X Y c r := by
  obtain ⟨⟨a, b⟩, ν, x, y⟩ := r
  rfl

/-! ## §2 — the inverse block matrix -/

/-- **The inverse of the tensorator**, as a block matrix: the transpose of the
double-dual index pattern with reciprocal coefficients.  Every row (of the target)
has exactly one nonzero entry, at the unique source index mapping to it. -/
noncomputable def tensoratorInv (S : FusionSystem n k) (X Y : FusionMat n k) :
    dual S (dual S (tensorObj S X Y)) ⟶
      tensorObj S (dual S (dual S X)) (dual S (dual S Y)) :=
  fun c => Matrix.of fun q r =>
    if q = tensorIdxMap S X Y c r then (tensorCoeff S X Y c r)⁻¹ else 0

/-- The inverse matrix on the index pattern: the reciprocal coefficient. -/
theorem tensoratorInv_apply_self (S : FusionSystem n k) (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensoratorInv S X Y c (tensorIdxMap S X Y c r) r = (tensorCoeff S X Y c r)⁻¹ := by
  simp only [tensoratorInv, Matrix.of_apply, if_true]

/-- The inverse matrix vanishes off the index pattern. -/
theorem tensoratorInv_apply_of_ne (S : FusionSystem n k) (X Y : FusionMat n k) (c : Fin n)
    (q : (dual S (dual S (tensorObj S X Y))).blk c)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c)
    (h : q ≠ tensorIdxMap S X Y c r) :
    tensoratorInv S X Y c q r = 0 := by
  simp only [tensoratorInv, Matrix.of_apply, if_neg h]

/-! ## §3 — the two composite identities -/

/-- The twist is nonzero on every supported channel: the hypothesis of the
morphism-level comparison. -/
def TwistNonzero (S : FusionSystem n k) : Prop :=
  ∀ (a b c : Fin n), 0 < S.ring.N a b c → derivedJGen S a b c ≠ 0

/-- `tensorator ≫ tensoratorInv` is the identity, when the twist does not vanish
on supported channels.  The coefficient at a matched index pair is `derivedJGen`
at the doubly dual labels, whose channel is the same supported channel. -/
theorem tensorator_mul_tensoratorInv (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) :
    tensorator S X Y ≫ tensoratorInv S X Y =
      𝟙 (tensorObj S (dual S (dual S X)) (dual S (dual S Y))) := by
  funext c
  have hw : ∀ r, tensorCoeff S X Y c r ≠ 0 := by
    intro r
    obtain ⟨⟨a, b⟩, ν, x, y⟩ := r
    have hN : 0 < S.ring.N a b c := Nat.zero_lt_of_lt ν.isLt
    exact hJ _ _ _ (by simpa only [S.ring.dual_involutive] using hN)
  show (Matrix.of fun r q =>
      if q = tensorIdxMap S X Y c r then tensorCoeff S X Y c r else 0) *
    (Matrix.of fun q r =>
      if q = tensorIdxMap S X Y c r then (tensorCoeff S X Y c r)⁻¹ else 0) =
    (1 : Matrix ((tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c)
      ((tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) k)
  simp only [← tensorIdxEquiv_apply]
  exact monomial_mul_inv (tensorIdxEquiv S X Y c) (tensorCoeff S X Y c) hw

/-- `tensoratorInv ≫ tensorator` is the identity: this is the composite that needs
*every* target index to have a source preimage, i.e. surjectivity of the index map
— here the inverse index equivalence supplies it. -/
theorem tensoratorInv_mul_tensorator (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) :
    tensoratorInv S X Y ≫ tensorator S X Y =
      𝟙 (dual S (dual S (tensorObj S X Y))) := by
  funext c
  have hw : ∀ r, tensorCoeff S X Y c r ≠ 0 := by
    intro r
    obtain ⟨⟨a, b⟩, ν, x, y⟩ := r
    have hN : 0 < S.ring.N a b c := Nat.zero_lt_of_lt ν.isLt
    exact hJ _ _ _ (by simpa only [S.ring.dual_involutive] using hN)
  show (Matrix.of fun q r =>
      if q = tensorIdxMap S X Y c r then (tensorCoeff S X Y c r)⁻¹ else 0) *
    (Matrix.of fun r q =>
      if q = tensorIdxMap S X Y c r then tensorCoeff S X Y c r else 0) =
    (1 : Matrix ((dual S (dual S (tensorObj S X Y))).blk c)
      ((dual S (dual S (tensorObj S X Y))).blk c) k)
  simp only [← tensorIdxEquiv_apply]
  exact inv_mul_monomial (tensorIdxEquiv S X Y c) (tensorCoeff S X Y c) hw

/-! ## §4 — the tensorator is an isomorphism -/

/-- **The double-dual tensorator as an isomorphism** `X** ⊗ Y** ≅ (X ⊗ Y)**`,
for arbitrary objects `X`, `Y`, whenever the derived twist is nonzero on
supported channels. -/
noncomputable def tensoratorIso (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) :
    tensorObj S (dual S (dual S X)) (dual S (dual S Y)) ≅
      dual S (dual S (tensorObj S X Y)) :=
  Iso.mk (tensorator S X Y) (tensoratorInv S X Y)
    (tensorator_mul_tensoratorInv S hJ X Y) (tensoratorInv_mul_tensorator S hJ X Y)

/-- **The tensorator is invertible** at morphism level. -/
theorem isIso_tensorator (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) : IsIso (tensorator S X Y) :=
  (tensoratorIso S hJ X Y).isIso_hom

/-- The forward arrow of `tensoratorIso` is the tensorator. -/
theorem tensoratorIso_hom (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) :
    (tensoratorIso S hJ X Y).hom = tensorator S X Y := rfl

/-- The inverse arrow of `tensoratorIso` is `tensoratorInv`. -/
theorem tensoratorIso_inv (S : FusionSystem n k) (hJ : TwistNonzero S)
    (X Y : FusionMat n k) :
    (tensoratorIso S hJ X Y).inv = tensoratorInv S X Y := rfl

/-! ## §5 — pointed data: the hypothesis is discharged

On pointed data (`WP2.Pointed`: `a ⊗ b` is a single simple) the derived twist is
`κ_a κ_b / κ_c` and hence nowhere zero on supported channels
(`DerivedJPointed.derivedJGen_ne_zero_of_pointed`), so `twistNonzero_of_pointed`
discharges the hypothesis of §4 on **every** pointed datum.  On the tree that
covers the systems whose pointedness is on record — `pointed_VecZ2`,
`pointed_VecZ2Twisted`, `Z2SqH.pointed` (`DerivedJCoherent`/`DoubleDualTensorator`)
and `Z3Omega.pointed` — and §7 carries the honest `(Z/2)²` instantiation out in
full.  The inverse entry is the reciprocal `δ(κ)` gauge matrix. -/

/-- **Pointed data satisfy the comparison hypothesis.** -/
theorem twistNonzero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) : TwistNonzero S :=
  fun a b c hN => derivedJGen_ne_zero_of_pointed S hn hP hN

/-- **The double-dual tensorator is an isomorphism on pointed data.** -/
noncomputable def tensoratorIso_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) (X Y : FusionMat n k) :
    tensorObj S (dual S (dual S X)) (dual S (dual S Y)) ≅
      dual S (dual S (tensorObj S X Y)) :=
  tensoratorIso S (twistNonzero_of_pointed S hn hP) X Y

/-- **`IsIso` on pointed data**, with the inverse block matrix `tensoratorInv`. -/
theorem isIso_tensorator_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) (X Y : FusionMat n k) : IsIso (tensorator S X Y) :=
  isIso_tensorator S (twistNonzero_of_pointed S hn hP) X Y

/-- **The pointed channel coefficient**: on pointed data the tensorator's
coefficient at *any* source index — any objects `X`, `Y` — is `κ_a κ_b / κ_c` at
the index's own labels.  This is `channelTwist_diagonal_pointed` read on the
source side of the tensorator. -/
theorem tensorCoeff_pointed (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorCoeff S X Y c r = S.kappa r.1.1 * S.kappa r.1.2 / S.kappa c := by
  have hN : 0 < S.ring.N r.1.1 r.1.2 c := Nat.zero_lt_of_lt r.2.1.isLt
  unfold tensorCoeff
  simp only [S.ring.dual_involutive]
  exact derivedJGen_eq_delta_kappa_of_pointed S hn hP hN

/-- **The tensorator's block matrix on pointed data** is the `δ(κ)` gauge matrix:
on every matched index pair, of every objects `X`, `Y`, the entry is
`κ_a κ_b / κ_c`. -/
theorem tensorator_apply_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensorator S X Y c r (tensorIdxMap S X Y c r) =
      S.kappa r.1.1 * S.kappa r.1.2 / S.kappa c := by
  rw [tensorator_apply_self, tensorCoeff_pointed S hn hP]

/-- **The inverse block matrix on pointed data**: the reciprocal `δ(κ)` gauge
matrix, on every matched index pair of every objects `X`, `Y`. -/
theorem tensoratorInv_apply_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) (X Y : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (dual S (dual S X)) (dual S (dual S Y))).blk c) :
    tensoratorInv S X Y c (tensorIdxMap S X Y c r) r =
      (S.kappa r.1.1 * S.kappa r.1.2 / S.kappa c)⁻¹ := by
  rw [tensoratorInv_apply_self, tensorCoeff_pointed S hn hP]

/-- **The inverse restricts to `DerivedJBlockMatrix`'s channel inverse**: on the
`(a,b)`-channel of `sim a ⊗ sim b` the inverse entry is `(derivedJGen S a b c)⁻¹`,
the scalar of `tensoratorInvBlock`/`invBlock_mul_tensorator` (§6c of
`DoubleDualTensorator`), with no hypothesis at all. -/
theorem tensoratorInv_entry_sim (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n)
    (ν : Fin (S.ring.N a b c)) :
    tensoratorInv S (sim a) (sim b) c (simTensTgt S hn a b c ν)
        (simTensSrc S hn a b c ν) = (derivedJGen S a b c)⁻¹ := by
  rw [show simTensTgt S hn a b c ν =
      tensorIdxMap S (sim a) (sim b) c (simTensSrc S hn a b c ν) from rfl,
    tensoratorInv_apply_self, tensorCoeff_simTensSrc]
  simp only [S.ring.dual_involutive]

/-- **The inverse block matrix on pointed data, in channel form**: on the
`(a,b)`-channel of `sim a ⊗ sim b` the inverse entry is `(κ_a κ_b / κ_c)⁻¹`, the
reciprocal of the forward entry `tensorator_entry_sim_pointed`. -/
theorem tensoratorInv_entry_sim_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) (a b c : Fin n) (hN : 0 < S.ring.N a b c)
    (ν : Fin (S.ring.N a b c)) :
    tensoratorInv S (sim a) (sim b) c (simTensTgt S hn a b c ν) (simTensSrc S hn a b c ν) =
      (S.kappa a * S.kappa b / S.kappa c)⁻¹ := by
  rw [show simTensTgt S hn a b c ν =
      tensorIdxMap S (sim a) (sim b) c (simTensSrc S hn a b c ν) from rfl,
    tensoratorInv_apply_self, tensorCoeff_simTensSrc]
  simp only [S.ring.dual_involutive]
  rw [derivedJGen_eq_delta_kappa_of_pointed S hn hP hN]

/-! ## §6 — the channel form at simples, and the exactness of the hypothesis -/

/-- **The inverse at simples is the scalar matrix `(derivedJGen S a b c)⁻¹`** —
hypothesis-free, the inverse companion of `tensorator_apply_sim`. -/
theorem tensoratorInv_apply_sim (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n)
    (hN : 0 < S.ring.N a b c)
    (q : (dual S (dual S (tensorObj S (sim a) (sim b)))).blk c)
    (r : (tensorObj S (dual S (dual S (sim a))) (dual S (dual S (sim b)))).blk c) :
    tensoratorInv S (sim a) (sim b) c q r = (derivedJGen S a b c)⁻¹ := by
  haveI := simDualTensorBlock_subsingleton S a b c
  haveI := simTensorDualBlock_subsingleton S a b c
  rw [Subsingleton.elim q (simTensTgt S hn a b c ⟨0, hN⟩),
    Subsingleton.elim r (simTensSrc S hn a b c ⟨0, hN⟩)]
  exact tensoratorInv_entry_sim S hn a b c ⟨0, hN⟩

/-- **The hypothesis is exact**: the tensorator is invertible on every pair of
objects if and only if the derived twist does not vanish on supported channels.
So `TwistNonzero` is not a convenient sufficient condition — it is *the* condition
under which `(−)**` can be given a tensorator at all.  (`→` is
`isIso_tensorator`; `←` reads the contradiction off the `(a,b)`-channel of
`sim a ⊗ sim b`, where the tensorator is the scalar `derivedJGen S a b c`.) -/
theorem tensorator_isIso_iff (S : FusionSystem n k) :
    TwistNonzero S ↔ ∀ (X Y : FusionMat n k), IsIso (tensorator S X Y) := by
  constructor
  · intro hJ X Y
    exact isIso_tensorator S hJ X Y
  · intro h a b c hN h0
    obtain ⟨g, hg, -⟩ := h (sim a) (sim b)
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have hzero : tensorator S (sim a) (sim b) c = 0 := by
      ext r q
      rw [tensorator_apply_sim S hn a b c hN r q, h0]
      rfl
    have hcomp : tensorator S (sim a) (sim b) c * g c = 1 := congrFun hg c
    rw [hzero, Matrix.zero_mul] at hcomp
    have hr := congrFun (congrFun hcomp (simTensSrc S hn a b c ⟨0, hN⟩))
      (simTensSrc S hn a b c ⟨0, hN⟩)
    simp only [Matrix.one_apply_eq, Matrix.zero_apply] at hr
    exact zero_ne_one hr

end FusionMat

/-! ## §7 — a concrete datum whose twist is not `1`

The honest `(Z/2)²` datum `Z2SqH.system` (`Examples/Z2SqHonest.lean`) is the tree's
first datum on which the tensorator is **not** the naive `dual_dual`
identification: the twist on the channel `1 ⊗ 2 ∋ 3` is `-1`
(`tensorator_ne_naive_Z2SqH`).  It is pointed (`Z2SqH.pointed`), so the
morphism-level comparison still exists — the inverse entry on that channel is
`(-1)⁻¹ = -1`.  This is the concrete content of "the twist is what makes the
comparison invertible". -/

/-- **The double-dual tensorator is an isomorphism on the honest `(Z/2)²`
datum**, for every pair of objects — although it differs from the naive
identification. -/
theorem isIso_tensorator_Z2SqH (X Y : FusionMat 4 ℝ) :
    IsIso (FusionMat.tensorator Z2SqH.system X Y) :=
  FusionMat.isIso_tensorator_pointed Z2SqH.system (by norm_num) Z2SqH.pointed X Y

set_option maxHeartbeats 1000000 in
/-- The inverse entry on the channel `1 ⊗ 2 ∋ 3` of the honest `(Z/2)²` datum is
`-1`: the reciprocal of `tensorator_entry_Z2SqH`. -/
theorem tensoratorInv_entry_Z2SqH
    (hN : 0 < Z2SqH.system.ring.N 1 2 3) (ν : Fin (Z2SqH.system.ring.N 1 2 3)) :
    FusionMat.tensoratorInv Z2SqH.system (sim 1) (sim 2) 3
        (FusionMat.simTensTgt Z2SqH.system (by norm_num) 1 2 3 ν)
        (FusionMat.simTensSrc Z2SqH.system (by norm_num) 1 2 3 ν) = -1 := by
  rw [FusionMat.tensoratorInv_entry_sim Z2SqH.system (by norm_num) 1 2 3 ν,
    FusionMat.derivedJGen_Z2SqH_one_two_three]
  norm_num

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.monomial_mul_inv
#print axioms FusionCategory.inv_mul_monomial
#print axioms FusionCategory.FusionMat.tensorIdxEquiv_apply
#print axioms FusionCategory.FusionMat.tensoratorInv
#print axioms FusionCategory.FusionMat.tensorator_mul_tensoratorInv
#print axioms FusionCategory.FusionMat.tensoratorInv_mul_tensorator
#print axioms FusionCategory.FusionMat.tensoratorIso
#print axioms FusionCategory.FusionMat.isIso_tensorator
#print axioms FusionCategory.FusionMat.twistNonzero_of_pointed
#print axioms FusionCategory.FusionMat.tensoratorIso_pointed
#print axioms FusionCategory.FusionMat.isIso_tensorator_pointed
#print axioms FusionCategory.FusionMat.tensorCoeff_pointed
#print axioms FusionCategory.FusionMat.tensorator_apply_pointed
#print axioms FusionCategory.FusionMat.tensoratorInv_apply_pointed
#print axioms FusionCategory.FusionMat.tensoratorInv_entry_sim
#print axioms FusionCategory.FusionMat.tensoratorInv_entry_sim_pointed
#print axioms FusionCategory.FusionMat.tensoratorInv_apply_sim
#print axioms FusionCategory.FusionMat.tensorator_isIso_iff
#print axioms FusionCategory.FusionMat.tensoratorIso_hom
#print axioms FusionCategory.FusionMat.tensoratorIso_inv
#print axioms FusionCategory.isIso_tensorator_Z2SqH
#print axioms FusionCategory.tensoratorInv_entry_Z2SqH
