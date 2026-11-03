/-
WP2 round 2, member m7, direction D7 (Task 2.2, the trace correspondence).

# The categorical trace on the canonical block scaffold

`Statements2.lean` freezes Task 2.2 as four `Prop`s about a *parameter*
`trSimple : ∀ {n}, FusionSystem n k → Fin n → k → k`: `TraceOfScalar`,
`TraceOfPivotalComponent`, `TraceProduct_eq_kappa`, `TraceGlobalDim_eq_pseudoUnitary`.
This file defines that parameter for the reconstruction — not by the formula it
must satisfy, but as the composite of the frozen definition site `WP2.trDual`,

  `Tr(f) = η_X ≫ (f ▷ X*) ≫ ε_{X*} : 1 ⟶ 1`,

at the simple `X_i`, with `η = coevSim` and `ε = evSim` the label data
`S.coev i` / `S.ev i*` on the unit channel, with the whiskering `▷` the landed
`tensorHom` of `ReconTensor.lean`, and with the resulting endomorphism of the
unit read as a scalar through the block identification
`End (sim 0) ≃+* k` (`endSimEquiv` below) — i.e. exactly
`WP2.trDualScalar (IsFusionCategory.endUnit …)`.

The content is the *collapse*: at a simple, the `0`-block of `X_i ⊗ X_{i*}` is
`1 × 1` (`FusionRing.dual_coeff` plus multiplicity-freeness), the middle leg is
the scalar `a` times the identity, and no associator is traversed, so no
`F`-entry enters and `Tr(a · id_{X_i}) = a · coev_i · ev_{i*}`, which is the
frozen `TraceOfScalar`.  The other three frozen `Prop`s follow from the landed
glue of `Statements2` §5, and the two `dim` readings (`dim P i`, `dimENO P i`)
are the same functional at `a = p_i`.

Axiom budget `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `axiom`,
no `native_decide`; nothing is identified with `S.J`.
-/
import FusionCategory.ReconTensorApply
import FusionCategory.ReconUnit
import FusionCategory.Statements2
import FusionCategory.Triangle
import FusionCategory.PseudoUnitary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false

universe u v

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §0 — a matrix lemma for the block calculus -/

section BlockDiagSmul

variable {L : Type} {ι κ : L → Type}
variable [Fintype L] [DecidableEq L]
variable [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
variable [∀ l, DecidableEq (ι l)] [∀ l, DecidableEq (κ l)]

/-- The entries of a scalar multiple of the identity matrix. -/
theorem smul_one_apply {ι : Type} [DecidableEq ι] (a : k) (x y : ι) :
    (a • (1 : Matrix ι ι k)) x y = if x = y then a else 0 := by
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : x = y
  · simp [h]
  · simp [h]

end BlockDiagSmul

/-! ## §1 — the label-level tensor is `k`-linear in each factor -/

section TensorHomSmul

variable (S : FusionSystem n k)

/-- The tensor of morphisms is `k`-linear in the first factor, entrywise — the
design note's entrywise formula (`tensorHom_apply`) together with the identity
`(a · f) x x' = a · f x x'`. -/
theorem tensorHom_smul_left_apply {X X' Y Y' : FusionMat n k} (a : k) (f : X ⟶ X')
    (g : Y ⟶ Y') (c : Fin n) (r : (tensorObj S X Y).blk c)
    (s : (tensorObj S X' Y').blk c) :
    tensorHom S (a • f) g c r s = a * tensorHom S f g c r s := by
  obtain ⟨p, ν, x, y⟩ := r
  obtain ⟨q, ν', x', y'⟩ := s
  by_cases hpq : p = q
  · subst hpq
    have hfa : (a • f) p.1 x x' = a * f p.1 x x' := by
      rw [show (a • f) p.1 = a • f p.1 from rfl, Matrix.smul_apply, smul_eq_mul]
    rw [tensorHom_apply, tensorHom_apply, hfa]
    ring
  · rw [tensorHom_apply_ne S (a • f) g c hpq, tensorHom_apply_ne S f g c hpq, mul_zero]

end TensorHomSmul

/-! ## §2 — the trace morphism at a simple -/

section TraceDefs

variable (S : FusionSystem n k)

/-- The scalar endomorphism `a · id_{X_i}`: the endomorphism of the simple whose
block entry is the scalar `a` (the parameter of the frozen `trSimple S i a`). -/
def scalarEndo (a : k) (i : Fin n) : sim (k := k) i ⟶ sim (k := k) i :=
  a • 𝟙 (sim (k := k) i)

/-- The `(i,i)`-block of the scalar endomorphism is the constant `a`. -/
theorem scalarEndo_apply (a : k) (i : Fin n) (x y : (sim (k := k) i).blk i) :
    scalarEndo a i i x y = a := by
  have hxy : x = y := by
    apply Fin.ext
    have hx : x.val < 1 := by simpa [sim] using x.isLt
    have hy : y.val < 1 := by simpa [sim] using y.isLt
    omega
  show (a • (1 : Matrix ((sim (k := k) i).blk i) ((sim (k := k) i).blk i) k)) x y = a
  rw [Matrix.smul_apply, Matrix.one_apply, hxy, smul_eq_mul]
  simp

/-- **Coevaluation at a simple**: on the unit channel of `X_i ⊗ X_{i*}` the
scalar `S.coev i`, zero elsewhere (where the target block is empty anyway). -/
def coevSim (hn : 0 < n) (i : Fin n) :
    sim (k := k) ⟨0, hn⟩ ⟶ tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i)) :=
  fun c => Matrix.of (fun _ _ => if c = ⟨0, hn⟩ then S.coev i else 0)

/-- **Evaluation at the dual label** `ε_{X_{i*}}`, on the skeleton's object
`X_i ⊗ X_{i*}` (the double dual is the identity on objects, so `X_{i**} ⊗ X_{i*}`
*is* `X_i ⊗ X_{i*}`), with the scalar `S.ev i*` on the unit channel. -/
def evSim (hn : 0 < n) (i : Fin n) :
    tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i)) ⟶ sim (k := k) ⟨0, hn⟩ :=
  fun c => Matrix.of (fun _ _ => if c = ⟨0, hn⟩ then S.ev (S.ring.dual i) else 0)

/-- **The trace morphism** `Tr(f) = η_{X_i} ≫ (f ▷ X_{i*}) ≫ ε_{X_{i*}} : 1 ⟶ 1`
of `WP2.trDual`, in the reconstruction, for `f = a · id_{X_i}`: the whiskering
`▷` is the landed `tensorHom`. -/
def traceMor (hn : 0 < n) (i : Fin n) (a : k) :
    sim (k := k) ⟨0, hn⟩ ⟶ sim (k := k) ⟨0, hn⟩ :=
  coevSim S hn i ≫ tensorHom S (scalarEndo (k := k) a i) (𝟙 (sim (k := k) (S.ring.dual i))) ≫
    evSim S hn i

/-- The canonical point of the unit object's block (which is `1 × 1`). -/
def unitPt (hn : 0 < n) : (sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩ := ⟨0, by simp⟩

/-- The trace of the scalar `a` at the simple `X_i`, as a scalar: the `(0,0)`
entry of the trace morphism, i.e. `WP2.trDualScalar` read through
`End (sim 0) ≃+* k` (`endSimEquiv`). -/
noncomputable def traceScalar (hn : 0 < n) (i : Fin n) (a : k) : k :=
  (traceMor S hn i a ⟨0, hn⟩) (unitPt (k := k) hn) (unitPt (k := k) hn)

end TraceDefs

/-! ## §3 — the collapse: the unit block of `X_i ⊗ X_{i*}` is `1 × 1` -/

section Main

variable (S : FusionSystem n k)

/-- The unit block of the pair object `X_i ⊗ X_{i*}` carries a single index
(`FusionRing.dual_coeff` plus multiplicity-freeness). -/
theorem pairUnitBlock_card (hn : 0 < n) (i : Fin n) :
    Fintype.card ((tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk
      ⟨0, hn⟩) = 1 := by
  rw [(tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).card_blk,
    tensorObj_sim_m, S.ring.dual_coeff hn i (S.ring.dual i)]
  simp

/-- The coevaluation block at the unit channel is the constant `S.coev i`. -/
theorem coevSim_block (hn : 0 < n) (i : Fin n) :
    coevSim S hn i ⟨0, hn⟩
      = Matrix.of (fun (_ : (sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩)
          (_ : (tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk
            ⟨0, hn⟩) => S.coev i) := by
  funext x y
  simp [coevSim]

/-- The evaluation block at the unit channel is the constant `S.ev i*`. -/
theorem evSim_block (hn : 0 < n) (i : Fin n) :
    evSim S hn i ⟨0, hn⟩
      = Matrix.of (fun (_ : (tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk
            ⟨0, hn⟩)
          (_ : (sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩) => S.ev (S.ring.dual i)) := by
  funext x y
  simp [evSim]

/-- The middle leg of the trace, on the unit channel: the scalar matrix `a`. -/
theorem traceMorBlock_apply (hn : 0 < n) (i : Fin n) (a : k)
    (r s : (tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk ⟨0, hn⟩) :
    tensorHom S (scalarEndo (k := k) a i) (𝟙 (sim (k := k) (S.ring.dual i))) ⟨0, hn⟩ r s
      = a * (if r = s then 1 else 0) := by
  show tensorHom S (a • 𝟙 (sim (k := k) i)) (𝟙 (sim (k := k) (S.ring.dual i))) ⟨0, hn⟩
    r s = a * (if r = s then 1 else 0)
  rw [tensorHom_smul_left_apply]
  rw [tensorHom_id]
  show a * (1 : Matrix ((tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk
      ⟨0, hn⟩) ((tensorObj S (sim (k := k) i)
        (sim (k := k) (S.ring.dual i))).blk ⟨0, hn⟩) k) r s
    = a * (if r = s then 1 else 0)
  rw [Matrix.one_apply]

/-- **The trace of a scalar at a simple, computed**: `Tr(a · id_{X_i}) =
a · coev_i · ev_{i*}`.  No `F`-entry enters: at a simple the three legs meet on
the unit block of `X_i ⊗ X_{i*}`, which is a single point, and the middle leg is
the scalar `a` times the identity. -/
theorem traceScalar_eq (hn : 0 < n) (i : Fin n) (a : k) :
    traceScalar S hn i a = S.coev i * a * S.ev (S.ring.dual i) := by
  have hcard := pairUnitBlock_card S hn i
  have hcoev := coevSim_block S hn i
  have hev := evSim_block S hn i
  have hTH := traceMorBlock_apply S hn i a
  show (coevSim S hn i ⟨0, hn⟩ * (tensorHom S (scalarEndo (k := k) a i)
      (𝟙 (sim (k := k) (S.ring.dual i))) ⟨0, hn⟩ * evSim S hn i ⟨0, hn⟩))
    (unitPt (k := k) hn) (unitPt (k := k) hn) = S.coev i * a * S.ev (S.ring.dual i)
  rw [hcoev, hev]
  simp only [Matrix.mul_apply, Matrix.of_apply, hTH]
  -- the `1 × 1` collapse of the double sum
  have hinner : ∀ x : (tensorObj S (sim (k := k) i) (sim (k := k) (S.ring.dual i))).blk
      ⟨0, hn⟩,
      (∑ y, (a * (if x = y then (1 : k) else 0)) * S.ev (S.ring.dual i))
        = a * S.ev (S.ring.dual i) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero, zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [show (∑ x, S.coev i * (∑ y, (a * (if x = y then (1 : k) else 0))
        * S.ev (S.ring.dual i)))
      = ∑ x, S.coev i * (a * S.ev (S.ring.dual i)) from
    Finset.sum_congr rfl fun x _ => by rw [hinner x]]
  rw [Finset.sum_const, Finset.card_univ, hcard]
  simp
  ring

end Main

/-! ## §4 — the canonical ring isomorphism `End (sim 0) ≃+* k`

This is the `end_unit` field of `IsFusionCategory` for the reconstruction, and the
map through which `WP2.trDualScalar` reads a trace as a scalar: the unit object's
only block is `1 × 1`, so "the entry" *is* a ring isomorphism. -/

section EndSim

variable (S : FusionSystem n k)

/-- Every element of the unit object's block is the canonical point. -/
theorem blk_unit_eq (hn : 0 < n) (x : (sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩) :
    x = unitPt (k := k) hn := by
  apply Fin.ext
  have hx : x.val < 1 := by simpa [sim] using x.isLt
  show x.val = 0
  omega

/-- The unit object's block carries a unique index. -/
theorem blk_unit_subsingleton (hn : 0 < n) :
    Subsingleton ((sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩) :=
  ⟨fun x y => (blk_unit_eq hn x).trans (blk_unit_eq hn y).symm⟩

/-- **The canonical ring isomorphism `End (sim 0) ≃+* k`** — the `End(1) = k` field
of `IsFusionCategory` for the reconstruction.  A morphism of the unit object is a
single block, and that block is a single entry. -/
noncomputable def endSimEquiv (hn : 0 < n) : End (sim (k := k) ⟨0, hn⟩) ≃+* k where
  toFun f := f ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
  invFun a := a • 𝟙 (sim (k := k) ⟨0, hn⟩)
  left_inv f := by
    funext c x y
    by_cases hc : c = ⟨0, hn⟩
    · subst hc
      have hx : x = unitPt (k := k) hn := blk_unit_eq hn x
      have hy : y = unitPt (k := k) hn := blk_unit_eq hn y
      subst hx
      subst hy
      show ((f ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn) •
          (1 : Matrix ((sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩)
              ((sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩) k)))
          (unitPt (k := k) hn) (unitPt (k := k) hn)
        = f ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
      rw [smul_one_apply, if_pos rfl]
    · haveI hE : IsEmpty ((sim (k := k) ⟨0, hn⟩).blk c) := by
        rw [show (sim (k := k) ⟨0, hn⟩).blk c = Fin (if c = ⟨0, hn⟩ then 1 else 0) from rfl,
          if_neg hc]
        infer_instance
      exact (IsEmpty.false x).elim
  right_inv a := by
    show (a • (1 : Matrix ((sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩)
        ((sim (k := k) ⟨0, hn⟩).blk ⟨0, hn⟩) k)) (unitPt (k := k) hn) (unitPt (k := k) hn) = a
    rw [smul_one_apply, if_pos rfl]
  map_add' f g := by
    show (f ⟨0, hn⟩ + g ⟨0, hn⟩) (unitPt (k := k) hn) (unitPt (k := k) hn)
      = f ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
        + g ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
    rw [Matrix.add_apply]
  map_mul' f g := by
    rw [End.mul_def]
    show (g ⟨0, hn⟩ * f ⟨0, hn⟩) (unitPt (k := k) hn) (unitPt (k := k) hn)
      = f ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
        * g ⟨0, hn⟩ (unitPt (k := k) hn) (unitPt (k := k) hn)
    rw [Matrix.mul_apply, Finset.sum_eq_single (unitPt (k := k) hn)]
    · ring
    · intro b _ hb
      exact absurd (blk_unit_eq hn b) hb
    · intro hb
      exact absurd (Finset.mem_univ _) hb

/-- `WP2.trDualScalar`-shape: the trace of a scalar at a simple, read as a scalar
through the canonical `End(1) = k`. -/
theorem traceScalar_eq_endSimEquiv (hn : 0 < n) (i : Fin n) (a : k) :
    traceScalar S hn i a = endSimEquiv (k := k) hn (traceMor S hn i a) := rfl

end EndSim

/-! ## §5 — the frozen interface of Task 2.2 -/

section Frozen

/-- The trace of the scalar `a` at the simple `X_i`, in the shape the frozen
statements of `Statements2` quantify over (`n = 0` has no simple; the value is
then irrelevant). -/
noncomputable def trSimple {m : ℕ} (S : FusionSystem m k) (i : Fin m) (a : k) : k :=
  if hn : 0 < m then traceScalar S hn i a else 0

/-- **The trace of a scalar, at the label level.** -/
theorem trSimple_eq (S : FusionSystem n k) (i : Fin n) (a : k) :
    trSimple S i a = S.coev i * a * S.ev (S.ring.dual i) := by
  have hn : 0 < n := by have := i.isLt; omega
  rw [trSimple, dif_pos hn, traceScalar_eq]

/-- **Task 2.2(b) — `TraceOfScalar`, proved** for the reconstruction's trace. -/
theorem traceOfScalar_trSimple :
    WP2.TraceOfScalar (k := k)
      (fun {m : ℕ} (S : FusionSystem m k) (i : Fin m) (a : k) => trSimple S i a) := by
  intro m S i a
  show trSimple S i a = a * S.coev i * S.ev (S.ring.dual i)
  rw [trSimple_eq]
  ring

/-- **Task 2.2(a) — `TraceOfPivotalComponent`, proved**: the trace of the pivotal
component is the categorical dimension `dim P i = p_i κ_i`, i.e. ENO's `d_i`. -/
theorem traceOfPivotalComponent_trSimple :
    WP2.TraceOfPivotalComponent (k := k)
      (fun {m : ℕ} (S : FusionSystem m k) (i : Fin m) (a : k) => trSimple S i a) :=
  WP2.traceOfPivotalComponent_of_traceOfScalar _ traceOfScalar_trSimple

/-- **Task 2.2(c) — `TraceProduct_eq_kappa`, proved**: `κ_i κ_{i*} = |X_i|²` read
through the trace. -/
theorem traceProduct_eq_kappa_trSimple :
    WP2.TraceProduct_eq_kappa (k := k)
      (fun {m : ℕ} (S : FusionSystem m k) (i : Fin m) (a : k) => trSimple S i a) :=
  WP2.traceProduct_of_traceOfScalar _ traceOfScalar_trSimple

/-- **Task 2.2(c) at `ℂ` — `TraceGlobalDim_eq_pseudoUnitary`, proved**: the sum of
the trace-level `κ_i κ_{i*}` over the simples is `FPdim` exactly when the datum is
pseudo-unitary (the `dim(C) = FPdim(C)` of the source, transported through the
trace correspondence). -/
theorem traceGlobalDim_eq_pseudoUnitary_trSimple :
    WP2.TraceGlobalDim_eq_pseudoUnitary
      (fun {m : ℕ} (S : FusionSystem m ℂ) (i : Fin m) (a : ℂ) => trSimple S i a) :=
  WP2.traceGlobalDim_iff_pseudoUnitary _ (traceProduct_eq_kappa_trSimple (k := ℂ))

/-- **ENO's dimension is the trace of the pivotal component**: `Tr(p_i) = d_i`. -/
theorem trSimple_pVal_eq_dimENO (S : FusionSystem n k) (P : PivotalStructure S) (i : Fin n) :
    trSimple S i (P.pVal i) = dimENO P i := by
  rw [trSimple_eq, dimENO]
  ring

/-- **The categorical dimension of a simple is the trace of its identity**:
`Tr(id_{X_i}) = κ_i`. -/
theorem trSimple_one_eq_kappa (S : FusionSystem n k) (i : Fin n) :
    trSimple S i 1 = S.kappa i := by
  rw [trSimple_eq, S.ev_dual i, FusionSystem.kappa]
  ring

/-- **The categorical dimension of a simple is the trace of its identity**, in
`dim` form: `Tr(p_i · id) = dim P i`. -/
theorem trSimple_pVal_eq_dim (S : FusionSystem n k) (P : PivotalStructure S) (i : Fin n) :
    trSimple S i (P.pVal i) = dim P i := by
  rw [trSimple_eq, dim, FusionSystem.kappa, S.ev_dual i]
  ring

end Frozen

/-- The `End(1) = k` witness for the reconstruction's unit object, in exactly the
shape of `IsFusionCategory.end_unit` (once D4/D5 identify `𝟙_` with `sim 0`). -/
theorem end_unit_witness (hn : 0 < n) :
    Nonempty (End (sim (k := k) ⟨0, hn⟩) ≃+* k) :=
  ⟨endSimEquiv hn⟩

/-- **The trace is nonzero on the identity of every simple** — the frozen
statements are not vacuous: `Tr(id_{X_i}) = κ_i ≠ 0`. -/
theorem trSimple_one_ne_zero (S : FusionSystem n k) (i : Fin n) : trSimple S i 1 ≠ 0 := by
  rw [trSimple_one_eq_kappa]
  exact S.kappa_ne_zero i

/-- **The trace is nondegenerate on a simple's endomorphism ring**:
`Tr(a · id_{X_i}) = 0 ↔ a = 0`.  (Both `coev i` and `ev i*` are nonzero, the latter
by `S.ev_dual` and `ev_ne_zero`.) -/
theorem trSimple_eq_zero_iff (S : FusionSystem n k) (i : Fin n) (a : k) :
    trSimple S i a = 0 ↔ a = 0 := by
  rw [trSimple_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (S.coev_ne_zero i)
      · exact h2
    · exact absurd h1 (S.ev_ne_zero (S.ring.dual i))
  · intro h
    rw [h]
    simp

/-- The trace is homogeneous in the scalar: `Tr(a · id) = a · Tr(id)`. -/
theorem traceScalar_eq_smul_one (S : FusionSystem n k) (hn : 0 < n) (i : Fin n) (a : k) :
    traceScalar S hn i a = a * traceScalar S hn i 1 := by
  rw [traceScalar_eq, traceScalar_eq]
  ring

/-- **The trace is gauge invariant**: the vertex gauge rescales `coev i` by `λ i`
and `ev i` by `λ i⁻¹`, and the trace reads `coev i` against `ev i*`; on the
dual-invariant gauge subgroup (`Gauge.gauge` takes `hlam`) the two factors cancel.
So Task 2.2's trace functional is an object of the *datum*, not of the chosen
evaluation normalisation — the same conclusion as `DerivedJ_gauge_invariant`, one
level down. -/
theorem trSimple_gauge (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (i : Fin n) (a : k) :
    trSimple (gauge S lam hlam) i a = trSimple S i a := by
  rw [trSimple_eq, trSimple_eq]
  have hne : ((lam i : k)) ≠ 0 := (lam i).ne_zero
  simp only [gauge, hlam i]
  field_simp

/-! ## §6 — the frozen trace functional is additive and `k`-homogeneous

These two lemmas are what extends Task 2.2 past the simples: an endomorphism of an
arbitrary object is a sum of block-diagonal pieces, and `TraceGlobalDim` is the sum
over the simples.  They hold in *any* monoidal preadditive (resp. monoidal linear)
category for the frozen `WP2.trDual`, with no rigidity hypothesis beyond the two
duals the definition site itself demands. -/

namespace WP2

section Linearity

open MonoidalCategory

variable {C : Type v} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
variable {X : C} [HasRightDual X] [HasRightDual (HasRightDual.rightDual X)]

/-- The frozen trace of the zero endomorphism vanishes. -/
theorem trDual_zero :
    WP2.trDual (X := X) (0 : X ⟶ HasRightDual.rightDual (HasRightDual.rightDual X)) = 0 := by
  simp [WP2.trDual]

/-- **The frozen trace is additive in the morphism.** -/
theorem trDual_add (f g : X ⟶ HasRightDual.rightDual (HasRightDual.rightDual X)) :
    WP2.trDual (f + g) = WP2.trDual f + WP2.trDual g := by
  simp only [WP2.trDual, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
    Preadditive.comp_add]

/-- **The frozen trace is `k`-homogeneous in the morphism.** -/
theorem trDual_smul {k : Type u} [Field k] [Linear k C] [MonoidalLinear k C] (a : k)
    (f : X ⟶ HasRightDual.rightDual (HasRightDual.rightDual X)) :
    WP2.trDual (a • f) = a • WP2.trDual f := by
  simp only [WP2.trDual, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

end Linearity

end WP2

/-! ## §4b — the trace of an *arbitrary* endomorphism of a simple

`End (sim i)` is `k` on the nose (`endo_sim_eq_smul`: the only non-empty block is
`1 × 1`), so the computation above covers every endomorphism, not just the scalar
multiples of the identity.  This is the strong form of Task 2.2(b): the
categorical trace on a simple is `κ_i` times the ring identification. -/

section TraceGeneral

variable (S : FusionSystem n k)

/-- The unique point of a simple's own block. -/
def simPt (i : Fin n) : (sim (k := k) i).blk i := ⟨0, by simp⟩

/-- Every point of a simple's own block is the canonical one. -/
theorem blk_sim_eq (i : Fin n) (x : (sim (k := k) i).blk i) : x = simPt (k := k) i := by
  apply Fin.ext
  have hx : x.val < 1 := by simpa [sim] using x.isLt
  show x.val = 0
  omega

/-- **Schur at the reconstruction, on the nose**: an endomorphism of a simple is a
scalar multiple of the identity — the only non-empty block is `1 × 1`. -/
theorem endo_sim_eq_smul (i : Fin n) (g : sim (k := k) i ⟶ sim (k := k) i) :
    g = (g i (simPt (k := k) i) (simPt (k := k) i)) • 𝟙 (sim (k := k) i) := by
  funext c x y
  by_cases hc : c = i
  · subst c
    have hx : x = simPt (k := k) i := blk_sim_eq i x
    have hy : y = simPt (k := k) i := blk_sim_eq i y
    subst hx
    subst hy
    show g i (simPt (k := k) i) (simPt (k := k) i)
      = ((g i (simPt (k := k) i) (simPt (k := k) i) •
          (1 : Matrix ((sim (k := k) i).blk i) ((sim (k := k) i).blk i) k)))
        (simPt (k := k) i) (simPt (k := k) i)
    rw [smul_one_apply, if_pos rfl]
  · haveI hE : IsEmpty ((sim (k := k) i).blk c) := by
      rw [show (sim (k := k) i).blk c = Fin (if c = i then 1 else 0) from rfl, if_neg hc]
      infer_instance
    exact (IsEmpty.false x).elim

/-- **The trace of an arbitrary endomorphism of a simple**: `Tr(g) = g_{ii} · κ_i`
in the form `coev_i · g_{ii} · ev_{i*}`.  With time-reversal (`ev_dual`) this is
`g_{ii} · κ_i`: the categorical trace on `End (sim i)` is `κ_i` times the ring
identification `endSimEquiv`. -/
theorem traceScalarG_eq (hn : 0 < n) (i : Fin n) (g : sim (k := k) i ⟶ sim (k := k) i) :
    (traceMor S hn i (g i (simPt (k := k) i) (simPt (k := k) i)) ⟨0, hn⟩)
        (unitPt (k := k) hn) (unitPt (k := k) hn)
      = S.coev i * (g i (simPt (k := k) i) (simPt (k := k) i)) * S.ev (S.ring.dual i) :=
  traceScalar_eq S hn i _

/-- The same, with the endomorphism itself on the left: `Tr(g)` depends on `g` only
through its single block entry. -/
theorem traceMor_congr (hn : 0 < n) (i : Fin n) (g g' : sim (k := k) i ⟶ sim (k := k) i)
    (h : g i (simPt (k := k) i) (simPt (k := k) i)
      = g' i (simPt (k := k) i) (simPt (k := k) i)) :
    traceMor S hn i (g i (simPt (k := k) i) (simPt (k := k) i))
      = traceMor S hn i (g' i (simPt (k := k) i) (simPt (k := k) i)) := by
  rw [h]

end TraceGeneral

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.tensorHom_smul_left_apply
#print axioms FusionCategory.scalarEndo
#print axioms FusionCategory.scalarEndo_apply
#print axioms FusionCategory.coevSim
#print axioms FusionCategory.evSim
#print axioms FusionCategory.traceMor
#print axioms FusionCategory.unitPt
#print axioms FusionCategory.traceScalar
#print axioms FusionCategory.pairUnitBlock_card
#print axioms FusionCategory.coevSim_block
#print axioms FusionCategory.evSim_block
#print axioms FusionCategory.traceMorBlock_apply
#print axioms FusionCategory.traceScalar_eq
#print axioms FusionCategory.blk_unit_eq
#print axioms FusionCategory.blk_unit_subsingleton
#print axioms FusionCategory.endSimEquiv
#print axioms FusionCategory.traceScalar_eq_endSimEquiv
#print axioms FusionCategory.trSimple
#print axioms FusionCategory.trSimple_eq
#print axioms FusionCategory.traceOfScalar_trSimple
#print axioms FusionCategory.traceOfPivotalComponent_trSimple
#print axioms FusionCategory.traceProduct_eq_kappa_trSimple
#print axioms FusionCategory.traceGlobalDim_eq_pseudoUnitary_trSimple
#print axioms FusionCategory.trSimple_pVal_eq_dimENO
#print axioms FusionCategory.trSimple_one_eq_kappa
#print axioms FusionCategory.trSimple_pVal_eq_dim
#print axioms FusionCategory.end_unit_witness
#print axioms FusionCategory.traceScalar_eq_smul_one
#print axioms FusionCategory.WP2.trDual_zero
#print axioms FusionCategory.WP2.trDual_add
#print axioms FusionCategory.WP2.trDual_smul
#print axioms FusionCategory.simPt
#print axioms FusionCategory.blk_sim_eq
#print axioms FusionCategory.endo_sim_eq_smul
#print axioms FusionCategory.traceScalarG_eq
#print axioms FusionCategory.traceMor_congr
#print axioms FusionCategory.trSimple_gauge
#print axioms FusionCategory.trSimple_one_ne_zero
#print axioms FusionCategory.trSimple_eq_zero_iff
