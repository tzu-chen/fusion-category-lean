/-
# WP2 round 2, member m6, direction D6 — rigidity on the canonical scaffold

This file re-bases round 1's duality data onto `FusionCategory.Recon`'s
block-carrying `FusionMat`:

* `FusionMat.dual S X` — the duality involution on objects
  (`m ∘ ring.dual`, `blk ∘ ring.dual`), with `dual_dual`;
* `FusionMat.ev S hn X : dual S X ⊗ X ⟶ unitObj hn` and
  `FusionMat.coev S hn X : unitObj hn ⟶ X ⊗ dual S X`, the evaluation and
  coevaluation block matrices.  Both are supported on the **unit channel**
  (`N a b 0 = δ_{b, a*}`, `dual_coeff`), where the two multiplicity indices of
  the pair live in the *same* block type `X.blk a*`; the entry is the delta on
  that block times `S.ev a` resp. `S.coev a`;
* `FusionMat.leftUnitor`/`rightUnitor` — the two unit identifications
  `unitObj ⊗ X ⟶ X`, `X ⊗ unitObj ⟶ X` as the canonical delta matrices
  (the `δ`-collapse of `left_unit`/`right_unit`).

Both `ev`/`coev` and the unitors are *delta matrices in the block index*: the
whole snake computation consists in collapsing sums against these deltas, with
the label bookkeeping supplied by `dual_coeff`/`left_unit`/`right_unit`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconUnit
import FusionCategory.ReconAssoc

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat

/-! ## Two objects with the same `m` and `blk` are equal

`FusionMat` carries the block types as data, but the remaining fields (the
`Fintype`/`DecidableEq` instances and the cardinality proofs) are subsingletons
resp. propositions, so `m` and `blk` determine the object.  This is what makes
`dual_dual` provable without transporting instances by hand. -/

theorem ext_m_blk {X Y : FusionMat n k} (hm : X.m = Y.m) (hb : X.blk = Y.blk) : X = Y := by
  obtain ⟨m, blk, ft, de, card⟩ := X
  obtain ⟨m', blk', ft', de', card'⟩ := Y
  simp only at hm hb
  subst hm
  subst hb
  have h1 : ft = ft' := by funext i; exact Subsingleton.elim _ _
  have h2 : de = de' := by funext i; exact Subsingleton.elim _ _
  subst h1
  subst h2
  have h3 : card = card' := by funext i; exact Subsingleton.elim _ _
  rw [h3]

/-! ## The dual object -/

/-- The dual object: the same multiplicities and blocks with the labels
dualized. -/
def dual (S : FusionSystem n k) (X : FusionMat n k) : FusionMat n k where
  m c := X.m (S.ring.dual c)
  blk c := X.blk (S.ring.dual c)
  fintype_blk c := X.fintype_blk (S.ring.dual c)
  decidableEq_blk c := X.decidableEq_blk (S.ring.dual c)
  card_blk c := X.card_blk (S.ring.dual c)

@[simp] theorem dual_m (S : FusionSystem n k) (X : FusionMat n k) (c : Fin n) :
    (dual S X).m c = X.m (S.ring.dual c) := rfl

@[simp] theorem dual_blk (S : FusionSystem n k) (X : FusionMat n k) (c : Fin n) :
    (dual S X).blk c = X.blk (S.ring.dual c) := rfl

@[simp] theorem dual_fintype_blk (S : FusionSystem n k) (X : FusionMat n k) (c : Fin n) :
    (dual S X).fintype_blk c = X.fintype_blk (S.ring.dual c) := rfl

/-- The double dual is the identity on objects. -/
theorem dual_dual (S : FusionSystem n k) (X : FusionMat n k) : dual S (dual S X) = X :=
  ext_m_blk
    (by funext c; exact congrArg X.m (S.ring.dual_involutive c))
    (by funext c; exact congrArg X.blk (S.ring.dual_involutive c))

@[simp] theorem dual_dual_m (S : FusionSystem n k) (X : FusionMat n k) (c : Fin n) :
    (dual S (dual S X)).m c = X.m c := by
  rw [dual_dual]

@[simp] theorem dual_dual_blk (S : FusionSystem n k) (X : FusionMat n k) (c : Fin n) :
    (dual S (dual S X)).blk c = X.blk c := by
  rw [dual_dual]

/-! ## The label facts at the unit channel

On the unit output channel the second label is *forced*: `N a b 0 = δ_{b,a*}`.
Every "unit channel" entry below reads this in one of its two directions. -/

theorem dual_label_of_unit (S : FusionSystem n k) (hn : 0 < n) {a b : Fin n}
    (ν : Fin (S.ring.N a b ⟨0, hn⟩)) : b = S.ring.dual a := by
  have h : 0 < S.ring.N a b ⟨0, hn⟩ := Nat.lt_of_le_of_lt (Nat.zero_le _) ν.isLt
  rw [S.ring.dual_coeff hn a b] at h
  by_cases hh : b = S.ring.dual a
  · exact hh
  · rw [if_neg hh] at h; exact absurd h (lt_irrefl 0)

theorem unit_channel_dual (S : FusionSystem n k) (hn : 0 < n) {a b : Fin n}
    (ν : Fin (S.ring.N a b ⟨0, hn⟩)) : S.ring.N a b ⟨0, hn⟩ = 1 := by
  rw [S.ring.dual_coeff hn a b, if_pos (dual_label_of_unit S hn ν)]

theorem unit_label_of_left (S : FusionSystem n k) (hn : 0 < n) {b c : Fin n}
    (ν : Fin (S.ring.N ⟨0, hn⟩ b c)) : b = c := by
  have h : 0 < S.ring.N ⟨0, hn⟩ b c := Nat.lt_of_le_of_lt (Nat.zero_le _) ν.isLt
  rw [S.ring.left_unit hn b c] at h
  by_cases hh : b = c
  · exact hh
  · rw [if_neg hh] at h; exact absurd h (lt_irrefl 0)

theorem unit_label_of_right (S : FusionSystem n k) (hn : 0 < n) {a b : Fin n}
    (ν : Fin (S.ring.N a ⟨0, hn⟩ b)) : a = b := by
  have h : 0 < S.ring.N a ⟨0, hn⟩ b := Nat.lt_of_le_of_lt (Nat.zero_le _) ν.isLt
  rw [S.ring.right_unit hn a b] at h
  by_cases hh : a = b
  · exact hh
  · rw [if_neg hh] at h; exact absurd h (lt_irrefl 0)

theorem unit_channel_left (S : FusionSystem n k) (hn : 0 < n) {b c : Fin n}
    (ν : Fin (S.ring.N ⟨0, hn⟩ b c)) : S.ring.N ⟨0, hn⟩ b c = 1 := by
  rw [S.ring.left_unit hn b c, if_pos (unit_label_of_left S hn ν)]

theorem unit_channel_right (S : FusionSystem n k) (hn : 0 < n) {a b : Fin n}
    (ν : Fin (S.ring.N a ⟨0, hn⟩ b)) : S.ring.N a ⟨0, hn⟩ b = 1 := by
  rw [S.ring.right_unit hn a b, if_pos (unit_label_of_right S hn ν)]

/-- The unit block of the unit object is `Fin 1`. -/
theorem unitObj_blk_zero (hn : 0 < n) :
    (unitObj (k := k) hn).blk ⟨0, hn⟩ = Fin 1 := by
  simp [unitObj]

/-! ## Evaluation and coevaluation -/

/-- Evaluation `X* ⊗ X ⟶ 𝟙`: supported on the unit channel, where the two
multiplicity indices live in the same block `X.blk a*`, delta on that block
times `S.ev` at the label of the second factor. -/
def ev (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S (dual S X) X ⟶ unitObj hn :=
  fun c => Matrix.of fun r _ =>
    if h : r.1.2 = S.ring.dual r.1.1 then
      (if (show X.blk (S.ring.dual r.1.1) from r.2.2.1) = h ▸ r.2.2.2 then S.ev r.1.2 else 0)
    else 0

/-- Coevaluation `𝟙 ⟶ X ⊗ X*`: supported on the unit channel, delta on the
common block times `S.coev` at the label of the first factor. -/
def coev (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    unitObj hn ⟶ tensorObj S X (dual S X) :=
  fun c => Matrix.of fun _ q =>
    if h : q.1.1 = S.ring.dual q.1.2 then
      (if q.2.2.1 = h.symm ▸ q.2.2.2 then S.coev q.1.1 else 0)
    else 0

/-- The evaluation entry, in the Σ-coordinates of `X* ⊗ X`. -/
theorem ev_apply (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : (dual S X).blk p.1) (t : X.blk p.2) (j : (unitObj hn).blk c) :
    ev S hn X c ⟨p, ν, s, t⟩ j
      = if h : p.2 = S.ring.dual p.1 then
          (if (show X.blk (S.ring.dual p.1) from s) = h ▸ t then S.ev p.2 else 0)
        else 0 :=
  rfl

/-- The coevaluation entry, in the Σ-coordinates of `X ⊗ X*`. -/
theorem coev_apply (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : X.blk p.1) (t : (dual S X).blk p.2) (j : (unitObj hn).blk c) :
    coev S hn X c j ⟨p, ν, s, t⟩
      = if h : p.1 = S.ring.dual p.2 then
          (if s = h.symm ▸ t then S.coev p.1 else 0)
        else 0 :=
  rfl

theorem ev_apply_of_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {p : Fin n × Fin n} (h : p.2 = S.ring.dual p.1) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : (dual S X).blk p.1) (t : X.blk p.2) (j : (unitObj hn).blk c) :
    ev S hn X c ⟨p, ν, s, t⟩ j
      = if (show X.blk (S.ring.dual p.1) from s) = h ▸ t then S.ev p.2 else 0 := by
  rw [ev_apply, dif_pos h]

theorem ev_apply_of_ne (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {p : Fin n × Fin n} (h : p.2 ≠ S.ring.dual p.1) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : (dual S X).blk p.1) (t : X.blk p.2) (j : (unitObj hn).blk c) :
    ev S hn X c ⟨p, ν, s, t⟩ j = 0 := by
  rw [ev_apply, dif_neg h]

theorem coev_apply_of_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {p : Fin n × Fin n} (h : p.1 = S.ring.dual p.2) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : X.blk p.1) (t : (dual S X).blk p.2) (j : (unitObj hn).blk c) :
    coev S hn X c j ⟨p, ν, s, t⟩
      = if s = h.symm ▸ t then S.coev p.1 else 0 := by
  rw [coev_apply, dif_pos h]

theorem coev_apply_of_ne (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {p : Fin n × Fin n} (h : p.1 ≠ S.ring.dual p.2) (ν : Fin (S.ring.N p.1 p.2 c))
    (s : X.blk p.1) (t : (dual S X).blk p.2) (j : (unitObj hn).blk c) :
    coev S hn X c j ⟨p, ν, s, t⟩ = 0 := by
  rw [coev_apply, dif_neg h]

/-! ## The unitors

`left_unit : N 0 b c = δ_{bc}` and `right_unit : N a 0 c = δ_{ac}` say that on
the unit leg the only surviving channel is the identity channel.  Concretely the
row type `(X ⊗ 𝟙).blk c` has no elements with second label `≠ 0` (the unit block
is `Fin 0` there) and no elements with first label `≠ c` (the channel is
`Fin 0` there), so the unitor is *determined* by the canonical index
`unitIdxR`; we take that as the definition (a delta matrix), which is both the
mathematically correct unitor and the form the snake collapse consumes. -/

/-- The canonical index of `X ⊗ 𝟙` over `j : X.blk c`. -/
def unitIdxR (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : X.blk c) : (tensorObj S X (unitObj hn)).blk c :=
  ⟨(c, ⟨0, hn⟩),
    ⟨0, by rw [S.ring.right_unit hn c c, if_pos rfl]; exact Nat.one_pos⟩,
    j,
    ⟨0, by simp [unitObj]⟩⟩

/-- The canonical index of `𝟙 ⊗ X` over `j : X.blk c`. -/
def unitIdxL (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : X.blk c) : (tensorObj S (unitObj hn) X).blk c :=
  ⟨(⟨0, hn⟩, c),
    ⟨0, by rw [S.ring.left_unit hn c c, if_pos rfl]; exact Nat.one_pos⟩,
    ⟨0, by simp [unitObj]⟩,
    j⟩

/-- The left unitor `𝟙 ⊗ X ⟶ X`: the identity on the canonical index. -/
def leftUnitor (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S (unitObj hn) X ⟶ X :=
  fun c => Matrix.of fun r j => if r = unitIdxL S hn X c j then 1 else 0

/-- The right unitor `X ⊗ 𝟙 ⟶ X`: the identity on the canonical index. -/
def rightUnitor (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S X (unitObj hn) ⟶ X :=
  fun c => Matrix.of fun r j => if r = unitIdxR S hn X c j then 1 else 0

theorem leftUnitor_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (unitObj hn) X).blk c) (j : X.blk c) :
    leftUnitor S hn X c r j = if r = unitIdxL S hn X c j then 1 else 0 := rfl

theorem rightUnitor_eq (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S X (unitObj hn)).blk c) (j : X.blk c) :
    rightUnitor S hn X c r j = if r = unitIdxR S hn X c j then 1 else 0 := rfl

/-- The right unitor absorbs any matrix on its left: composing against it
evaluates the other factor at the canonical index. -/
theorem mul_rightUnitor {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (A : Matrix ρ ((tensorObj S X (unitObj hn)).blk c) k) (b : ρ) (j : X.blk c) :
    (A * rightUnitor S hn X c) b j = A b (unitIdxR S hn X c j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (unitIdxR S hn X c j)]
  · rw [rightUnitor_eq, if_pos rfl, mul_one]
  · intro e _ hne
    rw [rightUnitor_eq, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The left unitor absorbs any matrix on its left. -/
theorem mul_leftUnitor {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (S : FusionSystem n k) (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (A : Matrix ρ ((tensorObj S (unitObj hn) X).blk c) k) (b : ρ) (j : X.blk c) :
    (A * leftUnitor S hn X c) b j = A b (unitIdxL S hn X c j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (unitIdxL S hn X c j)]
  · rw [leftUnitor_eq, if_pos rfl, mul_one]
  · intro e _ hne
    rw [leftUnitor_eq, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The snake equations, as frozen statements

The unitors are kept on the *outside*: `λ ≫ (coev ⊗ id) ≫ α ≫ (id ⊗ ev) = ρ`
and `ρ ≫ (id ⊗ coev) ≫ α⁻¹ ≫ (ev ⊗ id) = λ`.  Multiplied on the left by the
unitors, these are the two snake equations of the dual pair `(X, X*)`, and they
avoid needing the unitor inverses in the reduction.  (Both sides of the first
are morphisms `𝟙 ⊗ X ⟶ X`; both sides of the second `X* ⊗ 𝟙 ⟶ X*`.) -/

/-- **The left snake.**  `(coev ⊗ id) ≫ α ≫ (id ⊗ ev) ≫ ρ_X = λ_X`: the snake
`λ⁻¹ ≫ (coev ⊗ id) ≫ α ≫ (id ⊗ ev) ≫ ρ = 𝟙_X`, multiplied on the left by the
left unitor. -/
def SnakeLeft (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    whiskerRight S (coev S hn X) X
        ≫ associatorHom S X (dual S X) X ≫ whiskerLeft S X (ev S hn X) ≫ rightUnitor S hn X
      = leftUnitor S hn X

/-- **The right snake.**  `(id ⊗ coev) ≫ α⁻¹ ≫ (ev ⊗ id) ≫ λ_{X*} = ρ_{X*}`. -/
def SnakeRight (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    whiskerLeft S (dual S X) (coev S hn X)
        ≫ associatorInv S (dual S X) X (dual S X) ≫ whiskerRight S (ev S hn X) (dual S X)
        ≫ leftUnitor S hn (dual S X)
      = rightUnitor S hn (dual S X)

end FusionMat

end FusionCategory

open FusionCategory in
#print axioms FusionCategory.FusionMat.ext_m_blk
open FusionCategory in
#print axioms FusionCategory.FusionMat.dual_dual
open FusionCategory in
#print axioms FusionCategory.FusionMat.ev
open FusionCategory in
#print axioms FusionCategory.FusionMat.coev
open FusionCategory in
#print axioms FusionCategory.FusionMat.ev_apply
open FusionCategory in
#print axioms FusionCategory.FusionMat.coev_apply
open FusionCategory in
#print axioms FusionCategory.FusionMat.leftUnitor
open FusionCategory in
#print axioms FusionCategory.FusionMat.rightUnitor
open FusionCategory in
#print axioms FusionCategory.FusionMat.mul_rightUnitor
open FusionCategory in
#print axioms FusionCategory.FusionMat.mul_leftUnitor
open FusionCategory in
#print axioms FusionCategory.FusionMat.SnakeLeft
open FusionCategory in
#print axioms FusionCategory.FusionMat.SnakeRight
