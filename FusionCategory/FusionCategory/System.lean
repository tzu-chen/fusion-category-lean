import FusionCategory.Basic

/-!
# Skeletal fusion systems (F-symbols) — Step 2

Reference: Vercleyen thesis §3; EGNO Ch. 7; `haagerup-odd/Coefficients.lean`.

A `FusionSystem` is the skeletal data of a *multiplicity-free* fusion
category over a field `k`: fusion rules `N`, an associator `F`, the duality
normalisation `ev`/`coev` with its snake equations, and the double-dual twist
`J` that the pivotal axiom of `FusionCategory.Pivotal` reads.

## Why this file was rewritten

The previous version carried two defects, both found mechanically rather than
by inspection:

* its unit axioms were mutually inconsistent for `n ≥ 2`: at the index pattern
  `(0, b, 0, d, b, 0)` the left axiom forces the value `1` and the right axiom
  forces `0` for every `b ≠ 0`.  `FusionSystem` therefore had *no inhabitants*,
  and every theorem quantified over it was vacuous.  `vecZ2` at the end of this
  file is the regression test: a genuine inhabitant whose fields are all proved.
* the identity it called `pentagon` was not the pentagon.  It had eight free
  labels, where the F-matrix pentagon needs ten (the free final label was
  missing), and it fails on `Vec_{Z/2}^ω` for *every* `ω`, the trivial cocycle
  included.  The identity below has been checked exhaustively against the
  standard `Vec_{Z/2}^ω` associator for both `ω = ±1`.

## The six-index convention

`F a b c d e f` is `F^{abc}_d(e,f)`: `a`, `b`, `c` are the three factors,
`d` the composite `(a ⊗ b) ⊗ c ≅ a ⊗ (b ⊗ c)`, `e` the channel of `a ⊗ b` and
`f` the channel of `b ⊗ c`.  It vanishes unless all four channels are present
(`F_support`), which is what makes one scalar per six-tuple enough — and is why
`mult_free` is a field: with `N > 1` a single scalar slot cannot hold the
associator matrix.

## Why `J` is carried as data

`J` is the scalar by which the monoidal structure of `(−)**` acts on the
channel `(a,b;c)`.  In an honest rigid category it is *computed* from `ev`,
`coev` and `F`; that computation is not carried out here.  Carrying `J`
together with the coherence that any such computation satisfies is a
deliberate stopgap, recorded in `PLAN.md`: the derivation of `J` from the rigid
structure is the outstanding piece, and without it `J` is data that a
`FusionSystem` need not arise from a category with.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

/-- Skeletal data of a multiplicity-free fusion category over `k`.

The fields are, in order: the fusion ring; multiplicity-freeness; the
associator `F` with its support condition, pentagon and unit normalisations;
the duality normalisation `ev`, `coev` with the two snake equations; and the
double-dual twist `J` with its coherence. -/
structure FusionSystem (n : ℕ) (k : Type u) [Field k] where
  ring : FusionRing n
  /-- Multiplicity-free: every structure constant is `0` or `1`.

  With `N > 1` the single scalar `F a b c d e f` cannot hold the associator
  matrix, so this is part of the datum and not a convenience. -/
  mult_free : ∀ i j kk : Fin n, ring.N i j kk ≤ 1
  /-- The associator, `F a b c d e f = F^{abc}_d(e,f)`. -/
  F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → k
  /-- `F` vanishes off the fusion channels: a non-zero entry requires
  `e ∈ a ⊗ b`, `d ∈ e ⊗ c`, `f ∈ b ⊗ c` and `d ∈ a ⊗ f`. -/
  F_support : ∀ a b c d e f : Fin n,
    ¬ (0 < ring.N a b e ∧ 0 < ring.N e c d ∧ 0 < ring.N b c f ∧ 0 < ring.N a f d) →
    F a b c d e f = 0
  /-- The pentagon, in the F-matrix form.  Ten labels: `a b c d` the factors,
  `e` and `k` the two channels of `a ⊗ b` and `b ⊗ c` on the left, `x` the
  composite `(a ⊗ b) ⊗ c`, `i` the channel of `c ⊗ d`, `j` the channel of
  `k ⊗ d` and of `b ⊗ i`, `r` the final composite. -/
  pentagon : ∀ a b c d e i j r x : Fin n,
    (∑ k : Fin n, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j
  /-- Unit normalisation at `a = 1`: the only surviving channel is `e = b`,
  and then `d = f`. -/
  F_unit_left : ∀ (hn : 0 < n) (b c d f : Fin n), 0 < ring.N b c f →
    F ⟨0, hn⟩ b c d b f = if d = f then 1 else 0
  /-- Unit normalisation at `c = 1`: the only surviving channel is `f = b`,
  and then `d = e`. -/
  F_unit_right : ∀ (hn : 0 < n) (a b d e : Fin n), 0 < ring.N a b e →
    F a b ⟨0, hn⟩ d e b = if d = e then 1 else 0
  /-- Evaluation `X_{i*} ⊗ X_i → 1`, as a scalar. -/
  ev : Fin n → k
  /-- Coevaluation `1 → X_i ⊗ X_{i*}`, as a scalar. -/
  coev : Fin n → k
  ev_ne_zero : ∀ i, ev i ≠ 0
  coev_ne_zero : ∀ i, coev i ≠ 0
  /-- Left snake: the loop at `X_i`, `(ev ⊗ id) ∘ α ∘ (id ⊗ coev) = id`. -/
  snake_left : ∀ (hn : 0 < n) (i : Fin n),
    coev i * ev i * F i (ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1
  /-- Right snake: the same loop at `X_{i*}`. -/
  snake_right : ∀ (hn : 0 < n) (i : Fin n),
    coev i * ev i * F (ring.dual i) i (ring.dual i) (ring.dual i) ⟨0, hn⟩ ⟨0, hn⟩ = 1
  /-- The double-dual twist: the scalar of `X_a** ⊗ X_b** → (X_a ⊗ X_b)**`
  on the channel `c`. -/
  J : Fin n → Fin n → Fin n → k
  J_ne_zero : ∀ i j kk : Fin n, 0 < ring.N i j kk → J i j kk ≠ 0
  J_unit_left : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1
  J_unit_right : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1
  /-- Normalisation on the `i ⊗ i* ∋ 1` channel, which is what makes
  `p_dual` a theorem rather than an axiom. -/
  J_dual : ∀ (hn : 0 < n) (i : Fin n), J i (ring.dual i) ⟨0, hn⟩ = 1
  /-- Coherence of the twist: the two ways of comparing `(a ⊗ b ⊗ c)**` with
  `a** ⊗ b** ⊗ c**` agree.  This is the pentagon of a monoidal structure on an
  endofunctor that is the identity on objects. -/
  J_coherent : ∀ a b c d e f : Fin n,
    0 < ring.N a b e → 0 < ring.N e c d → 0 < ring.N b c f → 0 < ring.N a f d →
    J a b e * J e c d = J b c f * J a f d

namespace FusionSystem

variable {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)

/-- Underlying fusion ring. -/
abbrev toFusionRing : FusionRing n := S.ring

/-- F-symbol evaluated at given labels. -/
def FSymbol (a b c d e f : Fin n) : k := S.F a b c d e f

theorem pentagon_eq (a b c d e i j r x : Fin n) :
    (∑ k : Fin n, S.F a b c x e k * S.F a k d r x j * S.F b c d j k i) =
      S.F e c d r x i * S.F a b i r e j :=
  S.pentagon a b c d e i j r x

/-- The duality normalisation `κ i = coev i * ev i`.  By the snake equations
this is the inverse of the loop scalar `F^{i i* i}_i(1,1)`. -/
def kappa (i : Fin n) : k := S.coev i * S.ev i

theorem kappa_ne_zero (i : Fin n) : S.kappa i ≠ 0 :=
  mul_ne_zero (S.coev_ne_zero i) (S.ev_ne_zero i)

theorem kappa_loop (hn : 0 < n) (i : Fin n) :
    S.kappa i * S.F i (S.ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 :=
  S.snake_left hn i

end FusionSystem

/-! ## A genuine inhabitant: `Vec_{Z/2}`

The old `FusionSystem` had no inhabitants for `n ≥ 2`, so no theorem about it
could be tested against data.  This section supplies one: `Vec_{Z/2}` with the
trivial associator, `ev = coev = 1`, and the trivial twist.  Every field is
proved, and the pentagon is checked on all `512` label tuples — the regression
test for the defect above. -/

namespace VecZ2

/-- Fusion rules of `Vec_{Z/2}` with `0 = 1`, `1 = g`: `N a b c = 1` iff
`c = a + b` in `Z/2`. -/
def N (a b c : Fin 2) : ℕ :=
  if a = 0 then (if b = c then 1 else 0)
  else if b = 0 then (if a = c then 1 else 0)
  else (if c = 0 then 1 else 0)

/-- The fusion ring of `Vec_{Z/2}`. -/
def ring : FusionRing 2 where
  N := N
  dual := id
  dual_involutive := fun _ => rfl
  dual_zero := fun _ => rfl
  left_unit := by
    intro _ i j
    show N 0 i j = if i = j then 1 else 0
    simp only [N, Fin.zero_eta, if_true]
  right_unit := by
    intro _ i j
    show N i 0 j = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> decide
  dual_coeff := by
    intro _ i j
    show N i j 0 = if j = i then 1 else 0
    fin_cases i <;> fin_cases j <;> decide
  associativity := by
    intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide
  dual_symm := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The associator of `Vec_{Z/2}` with the trivial cocycle. -/
def F (a b c d e f : Fin 2) : ℚ :=
  if 0 < ring.N a b e ∧ 0 < ring.N e c d ∧ 0 < ring.N b c f ∧ 0 < ring.N a f d
    then 1 else 0

set_option maxHeartbeats 4000000 in
/-- The pentagon holds for `Vec_{Z/2}`'s associator on all `2^9` label tuples.
This is the check that the identity in `FusionSystem.pentagon` is the real
pentagon: the previous version of this file failed exactly here. -/
theorem F_pentagon : ∀ a b c d e i j r x : Fin 2,
    (∑ k : Fin 2, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j := by
  intro a b c d e i j r x
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
    fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases x <;> norm_num [F, ring, N]

/-- `Vec_{Z/2}` as a skeletal fusion system: trivial associator, unit
evaluation/coevaluation, trivial twist. -/
def system : FusionSystem 2 ℚ where
  ring := ring
  mult_free := by
    intro i j kk
    fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide
  F := F
  F_support := by
    intro a b c d e f h
    simp only [F]
    exact if_neg h
  pentagon := F_pentagon
  F_unit_left := by
    intro _ b c d f _
    fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases f <;>
      simp_all [F, ring, N]
  F_unit_right := by
    intro _ a b d e _
    fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
      simp_all [F, ring, N]
  ev := fun _ => 1
  coev := fun _ => 1
  ev_ne_zero := fun _ => one_ne_zero
  coev_ne_zero := fun _ => one_ne_zero
  snake_left := by
    intro _ i
    fin_cases i <;> norm_num [F, ring, N]
  snake_right := by
    intro _ i
    fin_cases i <;> norm_num [F, ring, N]
  J := fun _ _ _ => 1
  J_ne_zero := fun _ _ _ _ => one_ne_zero
  J_unit_left := fun _ _ => rfl
  J_unit_right := fun _ _ => rfl
  J_dual := fun _ _ => rfl
  J_coherent := by
    intro a b c d e f _ _ _ _
    simp

end VecZ2

end FusionCategory
