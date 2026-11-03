import Mathlib.Tactic
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

A third defect, found when trying to build the Fibonacci instance, was in the
duality normalisation: the right snake was written with the *reciprocal* of a
single `F` entry, where the associator enters through its inverse and the
correct scalar is the `(0,0)` entry of the *matrix inverse* of the block
`F^{i* i i*}_{i*}`.  The two agree for `1 × 1` blocks (every pointed category)
and differ for self-dual simples with a `2 × 2` block, which excludes Fibonacci
and Ising.  `Finv` below carries the inverse associator with its two inverse
laws, and `snake_right` reads `Finv ... 0 0`.

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
  /-- The inverse associator, `Finv a b c d f e`: the entry of `α⁻¹` from the
  channel `f` of `b ⊗ c` to the channel `e` of `a ⊗ b`.

  It is carried as data because the block of `F` at fixed `(a,b,c,d)` is a
  square matrix indexed by those two channel sets, and the two channel sets are
  *different* subsets of `Fin n` in general: there is no canonical way to call
  the inverse "a matrix indexed by `Fin n`", and restricting to subtypes gives
  two index types that are not syntactically equal.  Carrying `α⁻¹` with its
  two inverse laws is the honest formulation (an associator *is* an
  isomorphism), and it is exactly what the right snake equation needs.

  The order of the last two arguments is part of the contract and is easy to
  get wrong: `Finv a b c d f e` is the transpose of the inverse block, which is
  **not** in general `F a b c d e f`.  For `Vec_{Z/2}` every block is `1 × 1`,
  so both readings agree and the witness below may set `Finv` to the swapped
  `F`; Fibonacci's block `[[1/φ, 1], [1/φ, -1/φ]]` is an involution but not
  symmetric, and there the swapped `F` fails `Finv_comp`
  (`Examples/FibonacciIsing.lean` proves this as
  `Fibonacci.swapped_Finv_comp_ne_one`). -/
  Finv : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → k
  /-- `Finv` vanishes off the channels: a non-zero entry requires `f` to be a
  channel of `b ⊗ c` with `d` in `a ⊗ f`, and `e` a channel of `a ⊗ b` with
  `d` in `e ⊗ c`. -/
  Finv_support : ∀ a b c d f e : Fin n,
    ¬ (0 < ring.N b c f ∧ 0 < ring.N a f d ∧ 0 < ring.N a b e ∧ 0 < ring.N e c d) →
    Finv a b c d f e = 0
  /-- `α ∘ α⁻¹ = id` on the channels of `b ⊗ c`. -/
  Finv_comp : ∀ a b c d f' f : Fin n,
    0 < ring.N b c f' → 0 < ring.N a f' d → 0 < ring.N b c f → 0 < ring.N a f d →
    (∑ e : Fin n, Finv a b c d f' e * F a b c d e f) = if f' = f then 1 else 0
  /-- `α⁻¹ ∘ α = id` on the channels of `a ⊗ b`. -/
  F_comp_inv : ∀ a b c d e' e : Fin n,
    0 < ring.N a b e' → 0 < ring.N e' c d → 0 < ring.N a b e → 0 < ring.N e c d →
    (∑ f : Fin n, Finv a b c d f e' * F a b c d e f) = if e' = e then 1 else 0
  /-- Evaluation `X_{i*} ⊗ X_i → 1`, as a scalar. -/
  ev : Fin n → k
  /-- Coevaluation `1 → X_i ⊗ X_{i*}`, as a scalar. -/
  coev : Fin n → k
  ev_ne_zero : ∀ i, ev i ≠ 0
  coev_ne_zero : ∀ i, coev i ≠ 0
  /-- Left snake: the loop at `X_i`, `(ev ⊗ id) ∘ α ∘ (id ⊗ coev) = id`. -/
  snake_left : ∀ (hn : 0 < n) (i : Fin n),
    coev i * ev i * F i (ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1
  /-- Right snake: `(ev ⊗ id) ∘ α⁻¹ ∘ (id ⊗ coev) = id` on `X_{i*}`.

  The inverse associator contributes the entry `Finv i* i i* i* 0 0`, i.e. the
  `(0,0)` entry of the *matrix inverse* of the block `F^{i* i i*}_{i*}`, and
  **not** the reciprocal of the single entry `F^{i* i i*}_{i*}(0,0)`.  The two
  agree exactly when that block is `1 × 1` — in particular for every pointed
  category — and differ as soon as the block is bigger, which is the case for
  every self-dual simple `i` with `N i i 0 = N i i i = 1`.

  This is the second correction to this axiom, and the two earlier versions
  were wrong in opposite directions.  The original wrote both snakes with a
  factor of `F`, which forces `F^{i i* i}_i(0,0) = F^{i* i i*}_{i*}(0,0)` and
  excludes `Vec^ω_{Z/3}` for non-trivial `ω` (corrected in `a8d6178`).  The
  reciprocal version then excludes every self-dual simple whose block is not
  `1 × 1`: Fibonacci has `F^{τττ}_τ = [[1/φ, 1], [1/φ, -1/φ]]` (gauge with the
  golden ratio `φ`), whence `κ_τ = φ` from the left snake, while the reciprocal
  reading demands `κ_τ = 1/φ` from the right snake.  The matrix-inverse entry
  is `1/φ` as well, because that block is an involution, so the corrected
  equation reads `φ · 1/φ = 1`.  `Examples/Fibonacci.lean` and
  `Examples/Ising.lean` are the regression tests. -/
  snake_right : ∀ (hn : 0 < n) (i : Fin n),
    coev i * ev i * Finv (ring.dual i) i (ring.dual i) (ring.dual i)
      ⟨0, hn⟩ ⟨0, hn⟩ = 1
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
this is the inverse of the loop scalar `F^{i i* i}_i(1,1)`, and equals the
`(0,0)` entry of the inverse block `(F^{i* i i*}_{i*})⁻¹`. -/
def kappa (i : Fin n) : k := S.coev i * S.ev i

theorem kappa_ne_zero (i : Fin n) : S.kappa i ≠ 0 :=
  mul_ne_zero (S.coev_ne_zero i) (S.ev_ne_zero i)

theorem kappa_loop (hn : 0 < n) (i : Fin n) :
    S.kappa i * S.F i (S.ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 :=
  S.snake_left hn i

/-- The two snake equations together say that the two loop scalars of `i` — the
`(0,0)` entry of `F^{i i* i}_i` and the `(0,0)` entry of the *inverse* block
`(F^{i* i i*}_{i*})⁻¹` — are equal, both being `1 / κ i`.

For a `1 × 1` block, i.e. for every pointed category and for `Vec_{Z/2}`, this
is the statement `F · F' = 1` that the previous formulation recorded; for a
self-dual simple with a `2 × 2` block it is a genuinely different equation
(Fibonacci: `1/φ = 1/φ`, the transferred entry of an involution). -/
theorem snake_consistency (hn : 0 < n) (i : Fin n) :
    S.F i (S.ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ =
      S.Finv (S.ring.dual i) i (S.ring.dual i) (S.ring.dual i)
        ⟨0, hn⟩ ⟨0, hn⟩ := by
  have h1 := S.snake_left hn i
  have h2 := S.snake_right hn i
  have e1 : S.F i (S.ring.dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = (S.kappa i)⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  have e2 : S.Finv (S.ring.dual i) i (S.ring.dual i) (S.ring.dual i)
      ⟨0, hn⟩ ⟨0, hn⟩ = (S.kappa i)⁻¹ :=
    eq_inv_of_mul_eq_one_right h2
  rw [e1, e2]

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
  Finv := fun a b c d f e => F a b c d e f
  Finv_support := by
    intro a b c d f e h
    simp only [F]
    exact if_neg (fun hc => h ⟨hc.2.2.1, hc.2.2.2, hc.1, hc.2.1⟩)
  Finv_comp := by
    intro a b c d f' f _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases f' <;> fin_cases f <;>
      simp only [Fin.sum_univ_two, F] <;> simp_all [N, ring]
  F_comp_inv := by
    intro a b c d e' e _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases e' <;> fin_cases e <;>
      simp only [Fin.sum_univ_two, F] <;> simp_all [N, ring]
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

/-! ## A second witness: `Vec_{Z/2}` with the non-trivial cocycle

The trivial-cocycle witness above has `F ≡ 1`, so it cannot detect anything
about the associator.  This one has `F = -1` on the all-`g` block and `1` on the
unit-leg blocks, i.e. the associator of `Vec^ω_{Z/2}` for the non-trivial
3-cocycle `ω`.  It is also the first witness with `κ ≠ 1`: the snake equations
force `κ g = -1`, so `dim g = -1` while `FPdim g = 1`.

That last point is the reason to keep it: this `FusionSystem` carries *two*
pivotal structures, `p ≡ 1` with `dim g = -1` and `p g = -1` with `dim g = 1`;
the second is the one with positive dimensions, and it is spherical
(`Examples/VecZ2Twisted.lean`).  So "the" dimension of a simple is not a
property of the fusion ring and its associator alone, and the hypothesis of
ENO 8.23 is what selects the positive one — which is exactly why the conclusion
has content. -/

namespace VecZ2Twisted

/-- The associator of `Vec^ω_{Z/2}` for the non-trivial cocycle: `-1` on the
`g ⊗ g ⊗ g → g` block, `1` on every block with a unit leg. -/
def F (a b c d e f : Fin 2) : ℚ :=
  if 0 < VecZ2.ring.N a b e ∧ 0 < VecZ2.ring.N e c d ∧
      0 < VecZ2.ring.N b c f ∧ 0 < VecZ2.ring.N a f d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then -1 else 1)
  else 0

set_option maxHeartbeats 4000000 in
/-- The pentagon holds: for the cocycle on `Z/2` the only non-trivial identity
is `ω(g,g,g)² = 1`, satisfied by `-1`. -/
theorem F_pentagon : ∀ a b c d e i j r x : Fin 2,
    (∑ k : Fin 2, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j := by
  intro a b c d e i j r x
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
    fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases x <;>
    norm_num [F, VecZ2.ring, VecZ2.N]

/-- `Vec^ω_{Z/2}` for the non-trivial cocycle, as a skeletal fusion system. -/
def system : FusionSystem 2 ℚ where
  ring := VecZ2.ring
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
      simp_all [F, VecZ2.ring, VecZ2.N]
  F_unit_right := by
    intro _ a b d e _
    fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
      simp_all [F, VecZ2.ring, VecZ2.N]
  Finv := fun a b c d f e => F a b c d e f
  Finv_support := by
    intro a b c d f e h
    simp only [F]
    exact if_neg (fun hc => h ⟨hc.2.2.1, hc.2.2.2, hc.1, hc.2.1⟩)
  Finv_comp := by
    intro a b c d f' f _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases f' <;> fin_cases f <;>
      simp only [Fin.sum_univ_two, F] <;> simp_all [VecZ2.N, VecZ2.ring]
  F_comp_inv := by
    intro a b c d e' e _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases e' <;> fin_cases e <;>
      simp only [Fin.sum_univ_two, F] <;> simp_all [VecZ2.N, VecZ2.ring]
  ev := fun _ => 1
  coev := fun i => if i = 0 then 1 else -1
  ev_ne_zero := fun _ => one_ne_zero
  coev_ne_zero := by
    intro i
    fin_cases i <;> norm_num
  snake_left := by
    intro _ i
    fin_cases i <;> norm_num [F, VecZ2.ring, VecZ2.N]
  snake_right := by
    intro _ i
    fin_cases i <;> norm_num [F, VecZ2.ring, VecZ2.N]
  J := fun _ _ _ => 1
  J_ne_zero := fun _ _ _ _ => one_ne_zero
  J_unit_left := fun _ _ => rfl
  J_unit_right := fun _ _ => rfl
  J_dual := fun _ _ => rfl
  J_coherent := by
    intro a b c d e f _ _ _ _
    simp

/-- The duality normalisation of this witness: `κ = 1` at the unit and `-1` at
`g`.  In particular the dimension of `g` in the pivotal structure `p ≡ 1` is
`-1`, not `FPdim g = 1`. -/
theorem kappa_g : system.kappa 1 = -1 := by
  simp [FusionSystem.kappa, system, F, VecZ2.ring]

theorem kappa_unit : system.kappa 0 = 1 := by
  simp [FusionSystem.kappa, system]

end VecZ2Twisted

end FusionCategory
