import FusionCategory.PseudoUnitary
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# B4 — the settled statements of WP1 Tasks 1.1–1.5

**Statements and definitions only.**  No proposition of the programme is proved here:
every statement whose proof is WP1's is recorded as a `Prop`-valued definition (the house
style of `Grading.lean`'s `pivotal_iff_square`), so the file elaborates with no `sorry`,
no `axiom` and no proof.  Proofs are WP1's, and WP1's dependent work is held by the
batch's holding rule.

The four choices recorded here are argued in `decisions.md`; this file is their Lean
rendering.

* **The scalar contract (Task 1.1).**  The algebraic layer stays over `[Field k]`
  (`FusionSystem`, `PivotalStructure`, the twist, the census); the *analytic* target is
  stated over `ℂ` only, with positivity read through the predicate `Pos` below.  The `ℝ`
  originals are retained, not migrated.
* **The coherence form (Task 1.3).**  `J_coherent` is replaced by the form with the `F`
  factors *retained* (`J_coherent_retained`); the F-free qualified form
  (`J_coherent_qualified`) is the equivalent companion, and the two are equivalent
  (`J_coherent_forms_agree`; both directions are proved at general `k` in
  ``FusionCategory.Coherence` (landed)).
* **The gauge normalisation (Task 1.4).**  `ev (dual i) = ev i` is added to the
  signature (`EvDual`); with it the library's `dim P i = p i * kappa i` and ENO's
  `dim_i = p_i coev_i ev_{i*}` (`dimENO`) agree, and in the self-dual case they agree
  without it.
* **The antecedent of the exact target (Task 1.5).**  The target keeps the carried twist
  field and carries the compatibility hypothesis `J_match` — the carried `J` agrees with
  the *derived* twist `derivedJ` of WP2 Task 2.3 — in its antecedent.  `derivedJ` is a
  parameter here: its definition is WP2 Task 2.3's (held), and B4 fixes only its type,
  `derivedJ : FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`, so that the statement is a
  statement about *the* derived twist and not about an arbitrary table.  NOTE (the
  conformance audit's finding, kernel-checked as the two guard theorems below):
  `ENO823ExactC` is a *family* of statements — `J_match` at the carried twist holds by
  `rfl` for every datum, so the family's universal closure collapses to the unqualified
  exact form, which the pseudo-unitary `(Z/2)^2` datum with `J ≡ 1` refutes
  (`Examples/Z2SqFalseJ.lean`).  Non-vacuity is a property of Task 2.3's eventual
  `derivedJ` — WP3 proves `J_match` fails on that datum — not of the type; the family must
  be instantiated, never universally quantified.

Axiom budget of every declaration below: `[propext, Classical.choice, Quot.sound]`
(stated definitions inherit no other dependency; checked with `#print axioms`).
-/

set_option linter.unusedVariables false

universe u

namespace FusionCategory

/-! ## Task 1.1 — the scalar contract: positivity on `ℂ` -/

/-- **The positivity predicate of the scalar contract** (S2, Task 1.1): `z : ℂ` is a
positive real.  Defined once, and used by every `ℂ` statement below; it replaces `0 < ·`
wherever the source's scalar field is `ℂ`.

`Pos z := ∃ r : ℝ, 0 < r ∧ z = r`. -/
noncomputable def Pos (z : ℂ) : Prop := ∃ r : ℝ, 0 < r ∧ z = r

/-! ## Task 1.1 — the `ℂ` pseudo-unitarity predicate

The `ℝ` original `IsPseudoUnitary` is retained; this is the `ℂ` statement's hypothesis,
with the real `FPData` read in `ℂ` through `ℝ → ℂ` (the appendix of the proposal: "the
`Cx` restatement is the same rendering under the scalar contract, with a real `FPData`
embedded by `R → C`").  No pivotal structure appears in it. -/

/-- **Pseudo-unitarity at `ℂ`**: `Σ_i κ_i κ_{i*} = FPdim(C)`, the scalar equation
`dim(C) = FPdim(C)` of ENO §8.4, with the real global FP-dimension read through
`algebraMap ℝ ℂ`. -/
noncomputable def IsPseudoUnitaryC {n : ℕ} (S : FusionSystem n ℂ)
    (hFP : S.ring.FPData) : Prop :=
  (∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i)) = algebraMap ℝ ℂ hFP.globalDim

/-! ## Task 1.5(b) — the compatibility hypothesis `J_match` -/

/-- **`J_match`**: the twist carried by the datum agrees with a candidate twist `dJ` on
every supported channel.  This is the *relation*; the target below instantiates `dJ` with
the derived twist, which is what makes the hypothesis a restriction (the pointed
`Vec^ω_{(Z/2)^2}` datum with `J ≡ 1` fails it, since its derived twist is `δ(κ)`). -/
def J_match {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (dJ : Fin n → Fin n → Fin n → k) : Prop :=
  ∀ a b c : Fin n, 0 < S.ring.N a b c → S.J a b c = dJ a b c

section DerivedTwist

/- The **interface** of WP2 Task 2.3's derived twist, at the scalar field `ℂ`: a function
of the datum, computed from its associator and duality data.  Its *definition* is Task
2.3's and is held by the batch's holding rule; B4 fixes only its type — so that the target
below quantifies over *the* derived twist of a datum and not over a free table. -/
variable (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ)

/-! ## Task 1.5 — the exact target at `ℂ`

The rendering of `ENO823Exact` under the scalar contract: the existential conjunction is
reproduced verbatim, with `Pos (dim P i)` in place of `0 < dim P i`, `dim P i` read in `ℂ`
against `algebraMap ℝ ℂ (hFP.fpdim i)`, and the `J_match` qualification of Task 1.5(b)
added to the antecedent, on the model of Task 1.5(a). -/

/-- **ENO Proposition 8.23, exact form, at `ℂ` with the derived-twist qualification**: for
pseudo-unitary `S` whose carried twist is the derived one, there is a *unique* pivotal
structure which is spherical, whose dimensions are positive in the sense of `Pos`, and
whose dimensions are the Frobenius–Perron dimensions.

The existential conjunction is `ENO823Exact`'s, field for field, with `Pos (dim P i)` in
place of `0 < dim P i`.  Without the `J_match` conjunct the statement is false: the
pseudo-unitary `(Z/2)^2` datum with `J ≡ 1` admits no pivotal structure with
`dim = FPdim` (B3a). -/
noncomputable def ENO823ExactC {n : ℕ} (S : FusionSystem n ℂ)
    (hFP : S.ring.FPData) : Prop :=
  IsPseudoUnitaryC S hFP → J_match S (derivedJ S) →
    ∃! P : PivotalStructure S,
      P.IsSpherical ∧ (∀ i : Fin n, Pos (dim P i)) ∧
        (∀ i : Fin n, dim P i = algebraMap ℝ ℂ (hFP.fpdim i))

end DerivedTwist

/-! ## The two guard theorems (the conformance audit's finding)

`ENO823ExactC` is a family of statements parametrised by the candidate twist.  These two
theorems record, in the kernel, why the family must be instantiated at Task 2.3's
`derivedJ` and never universally quantified. -/

/-- `J_match` at the *carried* twist holds by `rfl` for every datum: the carried `J`
agrees with itself.  This is the trivial instantiation that the qualification must exclude. -/
theorem J_match_carried {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    J_match S S.J := fun a b c _ => rfl

/-- The universal closure of `ENO823ExactC` over its `derivedJ` parameter collapses the
qualification to nothing: instantiating at the carried twist `dJ := fun T => T.J` passes
`J_match` (by `J_match_carried`) and yields the *unqualified* exact form --- the one the
pseudo-unitary `(Z/2)^2` datum with `J ≡ 1` refutes (`Examples/Z2SqFalseJ.lean`:
`not_eno823Exact`).  `ENO823ExactC` is therefore true at the intended instantiation
(WP2 Task 2.3's `derivedJ`, where `J_match` is a genuine restriction) and false at the
carried twist. -/
theorem eno823ExactC_collapse {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData)
    (h : ∀ dJ : (∀ {m : ℕ}, FusionSystem m ℂ → Fin m → Fin m → Fin m → ℂ),
      ENO823ExactC dJ S hFP) :
    IsPseudoUnitaryC S hFP →
      ∃! P : PivotalStructure S,
        P.IsSpherical ∧ (∀ i : Fin n, Pos (dim P i)) ∧
          (∀ i : Fin n, dim P i = algebraMap ℝ ℂ (hFP.fpdim i)) :=
  fun hPU => h (fun {m} (T : FusionSystem m ℂ) => T.J) hPU (fun a b c _ => rfl)

/-! ## Task 1.3 — the coherence form of `J` (chosen: `F` retained) -/

/-- **The corrected `J_coherent`, chosen form: the `F`-factors retained.**

`J^e_ab · J^d_ec · F^{abc}_d(e,f) = J^f_bc · J^d_af · F^{abc}_d(e,f)` on the supported
channels.  Nothing is cancelled, so no nonzero side condition is needed; this is a
weakening of the field `FusionSystem.J_coherent` as it stands (which implies it — multiply
by the entry), and it implies the qualified F-free law below by cancellation.  At landing
the field `FusionSystem.J_coherent` is *replaced* by this body, not kept alongside. -/
def J_coherent_retained {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    S.J a b e * S.J e c d * S.F a b c d e f
      = S.J b c f * S.J a f d * S.F a b c d e f

/-- **The companion form: the F-free law qualified by the nonzero-entry side condition**
`h_F` (Bartlett's Corollary 3.26 shape).  Equivalent to `J_coherent_retained`; not the
chosen replacement, recorded so that the choice is visible and checkable. -/
def J_coherent_qualified {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d → S.F a b c d e f ≠ 0 →
    S.J a b e * S.J e c d = S.J b c f * S.J a f d

/-- **The two forms are equivalent**, so choosing the retained-`F` form neither strengthens
nor weakens the signature.  Both directions are proved at general `k` (no `sorry`, axiom
budget respected) in ``FusionCategory.Coherence` (landed)
(`retained_of_qualified`, `qualified_of_retained`), which is ready to land. -/
def J_coherent_forms_agree {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : Prop :=
  J_coherent_qualified S ↔ J_coherent_retained S

/-! ## Task 1.2 — the triangle law (a statement of Task 1.1–1.5, proved in WP1) -/

/-- **The triangle law**, the middle-unit entry: `F^{a 1 c}_d(a,c) = 1` on a supported
channel.  Not an axiom: the pentagon at `(a,1,1,c)` forces `t = t²`, and the `1 × 1`
block with `Finv_comp` forces `t ≠ 0`, hence `t = 1`.  Proved (no `sorry`, axiom budget
respected) in ``FusionCategory.Triangle` (landed), ready to land. -/
def TriangleLaw {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (a c d : Fin n), 0 < S.ring.N a c d → S.F a ⟨0, hn⟩ c d a c = 1

/-! ## Task 1.4 — the gauge-invariant duality normalisation -/

/-- **The gauge normalisation**, chosen as an axiom on the signature: evaluation is
invariant under duality, `ev_{i*} = ev_i`.  Landing adds it as a field of `FusionSystem`
(`ev_dual`); it is a gauge fixing, not a restriction — the vertex gauge
`coev i ↦ λ_i coev i`, `ev i ↦ ev i / λ_i` preserves the snakes and `κ`, and the actions
with `λ_{i*} = λ_i` reach the normalisation. -/
def EvDual {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : Prop :=
  ∀ i : Fin n, S.ev (S.ring.dual i) = S.ev i

/-- **ENO's dimension**, `d_i = p_i · coev_i · ev_{i*}`, with the evaluation taken at the
*dual* label, as the source writes it.  The library's `dim P i = p_i · κ_i` takes it at
`i`; the two differ by the gauge defect `ev_{i*}/ev_i`. -/
noncomputable def dimENO {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : k :=
  (P.p i : k) * S.coev i * S.ev (S.ring.dual i)

/-- **The two normalisations agree** under the chosen gauge normalisation: ENO's
`p_i coev_i ev_{i*}` equals the library's `dim P i = p_i coev_i ev_i`.  This is what makes
(K) gauge-invariant, hence the target a statement about the datum and not about a choice of
evaluations. -/
noncomputable def dimENO_eq_dim {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) : Prop :=
  ∀ (P : PivotalStructure S) (i : Fin n), dimENO P i = dim P i

/-- **The two normalisations agree in the self-dual case without the axiom**: when
`i* = i` the two readings are the same expression.  This is the sense in which the
Task 1.4 axiom is a normalisation of the non-self-dual labels only — in particular it is
vacuous on every self-dual instance. -/
noncomputable def dimENO_eq_dim_of_selfdual {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : Prop :=
  ∀ (P : PivotalStructure S) (i : Fin n), S.ring.dual i = i → dimENO P i = dim P i

/-! ## Task 1.1 — the `ℂ` forms of `pivotal_ext`, `IsPseudoUnitaryPivotal`,
`eno823_of_pseudoUnitary`, and the two directions of Task 1.5(a)

The `ℝ` originals are retained.  The `ℂ` forms keep their names, distinguished by the
namespace `Cx`; neither the order nor the modulus of the `ℝ` statements generalises, so
these are genuinely new declarations (the appendix of the proposal: "their proofs are
field-generic, but the `R` statements cannot simply be generalised: the order, the modulus
and the positivity conjunct fail").

Each of the four is a *closed proposition* — the `∀`-closure of the statement to be proved —
recorded as a `def` so that the file carries no proof.  WP1 discharges them; the proofs are
expected to follow `PseudoUnitary.lean` line for line, with `Pos` supplying the real witness
where the `ℝ` original uses the order directly. -/

namespace Cx

/-- **Task 1.1, `ℂ` form of `pivotal_ext`**: a pivotal structure is determined by its
dimension function.  (Field-generic: `mul_right_cancel₀ (kappa_ne_zero i)`.) -/
noncomputable def pivotal_ext : Prop :=
  ∀ {n : ℕ} {S : FusionSystem n ℂ} (P P' : PivotalStructure S),
    (∀ i : Fin n, dim P i = dim P' i) → P = P'

/-- **Task 1.1, `ℂ` form of `IsPseudoUnitaryPivotal`**: the dimension function of a
pivotal structure is positive (`Pos`) and multiplicative on the fusion ring.  This is the
conditional form's hypothesis: it assumes a pivotal structure rather than producing one. -/
structure IsPseudoUnitaryPivotal {n : ℕ} {S : FusionSystem n ℂ}
    (P : PivotalStructure S) : Prop where
  /-- Positivity, read through `Pos` — part of the source's conclusion, a hypothesis of
  this conditional form. -/
  pos : ∀ i : Fin n, Pos (dim P i)
  /-- Multiplicativity of the dimension on the fusion ring. -/
  mult : ∀ i kk : Fin n,
    (∑ j : Fin n, (S.ring.N i j kk : ℂ) * dim P j) = dim P i * dim P kk

/-- **Task 1.1, `ℂ` form of `eno823_of_pseudoUnitary`**: a pseudo-unitary pivotal
structure is spherical with the FP-dimensions, given Perron–Frobenius uniqueness.  Strictly
weaker than the exact form, which produces the pivotal structure.  (`Pos` supplies the real
witness that `PFUnique`, an `ℝ` statement, consumes.) -/
noncomputable def eno823_of_pseudoUnitary : Prop :=
  ∀ {n : ℕ} {S : FusionSystem n ℂ}, 0 < n →
    ∀ (hFP : S.ring.FPData), PFUnique S.ring hFP →
      ∀ (P : PivotalStructure S), IsPseudoUnitaryPivotal P → ENO823 S hFP

section DerivedTwist

variable (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ)

/-- **Task 1.5(a), `ℂ` form: exact implies bare, conditionally on the hypothesis.**  This
is the implication the Yang–Lee refutation leaves standing: the bare form has no
pseudo-unitarity antecedent, so the exact form implies it only under that antecedent (and
the `J_match` qualification). -/
noncomputable def eno823_of_exact : Prop :=
  ∀ {n : ℕ} {S : FusionSystem n ℂ} (hFP : S.ring.FPData),
    ENO823ExactC derivedJ S hFP → IsPseudoUnitaryC S hFP → J_match S (derivedJ S) →
      ENO823 S hFP

/-- **Task 1.5(a), `ℂ` form: bare implies exact, unconditionally.**  Uniqueness is
`pivotal_ext` (`Cx.pivotal_ext`), and the positivity conjunct is supplied by
`dim P i = f_i` with `f_i > 0`. -/
noncomputable def eno823_of_bare : Prop :=
  ∀ {n : ℕ} {S : FusionSystem n ℂ} (hFP : S.ring.FPData),
    ENO823 S hFP → ENO823ExactC derivedJ S hFP

end DerivedTwist

end Cx

end FusionCategory
