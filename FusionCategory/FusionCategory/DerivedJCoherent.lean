import FusionCategory.DerivedJPointed
import FusionCategory.DoubleDualTensorator
import FusionCategory.Coherence

/-!
# WP3 direction d1 — the fourth law for the derived twist

`FusionSystem`'s twist carries four laws (`J_ne_zero`, `J_unit_left`, `J_unit_right`,
`J_dual`, `J_coherent`).  WP3 replaces "`J` is data" by "`J` is computed"; three of the
four laws are theorems for the derived twist on arbitrary data
(`DerivedJLaws.derivedJGen_unit_left`, `_unit_right`, `_dual`).  This file attacks the
fourth, `J_coherent`.

## What is proved here

* `TwistQualified` and `coherent_of_qualified`: the displayed `F`-retained form of the law
  and its `F`-free form are equivalent for *any* table `J` — so the whole content of the
  fourth law is the sum-free equality `J a b e * J e c d = J b c f * J a f d` on the
  channels where `F a b c d e f ≠ 0` (this is `CoherenceCheck.Qualified`'s shape, with the
  twist left free; `twistQualified_systemJ` identifies the two).
* `coherent_free_of_coboundary` / `coherent_of_coboundary`: a table that is a coboundary
  `g a * g b / g c` of a nowhere-vanishing `g` satisfies the law; the `g`-factors cancel,
  so no associator algebra enters.
* **`derivedJGen_coherent_of_pointed`**: the derived twist satisfies the fourth law on
  every *pointed* datum, in general `n`, via the pointed `δ(κ)` theorem
  (`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed`) — `derivedJGen` is then a
  coboundary and `κ` is nowhere zero.  Per instance (§5):
  `derivedJGen_coherent_VecZ2`, `_VecZ2Twisted`, `_Z2SqH_system`, `_Z2SqH_systemH`, with
  the pointedness of those four data sets proved here (`pointed_VecZ2`,
  `pointed_VecZ2Twisted`, `pointed_Z2SqH_system`, `pointed_Z2SqH_systemH`).
* **`derivedJGen_coherent_of_J_match`**: on a datum whose carried twist already agrees
  with the derived one, the derived twist inherits the datum's own `J_coherent` field.
  With `derivedJGen_unit_left/_right/_dual` this says that wherever `J_match` is proved
  (WP3 Task 3.3's per-instance discharges) the derived twist satisfies the *whole* law
  set — no associator algebra is needed on that datum.
* **`derivedJGen_coherent_of_one`**: if the derived twist is identically `1` on the
  channels, it is coherent.  The exact computation of the closed form
  (`.ultramath/smw7dod9a/m1/cohcheck_all.py`) shows this is the case on `FibonacciSystem`,
  `IsingSystem` and `YangLee.system` — the three non-pointed data sets of the tree — so
  those three are covered as soon as their `J_match` is landed (d3/d4), through
  `derivedJGen_coherent_of_J_match` or through this lemma.
* **`exists_fusionSystem_derivedJGen`**: the assembly.  Given nonvanishing of the derived
  twist on the channels and the fourth law, there is a `FusionSystem` on the *same* ring,
  associator, inverse associator and duality data whose twist is the derived table — the
  literal content of "`J` is computed, not carried".  `exists_fusionSystem_derivedJGen_of_pointed`
  discharges the fourth law in that statement for pointed data, leaving only WP2's frozen
  `DerivedJ_ne_zero` as input.
* `derivedJGen_coherent_iff_omegaCoeff_cocycle`: the reduction the direction asks for —
  on any tuple whose four `omegaCoeff` brackets are nonzero (`OmegaNe`), the law for
  `derivedJGen` is *equivalent* to the associator-only identity
  `Ω(a,b;e)·Ω(e;c·d) = Ω(b,c;f)·Ω(a,f;d)` with `Ω = FusionMat.omegaCoeff`.  That identity
  is the exact remaining obligation: sum-free, free of `ev`/`coev`, stated purely in `F`
  and `Finv`.

## What is not proved here

Coherence of `derivedJGen` on arbitrary data.  The reduction above
(`derivedJGen_coherent_iff_omegaCoeff_cocycle`) locates the gap precisely: what is missing
is the associator-only cocycle identity for `omegaCoeff`.  Two structural facts about that
gap are worth recording for the next round.

1. *Every sum-free consequence of the axioms used so far needs a unique fusion channel.*
   `finv_mul_F_of_unique` (`Finv · F = 1`) needs the `a ⊗ b`-channel to be unique;
   `TriangleCheck.triangle` and the unit normalisations are the cases where that
   uniqueness is forced by `left_unit`/`right_unit`/`dual_coeff`; and the three pentagon
   instances of `DerivedJPointed` (`pentagon_P1`–`P3`) collapse their `k`-sum for the same
   reason.  Pointed data is exactly the case where this holds everywhere, which is why the
   law is proved there; on multiplicity-free non-pointed data the pentagon's `k`-sum keeps
   several terms (`FibonacciSystem`: `F^{τττ}_τ` is a `2 × 2` block, `IsingSystem`: the
   same for `F^{σσσ}_σ`), so the passage from the pentagon to a sum-free identity has to be
   made at the level of blocks rather than of scalars.
2. *No counterexample is to be expected.*  Under the nonvanishing hypotheses of
   `OmegaNe`, `comparisonScalar_spec` pins `ψ_{a,b}` to the unique channel scalar
   intertwining the evaluations, i.e. to the honest comparison map, and coherence of the
   resulting tensorator is the classical statement that `(−)**` is monoidal.  So the gap
   is one of derivation, not of truth: a refutation would have to exhibit a datum on which
   the written closed form differs from the mate, and `comparisonScalar_spec` excludes
   that wherever the divisor is nonzero.  `.ultramath/smw7dod9a/m1/cohcheck_all.py`
   evaluates the `F`-retained identity exactly on **all six** data sets of the census
   (`VecZ2`, `VecZ2Twisted`, `Z2SqH.system`, `Z2SqH.systemH`, `FibonacciSystem`,
   `IsingSystem`, `YangLee.system` — 210 supported label tuples in total) with `0`
   failures, and finds `derivedJGen ∈ {0, ±1}` throughout.

3. *The natural splitting does not work.*  With `P(x,y;z) = F x y z* 0 z x*` (a `1 × 1`
   block, so nonzero with elementary reciprocal) and `Q(x,y;z) = Finv y y* x* x* z* 0`
   (a genuine inverse-matrix entry), `omegaCoeff = Π · Ρ` with `Π = P/P'` and `Ρ = Q/Q'`,
   and **neither factor is a cocycle by itself**: on `Z2SqH.system` each has 12 failing
   tuples while their product has none
   (`.ultramath/smw7dod9a/m1/split.py`).  So the identity cannot be proved by splitting it
   into two simpler coherence statements; the two halves' defects cancel, which is a
   genuinely matrix-level phenomenon.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the two forms of the fourth law

`FusionSystem.J_coherent` retains the associator entry on both sides.  Since both sides
carry the *same* factor `F a b c d e f`, the retained form is equivalent to the `F`-free
form on the channels where that entry is nonzero — `CoherenceCheck.qualified_of_retained`
is one direction (already in the library); the other is here, for an arbitrary table. -/

/-- **The `F`-free form of the fourth law, for an arbitrary twist table**: the equality
`J a b e * J e c d = J b c f * J a f d` on every supported channel whose associator entry
is nonzero. -/
def TwistQualified (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d → S.F a b c d e f ≠ 0 →
    J a b e * J e c d = J b c f * J a f d

/-- **The `F`-free form implies the retained form** — multiply by the entry; when it
vanishes both sides do. -/
theorem coherent_of_qualified {S : FusionSystem n k} {J : Fin n → Fin n → Fin n → k}
    (h : TwistQualified S J) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  by_cases hF : S.F a b c d e f = 0
  · rw [hF, mul_zero, mul_zero]
  · rw [h a b c d e f h1 h2 h3 h4 hF]

/-- The derived twist's `F`-free form is `TwistQualified` at `derivedJGen`. -/
theorem derivedJGen_twistQualified_iff (S : FusionSystem n k) :
    TwistQualified S (derivedJGen S) ↔
      (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d → S.F a b c d e f ≠ 0 →
        derivedJGen S a b e * derivedJGen S e c d
          = derivedJGen S b c f * derivedJGen S a f d) :=
  Iff.rfl

/-- My `TwistQualified` at the carried twist is the library's `CoherenceCheck.Qualified`. -/
theorem twistQualified_systemJ_iff (S : FusionSystem n k) :
    TwistQualified S S.J ↔ CoherenceCheck.Qualified S := by
  constructor
  · intro h a b c d e f h1 h2 h3 h4 hF
    exact h a b c d e f h1 h2 h3 h4 hF
  · intro h a b c d e f h1 h2 h3 h4 hF
    exact h a b c d e f h1 h2 h3 h4 hF

/-! ## §2 — coboundaries are coherent

If the twist table is the coboundary of a nowhere-vanishing `g`, both sides of the
`F`-free law read `g a * g b * g c / g d` and the associator is irrelevant.  This is the
form in which the *pointed* `δ(κ)` theorem
(`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed`) discharges the fourth law. -/

/-- **A coboundary table satisfies the `F`-free fourth law.** -/
theorem coherent_free_of_coboundary {S : FusionSystem n k}
    {J : Fin n → Fin n → Fin n → k} (g : Fin n → k) (hg : ∀ i : Fin n, g i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → J a b c = g a * g b / g c) :
    TwistQualified S J := by
  intro a b c d e f h1 h2 h3 h4 _
  rw [hJ a b e h1, hJ e c d h2, hJ b c f h3, hJ a f d h4]
  have ha : g a ≠ 0 := hg a
  have hb : g b ≠ 0 := hg b
  have hc : g c ≠ 0 := hg c
  have he : g e ≠ 0 := hg e
  have hf : g f ≠ 0 := hg f
  have hd : g d ≠ 0 := hg d
  field_simp
  try ring

/-- **A coboundary table satisfies the fourth law** in the retained form. -/
theorem coherent_of_coboundary {S : FusionSystem n k}
    {J : Fin n → Fin n → Fin n → k} (g : Fin n → k) (hg : ∀ i : Fin n, g i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → J a b c = g a * g b / g c) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f :=
  coherent_of_qualified (coherent_free_of_coboundary g hg hJ)

/-- **The derived twist satisfies the fourth law wherever it is a coboundary.** -/
theorem derivedJGen_coherent_of_coboundary (S : FusionSystem n k) (g : Fin n → k)
    (hg : ∀ i : Fin n, g i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = g a * g b / g c) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f :=
  coherent_of_coboundary g hg hJ

/-- **The fourth law for the derived twist on pointed data**, in general `n`: the
`δ(κ)` theorem turns the derived twist into the coboundary of the duality normalisation,
and `κ` is nowhere zero (`FusionSystem.kappa_ne_zero`). -/
theorem derivedJGen_coherent_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  refine derivedJGen_coherent_of_coboundary S S.kappa (fun i => S.kappa_ne_zero i) ?_
  intro a b c hN
  exact derivedJGen_eq_delta_kappa_of_pointed S hn hP hN

/-- **The `F`-free form on pointed data.** -/
theorem derivedJGen_qualified_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) : TwistQualified S (derivedJGen S) :=
  coherent_free_of_coboundary S.kappa (fun i => S.kappa_ne_zero i)
    (fun a b c hN => derivedJGen_eq_delta_kappa_of_pointed S hn hP hN)

/-! ## §3 — coherence transfers along `J_match`

The derived twist is `S.J`-blind (`DerivedJLaws.derivedJGen_withJ`).  Where the datum's
carried twist *already agrees* with the derived one, the derived twist inherits the
datum's own `J_coherent` field.  With `derivedJGen_unit_left`, `_unit_right`, `_dual` this
says: once `J_match S (derivedJGen S)` is known, all four laws hold for the derived twist
on that datum. -/

/-- **Coherence transfers along `J_match`.** -/
theorem derivedJGen_coherent_of_J_match (S : FusionSystem n k)
    (hm : J_match S (derivedJGen S)) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  have h1' := hm a b e h1
  have h2' := hm e c d h2
  have h3' := hm b c f h3
  have h4' := hm a f d h4
  rw [← h1', ← h2', ← h3', ← h4']
  exact S.J_coherent a b c d e f h1 h2 h3 h4

/-- **The `F`-free form transfers along `J_match`** (given the entry is nonzero). -/
theorem derivedJGen_qualified_of_J_match (S : FusionSystem n k)
    (hm : J_match S (derivedJGen S)) : TwistQualified S (derivedJGen S) := by
  intro a b c d e f h1 h2 h3 h4 hF
  have h := derivedJGen_coherent_of_J_match S hm a b c d e f h1 h2 h3 h4
  exact mul_right_cancel₀ hF h


/-! ## §4 — the special case `derivedJGen ≡ 1`

`FibonacciSystem`, `IsingSystem` and `YangLee.system` carry `J ≡ 1`, and the exact
computation of the closed form (`.ultramath/smw7dod9a/m1/cohcheck.py`) gives
`derivedJGen ≡ 1` on all three.  Whenever that is known — it is exactly what
`J_match` amounts to there — the fourth law is the trivial equality `1 = 1`; the
`g ≡ 1` instance of §2 records it once. -/

/-- **A twist that is identically `1` on the channels is coherent.** -/
theorem derivedJGen_coherent_of_one (S : FusionSystem n k)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = 1) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f :=
  derivedJGen_coherent_of_coboundary S (fun _ => 1) (fun _ => one_ne_zero) (by
    intro a b c hN
    rw [hJ a b c hN]
    simp)

/-! ## §5 — pointedness of the tree's pointed data, and the assembly

The fourth law is proved for the derived twist on *all* pointed data (§2).  Three of
the tree's data sets are pointed (`VecZ2.system`, `VecZ2Twisted.system`,
`Z2SqH.systemH`; `Z2SqH.system` shares the ring of `Z2SqH.systemH`), so on them the
derived twist satisfies the law unconditionally.  The `∃ FusionSystem` statements at
the end record what that buys: on those data the twist can be *replaced by the
computation*, exactly as WP3 asks, with the nonvanishing law `J_ne_zero` (WP2's frozen
`DerivedJ_ne_zero`, open in general) as the only remaining input. -/

/-- Pointedness depends only on the fusion ring. -/
theorem pointed_of_ring_eq {S S' : FusionSystem n k} (h : S'.ring = S.ring)
    (hP : WP2.Pointed S) : WP2.Pointed S' := by
  intro a b
  obtain ⟨c, hc, hu⟩ := hP a b
  exact ⟨c, by rw [h]; exact hc, fun c' hc' => hu c' (by rw [h] at hc'; exact hc')⟩

/-- The derived twist is coherent on pointed data, without the case `n = 0`. -/
theorem derivedJGen_coherent_of_pointed' (S : FusionSystem n k) (hP : WP2.Pointed S) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    intro a
    exact a.elim0
  · exact derivedJGen_coherent_of_pointed S h0 hP

/-- **The twist is computed, not carried** — the general assembly.  Given the two
facts about `derivedJGen` that this file does not prove in general (nonvanishing on
the channels, and the fourth law), there is a `FusionSystem` on the same ring,
associator, inverse associator and duality data whose twist *is* the derived table.
Nothing else changes: `F`, `Finv`, `ev`, `coev` and the fusion ring are those of `S`,
so `derivedJGen` of the new datum is again `derivedJGen S`
(`DerivedJLaws.derivedJGen_withJ`). -/
theorem exists_fusionSystem_derivedJGen (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hc : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  ⟨withJ S (derivedJGen S) hne
      (fun hn j => derivedJGen_unit_left S hn j)
      (fun hn i => derivedJGen_unit_right S hn i)
      (fun hn i => derivedJGen_dual S hn i) hc,
    rfl, rfl, rfl, rfl, rfl⟩

/-- **Pointed data**: the assembly with the fourth law discharged (§2) and only the
nonvanishing law left as input. -/
theorem exists_fusionSystem_derivedJGen_of_pointed (S : FusionSystem n k)
    (hP : WP2.Pointed S)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  exists_fusionSystem_derivedJGen S hne (derivedJGen_coherent_of_pointed' S hP)


/-! ### The tree's pointed data sets -/

/-- `Vec_{Z/2}` is pointed. -/
theorem pointed_VecZ2 : WP2.Pointed VecZ2.system := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, by decide, by intro c hc; fin_cases c <;> simp_all [VecZ2.system, VecZ2.ring, VecZ2.N]⟩
  · exact ⟨1, by decide, by intro c hc; fin_cases c <;> simp_all [VecZ2.system, VecZ2.ring, VecZ2.N]⟩
  · exact ⟨1, by decide, by intro c hc; fin_cases c <;> simp_all [VecZ2.system, VecZ2.ring, VecZ2.N]⟩
  · exact ⟨0, by decide, by intro c hc; fin_cases c <;> simp_all [VecZ2.system, VecZ2.ring, VecZ2.N]⟩

/-- `Vec^ω_{Z/2}` with the non-trivial cocycle has the same fusion ring, so it is
pointed too. -/
theorem pointed_VecZ2Twisted : WP2.Pointed VecZ2Twisted.system :=
  pointed_of_ring_eq (S := VecZ2.system) (S' := VecZ2Twisted.system) rfl pointed_VecZ2

/-- The honest `(Z/2)²` datum is pointed (`DoubleDualTensorator.Z2SqH.pointed`). -/
theorem pointed_Z2SqH_system : WP2.Pointed Z2SqH.system := Z2SqH.pointed

/-- The same ring with the honest twist `δ(κ)`: still pointed. -/
theorem pointed_Z2SqH_systemH : WP2.Pointed Z2SqH.systemH :=
  pointed_of_ring_eq (S := Z2SqH.system) (S' := Z2SqH.systemH) rfl pointed_Z2SqH_system

/-- **The fourth law on `Vec_{Z/2}`.** -/
theorem derivedJGen_coherent_VecZ2 :
    ∀ a b c d e f : Fin 2, 0 < VecZ2.system.ring.N a b e →
      0 < VecZ2.system.ring.N e c d → 0 < VecZ2.system.ring.N b c f →
      0 < VecZ2.system.ring.N a f d →
      derivedJGen VecZ2.system a b e * derivedJGen VecZ2.system e c d
          * VecZ2.system.F a b c d e f
        = derivedJGen VecZ2.system b c f * derivedJGen VecZ2.system a f d
          * VecZ2.system.F a b c d e f :=
  derivedJGen_coherent_of_pointed' VecZ2.system pointed_VecZ2

/-- **The fourth law on `Vec^ω_{Z/2}`** (non-trivial cocycle). -/
theorem derivedJGen_coherent_VecZ2Twisted :
    ∀ a b c d e f : Fin 2, 0 < VecZ2Twisted.system.ring.N a b e →
      0 < VecZ2Twisted.system.ring.N e c d → 0 < VecZ2Twisted.system.ring.N b c f →
      0 < VecZ2Twisted.system.ring.N a f d →
      derivedJGen VecZ2Twisted.system a b e * derivedJGen VecZ2Twisted.system e c d
          * VecZ2Twisted.system.F a b c d e f
        = derivedJGen VecZ2Twisted.system b c f * derivedJGen VecZ2Twisted.system a f d
          * VecZ2Twisted.system.F a b c d e f :=
  derivedJGen_coherent_of_pointed' VecZ2Twisted.system pointed_VecZ2Twisted

/-- **The fourth law on `Z2SqH.system`** (the `(Z/2)²` datum with `J ≡ 1`). -/
theorem derivedJGen_coherent_Z2SqH_system :
    ∀ a b c d e f : Fin 4, 0 < Z2SqH.system.ring.N a b e →
      0 < Z2SqH.system.ring.N e c d → 0 < Z2SqH.system.ring.N b c f →
      0 < Z2SqH.system.ring.N a f d →
      derivedJGen Z2SqH.system a b e * derivedJGen Z2SqH.system e c d
          * Z2SqH.system.F a b c d e f
        = derivedJGen Z2SqH.system b c f * derivedJGen Z2SqH.system a f d
          * Z2SqH.system.F a b c d e f :=
  derivedJGen_coherent_of_pointed' Z2SqH.system pointed_Z2SqH_system

/-- **The fourth law on `Z2SqH.systemH`** (the honest `δ(κ)` twist). -/
theorem derivedJGen_coherent_Z2SqH_systemH :
    ∀ a b c d e f : Fin 4, 0 < Z2SqH.systemH.ring.N a b e →
      0 < Z2SqH.systemH.ring.N e c d → 0 < Z2SqH.systemH.ring.N b c f →
      0 < Z2SqH.systemH.ring.N a f d →
      derivedJGen Z2SqH.systemH a b e * derivedJGen Z2SqH.systemH e c d
          * Z2SqH.systemH.F a b c d e f
        = derivedJGen Z2SqH.systemH b c f * derivedJGen Z2SqH.systemH a f d
          * Z2SqH.systemH.F a b c d e f :=
  derivedJGen_coherent_of_pointed' Z2SqH.systemH pointed_Z2SqH_systemH


/-! ## §6 — the associator-only form of the remaining obligation

`DoubleDualTensorator.derivedJGen_eq_omegaCoeff` identifies the derived twist with the
`F`/`Finv`-only table `omegaCoeff` on any channel where the two bracket products are
nonzero — the four `ev`-factors cancel by `ev_dual`.  Consequently the `F`-free fourth
law for `derivedJGen` follows from the *associator-only* cocycle identity
`Ω(a,b;e)·Ω(e,c;d) = Ω(b,c;f)·Ω(a,f;d)` for `omegaCoeff`.  That identity is sum-free and
mentions no evaluation data at all: it is the exact statement a matrix-level argument
(the associator as a block matrix, the pentagon `S.pentagon` at `(a,b,c,d)`, and the
inverse laws `Finv_comp`/`F_comp_inv`) has to prove, and it is where the present file
stops. -/

open FusionMat in
/-- The two nonvanishing hypotheses `FusionMat.derivedJGen_eq_omegaCoeff` needs at
`(a,b,c)`, bundled. -/
def OmegaNe (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) : Prop :=
  (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
      S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0) ∧
    (S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
      S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
        (S.ring.dual c) ⟨0, hn⟩ ≠ 0)

/-- **The derived twist equals `omegaCoeff` under `OmegaNe`.** -/
theorem derivedJGen_eq_omegaCoeff_of_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (h : OmegaNe S hn a b c) :
    derivedJGen S a b c = FusionMat.omegaCoeff S a b c :=
  FusionMat.derivedJGen_eq_omegaCoeff S hn a b c h.1 h.2

/-- **The `F`-free fourth law is the associator-only cocycle identity**: on every tuple
whose four `omegaCoeff` brackets are nonzero, the law for `derivedJGen` is *equivalent*
to the `F`/`Finv`-only equality `Ω(a,b;e)·Ω(e,c;d) = Ω(b,c;f)·Ω(a,f;d)`.  This locates
the remaining obligation exactly. -/
theorem derivedJGen_coherent_iff_omegaCoeff_cocycle (S : FusionSystem n k) (hn : 0 < n) :
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f →
      OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d
        = derivedJGen S b c f * derivedJGen S a f d) ↔
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f →
      OmegaNe S hn a f d →
      FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
        = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d) := by
  constructor
  · intro h a b c d e f h1 h2 h3 h4 hA hB hC hD
    rw [← derivedJGen_eq_omegaCoeff_of_omegaNe S hn hA,
      ← derivedJGen_eq_omegaCoeff_of_omegaNe S hn hB,
      ← derivedJGen_eq_omegaCoeff_of_omegaNe S hn hC,
      ← derivedJGen_eq_omegaCoeff_of_omegaNe S hn hD]
    exact h a b c d e f h1 h2 h3 h4 hA hB hC hD
  · intro h a b c d e f h1 h2 h3 h4 hA hB hC hD
    rw [derivedJGen_eq_omegaCoeff_of_omegaNe S hn hA,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn hB,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn hC,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn hD]
    exact h a b c d e f h1 h2 h3 h4 hA hB hC hD

/-! ## §7 — the class on which the law is discharged *unconditionally*

The fourth law holds for the derived twist whenever the derived twist is the coboundary
of a nowhere-vanishing function.  That class is not vacuous and is not pointedness: it
contains every pointed datum (§2), every datum whose derived twist is identically `1`
(§4) — in particular `FibonacciSystem`, `IsingSystem` and `YangLee.system` by the exact
computation quoted in the module header — and, more generally, every datum on which the
closed form is *checked* to be a coboundary (a pivotal-type function `g` with
`derivedJGen S a b c = g a * g b / g c` on the channels).  It is the largest class the
transfer argument reaches. -/

/-- **The fourth law for the derived twist, in class form.** -/
theorem derivedJGen_coherent_of_exists_coboundary (S : FusionSystem n k)
    (h : ∃ g : Fin n → k, (∀ i : Fin n, g i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = g a * g b / g c) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  obtain ⟨g, hg, hJ⟩ := h
  exact derivedJGen_coherent_of_coboundary S g hg hJ

end FusionCategory

/-! ## Axiom audit -/
#print axioms FusionCategory.OmegaNe
#print axioms FusionCategory.derivedJGen_eq_omegaCoeff_of_omegaNe
#print axioms FusionCategory.derivedJGen_coherent_iff_omegaCoeff_cocycle
#print axioms FusionCategory.derivedJGen_coherent_of_exists_coboundary

#print axioms FusionCategory.pointed_VecZ2
#print axioms FusionCategory.pointed_VecZ2Twisted
#print axioms FusionCategory.pointed_Z2SqH_system
#print axioms FusionCategory.pointed_Z2SqH_systemH
#print axioms FusionCategory.derivedJGen_coherent_VecZ2
#print axioms FusionCategory.derivedJGen_coherent_VecZ2Twisted
#print axioms FusionCategory.derivedJGen_coherent_Z2SqH_system
#print axioms FusionCategory.derivedJGen_coherent_Z2SqH_systemH

#print axioms FusionCategory.derivedJGen_coherent_of_one
#print axioms FusionCategory.pointed_of_ring_eq
#print axioms FusionCategory.derivedJGen_coherent_of_pointed'
#print axioms FusionCategory.exists_fusionSystem_derivedJGen
#print axioms FusionCategory.exists_fusionSystem_derivedJGen_of_pointed


#print axioms FusionCategory.coherent_of_qualified
#print axioms FusionCategory.derivedJGen_twistQualified_iff
#print axioms FusionCategory.twistQualified_systemJ_iff
#print axioms FusionCategory.coherent_free_of_coboundary
#print axioms FusionCategory.coherent_of_coboundary
#print axioms FusionCategory.derivedJGen_coherent_of_coboundary
#print axioms FusionCategory.derivedJGen_coherent_of_pointed
#print axioms FusionCategory.derivedJGen_qualified_of_pointed
#print axioms FusionCategory.derivedJGen_coherent_of_J_match
#print axioms FusionCategory.derivedJGen_qualified_of_J_match
