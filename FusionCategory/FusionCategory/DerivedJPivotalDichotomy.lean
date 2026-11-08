import FusionCategory.DerivedJMate
import FusionCategory.DerivedJBlockMatrix
import FusionCategory.DerivedJPointed

/-!
# The exact shape of the target: the twist is a coboundary iff it vanishes nowhere and is pivotal

The swarm's target asks for a legal `FusionSystem n k` with

  `¬ ∃ φ, (∀ i, φ i ≠ 0) ∧ ∀ a b c, 0 < N a b c → derivedJGen a b c = φ a * φ b / φ c`.

This file fixes the exact logical shape of that statement, with no nonvanishing
hypothesis anywhere in the statements.

* `TwistCoboundary S` is the target's shape; `TwistNowhereZero S hn` says the computed
  twist is nonzero on every supported channel.

* **`twistCoboundary_iff`** (the main theorem): the target's shape holds **iff** the
  computed twist vanishes nowhere *and* the mate pairing has a pivotal factor:
  `TwistCoboundary S ↔ (∀ supported (a,b,c), OmegaNe S hn a b c) ∧ ∃ φ, PivotalFactor S φ`.
  So the two hypotheses that the earlier rounds carried separately — the frozen
  nonvanishing law `WP2.DerivedJ_ne_zero` (as `OmegaNe`) and the pivotal-factor
  obligation (`PivotalFactor`) — are not two side conditions: they are exactly the two
  halves of the target. Nothing else is left.

* **`not_twistCoboundary_iff`** (the dichotomy): a refutation has exactly **two shapes**,
  and they are disjoint (`twistVanishes_not_nowhereZero`):
  1. *degenerate*: the computed twist vanishes on some supported channel
     (`∃ a b c, 0 < N a b c ∧ derivedJGen a b c = 0`). By
     `pairScalar_ne_zero_of_twistCoboundary` this is necessarily a vanishing
     `pairScalar`, i.e. a genuine degeneracy of the boundary `Finv`-entry, not an artifact
     of total division and not a choice of gauge.
  2. *non-pivotal*: the twist vanishes nowhere but the mate pairing has **no** pivotal
     factor — a nowhere-vanishing non-coboundary, the literature's non-pivotal case.
  Shape 1 is *not* non-pivotality in that sense at all, and the two shapes never overlap.

* `pairScalar_ne_zero_of_twistCoboundary`, `pivotalFactor_of_twistCoboundary`,
  `twistCoboundary_of_pivotalFactor` are the transports, and
  `exists_derivedJGen_zero_iff_not_omegaNe` identifies shape 1 with a failure of the
  frozen nonvanishing law.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the two objects: the target's shape and nowhere-vanishing -/

/-- **The target's shape.**  The computed double-dual twist is the coboundary `δ(φ)` of a
nowhere-zero `φ` on every supported channel. -/
def TwistCoboundary (S : FusionSystem n k) : Prop :=
  ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
    ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c

/-- The computed twist vanishes nowhere on the supported channels. -/
def TwistNowhereZero (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c ≠ 0

/-- **Shape 1 of a refutation**: the computed twist vanishes on a supported channel. -/
def TwistVanishes (S : FusionSystem n k) : Prop :=
  ∃ a b c : Fin n, 0 < S.ring.N a b c ∧ derivedJGen S a b c = 0

/-! ## §2 — a coboundary of a nowhere-zero `φ` vanishes nowhere

This is the one structural fact that separates the two refutation shapes: a coboundary
description cannot hold at a channel where the twist vanishes, so the vanishing locus of
the twist is a *gauge-invariant obstruction* to the target's shape, independent of `φ`,
of any associator algebra, and of any nonvanishing hypothesis. -/

/-- **The target's shape vanishes nowhere.** -/
theorem twistNowhereZero_of_twistCoboundary (S : FusionSystem n k) (hn : 0 < n)
    (h : TwistCoboundary S) : TwistNowhereZero S hn := by
  obtain ⟨φ, hφ, hbc⟩ := h
  intro a b c hN
  rw [hbc a b c hN]
  exact div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c)

/-- **The target's shape forces the mate pairing to be nonvanishing**, with no extra
hypothesis: at a supported channel `derivedJGen = pairDual / pairScalar`, so a coboundary
description (`≠ 0`) forces `pairScalar ≠ 0` there.  Hence shape 1 of the dichotomy is
*always* a genuine degeneracy of the pairing, never an artifact of the total-division
convention. -/
theorem pairScalar_ne_zero_of_twistCoboundary (S : FusionSystem n k)
    (h : TwistCoboundary S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    pairScalar S a b c ≠ 0 := by
  obtain ⟨φ, hφ, hbc⟩ := h
  intro hP
  have h0 : derivedJGen S a b c = 0 := by
    rw [derivedJGen_eq_pairDual_div, hP, div_zero]
  have hne : φ a * φ b / φ c ≠ 0 :=
    div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c)
  have h := hbc a b c hN
  rw [h0] at h
  exact hne h.symm

/-- In particular the target's shape is nowhere zero on the supported channels. -/
theorem derivedJGen_ne_zero_of_twistCoboundary (S : FusionSystem n k)
    (h : TwistCoboundary S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    derivedJGen S a b c ≠ 0 :=
  twistNowhereZero_of_twistCoboundary S a.pos h a b c hN

/-! ## §3 — the two transports between the target's shape and `PivotalFactor` -/

/-- **A coboundary description of the twist is a pivotal factor**, with the
`pairScalar ≠ 0` side condition *derived*, not assumed. -/
theorem pivotalFactor_of_twistCoboundary (S : FusionSystem n k) (h : TwistCoboundary S) :
    ∃ φ : Fin n → k, PivotalFactor S φ := by
  obtain ⟨φ, hφ, hbc⟩ := h
  refine ⟨φ, pivotalFactor_of_coboundary S hφ ?_ hbc⟩
  intro a b c hN
  exact pairScalar_ne_zero_of_twistCoboundary S ⟨φ, hφ, hbc⟩ hN

/-- **A pivotal factor gives the target's shape**, the nonvanishing side coming from
`OmegaNe` through `pairScalar_ne_zero`. -/
theorem twistCoboundary_of_pivotalFactor (S : FusionSystem n k) (hn : 0 < n)
    (hΩ : ∀ a b c : Fin n, 0 < S.ring.N a b c → OmegaNe S hn a b c)
    {φ : Fin n → k} (h : PivotalFactor S φ) : TwistCoboundary S :=
  ⟨φ, h.1, derivedJGen_eq_coboundary_of_pivotalFactor S h
    (fun a b c hN => pairScalar_ne_zero S hn a b c (hΩ a b c hN).1)⟩

/-! ## §4 — the main theorem: the target's shape *is* `OmegaNe` plus `PivotalFactor` -/

/-- **The target's shape splits into exactly two independent halves.**

`TwistCoboundary S ↔ (∀ supported (a,b,c), OmegaNe S hn a b c) ∧ ∃ φ, PivotalFactor S φ`.

`OmegaNe` is a statement about the boundary associator block being invertible in a
specific entry (`DerivedJBlockMatrix.omegaNe_iff_finv`), `PivotalFactor` is a statement
about the class of the swap-dual ratio of that same pairing.  Together they are the
target — no third condition, and no nonvanishing hypothesis on `pairScalar` beyond
`OmegaNe`. -/
theorem twistCoboundary_iff (S : FusionSystem n k) (hn : 0 < n) :
    TwistCoboundary S ↔
      (∀ a b c : Fin n, 0 < S.ring.N a b c → OmegaNe S hn a b c) ∧
        ∃ φ : Fin n → k, PivotalFactor S φ := by
  constructor
  · intro h
    refine ⟨?_, pivotalFactor_of_twistCoboundary S h⟩
    intro a b c hN
    exact (derivedJGen_ne_zero_iff_omegaNe S hn hN).mp
      (derivedJGen_ne_zero_of_twistCoboundary S h hN)
  · rintro ⟨hΩ, φ, hφ⟩
    exact twistCoboundary_of_pivotalFactor S hn hΩ hφ

/-- The `TwistNowhereZero` form of the criterion. -/
theorem twistCoboundary_iff_nowhereZero (S : FusionSystem n k) (hn : 0 < n) :
    TwistCoboundary S ↔ TwistNowhereZero S hn ∧ ∃ φ : Fin n → k, PivotalFactor S φ := by
  rw [twistCoboundary_iff S hn]
  constructor
  · rintro ⟨hΩ, hφ⟩
    refine ⟨?_, hφ⟩
    intro a b c hN
    exact (derivedJGen_ne_zero_iff_omegaNe S hn hN).mpr (hΩ a b c hN)
  · rintro ⟨hZ, hφ⟩
    refine ⟨?_, hφ⟩
    intro a b c hN
    exact (derivedJGen_ne_zero_iff_omegaNe S hn hN).mp (hZ a b c hN)

/-- Shape 1 is exactly a failure of the frozen nonvanishing law `WP2.DerivedJ_ne_zero`
at a supported channel. -/
theorem exists_derivedJGen_zero_iff_not_omegaNe (S : FusionSystem n k) (hn : 0 < n) :
    TwistVanishes S ↔ ∃ a b c : Fin n, 0 < S.ring.N a b c ∧ ¬ OmegaNe S hn a b c := by
  constructor
  · rintro ⟨a, b, c, hN, h0⟩
    refine ⟨a, b, c, hN, ?_⟩
    intro hΩ
    exact (derivedJGen_ne_zero_iff_omegaNe S hn hN).mpr hΩ h0
  · rintro ⟨a, b, c, hN, hΩ⟩
    refine ⟨a, b, c, hN, ?_⟩
    by_contra hne
    exact hΩ ((derivedJGen_ne_zero_iff_omegaNe S hn hN).mp hne)

/-! ## §5 — the dichotomy: a refutation has exactly two disjoint shapes -/

/-- **A refutation has exactly two shapes.**  Either the computed twist vanishes on some
supported channel — the *degenerate* shape, which by
`pairScalar_ne_zero_of_twistCoboundary` is a genuine degeneration of the mate pairing and
therefore not non-pivotality in the literature's sense — or it vanishes nowhere and the
pairing has no pivotal factor, the *non-pivotal* shape. -/
theorem not_twistCoboundary_iff (S : FusionSystem n k) (hn : 0 < n) :
    ¬ TwistCoboundary S ↔
      TwistVanishes S ∨ (TwistNowhereZero S hn ∧ ¬ ∃ φ : Fin n → k, PivotalFactor S φ) := by
  rw [twistCoboundary_iff_nowhereZero S hn]
  constructor
  · intro h
    by_cases hZ : TwistNowhereZero S hn
    · refine Or.inr ⟨hZ, ?_⟩
      rintro ⟨φ, hφ⟩
      exact h ⟨hZ, ⟨φ, hφ⟩⟩
    · refine Or.inl ?_
      by_contra hV
      exact hZ (fun a b c hN h0 => hV ⟨a, b, c, hN, h0⟩)
  · rintro (⟨a, b, c, hN, h0⟩ | ⟨hZ, hnf⟩)
    · rintro ⟨hZ', _⟩
      exact hZ' a b c hN h0
    · exact fun h => hnf h.2

/-- The degenerate and non-pivotal shapes are disjoint. -/
theorem twistVanishes_not_nowhereZero (S : FusionSystem n k) (hn : 0 < n) :
    ¬ (TwistVanishes S ∧ TwistNowhereZero S hn) := by
  rintro ⟨⟨a, b, c, hN, h0⟩, hZ⟩
  exact hZ a b c hN h0

/-! ## §6 — where shape 1 actually lives: two explicit inverse-associator entries

`DerivedJBlockMatrix.omegaNe_iff_finv` reduces `OmegaNe` to the nonvanishing of the two
`Finv`-entries `Finv a* a b b c 1` and `Finv b b* a* a* c* 1`.  Composing with §5 turns
the degenerate refutation shape into a **finite, entry-level condition**: shape 1 fires
iff one of those two entries of an inverse associator block vanishes.  So the whole
degenerate question about `FusionSystem n k` is the question whether a multiplicity-free
associator block can be singular in those two positions — nothing about `ev`, `coev`, `J`
or gauge enters. -/

/-- **Shape 1 is the vanishing of one of two inverse-associator entries.** -/
theorem twistVanishes_iff_boundaryFinv_zero (S : FusionSystem n k) (hn : 0 < n) :
    TwistVanishes S ↔
      ∃ a b c : Fin n, 0 < S.ring.N a b c ∧
        (S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ = 0 ∨
          S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
            (S.ring.dual c) ⟨0, hn⟩ = 0) := by
  rw [exists_derivedJGen_zero_iff_not_omegaNe S hn]
  constructor
  · rintro ⟨a, b, c, hN, hΩ⟩
    refine ⟨a, b, c, hN, ?_⟩
    have hiff := omegaNe_iff_finv S hn hN (N_dual_swap S hN)
    by_contra hcon
    exact hΩ (hiff.mpr ⟨fun h1 => hcon (Or.inl h1), fun h2 => hcon (Or.inr h2)⟩)
  · rintro ⟨a, b, c, hN, h1 | h2⟩
    · refine ⟨a, b, c, hN, ?_⟩
      have hiff := omegaNe_iff_finv S hn hN (N_dual_swap S hN)
      exact fun hΩ => (hiff.mp hΩ).1 h1
    · refine ⟨a, b, c, hN, ?_⟩
      have hiff := omegaNe_iff_finv S hn hN (N_dual_swap S hN)
      exact fun hΩ => (hiff.mp hΩ).2 h2

/-! ## §7 — shape 1 needs a *multi-column* inverse block

The other half of the localisation: when the column set of the block `F^{y y* x*}_{x*}` is
a single element (`e = 1`), the inverse entry `omegaQ x y z` is a genuine reciprocal and
shape 1 cannot fire.  So the degenerate refutation shape is not available on any datum
whose blocks are small, and in particular not on pointed data. -/

/-- **The inverse boundary entry is nonzero when the block has a unique column.**  The
matrix-inverse law `Finv_comp` at the block `F^{y y* x*}_{x*}` is a sum whose every
`e ≠ 1` term vanishes by `Finv_support` under the uniqueness hypothesis, so the `e = 1`
term alone equals `1`. -/
theorem omegaQ_ne_zero_of_unique_col (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (h2 : 0 < S.ring.N (S.ring.dual y) (S.ring.dual x) (S.ring.dual z))
    (h3 : 0 < S.ring.N y (S.ring.dual z) (S.ring.dual x))
    (hcol : ∀ e : Fin n, 0 < S.ring.N y (S.ring.dual y) e →
      0 < S.ring.N e (S.ring.dual x) (S.ring.dual x) → e = ⟨0, hn⟩) :
    omegaQ S hn x y z ≠ 0 := by
  have hkey : (∑ e : Fin n,
      S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z) e *
        S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) e (S.ring.dual z)) = 1 := by
    simpa using S.Finv_comp y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
      (S.ring.dual z) (S.ring.dual z) h2 h3 h2 h3
  have hsingle : (∑ e : Fin n,
      S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z) e *
        S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) e (S.ring.dual z))
      = S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z) ⟨0, hn⟩ *
        S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z) := by
    refine Finset.sum_eq_single (⟨0, hn⟩ : Fin n) ?_ ?_
    · intro e _ hne
      have hz : S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
          (S.ring.dual z) e = 0 := by
        refine S.Finv_support y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
          (S.ring.dual z) e ?_
        rintro ⟨-, -, hA, hB⟩
        exact hne (hcol e hA hB)
      rw [hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  intro h0
  simp only [omegaQ] at h0
  rw [hsingle] at hkey
  rw [h0, zero_mul] at hkey
  exact zero_ne_one hkey

/-! ## §8 — pointed data cannot take the degenerate route

On pointed data the block `F^{y y* x*}_{x*}` has a single column: `y ⊗ y*` is a single
simple (`WP2.Pointed` uniqueness) and the unit is in it (`pointed_unit_mem`, from
`dual_coeff`).  So both `omegaQ` entries are reciprocals and shape 1 is empty — the target
reduces to the pivotal-factor obligation with no nonvanishing hypothesis at all. -/

/-- On pointed data the unit is a channel of `y ⊗ y*`. -/
theorem pointed_unit_mem (S : FusionSystem n k) (hn : 0 < n) (y : Fin n) :
    0 < S.ring.N y (S.ring.dual y) ⟨0, hn⟩ := by
  have h := S.ring.dual_coeff hn y (S.ring.dual y)
  rw [h]
  simp

/-- **The inverse boundary entry is nonzero on pointed data.** -/
theorem omegaQ_ne_zero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {x y z : Fin n}
    (h2 : 0 < S.ring.N (S.ring.dual y) (S.ring.dual x) (S.ring.dual z))
    (h3 : 0 < S.ring.N y (S.ring.dual z) (S.ring.dual x)) :
    omegaQ S hn x y z ≠ 0 := by
  refine omegaQ_ne_zero_of_unique_col S hn h2 h3 ?_
  intro e hA _
  exact pointed_unique S hP hA (pointed_unit_mem S hn y)

/-- **`OmegaNe` holds on pointed data**: the `F`-factors are boundary entries and the
`Finv`-factors are the nonzero `omegaQ` entries. -/
theorem omegaNe_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    OmegaNe S hn a b c := by
  have hba : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    N_dual_swap S hN
  have hbca : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) :=
    N_dual_shift S hn hP hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b :=
    N_dual_shift' S hn hP hbca
  have hF1 : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b ≠ 0 := by
    have h := boundary_F_ne_zero S hn hba
    simpa only [FusionRing.dual_dual] using h
  have hF2 : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) ≠ 0 :=
    boundary_F_ne_zero S hn hN
  have hQ1 : omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0 := by
    refine omegaQ_ne_zero_of_pointed S hn hP ?_ ?_
    · simpa only [FusionRing.dual_dual] using hN
    · simpa only [FusionRing.dual_dual] using hacb
  have hQ2 : omegaQ S hn a b c ≠ 0 :=
    omegaQ_ne_zero_of_pointed S hn hP hba hbca
  unfold OmegaNe
  exact ⟨mul_ne_zero hF1 (by simpa only [omegaQ, FusionRing.dual_dual] using hQ1),
    mul_ne_zero hF2 (by simpa only [omegaQ] using hQ2)⟩

/-- **On pointed data the target's shape is exactly the pivotal-factor obligation**, with
no nonvanishing hypothesis of any kind: shape 1 is empty there. -/
theorem twistCoboundary_iff_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) :
    TwistCoboundary S ↔ ∃ φ : Fin n → k, PivotalFactor S φ :=
  ⟨fun h => pivotalFactor_of_twistCoboundary S h, by
    rintro ⟨φ, hφ⟩
    exact twistCoboundary_of_pivotalFactor S hn
      (fun a b c hN => omegaNe_of_pointed S hn hP hN) hφ⟩

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.TwistCoboundary
#print axioms FusionCategory.TwistNowhereZero
#print axioms FusionCategory.TwistVanishes
#print axioms FusionCategory.twistNowhereZero_of_twistCoboundary
#print axioms FusionCategory.pairScalar_ne_zero_of_twistCoboundary
#print axioms FusionCategory.derivedJGen_ne_zero_of_twistCoboundary
#print axioms FusionCategory.pivotalFactor_of_twistCoboundary
#print axioms FusionCategory.twistCoboundary_of_pivotalFactor
#print axioms FusionCategory.twistCoboundary_iff
#print axioms FusionCategory.twistCoboundary_iff_nowhereZero
#print axioms FusionCategory.exists_derivedJGen_zero_iff_not_omegaNe
#print axioms FusionCategory.not_twistCoboundary_iff
#print axioms FusionCategory.twistVanishes_not_nowhereZero
#print axioms FusionCategory.twistVanishes_iff_boundaryFinv_zero
#print axioms FusionCategory.omegaQ_ne_zero_of_unique_col
#print axioms FusionCategory.pointed_unit_mem
#print axioms FusionCategory.omegaQ_ne_zero_of_pointed
#print axioms FusionCategory.omegaNe_of_pointed
#print axioms FusionCategory.twistCoboundary_iff_of_pointed
