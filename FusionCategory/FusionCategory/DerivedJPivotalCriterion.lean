/-
# The pivotal criterion, the degenerate escape, and how strong the funnel really is

This file settles three questions about the swarm's target

    ∃ φ : Fin n → k, (∀ i, φ i ≠ 0) ∧ ∀ a b c, 0 < S.ring.N a b c →
        derivedJGen S a b c = φ a * φ b / φ c            ("pivotal witness")

on a legal `FusionSystem` (all fields, no hypotheses about the datum):

## §1 — `derivedJGen` depends only on `(ring, F, Finv)`

`derivedJGen = ψ/ψ̌` and both comparison scalars carry the *same* `ev`-factors
(`ev_dual`), so the ratio is `ev`-free:

    derivedJGen S a b c = singleDualPair S b* a* c* / singleDualPair S a b c.

Consequence (`derivedJGen_congr`): two data with the same `ring`, `F` and `Finv` have
the same `derivedJGen`, whatever their `ev`/`coev`.  The pivotal question is therefore
a property of the **associator data alone**.

## §2 — the degenerate escape: a vanishing boundary entry refutes the target outright

`pairScalar S a b c = 0` on a *supported* channel gives `derivedJGen S a b c = 0` by
the total division of a field (`x / 0 = 0`), while `φ a * φ b / φ c ≠ 0` for every
nowhere-vanishing `φ`.  Hence

    (∃ a b c, 0 < N a b c ∧ pairScalar S a b c = 0) → ¬ (∃ φ, pivotal witness).

This costs **nothing else**: no `PivotalFactor`, no coboundary class, no cocycle
argument.  `pairScalar = singleDualPair * ev a * ev b` and `ev ≠ 0`, so the hypothesis
is exactly `F(b*,a*,c,1,c*,b) · Finv(a*,a,b,b,c,1) = 0` on a supported channel — the
search should look for a datum with one *zero boundary entry*.  In the complementary
case the target's witness is *equivalent* to `PivotalFactor`.

## §3 — the pivotal factors form a torsor over the ring characters

If `φ` and `ψ` are both pivotal then `ψ c / φ c = (ψ a / φ a)(ψ b / φ b)` on channels
(`pivotalFactor_ratio`, division-free): the quotient is a character of the fusion ring.
Conversely twisting by a character preserves `PivotalFactor`.

## §4 — the funnel is exactly twice as strong as the fourth law

With `A = Ψ(a,b;e)Ψ(e,c;d)`, `B = Ψ(b,c;f)Ψ(a,f;d)` and `A'`, `B'` the same at the
dual twin tuple (`Ψ := singleDualPair`), the coherence at the tuple is `A·F(T*) = B·F(T)`
and the fourth law is `B'/A = A'/B`; with `λ`, `λ'` the two coherence defects this is
`λ·λ' = 1` (`law_iff_defect_reciprocal`).  So `SingleDualCoherent` (`λ = 1`, `λ' = 1`)
is strictly more than the law, which is blind to the common value of the defects.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJFunctor
import FusionCategory.DerivedJMate
import FusionCategory.DerivedJLaws

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — `derivedJGen` is `ev`-free: it depends only on `(ring, F, Finv)` -/

/-- `pairScalar` is `singleDualPair` times the two `ev`-factors, by definition. -/
theorem pairScalar_eq_singleDualPair_mul (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) :
    pairScalar S x y z = singleDualPair S x y z * (S.ev x * S.ev y) := by
  rw [pairScalar_self S hn, singleDualPair, dif_pos hn]

/-- Nonvanishing of the pairing is nonvanishing of the `ev`-free part (`ev ≠ 0`). -/
theorem singleDualPair_ne_zero_iff_pairScalar (S : FusionSystem n k) (hn : 0 < n)
    (x y z : Fin n) :
    singleDualPair S x y z ≠ 0 ↔ pairScalar S x y z ≠ 0 := by
  rw [pairScalar_eq_singleDualPair_mul S hn]
  constructor
  · intro h h0
    exact h ((mul_eq_zero.mp h0).resolve_right (mul_ne_zero (S.ev_ne_zero x) (S.ev_ne_zero y)))
  · intro h h0
    exact h (by rw [h0, zero_mul])

/-- **The `ev`-free form of the derived twist.** -/
theorem derivedJGen_eq_singleDualPair_div (S : FusionSystem n k) (a b c : Fin n) :
    derivedJGen S a b c =
      singleDualPair S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) /
        singleDualPair S a b c := by
  have hn : 0 < n := a.pos
  rw [derivedJGen_eq_pairDual_div, pairDual,
    pairScalar_eq_singleDualPair_mul S hn, pairScalar_eq_singleDualPair_mul S hn]
  simp only [S.ev_dual]
  rw [mul_comm (S.ev b) (S.ev a)]
  exact mul_div_mul_right _ _ (mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b))

/-- **The pivotal question is a property of the associator data alone.** -/
theorem derivedJGen_congr {S S' : FusionSystem n k} (hring : S'.ring = S.ring)
    (hF : S'.F = S.F) (hFinv : S'.Finv = S.Finv) (a b c : Fin n) :
    derivedJGen S' a b c = derivedJGen S a b c := by
  rw [derivedJGen_eq_singleDualPair_div S' a b c, derivedJGen_eq_singleDualPair_div S a b c]
  simp only [singleDualPair, hring, hF, hFinv]

/-! ## §2 — the degenerate escape -/

/-- **The cheapest refutation of all**: a supported channel on which the *derived twist
itself* vanishes already kills every pivotal witness, since `φ a * φ b / φ c ≠ 0`.  This
is the sharp form; the pairing and the `ev`-free versions below are the two ways it is
reached from the datum's entries (`WP2.DerivedJ_ne_zero` is exactly the obligation that
it never happens). -/
theorem not_exists_pivotalWitness_of_derivedJGen_eq_zero (S : FusionSystem n k)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) (h0 : derivedJGen S a b c = 0) :
    ¬ ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c := by
  rintro ⟨φ, hφ, hJ⟩
  rw [hJ a b c hN] at h0
  exact div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c) h0

/-- **A vanishing pairing on a supported channel refutes the target outright.** -/
theorem not_exists_pivotalWitness_of_pairScalar_eq_zero (S : FusionSystem n k)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) (h0 : pairScalar S a b c = 0) :
    ¬ ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c := by
  rintro ⟨φ, hφ, hJ⟩
  have h1 : derivedJGen S a b c = 0 := by
    rw [derivedJGen_eq_pairDual_div, h0, div_zero]
  rw [hJ a b c hN] at h1
  exact div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c) h1

/-- The same refutation in the `ev`-free entries the search works with. -/
theorem not_exists_pivotalWitness_of_singleDualPair_eq_zero (S : FusionSystem n k)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) (h0 : singleDualPair S a b c = 0) :
    ¬ ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c := by
  refine not_exists_pivotalWitness_of_pairScalar_eq_zero S hN ?_
  rw [pairScalar_eq_singleDualPair_mul S a.pos, h0, zero_mul]

/-- **In the non-degenerate case the target's witness is exactly `PivotalFactor`.** -/
theorem pivotalWitness_iff_pivotalFactor (S : FusionSystem n k)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    (∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
        ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c)
      ↔ ∃ φ : Fin n → k, PivotalFactor S φ := by
  constructor
  · rintro ⟨φ, hφ, hJ⟩
    exact ⟨φ, pivotalFactor_of_coboundary S hφ hne hJ⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, hφ.1, derivedJGen_eq_coboundary_of_pivotalFactor S hφ hne⟩

/-- **The dichotomy the target's question splits into.** -/
theorem pivotal_dichotomy (S : FusionSystem n k) :
    (∃ a b c : Fin n, 0 < S.ring.N a b c ∧ pairScalar S a b c = 0) ∨
      (∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) := by
  by_cases h : ∃ a b c : Fin n, 0 < S.ring.N a b c ∧ pairScalar S a b c = 0
  · exact Or.inl h
  · exact Or.inr fun a b c hN => by
      by_contra h0
      exact h ⟨a, b, c, hN, h0⟩

/-! ## §3 — the pivotal factors form a torsor over the ring characters -/

/-- A nowhere-vanishing multiplicative function on the fusion ring. -/
def RingCharacter (S : FusionSystem n k) (χ : Fin n → k) : Prop :=
  (∀ i : Fin n, χ i ≠ 0) ∧ ∀ a b c : Fin n, 0 < S.ring.N a b c → χ c = χ a * χ b

theorem ringCharacter_one (S : FusionSystem n k) :
    RingCharacter S (fun _ => (1 : k)) := by
  refine ⟨fun _ => one_ne_zero, fun a b c _ => by rw [mul_one]⟩

/-- **Twisting a pivotal factor by a ring character gives a pivotal factor.** -/
theorem pivotalFactor_mul_ringCharacter (S : FusionSystem n k) {φ χ : Fin n → k}
    (h : PivotalFactor S φ) (hχ : RingCharacter S χ) :
    PivotalFactor S (fun i => φ i * χ i) := by
  obtain ⟨hφ, hfac⟩ := h
  obtain ⟨hχ0, hχm⟩ := hχ
  refine ⟨fun i => mul_ne_zero (hφ i) (hχ0 i), ?_⟩
  intro a b c hN
  show pairDual S a b c * (φ c * χ c)
    = pairScalar S a b c * ((φ a * χ a) * (φ b * χ b))
  rw [← mul_assoc, hfac a b c hN, hχm a b c hN]
  ring

/-- **The ratio of two pivotal factors is multiplicative** (division-free form). -/
theorem pivotalFactor_ratio (S : FusionSystem n k) {φ ψ : Fin n → k}
    (hφ : PivotalFactor S φ) (hψ : PivotalFactor S ψ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    ∀ a b c : Fin n, 0 < S.ring.N a b c → ψ c * (φ a * φ b) = φ c * (ψ a * ψ b) := by
  intro a b c hN
  have hP := hne a b c hN
  have e1 := hφ.2 a b c hN
  have e2 := hψ.2 a b c hN
  have h1 : pairScalar S a b c * (ψ c * (φ a * φ b))
      = pairScalar S a b c * (φ c * (ψ a * ψ b)) := by
    linear_combination (-(ψ c)) * e1 + (φ c) * e2
  exact mul_left_cancel₀ hP h1

/-- **`ψ/φ` is a ring character** for two pivotal factors. -/
theorem ringCharacter_ratio_of_pivotalFactor (S : FusionSystem n k) {φ ψ : Fin n → k}
    (hφ : PivotalFactor S φ) (hψ : PivotalFactor S ψ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    RingCharacter S (fun i => ψ i / φ i) := by
  refine ⟨fun i => div_ne_zero (hψ.1 i) (hφ.1 i), ?_⟩
  intro a b c hN
  have h := pivotalFactor_ratio S hφ hψ hne a b c hN
  have ha : φ a ≠ 0 := hφ.1 a
  have hb : φ b ≠ 0 := hφ.1 b
  have hc : φ c ≠ 0 := hφ.1 c
  show ψ c / φ c = ψ a / φ a * (ψ b / φ b)
  rw [div_mul_div_comm, div_eq_div_iff hc (mul_ne_zero ha hb)]
  linear_combination h

/-! ## §4 — the single-dual coherence defect, and what the fourth law measures -/

/-- **The single-dual coherence defect of a tuple.** -/
noncomputable def cohDefect (S : FusionSystem n k) (a b c d e f : Fin n) : k :=
  singleDualPair S a b e * singleDualPair S e c d *
      S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a)
        (S.ring.dual d) (S.ring.dual f) (S.ring.dual e) /
    (singleDualPair S b c f * singleDualPair S a f d * S.F a b c d e f)

/-- **The field lemma**: the single-dual defects `A·F2/(B·F1)` and `A'·F1/(B'·F2)`
multiply to `1` exactly when the two ratios `B'/A` and `A'/B` agree — the fourth law. -/
theorem defect_reciprocal_iff_ratio_eq {A A' B B' F1 F2 : k}
    (hA : A ≠ 0) (hB : B ≠ 0) (hB' : B' ≠ 0) (hF1 : F1 ≠ 0) (hF2 : F2 ≠ 0) :
    (A * F2 / (B * F1)) * (A' * F1 / (B' * F2)) = 1 ↔ B' / A = A' / B := by
  have hBF1 : B * F1 ≠ 0 := mul_ne_zero hB hF1
  have hBF2 : B' * F2 ≠ 0 := mul_ne_zero hB' hF2
  have hBB : B * B' ≠ 0 := mul_ne_zero hB hB'
  have h1 : (A * F2 / (B * F1)) * (A' * F1 / (B' * F2)) = (A * A') / (B * B') := by
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hBF1 hBF2) hBB]
    ring
  rw [h1, div_eq_iff hBB, div_eq_div_iff hA hB]
  constructor <;> intro h <;> linear_combination (-1) * h

/-- **The fourth law is the reciprocity of the two single-dual coherence defects.** -/
theorem law_iff_defect_reciprocal (S : FusionSystem n k)
    (hP : ∀ x y z : Fin n, 0 < S.ring.N x y z → singleDualPair S x y z ≠ 0)
    (a b c d e f : Fin n)
    (h1 : 0 < S.ring.N a b e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N a f d)
    (hF : S.F a b c d e f ≠ 0)
    (hFd : S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a)
      (S.ring.dual d) (S.ring.dual f) (S.ring.dual e) ≠ 0) :
    (derivedJGen S a b e * derivedJGen S e c d = derivedJGen S b c f * derivedJGen S a f d)
      ↔ cohDefect S a b c d e f *
          cohDefect S (S.ring.dual c) (S.ring.dual b) (S.ring.dual a)
            (S.ring.dual d) (S.ring.dual f) (S.ring.dual e) = 1 := by
  have hA : singleDualPair S a b e * singleDualPair S e c d ≠ 0 :=
    mul_ne_zero (hP a b e h1) (hP e c d h2)
  have hB : singleDualPair S b c f * singleDualPair S a f d ≠ 0 :=
    mul_ne_zero (hP b c f h3) (hP a f d h4)
  have hd1 : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) :=
    N_dual_symm S h1
  have hd2 : 0 < S.ring.N (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) :=
    N_dual_symm S h2
  have hB' : singleDualPair S (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) *
      singleDualPair S (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) ≠ 0 :=
    mul_ne_zero (hP _ _ _ hd1) (hP _ _ _ hd2)
  have hlaw : (derivedJGen S a b e * derivedJGen S e c d
      = derivedJGen S b c f * derivedJGen S a f d)
      ↔ (singleDualPair S (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) *
            singleDualPair S (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)) /
          (singleDualPair S a b e * singleDualPair S e c d) =
        (singleDualPair S (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) *
            singleDualPair S (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)) /
          (singleDualPair S b c f * singleDualPair S a f d) := by
    rw [derivedJGen_eq_singleDualPair_div, derivedJGen_eq_singleDualPair_div,
      derivedJGen_eq_singleDualPair_div, derivedJGen_eq_singleDualPair_div,
      div_mul_div_comm, div_mul_div_comm]
  rw [hlaw, cohDefect, cohDefect]
  simp only [FusionRing.dual_dual]
  exact (defect_reciprocal_iff_ratio_eq hA hB hB' hF hFd).symm

/-! ## §3b — the pivotal factor is normalised: `φ 1 = 1` and `φ (x*) = 1/φ x`

`derivedJGen` satisfies the unit and duality normalisations (`derivedJGen_unit_left`,
`derivedJGen_dual`, `DerivedJLaws`), so the pivotal system pins the witness at the unit
and inverts it on duals.  A pivotal factor is therefore a function on the dual-orbit set
modulo the character group — the smallest form a refutation has to rule out. -/

/-- **`φ 1 = 1`**: the pivotal factor is normalised at the unit object. -/
theorem pivotalFactor_unit (S : FusionSystem n k) {φ : Fin n → k}
    (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) : φ ⟨0, hn⟩ = 1 := by
  have hsup : 0 < S.ring.N ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [S.ring.left_unit hn]
    simp
  have hP : pairScalar S ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ≠ 0 := hne _ _ _ hsup
  have hJ : derivedJGen S ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ = 1 := derivedJGen_unit_left S hn ⟨0, hn⟩
  rw [derivedJGen_eq_pairDual_div, div_eq_one_iff_eq hP] at hJ
  have hfac := h.2 ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ hsup
  rw [hJ] at hfac
  have h1 : φ ⟨0, hn⟩ = φ ⟨0, hn⟩ * φ ⟨0, hn⟩ := mul_left_cancel₀ hP hfac
  have h2 : (1 : k) = φ ⟨0, hn⟩ := by
    have h3 : φ ⟨0, hn⟩ * 1 = φ ⟨0, hn⟩ * φ ⟨0, hn⟩ := by
      rw [mul_one]
      exact h1
    exact mul_left_cancel₀ (h.1 ⟨0, hn⟩) h3
  exact h2.symm

/-- **`φ x · φ (x*) = φ 1`**: the pivotal factor inverts on duals. -/
theorem pivotalFactor_mul_dual (S : FusionSystem n k) {φ : Fin n → k}
    (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) (x : Fin n) :
    φ x * φ (S.ring.dual x) = φ ⟨0, hn⟩ := by
  have hsup : 0 < S.ring.N x (S.ring.dual x) ⟨0, hn⟩ := by
    rw [S.ring.dual_coeff hn x (S.ring.dual x)]
    simp
  have hP : pairScalar S x (S.ring.dual x) ⟨0, hn⟩ ≠ 0 := hne _ _ _ hsup
  have hfac := h.2 x (S.ring.dual x) ⟨0, hn⟩ hsup
  rw [pairDual_dual_right S hn x] at hfac
  exact mul_left_cancel₀ hP hfac.symm

/-- The two normalisations together: `φ x · φ (x*) = 1` and `φ 1 = 1`. -/
theorem pivotalFactor_mul_dual_eq_one (S : FusionSystem n k) {φ : Fin n → k}
    (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) (x : Fin n) :
    φ x * φ (S.ring.dual x) = 1 := by
  rw [pivotalFactor_mul_dual S h hne hn x, pivotalFactor_unit S h hne hn]

/-! ## §3c — self-dual data: the pivotal factor is a sign system

`φ x · φ (x*) = φ 1 = 1` (`§3b`).  On a **self-dual** datum (`dual = id`, which is every
datum in the tree) this reads `φ x · φ x = 1`, i.e. `φ x = ±1`: the pivotal factor is a
*sign system*, exactly the classical Frobenius–Schur picture.  Three consequences,
all useful for the search:

* (necessary condition) the derived twist must take values in `{0, ±1}` on supported
  channels — over `ℚ` or `ℝ` a single channel with `derivedJGen = 2` refutes the target;
* the target's witness is a *sign* function, so the pivotal system becomes **linear over
  `ℤ/2`** (`log σ a + log σ b - log σ c = log J`), decidable by linear algebra instead of
  a search over `(k^*)^n`;
* `pivotalWitness_selfDual_iff_sign` records the reduction exactly. -/

/-- In a field, `x * x = 1` forces `x = ±1`. -/
theorem eq_one_or_neg_one_of_mul_self_eq_one {x : k} (h : x * x = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · left
    linear_combination h1
  · right
    linear_combination h1

/-- A quotient of three signs is a sign. -/
theorem sign_div {x y z : k} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) :
    x * y / z = 1 ∨ x * y / z = -1 := by
  rcases eq_one_or_neg_one_of_mul_self_eq_one hx with rfl | rfl <;>
    rcases eq_one_or_neg_one_of_mul_self_eq_one hy with rfl | rfl <;>
      rcases eq_one_or_neg_one_of_mul_self_eq_one hz with rfl | rfl <;> norm_num

/-- **On a self-dual datum the pivotal factor is a sign system**: `φ x * φ x = 1`. -/
theorem pivotalFactor_sq_eq_one_of_selfDual (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i) {φ : Fin n → k}
    (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) (x : Fin n) : φ x * φ x = 1 := by
  have h1 := pivotalFactor_mul_dual_eq_one S h hne hn x
  rwa [hdual x] at h1

/-- The same for a nowhere-vanishing witness of the target's coboundary condition. -/
theorem pivotalWitness_sq_eq_one_of_selfDual (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) {φ : Fin n → k} (hφ : ∀ i : Fin n, φ i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c) :
    ∀ x : Fin n, φ x * φ x = 1 :=
  fun x => pivotalFactor_sq_eq_one_of_selfDual S hdual
    (pivotalFactor_of_coboundary S hφ hne hJ) hne hn x

/-- **The necessary condition for the search**: on a self-dual datum every supported
channel of a pivotal datum has `derivedJGen ∈ {1, -1}`.  So one channel with any other
value (over `ℚ`: `2`, `1/2`, `3`, …; over `𝔽_p`: any `p > 3` residue) refutes the target
without any further analysis. -/
theorem derivedJGen_pm_one_of_selfDual_pivotalFactor (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i) {φ : Fin n → k}
    (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    derivedJGen S a b c = 1 ∨ derivedJGen S a b c = -1 := by
  rw [derivedJGen_eq_coboundary_of_pivotalFactor S h hne a b c hN]
  exact sign_div (pivotalFactor_sq_eq_one_of_selfDual S hdual h hne hn a)
    (pivotalFactor_sq_eq_one_of_selfDual S hdual h hne hn b)
    (pivotalFactor_sq_eq_one_of_selfDual S hdual h hne hn c)

/-- **The refutation criterion for self-dual data**: a supported channel whose derived
twist is neither `1` nor `-1` kills every pivotal witness. -/
theorem not_exists_pivotalWitness_of_selfDual_twist_ne_pm_one (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) {a b c : Fin n} (hN : 0 < S.ring.N a b c)
    (h1 : derivedJGen S a b c ≠ 1) (h2 : derivedJGen S a b c ≠ -1) :
    ¬ ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c := by
  rintro ⟨φ, hφ, hJ⟩
  rcases derivedJGen_pm_one_of_selfDual_pivotalFactor S hdual
    (pivotalFactor_of_coboundary S hφ hne hJ) hne hn hN with h | h
  · exact h1 h
  · exact h2 h

/-- **The reduction**: on a self-dual datum the target's witness can be taken to be a
sign system, and every sign system satisfying the channel equations is one.  Hence the
pivotal question is the solubility of a `ℤ/2`-linear system. -/
theorem pivotalWitness_selfDual_iff_sign (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hn : 0 < n) :
    (∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
        ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c)
      ↔ ∃ σ : Fin n → k, (∀ i : Fin n, σ i * σ i = 1) ∧
        ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = σ a * σ b / σ c := by
  constructor
  · rintro ⟨φ, hφ, hJ⟩
    exact ⟨φ, pivotalWitness_sq_eq_one_of_selfDual S hdual hne hn hφ hJ, hJ⟩
  · rintro ⟨σ, hσ, hJ⟩
    refine ⟨σ, fun i => ?_, hJ⟩
    intro h0
    have h1 : σ i * σ i = 1 := hσ i
    rw [h0] at h1
    exact zero_ne_one (show (0 : k) = 1 by simpa using h1)

/-- **The complete, hypothesis-free reduction for self-dual data**: the target's witness
exists iff the *sign system* `σ x * σ x = 1` solving the channel equations does.  The
forward direction needs no nonvanishing hypothesis: a witness already forces
`pairScalar ≠ 0` on support (otherwise the twist would vanish where `φ a φ b / φ c`
does not), which is exactly what `§3b` needs.  So on a self-dual datum the swarm's target
is a `ℤ/2`-linear solubility problem and nothing else. -/
theorem pivotalWitness_selfDual_iff_sign' (S : FusionSystem n k)
    (hdual : ∀ i : Fin n, S.ring.dual i = i) (hn : 0 < n) :
    (∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
        ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c)
      ↔ ∃ σ : Fin n → k, (∀ i : Fin n, σ i * σ i = 1) ∧
        ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = σ a * σ b / σ c := by
  constructor
  · rintro ⟨φ, hφ, hJ⟩
    have hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0 := by
      intro a b c hN h0
      have h1 : derivedJGen S a b c = 0 := by
        rw [derivedJGen_eq_pairDual_div, h0, div_zero]
      rw [hJ a b c hN] at h1
      exact div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c) h1
    exact ⟨φ, pivotalWitness_sq_eq_one_of_selfDual S hdual hne hn hφ hJ, hJ⟩
  · rintro ⟨σ, hσ, hJ⟩
    refine ⟨σ, fun i => ?_, hJ⟩
    intro h0
    have h1 : σ i * σ i = 1 := hσ i
    rw [h0] at h1
    exact zero_ne_one (show (0 : k) = 1 by simpa using h1)

/-! ## §4b — the law is strictly weaker than the coherence, as field algebra

`law_iff_defect_reciprocal` says the fourth law *is* `λ·λ' = 1`.  This is not an
artefact of the formalisation: the field elements below satisfy the law (and the
defect-reciprocity form) with all the nonvanishing hypotheses, while the coherence
defect at the tuple is `2 ≠ 1`.  So no algebraic manipulation of the law yields
`SingleDualCoherent`; the gap is real, and only the pentagon/snake structure of the
datum can close it. -/

/-- **The law with a nontrivial defect**: a kernel-checked separation of the fourth law
from the single-dual coherence at the level of field algebra. -/
theorem exists_law_with_nontrivial_defect :
    ∃ A A' B B' F1 F2 : ℚ,
      A ≠ 0 ∧ B ≠ 0 ∧ A' ≠ 0 ∧ B' ≠ 0 ∧ F1 ≠ 0 ∧ F2 ≠ 0 ∧
        B' / A = A' / B ∧
        (A * F2 / (B * F1)) * (A' * F1 / (B' * F2)) = 1 ∧
        A * F2 / (B * F1) ≠ 1 :=
  ⟨2, 1, 1, 2, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end FusionCategory

/-! ## §5 — axiom audit -/

#print axioms FusionCategory.pairScalar_eq_singleDualPair_mul
#print axioms FusionCategory.singleDualPair_ne_zero_iff_pairScalar
#print axioms FusionCategory.derivedJGen_eq_singleDualPair_div
#print axioms FusionCategory.derivedJGen_congr
#print axioms FusionCategory.not_exists_pivotalWitness_of_derivedJGen_eq_zero
#print axioms FusionCategory.not_exists_pivotalWitness_of_pairScalar_eq_zero
#print axioms FusionCategory.not_exists_pivotalWitness_of_singleDualPair_eq_zero
#print axioms FusionCategory.pivotalWitness_iff_pivotalFactor
#print axioms FusionCategory.pivotal_dichotomy
#print axioms FusionCategory.RingCharacter
#print axioms FusionCategory.ringCharacter_one
#print axioms FusionCategory.pivotalFactor_mul_ringCharacter
#print axioms FusionCategory.pivotalFactor_ratio
#print axioms FusionCategory.ringCharacter_ratio_of_pivotalFactor
#print axioms FusionCategory.cohDefect
#print axioms FusionCategory.defect_reciprocal_iff_ratio_eq
#print axioms FusionCategory.law_iff_defect_reciprocal
#print axioms FusionCategory.eq_one_or_neg_one_of_mul_self_eq_one
#print axioms FusionCategory.sign_div
#print axioms FusionCategory.pivotalFactor_sq_eq_one_of_selfDual
#print axioms FusionCategory.pivotalWitness_sq_eq_one_of_selfDual
#print axioms FusionCategory.derivedJGen_pm_one_of_selfDual_pivotalFactor
#print axioms FusionCategory.not_exists_pivotalWitness_of_selfDual_twist_ne_pm_one
#print axioms FusionCategory.pivotalWitness_selfDual_iff_sign
#print axioms FusionCategory.pivotalWitness_selfDual_iff_sign'
#print axioms FusionCategory.pivotalFactor_unit
#print axioms FusionCategory.pivotalFactor_mul_dual
#print axioms FusionCategory.pivotalFactor_mul_dual_eq_one
#print axioms FusionCategory.exists_law_with_nontrivial_defect
