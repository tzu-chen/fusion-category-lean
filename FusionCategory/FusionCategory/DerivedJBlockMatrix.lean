/-
# WP3 round 2, member m4, direction d4 — the boundary-block engine for the fourth law

`DerivedJCoherent.derivedJGen_coherent_iff_omegaCoeff_cocycle` reduces the fourth law
(`J_coherent`) for the derived twist to the associator-only identity

    omegaCoeff S a b e * omegaCoeff S e c d = omegaCoeff S b c f * omegaCoeff S a f d

on the tuples where the four `OmegaNe` brackets are nonzero, with

    omegaCoeff S a b c = (F a b c* 0 c a* * Finv b b* a* a* c* 0)
                       / (F b* a* c 0 c* b * Finv a* a b b c 0).

This file is the block-matrix layer for that identity.  Everything it touches is
*boundary*: both `F`-entries have the composite slot `d = <0>` (the unit) and both
`Finv`-entries have the channel slot `e = <0>`.  A unit in a slot forces the neighbouring
labels (`dual_coeff`), so those blocks are `1 x 1` and the inverse-associator laws
`Finv_comp` / `F_comp_inv` collapse to a single product — for exactly the reason they
collapse on pointed data, and with no pointedness hypothesis.

## What is proved here (kernel-checked, axiom budget `[propext, Classical.choice, Quot.sound]`)

* §1 — the boundary block is `1 x 1`: in `F x y z* 0 e f` the unit composite forces
  `e = z` and `f = x*` (`boundary_F_fst`, `boundary_F_snd`), and the entry vanishes off
  that pair (`boundary_F_eq_zero_of_fst`, `boundary_F_eq_zero_of_snd`).
* §2 — the boundary reciprocal `boundary_Finv_mul_F`
  `Finv x y z* 0 x* z * F x y z* 0 z x* = 1` for every present channel `0 < N x y z`,
  with `boundary_F_mul_Finv`, `boundary_F_ne_zero`, `boundary_Finv_ne_zero`,
  `boundary_Finv_eq_inv`, `boundary_F_eq_inv`, and the off-channel zero converses
  `boundary_F_eq_zero`, `boundary_Finv_eq_zero`.
* §3 — the hypothesis reduction `omegaNe_iff_finv`: the two `F`-factors of `OmegaNe` are
  *never* zero on a present channel, so given `0 < N a b c`, `0 < N b* a* c*`,
  `OmegaNe a b c` is exactly the nonvanishing of the two `Finv`-entries
  `Finv a* a b b c 0` and `Finv b b* a* a* c* 0`.  `OmegaNe` contains no `F`-information.
* §3 — a new closed form of the coefficient, **with no `F` at all**
  (`omegaCoeff_eq_OmegaFinv`): `omegaCoeff a b c` equals
  `(Finv b b* a* a* c* 0 * Finv b* a* c 0 b c*) / (Finv a b c* 0 a* c * Finv a* a b b c 0)`.
  Two of the four factors are genuine inverse-matrix entries, the other two are the
  reciprocals of the `1 x 1` blocks of §2; the previous round's `Pi * Rho` split becomes
  `Q R' / (R Q')` with `Q(x,y;z) = Finv y y* x* x* z* 0`, `R(x,y;z) = Finv x y z* 0 x* z`.
* §4 — the cocycle identity in `Finv`-only form: `OmegaFinv`, `OmegaCocycle`,
  `OmegaCocycleFinv`, the equivalence `omegaCocycle_iff_finv`, the `derivedJGen`-level
  equivalence `derivedJGen_coherent_iff_OmegaFinv_cocycle`, and the assemblies
  `derivedJGen_coherent_of_finv_cocycle`, `derivedJGen_coherent_retained_of_finv_cocycle`.
* §6 — **the two closed forms agree with no nonvanishing hypothesis**:
  `derivedJGen_eq_omegaCoeff_uncond` and `derivedJGen_eq_OmegaFinv`.  The tree's
  `derivedJGen_eq_omegaCoeff` carries `OmegaNe` only because its proof cancels by
  `field_simp`; with total division the zero patterns already agree, so `OmegaNe` is a
  hypothesis on the *shape of the fourth law*, not on the identity of the two forms.
* §7 — the fourth law's `F`-free form on the tuples with a unit among `a`, `b`, `c`
  (`derivedJGen_cocycle_of_a_unit` / `_b_unit` / `_c_unit` / `_of_unit`), with no
  `OmegaNe` hypothesis at all.
* §8 — the cocycle identity multiplied out: `OmegaCocycleRetained` is a polynomial
  identity among `Finv` entries with **no division**, and `omegaCocycleFinv_of_retained`
  proves it implies the ratio form (the four denominators are nonzero exactly by §2 and
  `OmegaNe`).  This is the form a pentagon-based derivation has to produce.

* §9 — **where the frozen nonvanishing lives**: `derivedJGen_ne_zero_iff_omegaNe`
  `0 < N a b c → (derivedJGen a b c ≠ 0 ↔ OmegaNe a b c)`.  So `WP2.DerivedJ_ne_zero` is
  not a statement about the twist: it is the nonvanishing of the two inverse-associator
  entries `Finv b b* a* a* c* 0` and `Finv a* a b b c 0` (equivalently, that `ψ_{a,b}` is
  an isomorphism on channel `c`).
* §10 — **the full assembly**: `derivedJGen_coherent_retained_of_ne` (the `F`-retained
  fourth law over *all* `N`-tuples, with `OmegaNe` *derived* from the nonvanishing and
  `F ≠ 0`), and `exists_fusionSystem_derivedJGen_of_finv_cocycle` /
  `..._of_retained`: `Finv`-only cocycle identity + global nonvanishing ⟹ a
  `FusionSystem` on the same ring, `F`, `Finv`, `ev`, `coev` whose twist is `derivedJGen`.
  The two inputs are exactly the two open statements; nothing else is assumed.

A word of warning about the assembly, recorded because it is easy to miss: the `F`-free law
on the `OmegaNe` tuples does **not** by itself give the `F`-retained `J_coherent`.  If
`OmegaNe` fails at `(a,b,e)` while holding at `(b,c,f)` and `(a,f,d)`, then
`derivedJGen a b e = 0` (by §9) while the right-hand side need not vanish — so the retained
law needs the nonvanishing *globally*, which is why §10 carries it as a hypothesis.

## Numerical corroboration (not a proof)

`.ultramath/smw7f657l/m4/finvform.py`, exact `Q(sqrt 5)` / `Q(sqrt 2)` / rational
arithmetic, `F`/`Finv`/`N` transcribed from the tree's own tables, `x/0 = 0` matching
Lean's total division, on all seven data sets of the census (`VecZ2`, `VecZ2Twisted`,
`Z2SqH.system`, `Z2SqH.systemH`, `Fibonacci`, `Ising`, `YangLee`; 210 supported
6-tuples): the boundary reciprocal holds on every present channel with **0** failures,
the `Finv`-only closed form agrees with the `F`-form on all `3 n^3` triples with **0**
failures, and the `Finv`-form cocycle identity has **0** failures.

## What is NOT in this file

A proof of the cocycle identity.  §4/§8 pin it down (no `F`, no `ev`, no division, no
`OmegaNe` on the closed forms) and prove that each form suffices for the fourth law; the
derivation from `S.pentagon` is still owed.  Two structural facts recorded here so that a
next round does not repeat the search:

1. The cocycle identity cannot come from a *sum-free boundary pentagon*, and the
   `k`-sum of `S.pentagon` cannot be collapsed by a unit at generic labels.  The boundary
   entries of `Omega` are the ones whose composite slot is a unit, so ask for the outer
   composite `r = <0>`; then the factor `F e c d r x i` has support `N x d <0>`, which
   forces `d = x*` — the fourth factor must be the dual of the composite of the first
   three — and its other support condition `N e i <0>` forces `e = i*`.  Those two
   conditions alone do not collapse the sum over the channels `k` of `b ⊗ c` (the surviving
   `k` are those with `N a k x` and `N k d j`); on `Fibonacci` the pentagon at `(τ,τ,τ,·)`
   keeps both `k = 1` and `k = τ`, since the `(τ,τ,τ)` block is `2 x 2`.  Pushing further,
   if one also takes `d = c*` (so that `x` is the composite of `a ⊗ b ⊗ c`) the same
   support conditions force `e = x`, i.e. `c` to be a channel of `a ⊗ b`, and the instance
   degenerates.  So a pentagon whose `k`-sum collapses by a unit exists only on degenerate
   tuples; at generic labels the identity needs a matrix cancellation, not a scalar one.
2. Consequently the honest shape of the remaining step is: prove `OmegaCocycleRetained`
   (§8) — a polynomial identity in `Finv` entries — from `S.pentagon` inverted (the
   pentagon for the inverse associator) at four-factor tuples with a dual factor, and then
   apply `omegaCocycleFinv_of_retained`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJCoherent

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §0 — algebraic helpers for the `1 x 1` cancellations -/

/-- A non-zero `F`-entry forces all four channels to be present. -/
theorem quad_of_F_ne_zero (S : FusionSystem n k) {a b c d e f : Fin n}
    (h : S.F a b c d e f ≠ 0) :
    0 < S.ring.N a b e ∧ 0 < S.ring.N e c d ∧ 0 < S.ring.N b c f ∧ 0 < S.ring.N a f d := by
  by_contra hc
  exact h (S.F_support a b c d e f hc)

/-- Cross-multiplied ratio identity: if `R * A = 1` and `R' * A' = 1`, the two ways of
writing `A Q / (A' Q')` agree. -/
theorem div_ratio_of_mul_eq_one {A R A' R' Q Q' : k} (h1 : R * A = 1) (h2 : R' * A' = 1) :
    A * Q / (A' * Q') = Q * R' / (R * Q') := by
  have hA : A ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact one_ne_zero h1.symm
  have hR : R ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact one_ne_zero h1.symm
  have hA' : A' ≠ 0 := fun h => by rw [h, mul_zero] at h2; exact one_ne_zero h2.symm
  have hR' : R' ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact one_ne_zero h2.symm
  rcases eq_or_ne Q' 0 with hQ' | hQ'
  · rw [hQ', mul_zero, div_zero, mul_zero, div_zero]
  · rw [div_eq_div_iff (mul_ne_zero hA' hQ') (mul_ne_zero hR hQ')]
    calc A * Q * (R * Q') = (R * A) * (Q * Q') := by ring
      _ = Q * Q' := by rw [h1, one_mul]
      _ = (R' * A') * (Q * Q') := by rw [h2, one_mul]
      _ = Q * R' * (A' * Q') := by ring

/-- Ratio identity when both numerator-blocks vanish. -/
theorem div_ratio_of_zero {A R A' R' Q Q' : k} (h1 : A = 0) (h2 : R = 0) :
    A * Q / (A' * Q') = Q * R' / (R * Q') := by
  simp [h1, h2]

/-- Ratio identity when the denominator-block vanishes. -/
theorem div_ratio_of_zero' {A R A' R' Q Q' : k} (h1 : R * A = 1) (h2 : A' = 0)
    (h3 : R' = 0) : A * Q / (A' * Q') = Q * R' / (R * Q') := by
  simp [h2, h3]

/-! ## §1 — a unit composite forces both channels of the boundary block -/

/-- `0 < N x f 1` forces `f = x*` (`dual_coeff`). -/
theorem eq_dual_of_pos_unit (S : FusionSystem n k) (hn : 0 < n) {x f : Fin n}
    (h : 0 < S.ring.N x f ⟨0, hn⟩) : f = S.ring.dual x := by
  rw [S.ring.dual_coeff hn x] at h
  by_cases hd : f = S.ring.dual x
  · exact hd
  · rw [if_neg hd] at h
    exact absurd h (lt_irrefl 0)

/-- `0 < N e c 1` forces `e = c*` (`dual_coeff`). -/
theorem eq_dual_of_pos_unit' (S : FusionSystem n k) (hn : 0 < n) {e c : Fin n}
    (h : 0 < S.ring.N e c ⟨0, hn⟩) : e = S.ring.dual c := by
  rw [S.ring.dual_coeff hn e] at h
  by_cases hd : c = S.ring.dual e
  · rw [hd, FusionRing.dual_dual]
  · rw [if_neg hd] at h
    exact absurd h (lt_irrefl 0)

/-- **The `x ⊗ y`-channel of the boundary block**: the unit composite forces `e = z`. -/
theorem boundary_F_fst (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : S.F x y (S.ring.dual z) ⟨0, hn⟩ e f ≠ 0) : e = z := by
  have h2 : 0 < S.ring.N e (S.ring.dual z) ⟨0, hn⟩ := (quad_of_F_ne_zero S h).2.1
  have h3 : e = S.ring.dual (S.ring.dual z) := eq_dual_of_pos_unit' S hn h2
  rwa [FusionRing.dual_dual] at h3

/-- **The `y ⊗ z*`-channel of the boundary block**: the unit composite forces `f = x*`. -/
theorem boundary_F_snd (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : S.F x y (S.ring.dual z) ⟨0, hn⟩ e f ≠ 0) : f = S.ring.dual x :=
  eq_dual_of_pos_unit S hn (quad_of_F_ne_zero S h).2.2.2

/-- The boundary block vanishes off the `x ⊗ y`-channel `z`. -/
theorem boundary_F_eq_zero_of_fst (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : e ≠ z) : S.F x y (S.ring.dual z) ⟨0, hn⟩ e f = 0 := by
  refine S.F_support x y (S.ring.dual z) ⟨0, hn⟩ e f ?_
  intro hcon
  have h3 : e = S.ring.dual (S.ring.dual z) := eq_dual_of_pos_unit' S hn hcon.2.1
  rw [FusionRing.dual_dual] at h3
  exact h h3

/-- The boundary block vanishes off the `y ⊗ z*`-channel `x*`. -/
theorem boundary_F_eq_zero_of_snd (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : f ≠ S.ring.dual x) : S.F x y (S.ring.dual z) ⟨0, hn⟩ e f = 0 := by
  refine S.F_support x y (S.ring.dual z) ⟨0, hn⟩ e f ?_
  intro hcon
  exact h (eq_dual_of_pos_unit S hn hcon.2.2.2)

/-! ## §2 — the boundary block is `1 x 1`: `Finv` is the reciprocal of `F` -/

/-- **The boundary reciprocal.**  On the block of the triple `(x, y, z*)` with unit
composite the `b ⊗ c`-channel set is the singleton `{x*}` (`dual_coeff`), so the inverse
associator law `F_comp_inv` collapses to the single product `Finv * F = 1`. -/
theorem boundary_Finv_mul_F (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z *
      S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) = 1 := by
  have hzz : 0 < S.ring.N z (S.ring.dual z) ⟨0, hn⟩ := pos_dual_coeff S hn z
  have hcomp := S.F_comp_inv x y (S.ring.dual z) ⟨0, hn⟩ z z hN hzz hN hzz
  have hsum : (∑ f : Fin n,
        S.Finv x y (S.ring.dual z) ⟨0, hn⟩ f z *
          S.F x y (S.ring.dual z) ⟨0, hn⟩ z f)
      = S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z *
        S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) := by
    refine Finset.sum_eq_single (S.ring.dual x) ?_ ?_
    · intro f _ hf
      have hz : S.F x y (S.ring.dual z) ⟨0, hn⟩ z f = 0 := by
        refine S.F_support x y (S.ring.dual z) ⟨0, hn⟩ z f ?_
        intro hcon
        exact hf (eq_dual_of_pos_unit S hn hcon.2.2.2)
      rw [hz, mul_zero]
    · intro hf
      exact absurd (Finset.mem_univ _) hf
  rw [hsum] at hcomp
  simpa using hcomp

/-- The boundary reciprocal in the other order. -/
theorem boundary_F_mul_Finv (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
      S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z = 1 := by
  rw [mul_comm]
  exact boundary_Finv_mul_F S hn hN

/-- **Nonvanishing of the boundary `F`-entry** on every present channel. -/
theorem boundary_F_ne_zero (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) ≠ 0 := by
  intro h0
  have h := boundary_Finv_mul_F S hn hN
  rw [h0, mul_zero] at h
  exact one_ne_zero h.symm

/-- **Nonvanishing of the boundary `Finv`-entry** on every present channel. -/
theorem boundary_Finv_ne_zero (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z ≠ 0 := by
  intro h0
  have h := boundary_Finv_mul_F S hn hN
  rw [h0, zero_mul] at h
  exact one_ne_zero h.symm

/-- The boundary `Finv`-entry is the reciprocal of the boundary `F`-entry. -/
theorem boundary_Finv_eq_inv (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z =
      (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x))⁻¹ :=
  eq_inv_of_mul_eq_one_right (boundary_F_mul_Finv S hn hN)

/-- The boundary `F`-entry is the reciprocal of the boundary `Finv`-entry. -/
theorem boundary_F_eq_inv (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z) :
    S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) =
      (S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z)⁻¹ :=
  eq_inv_of_mul_eq_one_right (boundary_Finv_mul_F S hn hN)

/-- Off the present channels the boundary `F`-entry vanishes. -/
theorem boundary_F_eq_zero (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : ¬ 0 < S.ring.N x y z) :
    S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) = 0 := by
  refine S.F_support x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) ?_
  intro hcon
  exact hN hcon.1

/-- Off the present channels the boundary `Finv`-entry vanishes. -/
theorem boundary_Finv_eq_zero (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : ¬ 0 < S.ring.N x y z) :
    S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z = 0 := by
  refine S.Finv_support x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z ?_
  intro hcon
  exact hN hcon.2.2.1

/-! ## §3 — the `Finv`-only closed form of the tensorator coefficient -/

/-- **The tensorator coefficient with no `F` at all**:

    Ω(a,b;c) = (Finv b b* a* a* c* 0 * Finv b* a* c 0 b c*) / (Finv a b c* 0 a* c * Finv a* a b b c 0)

The two `F`-factors of `omegaCoeff`'s original form are the reciprocals of the `1 x 1`
boundary blocks `Finv a b c* 0 a* c` and `Finv b* a* c 0 b c*` (§2). -/
theorem omegaCoeff_eq_OmegaFinv (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    FusionMat.omegaCoeff S a b c =
      (S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩ *
          S.Finv (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ b (S.ring.dual c)) /
        (S.Finv a b (S.ring.dual c) ⟨0, hn⟩ (S.ring.dual a) c *
          S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩) := by
  rw [FusionMat.omegaCoeff, dif_pos hn]
  by_cases h1 : 0 < S.ring.N a b c
  · have h1' := boundary_Finv_mul_F S hn h1
    by_cases h2 : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c)
    · have h2' := boundary_Finv_mul_F S hn h2
      simp only [FusionRing.dual_dual] at h2'
      exact div_ratio_of_mul_eq_one h1' h2'
    · have hA' : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b = 0 := by
        have h := boundary_F_eq_zero S hn (x := S.ring.dual b) (y := S.ring.dual a)
          (z := S.ring.dual c) h2
        simpa only [FusionRing.dual_dual] using h
      have hR' : S.Finv (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ b (S.ring.dual c) = 0 := by
        have h := boundary_Finv_eq_zero S hn (x := S.ring.dual b) (y := S.ring.dual a)
          (z := S.ring.dual c) h2
        simpa only [FusionRing.dual_dual] using h
      exact div_ratio_of_zero' h1' hA' hR'
  · exact div_ratio_of_zero
      (boundary_F_eq_zero S hn h1) (boundary_Finv_eq_zero S hn h1)

/-- **`OmegaNe` is the nonvanishing of the two `Finv`-entries.**  The two `F`-factors of
the bundle are boundary entries and are nonzero on every present channel
(`boundary_F_ne_zero`), so the bundle carries no information about `F`. -/
theorem omegaNe_iff_finv (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (hab : 0 < S.ring.N a b c)
    (hba : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c)) :
    OmegaNe S hn a b c ↔
      (S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0 ∧
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩ ≠ 0) := by
  have hF1 : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b ≠ 0 := by
    have := boundary_F_ne_zero S hn (x := S.ring.dual b) (y := S.ring.dual a)
      (z := S.ring.dual c) hba
    simpa only [FusionRing.dual_dual] using this
  have hF2 : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) ≠ 0 :=
    boundary_F_ne_zero S hn hab
  constructor
  · intro h
    exact ⟨fun h0 => h.1 (by rw [h0, mul_zero]), fun h0 => h.2 (by rw [h0, mul_zero])⟩
  · intro ⟨h1, h2⟩
    exact ⟨mul_ne_zero hF1 h1, mul_ne_zero hF2 h2⟩

end FusionCategory

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §4 — the cocycle identity in `Finv`-only form, and the assembly -/

/-- **The tensorator coefficient written with inverse-matrix entries only.**  Same value as
`FusionMat.omegaCoeff` (`omegaCoeff_eq_OmegaFinv'`), but no `F`, no `ev`, no `coev`. -/
noncomputable def OmegaFinv (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) : k :=
  (S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z) ⟨0, hn⟩ *
      S.Finv (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ y (S.ring.dual z)) /
    (S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z *
      S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩)

/-- `omegaCoeff` *is* `OmegaFinv`. -/
theorem omegaCoeff_eq_OmegaFinv' (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    FusionMat.omegaCoeff S a b c = OmegaFinv S hn a b c :=
  omegaCoeff_eq_OmegaFinv S hn a b c

/-- `derivedJGen` *is* `OmegaFinv` on an `OmegaNe` tuple. -/
theorem derivedJGen_eq_OmegaFinv_of_omegaNe (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (h : OmegaNe S hn a b c) : derivedJGen S a b c = OmegaFinv S hn a b c := by
  rw [derivedJGen_eq_omegaCoeff_of_omegaNe S hn h, omegaCoeff_eq_OmegaFinv']

/-- **The remaining obligation of the fourth law**, in the shape
`derivedJGen_coherent_iff_omegaCoeff_cocycle` states it (an `F`-form identity). -/
def OmegaCocycle (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
    FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
      = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d

/-- **The same identity with `F` deleted** — every factor is an inverse-matrix entry. -/
def OmegaCocycleFinv (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
    OmegaFinv S hn a b e * OmegaFinv S hn e c d = OmegaFinv S hn b c f * OmegaFinv S hn a f d

/-- **The cocycle identity is the same identity with `F` deleted.** -/
theorem omegaCocycle_iff_finv (S : FusionSystem n k) (hn : 0 < n) :
    OmegaCocycle S hn ↔ OmegaCocycleFinv S hn := by
  constructor
  · intro h a b c d e f h1 h2 h3 h4 hA hB hC hD
    rw [← omegaCoeff_eq_OmegaFinv', ← omegaCoeff_eq_OmegaFinv',
      ← omegaCoeff_eq_OmegaFinv', ← omegaCoeff_eq_OmegaFinv']
    exact h a b c d e f h1 h2 h3 h4 hA hB hC hD
  · intro h a b c d e f h1 h2 h3 h4 hA hB hC hD
    rw [omegaCoeff_eq_OmegaFinv', omegaCoeff_eq_OmegaFinv',
      omegaCoeff_eq_OmegaFinv', omegaCoeff_eq_OmegaFinv']
    exact h a b c d e f h1 h2 h3 h4 hA hB hC hD

/-- **The fourth law for `derivedJGen` follows from the `Finv`-only cocycle identity.**
This is `derivedJGen_coherent_iff_omegaCoeff_cocycle` composed with
`omegaCocycle_iff_finv`: the remaining obligation is an identity among inverse-matrix
entries of the associator, and it implies the `F`-free fourth law. -/
theorem derivedJGen_coherent_of_finv_cocycle (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleFinv S hn) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d
        = derivedJGen S b c f * derivedJGen S a f d :=
  (derivedJGen_coherent_iff_omegaCoeff_cocycle S hn).mpr
    ((omegaCocycle_iff_finv S hn).mpr h)

/-- **The `F`-retained fourth law from the `Finv`-only cocycle identity** — the shape
`FusionSystem.J_coherent` has, with the twist computed rather than carried. -/
theorem derivedJGen_coherent_retained_of_finv_cocycle (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleFinv S hn) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4 hA hB hC hD
  rw [derivedJGen_coherent_of_finv_cocycle S hn h a b c d e f h1 h2 h3 h4 hA hB hC hD]

/-! ## §5 — audit -/

#print axioms FusionCategory.div_ratio_of_mul_eq_one
#print axioms FusionCategory.boundary_F_fst
#print axioms FusionCategory.boundary_F_snd
#print axioms FusionCategory.boundary_Finv_mul_F
#print axioms FusionCategory.boundary_F_mul_Finv
#print axioms FusionCategory.boundary_F_ne_zero
#print axioms FusionCategory.boundary_Finv_ne_zero
#print axioms FusionCategory.boundary_Finv_eq_inv
#print axioms FusionCategory.boundary_F_eq_inv
#print axioms FusionCategory.boundary_F_eq_zero
#print axioms FusionCategory.boundary_Finv_eq_zero
#print axioms FusionCategory.omegaCoeff_eq_OmegaFinv
#print axioms FusionCategory.omegaNe_iff_finv
#print axioms FusionCategory.omegaCoeff_eq_OmegaFinv'
#print axioms FusionCategory.derivedJGen_eq_OmegaFinv_of_omegaNe
#print axioms FusionCategory.omegaCocycle_iff_finv
#print axioms FusionCategory.derivedJGen_coherent_of_finv_cocycle
#print axioms FusionCategory.derivedJGen_coherent_retained_of_finv_cocycle

/-! ## §6 — the two closed forms agree unconditionally

`DoubleDualTensorator.derivedJGen_eq_omegaCoeff` carries the two nonvanishing hypotheses of
`OmegaNe` because its proof cancels by `field_simp`.  With the total-division convention of
a field the identity holds with the hypotheses removed: both zero patterns agree, because
`comparisonScalar` and `omegaCoeff` have the *same* numerator (up to the crossed `ev`
factors, which are nonzero) and the same denominator.  So `derivedJGen` is the associator
table `omegaCoeff` **everywhere**, and `OmegaNe` is not a hypothesis on the two forms'
agreement but only on the shape of the fourth law. -/

/-- If both `A` and `R` vanish together, the ratio is unchanged; the "total division"
bookkeeping that removes `field_simp`'s nonvanishing hypotheses. -/
theorem div_div_same {u D1 D2 : k} (hu : u ≠ 0) : u / D1 / (u / D2) = D2 / D1 := by
  by_cases h1 : D1 = 0
  · simp [h1]
  by_cases h2 : D2 = 0
  · simp [h2]
  · field_simp

/-- The crossed `ev`-factors cancel out of `omegaCoeff`'s ratio. -/
theorem cancel_ev {A Q A' Q' ea eb : k} (ha : ea ≠ 0) (hb : eb ≠ 0) :
    A * Q * eb * ea / (A' * Q' * ea * eb) = A * Q / (A' * Q') := by
  by_cases h : A' * Q' = 0
  · simp [h]
  · field_simp

/-- **The derived twist is the associator table `omegaCoeff`, with no nonvanishing
hypothesis.**  (`DoubleDualTensorator.derivedJGen_eq_omegaCoeff` needs `OmegaNe`; here the
only input is `ev ≠ 0`.) -/
theorem derivedJGen_eq_omegaCoeff_uncond (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    derivedJGen S a b c = FusionMat.omegaCoeff S a b c := by
  have h1 : comparisonScalar S a b c =
      S.ev c / (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ * S.ev a * S.ev b) := by
    rw [comparisonScalar_def, dif_pos hn]
  have h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) =
      S.ev c / (S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩ *
        S.ev b * S.ev a) := by
    rw [comparisonScalar_def, dif_pos hn]
    simp only [FusionRing.dual_dual, S.ev_dual]
  rw [derivedJGen_def, h1, h2, div_div_same (S.ev_ne_zero c), FusionMat.omegaCoeff, dif_pos hn]
  exact cancel_ev (S.ev_ne_zero a) (S.ev_ne_zero b)

/-- **`derivedJGen` is `OmegaFinv` everywhere** — the `Finv`-only closed form, with no
hypothesis at all. -/
theorem derivedJGen_eq_OmegaFinv (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    derivedJGen S a b c = OmegaFinv S hn a b c := by
  rw [derivedJGen_eq_omegaCoeff_uncond S hn, omegaCoeff_eq_OmegaFinv']

/-- `omegaCoeff` and `derivedJGen` therefore satisfy the same fourth-law statement with no
`OmegaNe` side condition on the agreement of the two forms. -/
theorem derivedJGen_coherent_iff_OmegaFinv_cocycle (S : FusionSystem n k) (hn : 0 < n) :
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d
        = derivedJGen S b c f * derivedJGen S a f d) ↔ OmegaCocycleFinv S hn := by
  rw [← omegaCocycle_iff_finv]
  exact derivedJGen_coherent_iff_omegaCoeff_cocycle S hn

#print axioms FusionCategory.div_div_same
#print axioms FusionCategory.cancel_ev
#print axioms FusionCategory.derivedJGen_eq_omegaCoeff_uncond
#print axioms FusionCategory.derivedJGen_eq_OmegaFinv
#print axioms FusionCategory.derivedJGen_coherent_iff_OmegaFinv_cocycle

/-! ## §7 — the identity on the tuples with a unit factor

The fourth law's `F`-free form on a tuple with `a = 1`, `b = 1` or `c = 1`.  These tuples
are *not* excluded by `OmegaNe` (e.g. `OmegaNe 1 b b` holds whenever `Finv b b* 1 1 b* 0` is
nonzero), so this is a real fragment of the identity — and it needs no `OmegaNe` at all,
because the three unit normalisations `derivedJGen_unit_left`, `derivedJGen_unit_right`
already kill the extra factor.  (The remaining degenerate cases `e = 1` and `f = 1` do
appear inside the `OmegaNe` statement — they reduce the identity to
`derivedJGen a* c f * derivedJGen a f c = 1` and its mirror — and are *not* covered here.) -/

/-- The fourth law's `F`-free form at `a = 1`. -/
theorem derivedJGen_cocycle_of_a_unit (S : FusionSystem n k) (hn : 0 < n) {b c d e f : Fin n}
    (h1 : 0 < S.ring.N ⟨0, hn⟩ b e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N ⟨0, hn⟩ f d) :
    derivedJGen S ⟨0, hn⟩ b e * derivedJGen S e c d
      = derivedJGen S b c f * derivedJGen S ⟨0, hn⟩ f d := by
  have he : e = b := unique_left_unit S hn b e h1
  have hf : d = f := unique_left_unit S hn f d h4
  rw [he, hf, derivedJGen_unit_left S hn b, derivedJGen_unit_left S hn f]
  ring

/-- The fourth law's `F`-free form at `b = 1`. -/
theorem derivedJGen_cocycle_of_b_unit (S : FusionSystem n k) (hn : 0 < n) {a c d e f : Fin n}
    (h1 : 0 < S.ring.N a ⟨0, hn⟩ e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N ⟨0, hn⟩ c f) (h4 : 0 < S.ring.N a f d) :
    derivedJGen S a ⟨0, hn⟩ e * derivedJGen S e c d
      = derivedJGen S ⟨0, hn⟩ c f * derivedJGen S a f d := by
  have he : e = a := unique_right_unit S hn a e h1
  have hf : f = c := unique_left_unit S hn c f h3
  rw [he, hf, derivedJGen_unit_right S hn a, derivedJGen_unit_left S hn c]

/-- The fourth law's `F`-free form at `c = 1`. -/
theorem derivedJGen_cocycle_of_c_unit (S : FusionSystem n k) (hn : 0 < n) {a b d e f : Fin n}
    (h1 : 0 < S.ring.N a b e) (h2 : 0 < S.ring.N e ⟨0, hn⟩ d)
    (h3 : 0 < S.ring.N b ⟨0, hn⟩ f) (h4 : 0 < S.ring.N a f d) :
    derivedJGen S a b e * derivedJGen S e ⟨0, hn⟩ d
      = derivedJGen S b ⟨0, hn⟩ f * derivedJGen S a f d := by
  have hd : d = e := unique_right_unit S hn e d h2
  have hf : f = b := unique_right_unit S hn b f h3
  rw [hd, hf, derivedJGen_unit_right S hn e, derivedJGen_unit_right S hn b]
  ring

/-- **The fourth law's `F`-free form on every tuple with a unit among `a`, `b`, `c`** —
no `OmegaNe` hypothesis. -/
theorem derivedJGen_cocycle_of_unit (S : FusionSystem n k) (hn : 0 < n) {a b c d e f : Fin n}
    (h1 : 0 < S.ring.N a b e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N a f d)
    (hu : a = ⟨0, hn⟩ ∨ b = ⟨0, hn⟩ ∨ c = ⟨0, hn⟩) :
    derivedJGen S a b e * derivedJGen S e c d
      = derivedJGen S b c f * derivedJGen S a f d := by
  rcases hu with h | h | h
  · subst h
    exact derivedJGen_cocycle_of_a_unit S hn h1 h2 h3 h4
  · subst h
    exact derivedJGen_cocycle_of_b_unit S hn h1 h2 h3 h4
  · subst h
    exact derivedJGen_cocycle_of_c_unit S hn h1 h2 h3 h4

#print axioms FusionCategory.derivedJGen_cocycle_of_a_unit
#print axioms FusionCategory.derivedJGen_cocycle_of_b_unit
#print axioms FusionCategory.derivedJGen_cocycle_of_c_unit
#print axioms FusionCategory.derivedJGen_cocycle_of_unit

/-! ## §8 — the division-free form of the cocycle identity

`OmegaFinv x y z` is a ratio `n / d`; the cocycle identity is therefore an identity of two
products of two ratios, and multiplying out gives a **polynomial identity in `Finv`-entries
alone**, with no division and hence no nonvanishing side condition:

    [Q(a,b;e)R(b*,a*;e*)][Q(e,c;d)R(c*,e*;d*)] d(b,c;f) d(a,f;d)
      = [R(a,b;e)Q(b*,a*;e*)][R(e,c;d)Q(c*,e*;d*)] n(b,c;f) n(a,f;d)

This is the form a pentagon-based derivation produces (the pentagon is an identity of
scalars, hence survives any product), and `omegaCocycleFinv_of_retained` proves that it
suffices: on the `OmegaNe` tuples the four denominators are nonzero
(`boundary_Finv_ne_zero` for the `R`-factor, `OmegaNe` for the `Q`-factor), so the ratio
form follows by `div_mul_div_eq_iff`. -/

/-- `Q(x,y;z) = Finv y y* x* x* z* 0`: the `(z*, 0)`-entry of the inverse associator block
of the triple `(y, y*, x*)` at composite `x*`. -/
noncomputable def omegaQ (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) : k :=
  S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z) ⟨0, hn⟩

/-- `R(x,y;z) = Finv x y z* 0 x* z`: the `1 x 1` boundary block of the triple `(x, y, z*)`
at unit composite. -/
noncomputable def omegaR (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) : k :=
  S.Finv x y (S.ring.dual z) ⟨0, hn⟩ (S.ring.dual x) z

/-- `OmegaFinv` as a ratio of the two block scalars. -/
theorem OmegaFinv_eq_Q_div (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) :
    OmegaFinv S hn x y z =
      omegaQ S hn x y z * omegaR S hn (S.ring.dual y) (S.ring.dual x) (S.ring.dual z) /
        (omegaR S hn x y z * omegaQ S hn (S.ring.dual y) (S.ring.dual x) (S.ring.dual z)) := by
  simp only [OmegaFinv, omegaQ, omegaR, FusionRing.dual_dual]

/-- Four ratios are equal iff the cross-multiplied products are (all denominators nonzero). -/
theorem div_mul_div_eq_iff {n1 n2 n3 n4 d1 d2 d3 d4 : k} (h1 : d1 ≠ 0) (h2 : d2 ≠ 0)
    (h3 : d3 ≠ 0) (h4 : d4 ≠ 0) :
    n1 / d1 * (n2 / d2) = n3 / d3 * (n4 / d4) ↔ n1 * n2 * (d3 * d4) = n3 * n4 * (d1 * d2) := by
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h3 h4)]

/-- **The cocycle identity multiplied out**: a polynomial identity among inverse-matrix
entries, with no division. -/
def OmegaCocycleRetained (S : FusionSystem n k) (hn : 0 < n) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
    (omegaQ S hn a b e * omegaR S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e)) *
      (omegaQ S hn e c d * omegaR S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)) *
      ((omegaR S hn b c f * omegaQ S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f)) *
        (omegaR S hn a f d * omegaQ S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)))
    = (omegaQ S hn b c f * omegaR S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f)) *
      (omegaQ S hn a f d * omegaR S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)) *
      ((omegaR S hn a b e * omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e)) *
        (omegaR S hn e c d * omegaQ S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)))

/-- **The division-free form implies the ratio form.** -/
theorem omegaCocycleFinv_of_retained (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleRetained S hn) : OmegaCocycleFinv S hn := by
  intro a b c d e f h1 h2 h3 h4 hA hB hC hD
  have hQ1 : omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hA.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ2 : omegaQ S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hB.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ3 : omegaQ S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hC.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ4 : omegaQ S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hD.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hd1 : omegaR S hn a b e * omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h1) hQ1
  have hd2 : omegaR S hn e c d * omegaQ S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h2) hQ2
  have hd3 : omegaR S hn b c f * omegaQ S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h3) hQ3
  have hd4 : omegaR S hn a f d * omegaQ S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h4) hQ4
  rw [OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div]
  exact (div_mul_div_eq_iff hd1 hd2 hd3 hd4).mpr (h a b c d e f h1 h2 h3 h4 hA hB hC hD)

/-- **The ratio form implies the division-free form.** -/
theorem omegaCocycleRetained_of_finv (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleFinv S hn) : OmegaCocycleRetained S hn := by
  intro a b c d e f h1 h2 h3 h4 hA hB hC hD
  have hQ1 : omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hA.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ2 : omegaQ S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hB.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ3 : omegaQ S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hC.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hQ4 : omegaQ S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d) ≠ 0 := by
    have h' := (mul_ne_zero_iff.mp hD.1).2
    simpa only [omegaQ, FusionRing.dual_dual] using h'
  have hd1 : omegaR S hn a b e * omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual e)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h1) hQ1
  have hd2 : omegaR S hn e c d * omegaQ S hn (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h2) hQ2
  have hd3 : omegaR S hn b c f * omegaQ S hn (S.ring.dual c) (S.ring.dual b) (S.ring.dual f)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h3) hQ3
  have hd4 : omegaR S hn a f d * omegaQ S hn (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)
      ≠ 0 := mul_ne_zero (boundary_Finv_ne_zero S hn h4) hQ4
  have hratio := h a b c d e f h1 h2 h3 h4 hA hB hC hD
  rw [OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div, OmegaFinv_eq_Q_div] at hratio
  exact (div_mul_div_eq_iff hd1 hd2 hd3 hd4).mp hratio

/-- **The three forms of the remaining obligation are one.**  The fourth law in
`omegaCoeff` form, in `Finv`-ratio form, and as a division-free polynomial identity among
inverse-matrix entries are all equivalent. -/
theorem omegaCocycle_iff_retained (S : FusionSystem n k) (hn : 0 < n) :
    OmegaCocycle S hn ↔ OmegaCocycleRetained S hn :=
  ⟨fun h => omegaCocycleRetained_of_finv S hn ((omegaCocycle_iff_finv S hn).mp h),
   fun h => (omegaCocycle_iff_finv S hn).mpr (omegaCocycleFinv_of_retained S hn h)⟩

/-- **The fourth law from the division-free cocycle identity.** -/
theorem derivedJGen_coherent_of_retained (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleRetained S hn) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d
        = derivedJGen S b c f * derivedJGen S a f d :=
  derivedJGen_coherent_of_finv_cocycle S hn (omegaCocycleFinv_of_retained S hn h)

#print axioms FusionCategory.OmegaFinv_eq_Q_div
#print axioms FusionCategory.div_mul_div_eq_iff
#print axioms FusionCategory.omegaCocycleRetained_of_finv
#print axioms FusionCategory.omegaCocycle_iff_retained
#print axioms FusionCategory.omegaCocycleFinv_of_retained
#print axioms FusionCategory.derivedJGen_coherent_of_retained

/-! ## §9 — where the frozen nonvanishing `WP2.DerivedJ_ne_zero` actually lives

`derivedJGen = OmegaFinv` (§6) and `OmegaFinv = Q R' / (R Q')` (§8).  On a present channel
the two `R`-factors are nonzero by §2, and `N b* a* c* = N a b c` (`dual_symm`), so
`derivedJGen a b c ≠ 0` is **exactly** `OmegaNe a b c` — the nonvanishing of the two
genuine inverse-matrix entries `Finv b b* a* a* c* 0` and `Finv a* a b b c 0`.  So the
frozen `WP2.DerivedJ_ne_zero` is not a statement about the twist at all: it is the
statement that two entries of the inverse associator are nonzero, i.e. (for an honest
datum) that the comparison map `ψ_{a,b}` is an isomorphism on the channel `c`. -/

/-- `N a b c = N b* a* c*` (`dual_symm`). -/
theorem N_dual_swap (S : FusionSystem n k) {a b c : Fin n} (h : 0 < S.ring.N a b c) :
    0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) := by
  rw [← S.ring.dual_symm a b c]
  exact h

/-- `a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0` — the total-division bookkeeping. -/
theorem div_ne_zero_iff' {a b : k} : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun h0 => h (by rw [h0, zero_div]), fun h0 => h (by rw [h0, div_zero])⟩
  · rintro ⟨ha, hb⟩
    exact div_ne_zero ha hb

/-- **The nonvanishing of the derived twist is `OmegaNe`.**  This is the exact locus of the
frozen `WP2.DerivedJ_ne_zero`: given `0 < N a b c` and `0 < n`,
`derivedJGen a b c ≠ 0 ↔ OmegaNe a b c`. -/
theorem derivedJGen_ne_zero_iff_omegaNe (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (hN : 0 < S.ring.N a b c) :
    derivedJGen S a b c ≠ 0 ↔ OmegaNe S hn a b c := by
  have hN' : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    N_dual_swap S hN
  have hR : omegaR S hn a b c ≠ 0 := boundary_Finv_ne_zero S hn hN
  have hR' : omegaR S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0 := by
    have h := boundary_Finv_ne_zero S hn hN'
    simpa only [omegaR, FusionRing.dual_dual] using h
  rw [derivedJGen_eq_OmegaFinv, OmegaFinv_eq_Q_div, div_ne_zero_iff',
    omegaNe_iff_finv S hn hN hN']
  constructor
  · rintro ⟨hn1, hd1⟩
    refine ⟨?_, ?_⟩
    · have h := (mul_ne_zero_iff.mp hd1).2
      simpa only [omegaQ, FusionRing.dual_dual] using h
    · have h := (mul_ne_zero_iff.mp hn1).1
      simpa only [omegaQ, FusionRing.dual_dual] using h
  · rintro ⟨h1, h2⟩
    have hQ' : omegaQ S hn (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0 := by
      simpa only [omegaQ, FusionRing.dual_dual] using h1
    have hQ : omegaQ S hn a b c ≠ 0 := by
      simpa only [omegaQ] using h2
    exact ⟨mul_ne_zero hQ hR', mul_ne_zero hR hQ'⟩

#print axioms FusionCategory.N_dual_swap
#print axioms FusionCategory.div_ne_zero_iff'
#print axioms FusionCategory.derivedJGen_ne_zero_iff_omegaNe

/-! ## §10 — the full assembly, with the two open inputs explicit

`DerivedJCoherent.exists_fusionSystem_derivedJGen` consumes exactly two inputs: the global
nonvanishing of `derivedJGen` on the channels (the frozen `WP2.DerivedJ_ne_zero`) and the
`F`-retained fourth law over *all* `N`-tuples.  §9 identifies the nonvanishing with
`OmegaNe`, so the `OmegaNe` hypotheses of `derivedJGen_coherent_of_finv_cocycle` become
automatic wherever `F` is nonzero — and where `F` vanishes the retained law is trivial.
Hence: **`Finv`-only cocycle identity + global nonvanishing ⟹ the fixpoint datum**. -/

/-- **The `F`-retained fourth law from the `Finv`-only cocycle identity and the global
nonvanishing** — no `OmegaNe` side condition left, because it is derived. -/
theorem derivedJGen_coherent_retained_of_ne (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleFinv S hn)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  by_cases hF : S.F a b c d e f = 0
  · rw [hF, mul_zero, mul_zero]
  · have hA : OmegaNe S hn a b e :=
      (derivedJGen_ne_zero_iff_omegaNe S hn h1).mp (hne a b e h1)
    have hB : OmegaNe S hn e c d :=
      (derivedJGen_ne_zero_iff_omegaNe S hn h2).mp (hne e c d h2)
    have hC : OmegaNe S hn b c f :=
      (derivedJGen_ne_zero_iff_omegaNe S hn h3).mp (hne b c f h3)
    have hD : OmegaNe S hn a f d :=
      (derivedJGen_ne_zero_iff_omegaNe S hn h4).mp (hne a f d h4)
    rw [derivedJGen_coherent_of_finv_cocycle S hn h a b c d e f h1 h2 h3 h4 hA hB hC hD]

/-- **The fixpoint datum from the `Finv`-only cocycle identity and the global
nonvanishing**: there is a `FusionSystem` on the same ring, associator, inverse associator
and duality data whose twist is `derivedJGen S`.  The two inputs are exactly the two open
statements (`OmegaCocycleFinv` and `WP2.DerivedJ_ne_zero`); nothing else is assumed. -/
theorem exists_fusionSystem_derivedJGen_of_finv_cocycle (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleFinv S hn)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  exists_fusionSystem_derivedJGen S hne (derivedJGen_coherent_retained_of_ne S hn h hne)

/-- Same, from the division-free form of the cocycle identity (§8). -/
theorem exists_fusionSystem_derivedJGen_of_retained (S : FusionSystem n k) (hn : 0 < n)
    (h : OmegaCocycleRetained S hn)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  exists_fusionSystem_derivedJGen_of_finv_cocycle S hn
    (omegaCocycleFinv_of_retained S hn h) hne

#print axioms FusionCategory.derivedJGen_coherent_retained_of_ne
#print axioms FusionCategory.exists_fusionSystem_derivedJGen_of_finv_cocycle
#print axioms FusionCategory.exists_fusionSystem_derivedJGen_of_retained

/-! ## Audit (continued) — the declarations not covered above -/

#print axioms FusionCategory.quad_of_F_ne_zero
#print axioms FusionCategory.div_ratio_of_zero
#print axioms FusionCategory.div_ratio_of_zero'
#print axioms FusionCategory.eq_dual_of_pos_unit
#print axioms FusionCategory.eq_dual_of_pos_unit'
#print axioms FusionCategory.boundary_F_eq_zero_of_fst
#print axioms FusionCategory.boundary_F_eq_zero_of_snd
#print axioms FusionCategory.OmegaFinv
#print axioms FusionCategory.OmegaCocycle
#print axioms FusionCategory.OmegaCocycleFinv
#print axioms FusionCategory.OmegaCocycleRetained
#print axioms FusionCategory.omegaQ
#print axioms FusionCategory.omegaR
