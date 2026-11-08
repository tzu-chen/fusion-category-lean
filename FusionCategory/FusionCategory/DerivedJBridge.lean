/-
# WP3 — the bridges: from `J_match` to (M), to the settled twist, and to ENO 8.23

`DerivedJScalar.lean` computes the twist (`comparisonScalar`, `derivedJGen`),
`DerivedJLaws.lean` proves three of the four `FusionSystem` laws for it on arbitrary
data, `DimMult.lean` / `DimMultC.lean` derive ENO 8.23 from the multiplicativity sum
identity

    (M)   Σ_c N^c_ab · J^c_ab · κ_c = κ_a κ_b

carried as a hypothesis, and `Prop821CNorm.lean` identifies the per-channel form (K)
of (M) with `J_match` at the table `settledJ`.  What none of them does is *connect*
the computed twist to those consumers.  This file is that joint, and nothing else:

* **§0 — the derived twist transports along a scalar extension.**  `comparisonScalar`
  and `derivedJGen` are built from `(F, Finv, ev, coev, ring)`, all of which
  `Transport.mapSystem` pushes along a ring hom, so
  `derivedJGen (mapSystem f S) = f ∘ derivedJGen S` and the qualification `J_match`
  at the derived twist is invariant under scalar extension
  (`j_match_derived_mapSystem_iff`).  This is what carries a computation at `ℝ`
  (`Examples/FibonacciIsing.lean`, `Examples/YangLee.lean`) to the transported `ℂ`
  copies `Transported.FibonacciC` / `IsingC`, which is where the frozen `ℂ` targets
  live: without it the `ℝ` computation is unusable at `ℂ`.

* **§1 — (M) *is* a statement about the derived table (WP3 Task 3.6).**  The sum in
  (M) runs over the channels `0 < N a b c` only, and on those `J_match` identifies
  the carried twist with the computed one, so (M) transfers verbatim:
  `dimMult_derived_of_match`.  The point is not the transfer but the *test*: the
  derivation programme's acceptance criterion is that the **computed** table
  satisfies (M), and `dimMult_iff_derived_sum` says that criterion holds of a datum
  exactly when (M) holds of the carried twist.  So (M) is not weakened or altered by
  passing to the computed twist — per instance the computation passes the test iff
  the instance did.

* **§2 — the conditional bridge to `settledJ` at `ℂ`.**  On pseudo-unitary data with
  (M) and one pivotal structure, `DimMultC`'s analytic chain pins the normalised
  twist to `FPdim_c/(FPdim_a FPdim_b)` (`twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c`);
  `settledJ_eq_of_twistNorm` rewrites that into the table
  `settledJ S hFP`, and `J_match` at the derived twist finishes the identification:
  `derivedJ_eq_settledJ_of_dimMult_pseudoUnitary`.  This is Task 2.3 target 1 on the
  route through the *carried* twist, and the two hypotheses are exactly what that route
  needs: the analytic chain computes the normalised twist `twistNorm S`, i.e. a function
  of `S.J`, and it produces the FP-ratio value only under (M); `J_match` is then what
  carries a statement about `S.J` over to the computed table.  The frozen statement
  (`Statements2.DerivedJ_eq_settledJ`) has neither hypothesis, so a proof of *it* must
  compute `derivedJ` directly instead — WP3 Task 3.2's mate argument plus the
  pseudo-unitarity rescaling, not attempted here.

* **§3 — the per-instance discharge at the `ℂ` copies.**  Fibonacci and Ising carry
  (M) unconditionally (`Transported.dimMult_fibonacciC`, `dimMult_isingC`), so
  *  the computed twist satisfies (M) there (`dimMult_derived_fibonacciC`, needing
      only `J_match` at the computed twist — one scalar row per system, d3's job);
  *  the derived twist is the settled one (`derivedJ_eq_settledJ_fibonacciC`);
  *  and the frozen exact target `ENO823ExactC derivedJ` holds **unconditionally**
      (`eno823ExactC_derived_fibonacciC`): its `J_match` antecedent is simply not
      needed, because (M) already holds of the carried twist.

* **§4 — the fixpoint of the derivation.**  Given the two facts still open elsewhere
  (nonvanishing, `WP2.DerivedJ_ne_zero`, and coherence, `derivedJGen_coherent`),
  `withJ_derived` is the `FusionSystem` with its carried twist *replaced* by the
  computed one.  It is the exact form of the slogan "`J` is data no longer": the
  computed table is a legal twist on the datum it was computed from
  (`J_match_withJ_derived`), and re-deriving from that datum returns it unchanged
  (`derivedJGen_withJ_derived`).

Everything here is field-generic where it can be; the `ℂ` statements are the frozen
ones.  Axiom budget `[propext, Classical.choice, Quot.sound]`, audited at the end.
-/
import FusionCategory.DerivedJScalar
import FusionCategory.DerivedJLaws
import FusionCategory.DimMult
import FusionCategory.DimMultC
import FusionCategory.Prop821CNorm
import FusionCategory.Transport
import FusionCategory.Examples.FibonacciIsing

universe u

namespace FusionCategory

open Finset BigOperators

/-! ## §0 — the derived twist transports along a scalar extension

`Transport.mapSystem f S` changes only the scalars (`F`, `Finv`, `ev`, `coev`, `J` are
composed with `f`); the fusion ring is untouched.  The comparison scalar is a quotient of
products of `F`, `Finv`, `ev`, so it transports, and so does the twist. -/

section TransportDerived

variable {n : ℕ} {k K : Type u} [Field k] [Field K]

/-- **The comparison scalar transports**: it is a quotient of products of `F`, `Finv` and
`ev`, each of which `Transport.mapSystem` pushes along `f`. -/
theorem comparisonScalar_mapSystem (f : k →+* K) (S : FusionSystem n k) (x y z : Fin n) :
    comparisonScalar (Transport.mapSystem f S) x y z = f (comparisonScalar S x y z) := by
  have hFinv : ∀ a b c d e g : Fin n,
      (Transport.mapSystem f S).Finv a b c d e g = f (S.Finv a b c d e g) :=
    fun _ _ _ _ _ _ => rfl
  by_cases hn : 0 < n
  · rw [comparisonScalar_def, comparisonScalar_def, dif_pos hn, dif_pos hn]
    simp [map_div₀, map_mul, hFinv]
  · rw [comparisonScalar_def, comparisonScalar_def, dif_neg hn, dif_neg hn, map_zero]

/-- **The derived twist transports**: `derivedJGen (mapSystem f S) = f ∘ derivedJGen S`. -/
theorem derivedJGen_mapSystem (f : k →+* K) (S : FusionSystem n k) (a b c : Fin n) :
    derivedJGen (Transport.mapSystem f S) a b c = f (derivedJGen S a b c) := by
  unfold derivedJGen
  simp only [Transport.mapSystem_ring]
  rw [comparisonScalar_mapSystem, comparisonScalar_mapSystem, map_div₀]

/-- **`J_match` at the computed twist is invariant under scalar extension.**  The
qualification is therefore a property of the datum and the computation, not of the field
it is read in — which is what lets a computation over `ℝ` discharge the `ℂ` targets. -/
theorem j_match_derived_mapSystem_iff (f : k →+* K) (S : FusionSystem n k) :
    J_match (Transport.mapSystem f S) (derivedJGen (Transport.mapSystem f S)) ↔
      J_match S (derivedJGen S) := by
  constructor
  · intro h a b c hN
    refine f.injective ?_
    have h' := h a b c hN
    simpa only [Transport.mapSystem_J, derivedJGen_mapSystem] using h'
  · intro h a b c hN
    have h' := h a b c hN
    simpa only [Transport.mapSystem_J, derivedJGen_mapSystem] using congrArg f h'

/-- The `ℝ → ℂ` case of `j_match_derived_mapSystem_iff`, at B4's frozen interface
`derivedJ` (`derivedJ S` is `derivedJGen S` by `rfl`). -/
theorem j_match_derived_mapC_iff (S : FusionSystem n ℝ) :
    J_match (Transport.mapSystem (algebraMap ℝ ℂ) S)
        (derivedJ (Transport.mapSystem (algebraMap ℝ ℂ) S)) ↔
      J_match S (derivedJGen S) :=
  j_match_derived_mapSystem_iff (algebraMap ℝ ℂ) S

end TransportDerived

/-! ## §1 — (M) is a statement about the computed twist

WP3 Task 3.6's acceptance test.  The sum in (M) runs over all of `Fin n`, but every term
with `N a b c = 0` vanishes on both sides, so only the supported channels matter — and
there `J_match` replaces the carried twist by the computed one. -/

section DimMultDerived

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}

/-- **(M) at the computed twist, from (M) at the carried one.**  This is WP3 Task 3.6's
per-instance form: `J_match S (derivedJGen S)` transfers multiplicativity of the twist to
the computation.  Field-generic. -/
theorem dimMult_derived_of_match (hJ : J_match S (derivedJGen S))
    (hM : DimMultiplicative S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * derivedJGen S a b c * S.kappa c)
        = S.kappa a * S.kappa b := by
  intro a b
  rw [← hM a b]
  exact Finset.sum_congr rfl (fun c _ => by
    rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h0 | hpos
    · rw [h0]; simp
    · rw [hJ a b c hpos])

/-- **The acceptance test is (M), not a weakening of it**: on a datum whose carried twist
matches the computed one, (M) holds of the carried twist *if and only if* the channel sum
of the computed twist is the character value. -/
theorem dimMult_iff_derived_sum (hJ : J_match S (derivedJGen S)) :
    DimMultiplicative S ↔ ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * derivedJGen S a b c * S.kappa c)
        = S.kappa a * S.kappa b :=
  ⟨fun hM => dimMult_derived_of_match hJ hM,
   fun h => dimMult_of_twistSum (derivedJGen S) hJ h⟩

end DimMultDerived

/-- The `ℝ` form of `dimMult_derived_of_match` — literally the task's statement at
`k = ℝ`. -/
theorem dimMult_derived_of_match_real {n : ℕ} {S : FusionSystem n ℝ}
    (hJ : J_match S (derivedJGen S)) (hM : DimMultiplicative S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℝ) * derivedJGen S a b c * S.kappa c)
        = S.kappa a * S.kappa b :=
  dimMult_derived_of_match hJ hM

/-- The same at B4's frozen interface `derivedJ` (`ℂ`). -/
theorem dimMult_derivedJ_of_match {n : ℕ} {S : FusionSystem n ℂ}
    (hJ : J_match S (derivedJ S)) (hM : DimMultiplicative S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * derivedJ S a b c * S.kappa c)
        = S.kappa a * S.kappa b :=
  dimMult_derived_of_match hJ hM

/-! ## §2 — the conditional bridge to the settled twist at `ℂ`

`settledJ S hFP` is the table `f_c κ_a κ_b / (κ_c f_a f_b)`; `Prop821CNorm.j_match_settledJ_iff`
says `J_match` at it is the per-channel law (K), and (K) is what the analytic chain of
`DimMultC` proves from (M) + pseudo-unitarity + one pivotal structure.  So the composition
is the settled-twist bridge, under exactly those hypotheses. -/

section SettledBridge

variable {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k] {S : FusionSystem n k}

/-- **The normalised twist, read as `settledJ`**: if `twistNorm` takes the FP-ratio value
on a channel, the settled table reproduces the carried twist there.  Pure algebra — the
`κ`'s cancel. -/
theorem settledJ_eq_of_twistNorm (hFP : S.ring.FPData) (a b c : Fin n)
    (hK : twistNorm S a b c = algebraMap ℝ k (hFP.fpdim c) /
      (algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b))) :
    settledJ S hFP a b c = S.J a b c := by
  have hfa : algebraMap ℝ k (hFP.fpdim a) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos a))
  have hfb : algebraMap ℝ k (hFP.fpdim b) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos b))
  have hfab : algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b) ≠ 0 :=
    mul_ne_zero hfa hfb
  have hκa : S.kappa a ≠ 0 := S.kappa_ne_zero a
  have hκb : S.kappa b ≠ 0 := S.kappa_ne_zero b
  have hκc : S.kappa c ≠ 0 := S.kappa_ne_zero c
  unfold twistNorm at hK
  rw [div_eq_div_iff (mul_ne_zero hκa hκb) hfab] at hK
  simp only [settledJ]
  field_simp
  linear_combination -hK

end SettledBridge

section SettledC

variable {n : ℕ} {S : FusionSystem n ℂ}

/-- **The settled-twist bridge at `ℂ`, conditional on (M).**  On pseudo-unitary data whose
twist is the computed one, the computed twist *is* `settledJ` — Task 2.3 target 1
(`DerivedJ_eq_settledJ`) on the route through the carried twist.  (M) is the input that route
cannot do without: `DimMultC`'s analytic chain computes `twistNorm S`, a function of the
carried `S.J`, and pins it to the FP-ratio only under (M); `J_match` moves that conclusion to
the computed table.  No nonemptiness hypothesis on the label set is needed: a supported
channel `0 < N a b c` already supplies one. -/
theorem derivedJ_eq_settledJ_of_dimMult_pseudoUnitary (hFP : S.ring.FPData)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hJ : J_match S (derivedJ S)) : DerivedJ_eq_settledJ S hFP := by
  intro a b c hN
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact a.elim0)
  have hK := twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c hFP hn hM hPU P a b c hN
  have hs := settledJ_eq_of_twistNorm hFP a b c hK
  exact (hJ a b c hN).symm.trans hs.symm

/-- **Composition with `J_match`**: under the same hypotheses the *carried* twist is the
settled one, i.e. the per-channel law (K) — so multiplicativity of every pivotal dimension
follows (`Prop821CNorm.mult_of_J_match_settledJ`). -/
theorem j_match_settledJ_of_match_dimMult (hFP : S.ring.FPData)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hJ : J_match S (derivedJ S)) : J_match S (settledJ S hFP) :=
  j_match_settledJ_of_bridge S hFP
    (derivedJ_eq_settledJ_of_dimMult_pseudoUnitary hFP hM hPU P hJ) hJ

/-- **The frozen target, decomposed into its three inputs.**  `WP2.DerivedJ_eq_settledJ` as
frozen in `Statements2.lean` relates the *computed* twist to the settled table on every
pseudo-unitary datum, and carries no other hypothesis.  This theorem is its decomposition:

* `hJ` — per datum, the carried twist is the computed one (`J_match`, i.e. WP3 Task 3.3's
  per-instance obligation, the only genuinely instance-specific input);
* `hM` — per datum, the multiplicativity sum identity (M), which is WP4's trace identity
  (`trace_iff_dimMult`) and ENO 8.23's analytic content;
* `P` — per datum, one pivotal structure, which is what `SqrtData.toPivotal` supplies.

Given those, the frozen statement holds of the computation.  So nothing in this section is a
weakening of the freeze; the hypotheses are a precise statement of what WP3 and WP4 still owe,
and each of them is discharged on the tree's instances in §3 (Fibonacci, Ising) or in the
`DimMult` round (all six data sets for (M)). -/
theorem WP2_DerivedJ_eq_settledJ_of_match_dimMult
    (P : ∀ {n : ℕ} (S : FusionSystem n ℂ), PivotalStructure S)
    (hM : ∀ {n : ℕ} (S : FusionSystem n ℂ), DimMultiplicative S)
    (hJ : ∀ {n : ℕ} (S : FusionSystem n ℂ), J_match S (derivedJ S)) :
    WP2.DerivedJ_eq_settledJ (fun {n : ℕ} (S : FusionSystem n ℂ) => derivedJ S) := by
  intro n S hFP hPU a b c hN
  exact derivedJ_eq_settledJ_of_dimMult_pseudoUnitary hFP (hM S) hPU (P S) (hJ S) a b c hN

end SettledC

/-! ## §3 — the per-instance discharge at the `ℂ` copies of Fibonacci and Ising

At both systems `J ≡ 1` and `κ = FPdim`, so (M) is the character identity and is already
proved (`Transported.dimMult_fibonacciC`, `Transported.dimMult_isingC`).  Hence:

* the computed twist passes the acceptance test as soon as it matches the carried twist
  (`dimMult_derived_fibonacciC` / `_isingC`),
* the computed twist is the settled one (`derivedJ_eq_settledJ_...`),
* and the frozen target `ENO823ExactC derivedJ` holds outright, its `J_match` antecedent
  being unused: (M) holds of the carried twist, so no identification is required.

The `J_match` at the computed twist is the one scalar computation of WP3 Task 3.3 that
lives in `Examples/FibonacciIsing.lean`.  It is a hypothesis here
(`hJ : J_match ... (derivedJ ...)`), and `j_match_derived_fibonacciC_iff` below says the
hypothesis is exactly its `ℝ` form — so the `ℝ` computation plugs in unchanged, through
`derivedJ_eq_settledJ_fibonacciC_of_real`.  That reduction is stated once, generically, as
`derivedJ_eq_settledJ_mapSystem_of_real`: (M), pseudo-unitarity, one pivotal structure and
`J_match` at `ℝ` give the frozen `ℂ` target on the scalar copy of *any* system, so a future
instance costs one `J_match` computation and no arithmetic at `ℂ`. -/

section Derived

/-- **ENO 8.23's exact target at the computed twist, for every datum that satisfies (M).**
`ENO823ExactC derivedJ S hFP` is `IsPseudoUnitaryC S hFP → J_match S (derivedJ S) → ∃! P, ...`:
the two antecedents are the *qualifications* of the exact statement, not its content.  Under
(M) the content is already available — `DimMultC.eno823ExactC_of_dimMult` produces the unique
spherical pivotal structure with the FP-dimensions from (M), pseudo-unitarity and any one
pivotal structure — so both antecedents are carried and unused here.  Every per-instance
statement in the next section is this theorem plus that instance's (M). -/
theorem eno823ExactC_derivedJ_of_dimMult {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S) (P : PivotalStructure S) :
    ENO823ExactC derivedJ S hFP := by
  intro hPU _hJ
  exact eno823ExactC_of_dimMult hFP hn hM hPU P

end Derived

section Copies

/-- **The `ℂ` bridge for a transported system.**  Every input of the settled-twist bridge at
`Transport.mapSystem (algebraMap ℝ ℂ) S` is the image of its `ℝ` counterpart: (M) transports
(`Transport.mapSystem_dimMult`), pseudo-unitarity transports
(`Transport.isPseudoUnitaryC_of_algebraMap`), a pivotal structure transports
(`Transport.mapPivotal`), and `J_match` at the computed twist transports
(`j_match_derived_mapC_iff`).  So **one** computation over `ℝ` discharges the frozen `ℂ`
target for the scalar copy, without redoing any arithmetic — which is why the two instances
below are the generic theorem plus one `J_match` statement each. -/
theorem derivedJ_eq_settledJ_mapSystem_of_real {n : ℕ} {S : FusionSystem n ℝ}
    (hFP : S.ring.FPData) (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) (hJ : J_match S (derivedJGen S)) :
    DerivedJ_eq_settledJ (Transport.mapSystem (algebraMap ℝ ℂ) S) hFP :=
  derivedJ_eq_settledJ_of_dimMult_pseudoUnitary (S := Transport.mapSystem (algebraMap ℝ ℂ) S)
    hFP (Transport.mapSystem_dimMult (algebraMap ℝ ℂ) S hM)
    (Transport.isPseudoUnitaryC_of_algebraMap hFP hPU)
    (Transport.mapPivotal (algebraMap ℝ ℂ) P)
    ((j_match_derived_mapC_iff S).mpr hJ)

/-- `J_match` at the computed twist on the `ℂ` Fibonacci copy *is* `J_match` at the
computed twist over `ℝ`, where the finite computation is done. -/
theorem j_match_derived_fibonacciC_iff :
    J_match Transported.FibonacciC (derivedJ Transported.FibonacciC) ↔
      J_match FibonacciSystem (derivedJGen FibonacciSystem) :=
  j_match_derived_mapC_iff _

/-- The Ising form. -/
theorem j_match_derived_isingC_iff :
    J_match Transported.IsingC (derivedJ Transported.IsingC) ↔
      J_match IsingSystem (derivedJGen IsingSystem) :=
  j_match_derived_mapC_iff _

/-- The pivotal structure of the `ℂ` Fibonacci copy: the hand-built `p ≡ 1` structure of
the `ℝ` system, pushed along `ℝ → ℂ`. -/
noncomputable def fibonacciCPivotal : PivotalStructure Transported.FibonacciC :=
  Transport.mapPivotal (algebraMap ℝ ℂ) FibonacciPivotal

/-- The pivotal structure of the `ℂ` Ising copy. -/
noncomputable def isingCPivotal : PivotalStructure Transported.IsingC :=
  Transport.mapPivotal (algebraMap ℝ ℂ) IsingPivotal

/-- **(M) at the computed twist, Fibonacci over `ℝ`** — WP3 Task 3.6 at the field where the
computation lives. -/
theorem dimMult_derived_fibonacciSystem
    (hJ : J_match FibonacciSystem (derivedJGen FibonacciSystem)) :
    ∀ a b : Fin 2,
      (∑ c : Fin 2, (FibonacciSystem.ring.N a b c : ℝ)
          * derivedJGen FibonacciSystem a b c * FibonacciSystem.kappa c)
        = FibonacciSystem.kappa a * FibonacciSystem.kappa b :=
  dimMult_derived_of_match hJ FibonacciSystem_dimMultiplicative

/-- **(M) at the computed twist, Ising over `ℝ`.** -/
theorem dimMult_derived_isingSystem
    (hJ : J_match IsingSystem (derivedJGen IsingSystem)) :
    ∀ a b : Fin 3,
      (∑ c : Fin 3, (IsingSystem.ring.N a b c : ℝ)
          * derivedJGen IsingSystem a b c * IsingSystem.kappa c)
        = IsingSystem.kappa a * IsingSystem.kappa b :=
  dimMult_derived_of_match hJ IsingSystem_dimMultiplicative

/-- **(M) at the computed twist, Fibonacci at `ℂ`** — WP3 Task 3.6 for this instance. -/
theorem dimMult_derived_fibonacciC
    (hJ : J_match Transported.FibonacciC (derivedJ Transported.FibonacciC)) :
    ∀ a b : Fin 2,
      (∑ c : Fin 2, (Transported.FibonacciC.ring.N a b c : ℂ)
          * derivedJ Transported.FibonacciC a b c * Transported.FibonacciC.kappa c)
        = Transported.FibonacciC.kappa a * Transported.FibonacciC.kappa b :=
  dimMult_derived_of_match hJ Transported.dimMult_fibonacciC

/-- **(M) at the computed twist, Ising at `ℂ`.** -/
theorem dimMult_derived_isingC
    (hJ : J_match Transported.IsingC (derivedJ Transported.IsingC)) :
    ∀ a b : Fin 3,
      (∑ c : Fin 3, (Transported.IsingC.ring.N a b c : ℂ)
          * derivedJ Transported.IsingC a b c * Transported.IsingC.kappa c)
        = Transported.IsingC.kappa a * Transported.IsingC.kappa b :=
  dimMult_derived_of_match hJ Transported.dimMult_isingC

/-- **The computed twist of the `ℂ` Fibonacci copy is the settled one.** -/
theorem derivedJ_eq_settledJ_fibonacciC
    (hJ : J_match Transported.FibonacciC (derivedJ Transported.FibonacciC)) :
    DerivedJ_eq_settledJ Transported.FibonacciC Transported.fibonacciFPData :=
  derivedJ_eq_settledJ_of_dimMult_pseudoUnitary (S := Transported.FibonacciC)
    Transported.fibonacciFPData Transported.dimMult_fibonacciC
    Transported.isPseudoUnitaryC_fibonacci fibonacciCPivotal hJ

/-- **The computed twist of the `ℂ` Ising copy is the settled one.** -/
theorem derivedJ_eq_settledJ_isingC
    (hJ : J_match Transported.IsingC (derivedJ Transported.IsingC)) :
    DerivedJ_eq_settledJ Transported.IsingC Transported.isingFPData :=
  derivedJ_eq_settledJ_of_dimMult_pseudoUnitary (S := Transported.IsingC)
    Transported.isingFPData Transported.dimMult_isingC
    Transported.isPseudoUnitaryC_ising isingCPivotal hJ

/-- **The settled-twist bridge at the `ℝ` computation**: taking `J_match` at the `ℝ` system —
the statement of WP3 Task 3.3 that lives next to the tables in
`Examples/FibonacciIsing.lean` — gives the `ℂ` instance with no further input.  This is the
form in which the finite `√5` computation is consumed: it never has to be redone at `ℂ`. -/
theorem derivedJ_eq_settledJ_fibonacciC_of_real
    (hJ : J_match FibonacciSystem (derivedJGen FibonacciSystem)) :
    DerivedJ_eq_settledJ Transported.FibonacciC Transported.fibonacciFPData :=
  derivedJ_eq_settledJ_fibonacciC (j_match_derived_fibonacciC_iff.mpr hJ)

/-- The Ising form of `derivedJ_eq_settledJ_fibonacciC_of_real`. -/
theorem derivedJ_eq_settledJ_isingC_of_real
    (hJ : J_match IsingSystem (derivedJGen IsingSystem)) :
    DerivedJ_eq_settledJ Transported.IsingC Transported.isingFPData :=
  derivedJ_eq_settledJ_isingC (j_match_derived_isingC_iff.mpr hJ)

/-- **WP3 Task 3.3 at Fibonacci (`ℂ`): the frozen exact target at the *computed* twist**,
with no `J_match` input needed — pseudo-unitarity alone, because (M) holds of the carried
twist here and `ENO823ExactC`'s antecedent is only ever used to get (M). -/
theorem eno823ExactC_derived_fibonacciC :
    ENO823ExactC derivedJ Transported.FibonacciC Transported.fibonacciFPData :=
  eno823ExactC_derivedJ_of_dimMult (S := Transported.FibonacciC) Transported.fibonacciFPData
    (by norm_num) Transported.dimMult_fibonacciC fibonacciCPivotal

/-- **WP3 Task 3.3 at Ising (`ℂ`).** -/
theorem eno823ExactC_derived_isingC :
    ENO823ExactC derivedJ Transported.IsingC Transported.isingFPData :=
  eno823ExactC_derivedJ_of_dimMult (S := Transported.IsingC) Transported.isingFPData
    (by norm_num) Transported.dimMult_isingC isingCPivotal

/-- The same conclusion routed through the derivation, as `DimMultC.eno823ExactC_of_derivedJ`
states it: `J_match` at the computed twist plus (M) at the computed table.  This is the
route the general programme uses, checked to be consistent with the direct one. -/
theorem eno823ExactC_derived_fibonacciC_via_match
    (hJ : J_match Transported.FibonacciC (derivedJ Transported.FibonacciC)) :
    ENO823ExactC derivedJ Transported.FibonacciC Transported.fibonacciFPData :=
  eno823ExactC_of_derivedJ derivedJ Transported.FibonacciC Transported.fibonacciFPData
    (by norm_num) fibonacciCPivotal (dimMult_derived_fibonacciC hJ)

/-- The Ising form of the derived-table route. -/
theorem eno823ExactC_derived_isingC_via_match
    (hJ : J_match Transported.IsingC (derivedJ Transported.IsingC)) :
    ENO823ExactC derivedJ Transported.IsingC Transported.isingFPData :=
  eno823ExactC_of_derivedJ derivedJ Transported.IsingC Transported.isingFPData
    (by norm_num) isingCPivotal (dimMult_derived_isingC hJ)

end Copies

/-! ## §4 — the fixpoint: a datum whose carried twist *is* the computed one

`withJ S J ...` (`DerivedJLaws.lean`) replaces the carried twist.  Instantiating it at
`derivedJGen S` needs exactly the two facts WP3 is still proving elsewhere — nonvanishing
(`WP2.DerivedJ_ne_zero`) and coherence (`derivedJGen_coherent`) — and the three unit laws,
which are theorems (`derivedJGen_unit_left`, `_right`, `_dual`).  The result is the form of
"`J` is computed": a `FusionSystem` with the same `(ring, F, ev, coev)` whose twist field
is the computation, on which the computation is a legal twist (`J_match_withJ_derived`,
`rfl`) and is invariant under re-derivation (`derivedJGen_withJ_derived`, `rfl`). -/

section Fixpoint

variable {n : ℕ} {k : Type u} [Field k]

/-- **The datum with its carried twist replaced by the computed one.**  `hne` is
nonvanishing of the computation on supported channels (WP2's open target), `hcoh` is the
coherence law for it (the fourth `J`-law, open). -/
noncomputable def withJ_derived (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hcoh : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f) :
    FusionSystem n k :=
  withJ S (derivedJGen S) hne
    (fun hn j => derivedJGen_unit_left S hn j)
    (fun hn i => derivedJGen_unit_right S hn i)
    (fun hn i => derivedJGen_dual S hn i)
    hcoh

/-- The twist carried by `withJ_derived` **is** the computed one, on the nose. -/
@[simp] theorem withJ_derived_J (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hcoh : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f)
    (a b c : Fin n) :
    (withJ_derived S hne hcoh).J a b c = derivedJGen S a b c := rfl

/-- **`J_match` holds of the datum `withJ_derived` by `rfl`**: replacing the carried twist
by the computation makes the two agree everywhere, so the qualification is discharged by
construction. -/
theorem J_match_withJ_derived (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hcoh : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f) :
    J_match (withJ_derived S hne hcoh) (derivedJGen (withJ_derived S hne hcoh)) :=
  fun _ _ _ _ => rfl

/-- **Re-deriving is the identity on its own output**: the computation reads only
`(ring, F, Finv, ev, coev)`, which `withJ` leaves alone.  So `withJ_derived` is a genuine
fixpoint of the derivation. -/
theorem derivedJGen_withJ_derived (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hcoh : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f)
    (a b c : Fin n) :
    derivedJGen (withJ_derived S hne hcoh) a b c = derivedJGen S a b c := rfl

/-- **The multiplicativity test of the replaced datum is the test of the computed table.**
`withJ_derived` carries `derivedJGen S`, so (M) for it is literally WP3 Task 3.6's
statement about the computation. -/
theorem dimMult_withJ_derived_iff (S : FusionSystem n k)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (hcoh : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f) :
    DimMultiplicative (withJ_derived S hne hcoh) ↔
      ∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : k) * derivedJGen S a b c * S.kappa c)
          = S.kappa a * S.kappa b :=
  Iff.rfl

end Fixpoint

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.comparisonScalar_mapSystem
#print axioms FusionCategory.derivedJGen_mapSystem
#print axioms FusionCategory.j_match_derived_mapSystem_iff
#print axioms FusionCategory.j_match_derived_mapC_iff
#print axioms FusionCategory.dimMult_derived_of_match
#print axioms FusionCategory.dimMult_iff_derived_sum
#print axioms FusionCategory.dimMult_derived_of_match_real
#print axioms FusionCategory.dimMult_derivedJ_of_match
#print axioms FusionCategory.settledJ_eq_of_twistNorm
#print axioms FusionCategory.derivedJ_eq_settledJ_of_dimMult_pseudoUnitary
#print axioms FusionCategory.j_match_settledJ_of_match_dimMult
#print axioms FusionCategory.WP2_DerivedJ_eq_settledJ_of_match_dimMult
#print axioms FusionCategory.eno823ExactC_derivedJ_of_dimMult
#print axioms FusionCategory.dimMult_derived_fibonacciSystem
#print axioms FusionCategory.dimMult_derived_isingSystem
#print axioms FusionCategory.derivedJ_eq_settledJ_mapSystem_of_real
#print axioms FusionCategory.j_match_derived_fibonacciC_iff
#print axioms FusionCategory.j_match_derived_isingC_iff
#print axioms FusionCategory.fibonacciCPivotal
#print axioms FusionCategory.isingCPivotal
#print axioms FusionCategory.dimMult_derived_fibonacciC
#print axioms FusionCategory.dimMult_derived_isingC
#print axioms FusionCategory.derivedJ_eq_settledJ_fibonacciC
#print axioms FusionCategory.derivedJ_eq_settledJ_isingC
#print axioms FusionCategory.derivedJ_eq_settledJ_fibonacciC_of_real
#print axioms FusionCategory.derivedJ_eq_settledJ_isingC_of_real
#print axioms FusionCategory.eno823ExactC_derived_fibonacciC
#print axioms FusionCategory.eno823ExactC_derived_isingC
#print axioms FusionCategory.eno823ExactC_derived_fibonacciC_via_match
#print axioms FusionCategory.eno823ExactC_derived_isingC_via_match
#print axioms FusionCategory.withJ_derived
#print axioms FusionCategory.withJ_derived_J
#print axioms FusionCategory.J_match_withJ_derived
#print axioms FusionCategory.derivedJGen_withJ_derived
#print axioms FusionCategory.dimMult_withJ_derived_iff
