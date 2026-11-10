import FusionCategory.Examples.YangLee
import FusionCategory.DerivedJBridge
import FusionCategory.DerivedJBlockMatrix
import FusionCategory.Transport

/-!
# WP3: Yang–Lee, the seventh data set — the derived twist is `1`, and it matches

`docs/bartlett_check.py` computed `derivedJGen YangLee.system = 1` on every supported
channel; this file kernel-checks it, together with the four things that depend on it:
`J_match` (the carried twist *is* the computed one), nonvanishing (the frozen
`DerivedJ.DerivedJ_ne_zero` at this datum, over `ℝ` and over `ℂ`), the fourth law
(through `derivedJGen_coherent_of_J_match`), and the sharpness of the `settledJ` bridge:
at `(τ, τ; 1)` the derived twist is `1` while `settledJ` is `(κ_τ/φ)² = φ⁻⁴ ≠ 1`, so the
per-datum bridge `DerivedJ_eq_settledJ` is *false* at this datum and the pseudo-unitarity
in the conditional form is not removable — the docstring's script-level remark
(`DerivedJScalar.DerivedJ_eq_settledJ`) becomes a theorem here.

Yang–Lee is the one tree datum whose twist is `1` while `κ = (1, -1/φ)` is *not* the
FP-dimension: it is not pseudo-unitary, so it cannot be reached by the
coboundary/pivotal route and it is not pointed either.  Its `dual` is the identity but —
unlike `Fibonacci.dual`, which is *literally* `id` — `YangLee.dual` is
`Examples.fibDual`, the pattern-matching double-dual of `FibonacciRing`, so
`dual (dual i)` is not definitionally `i`.  The computation below therefore avoids the
`dual_dual` rewrite the Fibonacci proof uses and instead checks the dual-invariance of
the denominator pair directly by `decide` in `ℤ[√5]` (`psiDen_dual_comm`).

## The closed form

With `dual = id` on labels and `ev ≡ 1`, the comparison scalar on a channel `z` of
`x ⊗ y` is

  `comparisonScalar x y z = ev z / (F y x z 1 z y · Finv x x y y z 1 · ev x · ev y)`,

so with `ev = 1` its denominator is one pair product `psiDen x y z` of `ℤ[√5]`.  Two
kernel checks on the eight triples of `Fin 2` finish it: `psiDen` is invariant under
`(b,a,c) ↦ (b*,a*,c*)` (`psiDen_dual_comm`), and its norm form is non-zero on the
supported channels (`psiDen_norm_ne`), so the comparison scalar does not vanish there
and `derivedJGen a b c = ψ a b c / ψ b a c = 1`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Finset BigOperators

namespace FusionCategory

namespace YangLee

/-! ## The comparison scalar of Yang–Lee in the pair model `ℤ[√5]` -/

/-- `ev = 1` in the pair model. -/
theorem evPair_zval (i : Fin 2) : ZP.zval s5 (evPair i) = 1 := by
  simp only [evPair, ZP.zval]
  norm_num

/-- The pair for the denominator `F y* x* z 1 z* y · Finv x* x y y z 1` of the comparison
scalar, in `ℤ[√5]`.  (`dual = id` on labels, but not definitionally: `dual` is
`fibDual`, so it is kept in the arguments and shown to be inert by `psiDen_dual_comm`.) -/
def psiDen (x y z : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (Fpair (dual y) (dual x) z 0 (dual z) y) (FinvPair (dual x) x y y z 0)

/-- The comparison scalar is `1` over the value of `psiDen` halved. -/
theorem comparisonScalar_eq_psiDen (x y z : Fin 2) :
    comparisonScalar system x y z = 1 / (ZP.zval s5 (psiDen x y z) / 2) := by
  unfold comparisonScalar
  rw [dif_pos (show 0 < 2 by norm_num)]
  show ZP.zval s5 (evPair z) / (ZP.zval s5 (Fpair (dual y) (dual x) z 0 (dual z) y) *
      ZP.zval s5 (FinvPair (dual x) x y y z 0) * ZP.zval s5 (evPair x) *
      ZP.zval s5 (evPair y)) = 1 / (ZP.zval s5 (psiDen x y z) / 2)
  rw [evPair_zval, evPair_zval, evPair_zval, psiDen,
    ZP.zval_two (s := s5) (d := 5) s5_sq]
  simp only [mul_one]

/-- **`dual` is inert on the denominator pair**: the pair at `(b*, a*, c*)` is the pair at
`(b, a, c)` — checked on all eight triples.  This is the step `Fibonacci`'s proof gets from
`rfl` (`Fibonacci.dual` is the identity function); `fibDual` does not reduce on a variable,
so it is a `decide` here. -/
theorem psiDen_dual_comm : ∀ a b c : Fin 2,
    ZP.peq (psiDen (dual b) (dual a) (dual c)) (psiDen a b c) = true := by
  decide

/-- Hence the comparison scalar is dual-invariant. -/
theorem comparisonScalar_dual (a b c : Fin 2) :
    comparisonScalar system (system.ring.dual b) (system.ring.dual a) (system.ring.dual c)
      = comparisonScalar system a b c := by
  show comparisonScalar system (dual b) (dual a) (dual c) = comparisonScalar system a b c
  rw [comparisonScalar_eq_psiDen, comparisonScalar_eq_psiDen,
    ZP.zval_of_peq (s := s5) (psiDen_dual_comm a b c)]

/-- On a supported channel the norm form of the denominator pair is non-zero: the five
channels of `1 ⊗ 1 = 1`, `1 ⊗ τ = τ`, `τ ⊗ 1 = τ`, `τ ⊗ τ = 1 ⊕ τ`, where the `2 × 2`
block `F^{τττ}_τ = [[-φ, 1], [-φ, φ]]` enters through `Fpair`/`FinvPair`. -/
theorem psiDen_norm_ne : ∀ (x y z : Fin 2), 0 < N x y z →
    (psiDen x y z).1 ^ 2 ≠ 5 * (psiDen x y z).2 ^ 2 := by
  decide

/-- The comparison scalar does not vanish on a supported channel. -/
theorem comparisonScalar_ne_zero_derived (x y z : Fin 2) (h : 0 < N x y z) :
    comparisonScalar system x y z ≠ 0 := by
  rw [comparisonScalar_eq_psiDen]
  exact div_ne_zero one_ne_zero
    (div_ne_zero (ZP.zval_ne_zero_of_norm_ne s5_sq (psiDen_norm_ne x y z h)) two_ne_zero)

/-- **The derived twist of Yang–Lee is trivial on every channel** — the Lean form of the
value `docs/bartlett_check.py` computed.  The twist of Yang–Lee is *not* a coboundary of
its `κ` and the datum is not pointed, so this is not an instance of any of the landed
general forms: it is the closed form of the data set itself. -/
theorem derivedJGen_eq_one (a b c : Fin 2) (h : 0 < N a b c) :
    derivedJGen system a b c = 1 := by
  rw [derivedJGen_def, comparisonScalar_dual]
  exact div_self (comparisonScalar_ne_zero_derived a b c h)

/-- **Nonvanishing on every supported channel** (the `ℝ` form of the frozen
`DerivedJ.DerivedJ_ne_zero` at this datum). -/
theorem derivedJGen_ne_zero (a b c : Fin 2) (h : 0 < N a b c) :
    derivedJGen system a b c ≠ 0 := by
  rw [derivedJGen_eq_one a b c h]
  exact one_ne_zero

/-- **The `OmegaNe` bundle holds at Yang–Lee**, by the characterisation
`derivedJGen_ne_zero_iff_omegaNe` of the frozen nonvanishing. -/
theorem omegaNe (a b c : Fin 2) (h : 0 < N a b c) :
    OmegaNe system (by norm_num : 0 < 2) a b c :=
  (derivedJGen_ne_zero_iff_omegaNe system (by norm_num : 0 < 2) h).mp
    (derivedJGen_ne_zero a b c h)

/-! ## `J_match` at the derived twist, and the laws that follow -/

/-- **WP3 Task 3.3 for Yang–Lee**: the carried twist is the computed one.  The carried
`J` is `1` by definition, and the computation returns `1` on every supported channel
(`derivedJGen_eq_one`), so the seventh data set carries its own derived twist. -/
theorem YangLeeSystem_J_match : J_match system (derivedJGen system) := by
  intro a b c h
  show (1 : ℝ) = derivedJGen system a b c
  exact (derivedJGen_eq_one a b c h).symm

/-- **The fourth law for the derived twist of Yang–Lee**, inherited from the datum's own
`J_coherent` through `J_match` — no associator algebra. -/
theorem derivedJGen_coherent : ∀ a b c d e f : Fin 2,
    0 < N a b e → 0 < N e c d → 0 < N b c f → 0 < N a f d →
    derivedJGen system a b e * derivedJGen system e c d * system.F a b c d e f
      = derivedJGen system b c f * derivedJGen system a f d * system.F a b c d e f :=
  derivedJGen_coherent_of_J_match system YangLeeSystem_J_match

/-- **The twist is computed, not carried**: a `FusionSystem` on Yang–Lee's ring,
associator, inverse associator, evaluations and coevaluations whose twist *is* the derived
table.  Both inputs of the general assembly are discharged above, so this is the seventh
data set's instance of `exists_fusionSystem_derivedJGen`. -/
theorem exists_derived_twist :
    ∃ S' : FusionSystem 2 ℝ,
      S'.F = system.F ∧ S'.Finv = system.Finv ∧ S'.ev = system.ev ∧ S'.coev = system.coev
        ∧ S'.J = derivedJGen system :=
  exists_fusionSystem_derivedJGen system derivedJGen_ne_zero derivedJGen_coherent

/-- The fixpoint datum of the derivation at Yang–Lee, with `J_match` at the computed
twist by `rfl` — re-deriving from it returns it unchanged. -/
noncomputable def derived : FusionSystem 2 ℝ :=
  withJ_derived system derivedJGen_ne_zero derivedJGen_coherent

/-- `J_match` holds of the fixpoint datum by `rfl`. -/
theorem derived_J_match : J_match derived (derivedJGen derived) :=
  J_match_withJ_derived system derivedJGen_ne_zero derivedJGen_coherent

/-- Re-deriving is the identity on the fixpoint datum. -/
theorem derivedJGen_derived (a b c : Fin 2) : derivedJGen derived a b c = derivedJGen system a b c :=
  derivedJGen_withJ_derived system derivedJGen_ne_zero derivedJGen_coherent a b c

/-! ## The pseudo-unitarity of the `settledJ` bridge cannot be dropped

`DerivedJScalar.DerivedJ_eq_settledJ`'s docstring records, from
`docs/bartlett_check.py`, that on Yang–Lee the derived twist is `1` on the `τ ⊗ τ`
channels while the settled twist `settledJ = f_c κ_a κ_b / (κ_c f_a f_b)` is not; that is
why the bridge carries `IsPseudoUnitaryC` and why
`derivedJ_eq_settledJ_of_dimMult_pseudoUnitary` needs four hypotheses.  The theorems below
make the counterexample a theorem rather than a script reading: at `(τ, τ; 1)` the derived
twist is `1` while `settledJ = (κ_τ/φ)² = φ^{-4} ≠ 1` (`κ_τ = -1/φ`).  So the *per-datum*
bridge `DerivedJ_eq_settledJ S hFP` — the statement the conditional bridge proves under its
hypotheses — is false at this datum, and the pseudo-unitarity in it is doing independent
work (compare `dimMult_alone_insufficient`, the same split for ENO 8.23). -/

/-- `settledJ` at the channel `(τ, τ; 1)` is `(κ_τ / φ)²`: the two `f`-factors and the two
`κ`-factors are all at `τ`, and `f_1 = κ_0 = 1`. -/
theorem settledJ_one_one_zero :
    settledJ system FusionCategory.Examples.FibonacciFPData 1 1 0
      = (system.kappa 1 / FusionCategory.Examples.fibFPdim 1) ^ 2 := by
  simp only [settledJ, kappa_zero, kappa_one, FusionCategory.Examples.FibonacciFPData,
    FusionCategory.Examples.fibFPdim]
  norm_num
  field_simp

/-- **`settledJ` is not `1` at Yang–Lee**: `(κ_τ/φ)² = φ^{-4}`. -/
theorem settledJ_one_one_zero_ne_one :
    settledJ system FusionCategory.Examples.FibonacciFPData 1 1 0 ≠ 1 := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := s5_sq
  have hs0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  simp only [settledJ, kappa_zero, kappa_one, FusionCategory.Examples.FibonacciFPData,
    FusionCategory.Examples.fibFPdim]
  norm_num
  intro h
  have hden : (1 + Real.sqrt 5) / 2 * ((1 + Real.sqrt 5) / 2) ≠ 0 := by positivity
  rw [div_eq_iff hden] at h
  nlinarith [h, hs, hs0]

/-- **`settledJ` is not the derived twist at Yang–Lee**: this is the kernel form of the
counterexample the `DerivedJ_eq_settledJ` docstring cites. -/
theorem settledJ_ne_derivedJGen :
    settledJ system FusionCategory.Examples.FibonacciFPData 1 1 0
      ≠ derivedJGen system 1 1 0 := by
  rw [derivedJGen_eq_one 1 1 0 (by decide)]
  exact settledJ_one_one_zero_ne_one

end YangLee

/-! ## The frozen `ℂ` interface: the seventh data set at `DerivedJ`

`DerivedJ.DerivedJ_ne_zero` and `ENO823ExactC` are stated over `ℂ` at the frozen symbol
`derivedJ`.  The `ℝ` computation transfers along `algebraMap ℝ ℂ`
(`derivedJGen_mapSystem`, `j_match_derived_mapC_iff`), so Yang–Lee's corner of the frozen
statement is unconditional. -/

/-- **`J_match` at the frozen `ℂ` interface** for the scalar copy of Yang–Lee. -/
theorem Transported.YangLeeC_J_match :
    J_match Transported.YangLeeC (derivedJ Transported.YangLeeC) :=
  (j_match_derived_mapC_iff YangLee.system).mpr YangLee.YangLeeSystem_J_match

/-- **The frozen nonvanishing `DerivedJ.DerivedJ_ne_zero` at the Yang–Lee datum**: on
every supported channel the frozen `derivedJ` does not vanish at `Transported.YangLeeC`. -/
theorem Transported.YangLeeC_derivedJ_ne_zero (a b c : Fin 2)
    (h : 0 < Transported.YangLeeC.ring.N a b c) :
    derivedJ Transported.YangLeeC a b c ≠ 0 := by
  have hN : 0 < YangLee.N a b c := by
    have h1 := h
    simp only [Transport.mapSystem_ring] at h1
    exact h1
  have hne : derivedJGen YangLee.system a b c ≠ 0 := YangLee.derivedJGen_ne_zero a b c hN
  have heq : derivedJ Transported.YangLeeC a b c
      = algebraMap ℝ ℂ (derivedJGen YangLee.system a b c) :=
    derivedJGen_mapSystem (algebraMap ℝ ℂ) YangLee.system a b c
  rw [heq]
  intro h0
  refine hne (?_)
  have hinj : Function.Injective (algebraMap ℝ ℂ) := by
    intro x y hxy
    simpa using congrArg Complex.re hxy
  exact hinj (by simpa using h0)

/-- `settledJ` transports along `algebraMap ℝ ℂ` at the `(τ, τ; 1)` channel: both `κ` and
the `f`-factors are scalar images of the `ℝ` ones. -/
theorem Transported.settledJ_yangLeeC_one_one_zero :
    settledJ Transported.YangLeeC FusionCategory.Examples.FibonacciFPData 1 1 0
      = algebraMap ℝ ℂ
          (settledJ YangLee.system FusionCategory.Examples.FibonacciFPData 1 1 0) := by
  simp only [settledJ, Transport.mapSystem_kappa, map_div₀, map_mul]
  norm_num

/-- **The per-datum `settledJ` bridge is FALSE without pseudo-unitarity**, in the frozen
`ℂ` language: at `Transported.YangLeeC` the frozen `derivedJ` is `1` on `(τ, τ; 1)` while
`settledJ` is `φ^{-4}`.  So the fourth hypothesis `IsPseudoUnitaryC` of
`derivedJ_eq_settledJ_of_dimMult_pseudoUnitary` is not removable — the honest statement is
the conditional one. -/
theorem Transported.not_derivedJ_eq_settledJ_yangLeeC :
    ¬ DerivedJ_eq_settledJ Transported.YangLeeC FusionCategory.Examples.FibonacciFPData := by
  intro h
  have hN : 0 < Transported.YangLeeC.ring.N 1 1 0 := by decide
  have h1 := h 1 1 0 hN
  rw [show derivedJ Transported.YangLeeC 1 1 0 = 1 from by
        rw [derivedJ_apply, show (Transported.YangLeeC : FusionSystem 2 ℂ)
            = Transport.mapSystem (algebraMap ℝ ℂ) YangLee.system from rfl,
          derivedJGen_mapSystem, YangLee.derivedJGen_eq_one 1 1 0 (by decide)]
        norm_num,
      settledJ_yangLeeC_one_one_zero] at h1
  have hinj : Function.Injective (algebraMap ℝ ℂ) := by
    intro x y hxy
    simpa using congrArg Complex.re hxy
  exact YangLee.settledJ_one_one_zero_ne_one (hinj (by rw [map_one]; exact h1)).symm

end FusionCategory

/-! ## Axiom audit (the budget is `[propext, Classical.choice, Quot.sound]`) -/

#print axioms FusionCategory.YangLee.evPair_zval
#print axioms FusionCategory.YangLee.comparisonScalar_eq_psiDen
#print axioms FusionCategory.YangLee.psiDen_dual_comm
#print axioms FusionCategory.YangLee.comparisonScalar_dual
#print axioms FusionCategory.YangLee.psiDen_norm_ne
#print axioms FusionCategory.YangLee.comparisonScalar_ne_zero_derived
#print axioms FusionCategory.YangLee.derivedJGen_eq_one
#print axioms FusionCategory.YangLee.derivedJGen_ne_zero
#print axioms FusionCategory.YangLee.omegaNe
#print axioms FusionCategory.YangLee.YangLeeSystem_J_match
#print axioms FusionCategory.YangLee.derivedJGen_coherent
#print axioms FusionCategory.YangLee.exists_derived_twist
#print axioms FusionCategory.YangLee.derived
#print axioms FusionCategory.YangLee.derived_J_match
#print axioms FusionCategory.YangLee.derivedJGen_derived
#print axioms FusionCategory.Transported.YangLeeC_J_match
#print axioms FusionCategory.Transported.YangLeeC_derivedJ_ne_zero
#print axioms FusionCategory.YangLee.settledJ_one_one_zero
#print axioms FusionCategory.YangLee.settledJ_one_one_zero_ne_one
#print axioms FusionCategory.YangLee.settledJ_ne_derivedJGen
#print axioms FusionCategory.Transported.settledJ_yangLeeC_one_one_zero
#print axioms FusionCategory.Transported.not_derivedJ_eq_settledJ_yangLeeC
