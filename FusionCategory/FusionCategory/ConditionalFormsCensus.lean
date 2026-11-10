import FusionCategory.Examples.FibonacciIsing
import FusionCategory.DerivedJMate
import FusionCategory.DerivedJFunctor
import FusionCategory.DerivedJOmegaPivotal
import FusionCategory.DerivedJPivotalDichotomy
import FusionCategory.DerivedJCoherent
import FusionCategory.PointedPair
import FusionCategory.Z3Omega
import FusionCategory.DerivedJYangLee

/-!
# The conditional WP3 forms, instantiated on the tree's data sets

WP3's fourth law for the computed twist `derivedJGen` is landed in *conditional*
form: the coboundary class (`DerivedJCoherent`), the mate-picture `PairCocycle`
(`DerivedJMate`), the single-dual coherences `SingleDualCoherent` /
`SingleDualPairCoherent` (`DerivedJFunctor`), and the two-obligation assembly
`derivedJGen_coherent_of_omegaCocycle_of_omegaNe` (`DerivedJOmegaPivotal`).  Every
one of those was stated, and none was ever *instantiated*: before this file,
`PairCocycle`, `SingleDualCoherent` and `TwistCoboundary` occurred only in the
modules that define them, so a reader could not tell whether the hypotheses are
satisfiable at all.

This file instantiates them, on both halves of the tree:

* **pointed data** — `pointed_conditional_forms` discharges `PairCocycle`,
  `CrossCocycle`, `TwistCoboundary`, `PivotalFactor S S.kappa` and `OmegaNe` from
  `WP2.Pointed` alone, using only landed lemmas; it is instantiated at
  `VecZ2.system`, `VecZ2Twisted.system`, `Z2SqH.system`, `Z2SqH.systemH` and
  `Z3Omega.system` (`Vec^ω_{Z/3}`, the only datum of the tree with `dual ≠ id`);
* **the two non-pointed data sets** — for `Fibonacci.system` and `Ising.system`,
  where nothing was known before:
  - `omegaNe_all`: `OmegaNe` on *every* supported channel.  The second factor of
    `OmegaNe` is a second `ev`-free pair product (`psiDen2`), whose norm form is
    non-zero on supported channels by `decide` in `ℤ[√5]`, resp. `ℤ[√2]`; the
    first is the landed `psiDen`.  `omegaNe_of_pointed` was the only discharge of
    this obligation in the tree, and it does not apply here.
  - `singleDualPairCoherent`, hence `singleDualCoherent` through
    `singleDualCoherent_of_pair`: the `ℤ[√d]`-pair form of the identity is
    `decide`d on the supported quadruples (`sdp_pair`) and transported by
    `ZP.zval_three`.
  - `pairCocycle`, `crossCocycle`, `pivotalFactor_one` (with `φ ≡ 1`),
    `twistCoboundary`, `omegaCoeff_cocycle`, and `fourthLaw_via_assembly` — the
    landed two-obligation assembly with both obligations discharged.

* **`YangLee.system`** — the same list, on the pair model of
  `DerivedJYangLee.lean` (`dual = fibDual`, kept in the arguments): `psiDen2` is
  the second `OmegaNe` factor there too, and the fourth law comes from the landed
  `YangLee.omegaNe` and `YangLee.derivedJGen_eq_one`.  So the census covers every
  data set of the tree.

`quadruple_supported_nonempty` in each block shows the `decide`d hypotheses are
not vacuous: the unit-slot quadruple is supported.

Nothing here proves the *unconditional* fourth law, and nothing here assumes it:
`fourthLaw_via_assembly` is the landed conditional theorem applied to a datum, and
its hypotheses are proved, not quoted.

Axiom budget: `[propext, Classical.choice, Quot.sound]`, no `sorry`, no
`native_decide`; the exact computations are `decide` over `ℤ[√d]` integer pairs,
as in `Examples/FibonacciIsing.lean`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Matrix Finset BigOperators

namespace FusionCategory

namespace Fibonacci

/-- The second `OmegaNe` factor, in the pair model: the `F`/`Finv` product
`F a b c* 0 c a* · Finv b b* a* a* c* 0` of `DerivedJCoherent.OmegaNe`, at `dual = id`. -/
def psiDen2 (x y z : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (Fpair x y z 0 z x) (FinvPair y y x x z 0)

/-- Its norm form is non-zero on every supported channel. -/
theorem psiDen2_norm_ne : ∀ (x y z : Fin 2), 0 < N x y z →
    (psiDen2 x y z).1 ^ 2 ≠ 5 * (psiDen2 x y z).2 ^ 2 := by
  decide

/-- The first `OmegaNe` factor is `psiDen` halved. -/
theorem pairFactor_eq_psiDen (x y z : Fin 2) :
    F y x z 0 z y * Finv x x y y z 0 = ZP.zval s5 (psiDen x y z) / 2 := by
  simp only [F, Finv, psiDen, ZP.zval_two (s := s5) (d := 5) s5_sq]

/-- The second `OmegaNe` factor is `psiDen2` halved. -/
theorem pairFactor2_eq (x y z : Fin 2) :
    F x y z 0 z x * Finv y y x x z 0 = ZP.zval s5 (psiDen2 x y z) / 2 := by
  simp only [F, Finv, psiDen2, ZP.zval_two (s := s5) (d := 5) s5_sq]

/-- **`OmegaNe` holds on every supported channel of the Fibonacci system** — the
first non-pointed datum on which the nonvanishing obligation is discharged. -/
theorem omegaNe_all (hn : 0 < 2) (a b c : Fin 2) (h : 0 < N a b c) :
    OmegaNe system hn a b c := by
  refine ⟨?_, ?_⟩
  · show F b a c 0 c b * Finv a a b b c 0 ≠ 0
    rw [pairFactor_eq_psiDen a b c]
    exact div_ne_zero (ZP.zval_ne_zero_of_norm_ne s5_sq (psiDen_norm_ne a b c h)) two_ne_zero
  · show F a b c 0 c a * Finv b b a a c 0 ≠ 0
    rw [pairFactor2_eq a b c]
    exact div_ne_zero (ZP.zval_ne_zero_of_norm_ne s5_sq (psiDen2_norm_ne a b c h)) two_ne_zero

/-- The mate pairing does not vanish on a supported channel. -/
theorem pairScalar_ne_zero_all (a b c : Fin 2) (h : 0 < N a b c) :
    pairScalar system a b c ≠ 0 := by
  have hn : 0 < 2 := by norm_num
  have hne : F b a c 0 c b * Finv a a b b c 0 ≠ 0 := (omegaNe_all hn a b c h).1
  rw [pairScalar_def, dif_pos hn]
  show F b a c 0 c b * Finv a a b b c 0 * system.ev a * system.ev b ≠ 0
  exact mul_ne_zero (mul_ne_zero hne (system.ev_ne_zero a)) (system.ev_ne_zero b)

end Fibonacci

end FusionCategory

namespace FusionCategory

namespace Fibonacci

/-- The triple product of pairs underlying `SingleDualPairCoherent`. -/
def tri (x y z : ℤ × ℤ) : ℤ × ℤ := ZP.Zmul 5 (ZP.Zmul 5 x y) z

/-- The ``ev`-free coherence identity, decided on the pairs. -/
theorem sdp_pair : ∀ (a b c d e f : Fin 2), 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    ZP.peq (tri (psiDen a b e) (psiDen e c d) (Fpair c b a d f e))
      (tri (psiDen b c f) (psiDen a f d) (Fpair a b c d e f)) = true := by
  decide

/-- The `decide`d hypotheses are not vacuous: the unit-slot quadruple is supported. -/
theorem quadruple_supported_nonempty :
    ∃ a b c d e f : Fin 2, 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d :=
  ⟨0, 0, 0, 0, 0, 0, by decide⟩

theorem singleDualPair_eq (x y z : Fin 2) :
    singleDualPair system x y z = ZP.zval s5 (psiDen x y z) / 2 := by
  simp only [singleDualPair, dif_pos (show 0 < 2 by norm_num)]
  show F y x z 0 z y * Finv x x y y z 0 = ZP.zval s5 (psiDen x y z) / 2
  exact pairFactor_eq_psiDen x y z

/-- **The `ev`-free, division-free single-dual coherence holds on Fibonacci.** -/
theorem singleDualPairCoherent : SingleDualPairCoherent system := by
  intro a b c d e f h1 h2 h3 h4
  have key := ZP.zval_of_peq (s := s5) (sdp_pair a b c d e f h1 h2 h3 h4)
  simp only [tri] at key
  rw [singleDualPair_eq a b e, singleDualPair_eq e c d, singleDualPair_eq b c f,
    singleDualPair_eq a f d]
  show ZP.zval s5 (psiDen a b e) / 2 * (ZP.zval s5 (psiDen e c d) / 2) *
      ZP.zval s5 (Fpair c b a d f e)
    = ZP.zval s5 (psiDen b c f) / 2 * (ZP.zval s5 (psiDen a f d) / 2) *
      ZP.zval s5 (Fpair a b c d e f)
  have hL : ZP.zval s5 (psiDen a b e) / 2 * (ZP.zval s5 (psiDen e c d) / 2) *
      ZP.zval s5 (Fpair c b a d f e)
      = ZP.zval s5 (psiDen a b e) * ZP.zval s5 (psiDen e c d) *
        ZP.zval s5 (Fpair c b a d f e) / 4 := by
    ring
  have hR : ZP.zval s5 (psiDen b c f) / 2 * (ZP.zval s5 (psiDen a f d) / 2) *
      ZP.zval s5 (Fpair a b c d e f)
      = ZP.zval s5 (psiDen b c f) * ZP.zval s5 (psiDen a f d) *
        ZP.zval s5 (Fpair a b c d e f) / 4 := by
    ring
  rw [hL, hR,
    ZP.zval_three (s := s5) (d := 5) s5_sq (psiDen a b e) (psiDen e c d) (Fpair c b a d f e),
    ZP.zval_three (s := s5) (d := 5) s5_sq (psiDen b c f) (psiDen a f d) (Fpair a b c d e f),
    key]

end Fibonacci

end FusionCategory

namespace FusionCategory

namespace Fibonacci

theorem singleDualPair_ne_zero_all (a b c : Fin 2) (h : 0 < N a b c) :
    singleDualPair system a b c ≠ 0 :=
  singleDualPair_ne_zero_of_omegaNe system (show 0 < 2 by norm_num)
    (omegaNe_all (show 0 < 2 by norm_num) a b c h)

/-- **The single-dual coherence of `(−)*` holds on Fibonacci.** -/
theorem singleDualCoherent : SingleDualCoherent system :=
  singleDualCoherent_of_pair system singleDualPairCoherent singleDualPair_ne_zero_all

/-- **The associator-only cocycle identity holds on Fibonacci.** -/
theorem omegaCoeff_cocycle : ∀ a b c d e f : Fin 2, 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    FusionMat.omegaCoeff system a b e * FusionMat.omegaCoeff system e c d
      = FusionMat.omegaCoeff system b c f * FusionMat.omegaCoeff system a f d := by
  intro a b c d e f h1 h2 h3 h4
  have hn : 0 < 2 := by norm_num
  rw [← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn a b e h1),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn e c d h2),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn b c f h3),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn a f d h4),
    derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

/-- **`PairCocycle` holds on Fibonacci.** -/
theorem pairCocycle : PairCocycle system := by
  rw [← derivedJGen_qualified_iff_pairCocycle system (show 0 < 2 by norm_num)]
  intro a b c d e f h1 h2 h3 h4
  rw [derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

/-- **The division-free `CrossCocycle` holds on Fibonacci.** -/
theorem crossCocycle : CrossCocycle system :=
  (pairCocycle_iff_crossCocycle system pairScalar_ne_zero_all).mp pairCocycle

/-- **A pivotal factor exists on Fibonacci**: the twist is the coboundary of `1`. -/
theorem pivotalFactor_one : PivotalFactor system (fun _ => 1) := by
  refine ⟨fun _ => one_ne_zero, ?_⟩
  intro a b c h
  have hJ : derivedJGen system a b c = 1 := derivedJGen_eq_one a b c h
  have hPS : pairScalar system a b c ≠ 0 := pairScalar_ne_zero_all a b c h
  have hPD : pairDual system a b c = pairScalar system a b c := by
    have h := derivedJGen_eq_pairDual_div system a b c
    rw [hJ] at h
    exact (div_eq_one_iff_eq hPS).mp h.symm
  show pairDual system a b c * 1 = pairScalar system a b c * (1 * 1)
  rw [hPD]
  ring

/-- **The twist is a coboundary on Fibonacci.** -/
theorem twistCoboundary : TwistCoboundary system :=
  ⟨fun _ => 1, fun _ => one_ne_zero, fun a b c h => by
    rw [derivedJGen_eq_one a b c h]
    ring⟩

/-- **The two-obligation assembly instantiated on Fibonacci**: the fourth law for
`derivedJGen` from the landed assembly, with both obligations discharged. -/
theorem fourthLaw_via_assembly :
    ∀ a b c d e f : Fin 2, 0 < N a b e → 0 < N e c d → 0 < N b c f → 0 < N a f d →
      derivedJGen system a b e * derivedJGen system e c d * system.F a b c d e f
        = derivedJGen system b c f * derivedJGen system a f d * system.F a b c d e f := by
  refine derivedJGen_coherent_of_omegaCocycle_of_omegaNe system (show 0 < 2 by norm_num)
    omegaCoeff_cocycle ?_
  intro a b c d e f h1 h2 h3 h4 _
  exact ⟨omegaNe_all (show 0 < 2 by norm_num) a b e h1,
    omegaNe_all (show 0 < 2 by norm_num) e c d h2,
    omegaNe_all (show 0 < 2 by norm_num) b c f h3,
    omegaNe_all (show 0 < 2 by norm_num) a f d h4⟩

end Fibonacci

end FusionCategory

namespace FusionCategory

namespace Ising

/-- The second `OmegaNe` factor, in the pair model (at `dual = id`). -/
def psiDen2 (x y z : Fin 3) : ℤ × ℤ :=
  ZP.Zmul 2 (Fpair x y z 0 z x) (FinvPair y y x x z 0)

theorem psiDen2_norm_ne : ∀ (x y z : Fin 3), 0 < N x y z →
    (psiDen2 x y z).1 ^ 2 ≠ 2 * (psiDen2 x y z).2 ^ 2 := by
  decide

theorem pairFactor_eq_psiDen (x y z : Fin 3) :
    F y x z 0 z y * Finv x x y y z 0 = ZP.zval s2 (psiDen x y z) / 2 := by
  simp only [F, Finv, psiDen, ZP.zval_two (s := s2) (d := 2) s2_sq]

theorem pairFactor2_eq (x y z : Fin 3) :
    F x y z 0 z x * Finv y y x x z 0 = ZP.zval s2 (psiDen2 x y z) / 2 := by
  simp only [F, Finv, psiDen2, ZP.zval_two (s := s2) (d := 2) s2_sq]

/-- **`OmegaNe` holds on every supported channel of the Ising system.** -/
theorem omegaNe_all (hn : 0 < 3) (a b c : Fin 3) (h : 0 < N a b c) :
    OmegaNe system hn a b c := by
  refine ⟨?_, ?_⟩
  · show F b a c 0 c b * Finv a a b b c 0 ≠ 0
    rw [pairFactor_eq_psiDen a b c]
    exact div_ne_zero (ZP.zval_ne_zero_of_norm_ne s2_sq (psiDen_norm_ne a b c h)) two_ne_zero
  · show F a b c 0 c a * Finv b b a a c 0 ≠ 0
    rw [pairFactor2_eq a b c]
    exact div_ne_zero (ZP.zval_ne_zero_of_norm_ne s2_sq (psiDen2_norm_ne a b c h)) two_ne_zero

theorem pairScalar_ne_zero_all (a b c : Fin 3) (h : 0 < N a b c) :
    pairScalar system a b c ≠ 0 := by
  have hn : 0 < 3 := by norm_num
  have hne : F b a c 0 c b * Finv a a b b c 0 ≠ 0 := (omegaNe_all hn a b c h).1
  rw [pairScalar_def, dif_pos hn]
  show F b a c 0 c b * Finv a a b b c 0 * system.ev a * system.ev b ≠ 0
  exact mul_ne_zero (mul_ne_zero hne (system.ev_ne_zero a)) (system.ev_ne_zero b)

/-- The triple product of pairs underlying `SingleDualPairCoherent`. -/
def tri (x y z : ℤ × ℤ) : ℤ × ℤ := ZP.Zmul 2 (ZP.Zmul 2 x y) z

theorem sdp_pair : ∀ (a b c d e f : Fin 3), 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    ZP.peq (tri (psiDen a b e) (psiDen e c d) (Fpair c b a d f e))
      (tri (psiDen b c f) (psiDen a f d) (Fpair a b c d e f)) = true := by
  decide

/-- The `decide`d hypotheses are not vacuous: the unit-slot quadruple is supported. -/
theorem quadruple_supported_nonempty :
    ∃ a b c d e f : Fin 3, 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d :=
  ⟨0, 0, 0, 0, 0, 0, by decide⟩

theorem singleDualPair_eq (x y z : Fin 3) :
    singleDualPair system x y z = ZP.zval s2 (psiDen x y z) / 2 := by
  simp only [singleDualPair, dif_pos (show 0 < 3 by norm_num)]
  show F y x z 0 z y * Finv x x y y z 0 = ZP.zval s2 (psiDen x y z) / 2
  exact pairFactor_eq_psiDen x y z

/-- **The `ev`-free single-dual coherence holds on Ising.** -/
theorem singleDualPairCoherent : SingleDualPairCoherent system := by
  intro a b c d e f h1 h2 h3 h4
  have key := ZP.zval_of_peq (s := s2) (sdp_pair a b c d e f h1 h2 h3 h4)
  simp only [tri] at key
  rw [singleDualPair_eq a b e, singleDualPair_eq e c d, singleDualPair_eq b c f,
    singleDualPair_eq a f d]
  show ZP.zval s2 (psiDen a b e) / 2 * (ZP.zval s2 (psiDen e c d) / 2) *
      ZP.zval s2 (Fpair c b a d f e)
    = ZP.zval s2 (psiDen b c f) / 2 * (ZP.zval s2 (psiDen a f d) / 2) *
      ZP.zval s2 (Fpair a b c d e f)
  have hL : ZP.zval s2 (psiDen a b e) / 2 * (ZP.zval s2 (psiDen e c d) / 2) *
      ZP.zval s2 (Fpair c b a d f e)
      = ZP.zval s2 (psiDen a b e) * ZP.zval s2 (psiDen e c d) *
        ZP.zval s2 (Fpair c b a d f e) / 4 := by
    ring
  have hR : ZP.zval s2 (psiDen b c f) / 2 * (ZP.zval s2 (psiDen a f d) / 2) *
      ZP.zval s2 (Fpair a b c d e f)
      = ZP.zval s2 (psiDen b c f) * ZP.zval s2 (psiDen a f d) *
        ZP.zval s2 (Fpair a b c d e f) / 4 := by
    ring
  rw [hL, hR,
    ZP.zval_three (s := s2) (d := 2) s2_sq (psiDen a b e) (psiDen e c d) (Fpair c b a d f e),
    ZP.zval_three (s := s2) (d := 2) s2_sq (psiDen b c f) (psiDen a f d) (Fpair a b c d e f),
    key]

theorem singleDualPair_ne_zero_all (a b c : Fin 3) (h : 0 < N a b c) :
    singleDualPair system a b c ≠ 0 :=
  singleDualPair_ne_zero_of_omegaNe system (show 0 < 3 by norm_num)
    (omegaNe_all (show 0 < 3 by norm_num) a b c h)

theorem singleDualCoherent : SingleDualCoherent system :=
  singleDualCoherent_of_pair system singleDualPairCoherent singleDualPair_ne_zero_all

theorem omegaCoeff_cocycle : ∀ a b c d e f : Fin 3, 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    FusionMat.omegaCoeff system a b e * FusionMat.omegaCoeff system e c d
      = FusionMat.omegaCoeff system b c f * FusionMat.omegaCoeff system a f d := by
  intro a b c d e f h1 h2 h3 h4
  have hn : 0 < 3 := by norm_num
  rw [← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn a b e h1),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn e c d h2),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn b c f h3),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (omegaNe_all hn a f d h4),
    derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

theorem pairCocycle : PairCocycle system := by
  rw [← derivedJGen_qualified_iff_pairCocycle system (show 0 < 3 by norm_num)]
  intro a b c d e f h1 h2 h3 h4
  rw [derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

theorem crossCocycle : CrossCocycle system :=
  (pairCocycle_iff_crossCocycle system pairScalar_ne_zero_all).mp pairCocycle

theorem pivotalFactor_one : PivotalFactor system (fun _ => 1) := by
  refine ⟨fun _ => one_ne_zero, ?_⟩
  intro a b c h
  have hJ : derivedJGen system a b c = 1 := derivedJGen_eq_one a b c h
  have hPS : pairScalar system a b c ≠ 0 := pairScalar_ne_zero_all a b c h
  have hPD : pairDual system a b c = pairScalar system a b c := by
    have h := derivedJGen_eq_pairDual_div system a b c
    rw [hJ] at h
    exact (div_eq_one_iff_eq hPS).mp h.symm
  show pairDual system a b c * 1 = pairScalar system a b c * (1 * 1)
  rw [hPD]
  ring

theorem twistCoboundary : TwistCoboundary system :=
  ⟨fun _ => 1, fun _ => one_ne_zero, fun a b c h => by
    rw [derivedJGen_eq_one a b c h]
    ring⟩

theorem fourthLaw_via_assembly :
    ∀ a b c d e f : Fin 3, 0 < N a b e → 0 < N e c d → 0 < N b c f → 0 < N a f d →
      derivedJGen system a b e * derivedJGen system e c d * system.F a b c d e f
        = derivedJGen system b c f * derivedJGen system a f d * system.F a b c d e f := by
  refine derivedJGen_coherent_of_omegaCocycle_of_omegaNe system (show 0 < 3 by norm_num)
    omegaCoeff_cocycle ?_
  intro a b c d e f h1 h2 h3 h4 _
  exact ⟨omegaNe_all (show 0 < 3 by norm_num) a b e h1,
    omegaNe_all (show 0 < 3 by norm_num) e c d h2,
    omegaNe_all (show 0 < 3 by norm_num) b c f h3,
    omegaNe_all (show 0 < 3 by norm_num) a f d h4⟩

end Ising

end FusionCategory

namespace FusionCategory

universe u
variable {n : ℕ} {k : Type u} [Field k]

/-- **The landed conditional hypotheses of the WP3 reduction hold on pointed data**:
the mate-picture cocycle, its division-free form, the coboundary shape of the twist, a
pivotal factor, and the nonvanishing bundles.  No hypothesis remains. -/
theorem pointed_conditional_forms (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S) :
    PairCocycle S ∧ CrossCocycle S ∧ TwistCoboundary S ∧ PivotalFactor S S.kappa ∧
      (∀ a b c : Fin n, 0 < S.ring.N a b c → OmegaNe S hn a b c) := by
  have hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0 :=
    fun a b c h => pairScalar_ne_zero_of_pointed S hn hP h
  refine ⟨pairCocycle_of_pointed S hn hP,
    (pairCocycle_iff_crossCocycle S hne).mp (pairCocycle_of_pointed S hn hP),
    exists_coboundary_of_pointed S hn hP, ?_, ?_⟩
  · exact pivotalFactor_of_coboundary S (fun i => S.kappa_ne_zero i) hne
      (fun a b c h => derivedJGen_eq_delta_kappa_of_pointed S hn hP h)
  · intro a b c h
    exact omegaNe_of_pointed S hn hP h

theorem conditional_forms_VecZ2 :
    PairCocycle VecZ2.system ∧ CrossCocycle VecZ2.system ∧ TwistCoboundary VecZ2.system ∧
      PivotalFactor VecZ2.system VecZ2.system.kappa ∧
      (∀ a b c : Fin 2, 0 < VecZ2.system.ring.N a b c →
        OmegaNe VecZ2.system (show 0 < 2 by norm_num) a b c) :=
  pointed_conditional_forms VecZ2.system (show 0 < 2 by norm_num) pointed_VecZ2

theorem conditional_forms_VecZ2Twisted :
    PairCocycle VecZ2Twisted.system ∧ CrossCocycle VecZ2Twisted.system ∧
      TwistCoboundary VecZ2Twisted.system ∧
      PivotalFactor VecZ2Twisted.system VecZ2Twisted.system.kappa ∧
      (∀ a b c : Fin 2, 0 < VecZ2Twisted.system.ring.N a b c →
        OmegaNe VecZ2Twisted.system (show 0 < 2 by norm_num) a b c) :=
  pointed_conditional_forms VecZ2Twisted.system (show 0 < 2 by norm_num) pointed_VecZ2Twisted

theorem conditional_forms_Z2SqH_system :
    PairCocycle Z2SqH.system ∧ CrossCocycle Z2SqH.system ∧ TwistCoboundary Z2SqH.system ∧
      PivotalFactor Z2SqH.system Z2SqH.system.kappa ∧
      (∀ a b c : Fin 4, 0 < Z2SqH.system.ring.N a b c →
        OmegaNe Z2SqH.system (show 0 < 4 by norm_num) a b c) :=
  pointed_conditional_forms Z2SqH.system (show 0 < 4 by norm_num) pointed_Z2SqH_system

theorem conditional_forms_Z2SqH_systemH :
    PairCocycle Z2SqH.systemH ∧ CrossCocycle Z2SqH.systemH ∧
      TwistCoboundary Z2SqH.systemH ∧
      PivotalFactor Z2SqH.systemH Z2SqH.systemH.kappa ∧
      (∀ a b c : Fin 4, 0 < Z2SqH.systemH.ring.N a b c →
        OmegaNe Z2SqH.systemH (show 0 < 4 by norm_num) a b c) :=
  pointed_conditional_forms Z2SqH.systemH (show 0 < 4 by norm_num) pointed_Z2SqH_systemH

theorem conditional_forms_Z3Omega :
    PairCocycle Z3Omega.system ∧ CrossCocycle Z3Omega.system ∧ TwistCoboundary Z3Omega.system ∧
      PivotalFactor Z3Omega.system Z3Omega.system.kappa ∧
      (∀ a b c : Fin 3, 0 < Z3Omega.system.ring.N a b c →
        OmegaNe Z3Omega.system (show 0 < 3 by norm_num) a b c) :=
  pointed_conditional_forms Z3Omega.system (show 0 < 3 by norm_num) Z3Omega.pointed

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.Fibonacci.omegaNe_all
#print axioms FusionCategory.Fibonacci.singleDualPairCoherent
#print axioms FusionCategory.Fibonacci.singleDualCoherent
#print axioms FusionCategory.Fibonacci.pairCocycle
#print axioms FusionCategory.Fibonacci.crossCocycle
#print axioms FusionCategory.Fibonacci.pivotalFactor_one
#print axioms FusionCategory.Fibonacci.twistCoboundary
#print axioms FusionCategory.Fibonacci.fourthLaw_via_assembly
#print axioms FusionCategory.Ising.omegaNe_all
#print axioms FusionCategory.Ising.singleDualPairCoherent
#print axioms FusionCategory.Ising.singleDualCoherent
#print axioms FusionCategory.Ising.pairCocycle
#print axioms FusionCategory.Ising.crossCocycle
#print axioms FusionCategory.Ising.pivotalFactor_one
#print axioms FusionCategory.Ising.twistCoboundary
#print axioms FusionCategory.Ising.fourthLaw_via_assembly
#print axioms FusionCategory.pointed_conditional_forms
#print axioms FusionCategory.conditional_forms_VecZ2
#print axioms FusionCategory.conditional_forms_Z3Omega

namespace FusionCategory

namespace YangLeeCensus

open YangLee

/-- The second `OmegaNe` factor at Yang–Lee, in the pair model: `dual` is `fibDual`, so it
stays in the arguments. -/
def psiDen2 (x y z : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (Fpair x y (dual z) 0 z (dual x))
    (FinvPair y (dual y) (dual x) (dual x) (dual z) 0)

theorem psiDen2_norm_ne : ∀ (x y z : Fin 2), 0 < N x y z →
    (psiDen2 x y z).1 ^ 2 ≠ 5 * (psiDen2 x y z).2 ^ 2 := by
  decide

theorem pairFactor_eq_psiDen (x y z : Fin 2) :
    F (dual y) (dual x) z 0 (dual z) y * Finv (dual x) x y y z 0
      = ZP.zval s5 (psiDen x y z) / 2 := by
  simp only [F, Finv, psiDen, ZP.zval_two (s := s5) (d := 5) s5_sq]

theorem pairFactor2_eq (x y z : Fin 2) :
    F x y (dual z) 0 z (dual x) * Finv y (dual y) (dual x) (dual x) (dual z) 0
      = ZP.zval s5 (psiDen2 x y z) / 2 := by
  simp only [F, Finv, psiDen2, ZP.zval_two (s := s5) (d := 5) s5_sq]

/-- The mate pairing does not vanish on a supported channel, from the landed `OmegaNe`. -/
theorem pairScalar_ne_zero_all (a b c : Fin 2) (h : 0 < N a b c) :
    pairScalar system a b c ≠ 0 := by
  have hn : 0 < 2 := by norm_num
  have hne : F (dual b) (dual a) c 0 (dual c) b * Finv (dual a) a b b c 0 ≠ 0 :=
    (YangLee.omegaNe a b c h).1
  rw [pairScalar_def, dif_pos hn]
  show F (dual b) (dual a) c 0 (dual c) b * Finv (dual a) a b b c 0 *
    system.ev a * system.ev b ≠ 0
  exact mul_ne_zero (mul_ne_zero hne (system.ev_ne_zero a)) (system.ev_ne_zero b)

/-- The triple product of pairs underlying `SingleDualPairCoherent`. -/
def tri (x y z : ℤ × ℤ) : ℤ × ℤ := ZP.Zmul 5 (ZP.Zmul 5 x y) z

theorem sdp_pair : ∀ (a b c d e f : Fin 2), 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    ZP.peq (tri (psiDen a b e) (psiDen e c d)
        (Fpair (dual c) (dual b) (dual a) (dual d) (dual f) (dual e)))
      (tri (psiDen b c f) (psiDen a f d) (Fpair a b c d e f)) = true := by
  decide

/-- The `decide`d hypotheses are not vacuous at Yang–Lee either. -/
theorem quadruple_supported_nonempty :
    ∃ a b c d e f : Fin 2, 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d :=
  ⟨0, 0, 0, 0, 0, 0, by decide⟩

theorem singleDualPair_eq (x y z : Fin 2) :
    singleDualPair system x y z = ZP.zval s5 (psiDen x y z) / 2 := by
  simp only [singleDualPair, dif_pos (show 0 < 2 by norm_num)]
  show F (dual y) (dual x) z 0 (dual z) y * Finv (dual x) x y y z 0
      = ZP.zval s5 (psiDen x y z) / 2
  exact pairFactor_eq_psiDen x y z

/-- **The `ev`-free single-dual coherence holds on Yang–Lee.** -/
theorem singleDualPairCoherent : SingleDualPairCoherent system := by
  intro a b c d e f h1 h2 h3 h4
  have key := ZP.zval_of_peq (s := s5) (sdp_pair a b c d e f h1 h2 h3 h4)
  simp only [tri] at key
  rw [singleDualPair_eq a b e, singleDualPair_eq e c d, singleDualPair_eq b c f,
    singleDualPair_eq a f d]
  show ZP.zval s5 (psiDen a b e) / 2 * (ZP.zval s5 (psiDen e c d) / 2) *
      ZP.zval s5 (Fpair (dual c) (dual b) (dual a) (dual d) (dual f) (dual e))
    = ZP.zval s5 (psiDen b c f) / 2 * (ZP.zval s5 (psiDen a f d) / 2) *
      ZP.zval s5 (Fpair a b c d e f)
  have hL : ZP.zval s5 (psiDen a b e) / 2 * (ZP.zval s5 (psiDen e c d) / 2) *
      ZP.zval s5 (Fpair (dual c) (dual b) (dual a) (dual d) (dual f) (dual e))
      = ZP.zval s5 (psiDen a b e) * ZP.zval s5 (psiDen e c d) *
        ZP.zval s5 (Fpair (dual c) (dual b) (dual a) (dual d) (dual f) (dual e)) / 4 := by
    ring
  have hR : ZP.zval s5 (psiDen b c f) / 2 * (ZP.zval s5 (psiDen a f d) / 2) *
      ZP.zval s5 (Fpair a b c d e f)
      = ZP.zval s5 (psiDen b c f) * ZP.zval s5 (psiDen a f d) *
        ZP.zval s5 (Fpair a b c d e f) / 4 := by
    ring
  rw [hL, hR,
    ZP.zval_three (s := s5) (d := 5) s5_sq (psiDen a b e) (psiDen e c d)
      (Fpair (dual c) (dual b) (dual a) (dual d) (dual f) (dual e)),
    ZP.zval_three (s := s5) (d := 5) s5_sq (psiDen b c f) (psiDen a f d)
      (Fpair a b c d e f),
    key]

theorem singleDualPair_ne_zero_all (a b c : Fin 2) (h : 0 < N a b c) :
    singleDualPair system a b c ≠ 0 :=
  singleDualPair_ne_zero_of_omegaNe system (show 0 < 2 by norm_num)
    (YangLee.omegaNe a b c h)

/-- **The single-dual coherence of `(−)*` holds on Yang–Lee.** -/
theorem singleDualCoherent : SingleDualCoherent system :=
  singleDualCoherent_of_pair system singleDualPairCoherent singleDualPair_ne_zero_all

theorem omegaCoeff_cocycle : ∀ a b c d e f : Fin 2, 0 < N a b e → 0 < N e c d →
    0 < N b c f → 0 < N a f d →
    FusionMat.omegaCoeff system a b e * FusionMat.omegaCoeff system e c d
      = FusionMat.omegaCoeff system b c f * FusionMat.omegaCoeff system a f d := by
  intro a b c d e f h1 h2 h3 h4
  have hn : 0 < 2 := by norm_num
  rw [← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (YangLee.omegaNe a b e h1),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (YangLee.omegaNe e c d h2),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (YangLee.omegaNe b c f h3),
    ← derivedJGen_eq_omegaCoeff_of_omegaNe system hn (YangLee.omegaNe a f d h4),
    derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

/-- **`PairCocycle` holds on Yang–Lee.** -/
theorem pairCocycle : PairCocycle system := by
  rw [← derivedJGen_qualified_iff_pairCocycle system (show 0 < 2 by norm_num)]
  intro a b c d e f h1 h2 h3 h4
  rw [derivedJGen_eq_one a b e h1, derivedJGen_eq_one e c d h2,
    derivedJGen_eq_one b c f h3, derivedJGen_eq_one a f d h4]

theorem crossCocycle : CrossCocycle system :=
  (pairCocycle_iff_crossCocycle system pairScalar_ne_zero_all).mp pairCocycle

theorem pivotalFactor_one : PivotalFactor system (fun _ => 1) := by
  refine ⟨fun _ => one_ne_zero, ?_⟩
  intro a b c h
  have hJ : derivedJGen system a b c = 1 := derivedJGen_eq_one a b c h
  have hPS : pairScalar system a b c ≠ 0 := pairScalar_ne_zero_all a b c h
  have hPD : pairDual system a b c = pairScalar system a b c := by
    have h := derivedJGen_eq_pairDual_div system a b c
    rw [hJ] at h
    exact (div_eq_one_iff_eq hPS).mp h.symm
  show pairDual system a b c * 1 = pairScalar system a b c * (1 * 1)
  rw [hPD]
  ring

theorem twistCoboundary : TwistCoboundary system :=
  ⟨fun _ => 1, fun _ => one_ne_zero, fun a b c h => by
    rw [derivedJGen_eq_one a b c h]
    ring⟩

theorem fourthLaw_via_assembly :
    ∀ a b c d e f : Fin 2, 0 < N a b e → 0 < N e c d → 0 < N b c f → 0 < N a f d →
      derivedJGen system a b e * derivedJGen system e c d * system.F a b c d e f
        = derivedJGen system b c f * derivedJGen system a f d * system.F a b c d e f := by
  refine derivedJGen_coherent_of_omegaCocycle_of_omegaNe system (show 0 < 2 by norm_num)
    omegaCoeff_cocycle ?_
  intro a b c d e f h1 h2 h3 h4 _
  exact ⟨YangLee.omegaNe a b e h1, YangLee.omegaNe e c d h2,
    YangLee.omegaNe b c f h3, YangLee.omegaNe a f d h4⟩

end YangLeeCensus

end FusionCategory

/-! ## Axiom audit, Yang–Lee -/

#print axioms FusionCategory.YangLeeCensus.psiDen2_norm_ne
#print axioms FusionCategory.YangLeeCensus.singleDualPairCoherent
#print axioms FusionCategory.YangLeeCensus.singleDualCoherent
#print axioms FusionCategory.YangLeeCensus.pairCocycle
#print axioms FusionCategory.YangLeeCensus.crossCocycle
#print axioms FusionCategory.YangLeeCensus.pivotalFactor_one
#print axioms FusionCategory.YangLeeCensus.twistCoboundary
#print axioms FusionCategory.YangLeeCensus.fourthLaw_via_assembly
