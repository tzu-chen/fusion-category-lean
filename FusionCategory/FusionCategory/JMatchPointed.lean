import FusionCategory.DerivedJPointed
import FusionCategory.DerivedJCoherent
import FusionCategory.DerivedJBridge
import FusionCategory.Statements
import FusionCategory.Z3Omega
import FusionCategory.Examples.Z2SqHonest

/-!
# WP3 — `J_match` on the pointed data sets

`J_match S (derivedJGen S)` (WP3 Task 3.3) says the carried twist `S.J` *is* the
computed double-dual twist on every supported channel.  Round 1 landed it for the
two non-pointed tree data sets (`FibonacciSystem_J_match`, `IsingSystem_J_match`,
`Examples/FibonacciIsing.lean`); this file lands it for the pointed ones, through
the general pointed `δ(κ)` theorem of `DerivedJPointed.lean`.

The shape of every instance is the same and is isolated once:

* `J_match_of_delta_kappa` — on pointed data, `J_match` at the derived twist
  follows from the carried twist being the coboundary `δ(κ) = κ_a κ_b / κ_c` of
  the duality normalisation on channels;
* `derivedJGen_eq_delta_kappa_of_pointed` (landed, `DerivedJPointed.lean`) is the
  other factor: the *computed* twist is that coboundary.

What is left per system is the arithmetic identity `J = δ(κ)` on its own tables,
which is `fin_cases`/`decide` on `Fin 2`, resp. `Fin 3`, resp. `Fin 4` labels:

* `VecZ2.system_J_match` — `J ≡ 1`, `κ ≡ 1`;
* `VecZ2Twisted.system_J_match` — `J ≡ 1`, `κ = (1, -1)`, which *is* a character
  of the `Z/2` fusion rules, so the coboundary is trivial;
* `Z3Omega.system_J_match` — the first instance off the self-dual locus
  (`i* ≠ i`), with `κ = (1, ζ², ζ)` and `J = κ_a κ_b κ_c⁻¹`;
* `Z2SqH.systemH_J_match` — the honest `(Z/2)²` twist, assembled here from
  `Z2SqHonest.J_match` (the `δ(κ)` identity) and the pointed theorem; this is the
  datum whose false-twist sibling `Z2SqH.system` fails `J_match` (kernel-checked
  in `DerivedJScalar.lean`), which is exactly the contrast Task 1.5(b) records.

The agreement is *not* a definitional triviality: `derivedJGen` never reads `S.J`
(`DerivedJScalar.derivedJGen_def`), so each theorem identifies two independently
given tables.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the general pointed form of `J_match` -/

/-- **`J_match` from the carried coboundary, on pointed data.**  If the carried
twist is `δ(κ) = κ_a κ_b / κ_c` on every supported channel, then it is the
derived twist there: the computed twist is `δ(κ)` on all pointed data
(`derivedJGen_eq_delta_kappa_of_pointed`), and the two agree channel by channel.

This is the pointed half of WP3 Task 3.3 with the associator computation
factored out; the per-system instances below supply only `hJ`. -/
theorem J_match_of_delta_kappa (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = S.kappa a * S.kappa b / S.kappa c) :
    J_match S (derivedJGen S) := by
  intro a b c h
  rw [hJ a b c h]
  exact (derivedJGen_eq_delta_kappa_of_pointed S hn hP h).symm

/-- The same statement with the derived twist used for the carried one: on pointed
data, `J_match` *is* the statement that the carried twist is the coboundary. -/
theorem J_match_iff_delta_kappa (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S) :
    J_match S (derivedJGen S) ↔
      ∀ a b c : Fin n, 0 < S.ring.N a b c →
        S.J a b c = S.kappa a * S.kappa b / S.kappa c := by
  constructor
  · intro h a b c hN
    rw [h a b c hN]
    exact derivedJGen_eq_delta_kappa_of_pointed S hn hP hN
  · exact J_match_of_delta_kappa S hn hP

/-! ## §2 — `Vec_{Z/2}` with the trivial cocycle -/

/-- The duality normalisation of `Vec_{Z/2}` is trivial. -/
theorem VecZ2.kappa_eq_one (i : Fin 2) : VecZ2.system.kappa i = 1 := by
  simp [FusionSystem.kappa, VecZ2.system]

/-- `Vec_{Z/2}`: the carried twist is the coboundary `δ(κ) = 1`. -/
theorem VecZ2.J_eq_delta_kappa {a b c : Fin 2} (h : 0 < VecZ2.system.ring.N a b c) :
    VecZ2.system.J a b c =
      VecZ2.system.kappa a * VecZ2.system.kappa b / VecZ2.system.kappa c := by
  rw [VecZ2.kappa_eq_one, VecZ2.kappa_eq_one, VecZ2.kappa_eq_one]
  simp [VecZ2.system]

/-- **WP3 Task 3.3 for `Vec_{Z/2}`**: `J_match` at the derived twist. -/
theorem VecZ2.system_J_match : J_match VecZ2.system (derivedJGen VecZ2.system) :=
  J_match_of_delta_kappa VecZ2.system (by norm_num) pointed_VecZ2
    (fun _ _ _ h => VecZ2.J_eq_delta_kappa h)

/-! ## §3 — `Vec^ω_{Z/2}` with the non-trivial cocycle -/

/-- The duality normalisation of `Vec^ω_{Z/2}`: `κ 1 = -1`, `κ 0 = 1`. -/
theorem VecZ2Twisted.kappa_eq (i : Fin 2) :
    VecZ2Twisted.system.kappa i = if i = 0 then 1 else -1 := by
  fin_cases i <;> simp [FusionSystem.kappa, VecZ2Twisted.system]

/-- `Vec^ω_{Z/2}`: `κ = (1, -1)` is a character of the `Z/2` fusion rules, so the
coboundary is trivial on every channel — matching the carried `J ≡ 1`. -/
theorem VecZ2Twisted.J_eq_delta_kappa {a b c : Fin 2}
    (h : 0 < VecZ2Twisted.system.ring.N a b c) :
    VecZ2Twisted.system.J a b c =
      VecZ2Twisted.system.kappa a * VecZ2Twisted.system.kappa b /
        VecZ2Twisted.system.kappa c := by
  rw [VecZ2Twisted.kappa_eq, VecZ2Twisted.kappa_eq, VecZ2Twisted.kappa_eq]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [VecZ2Twisted.system, VecZ2.ring, VecZ2.N]

/-- **WP3 Task 3.3 for `Vec^ω_{Z/2}`**: `J_match` at the derived twist. -/
theorem VecZ2Twisted.system_J_match :
    J_match VecZ2Twisted.system (derivedJGen VecZ2Twisted.system) :=
  J_match_of_delta_kappa VecZ2Twisted.system (by norm_num) pointed_VecZ2Twisted
    (fun _ _ _ h => VecZ2Twisted.J_eq_delta_kappa h)

/-! ## §4 — `Vec^ω_{Z/3}`, the datum with `i* ≠ i` -/

/-- The carried twist of `Z3Omega` is `κ_a κ_b κ_c⁻¹`: `kapInv` is the table of
`κ⁻¹` (`kap_mul_kapInv`). -/
theorem Z3Omega.J_eq_delta_kappa (a b c : Fin 3) :
    Z3Omega.system.J a b c =
      Z3Omega.system.kappa a * Z3Omega.system.kappa b / Z3Omega.system.kappa c := by
  have hinv : Z3Omega.kapInv c = (Z3Omega.kap c)⁻¹ :=
    eq_inv_of_mul_eq_one_right (Z3Omega.kap_mul_kapInv c)
  show Z3Omega.kap a * Z3Omega.kap b * Z3Omega.kapInv c =
    Z3Omega.kap a * Z3Omega.kap b / Z3Omega.kap c
  rw [hinv, div_eq_mul_inv]

/-- **WP3 Task 3.3 for `Vec^ω_{Z/3}`**: `J_match` at the derived twist — the first
instantiation on data with `i* ≠ i`. -/
theorem Z3Omega.system_J_match : J_match Z3Omega.system (derivedJGen Z3Omega.system) :=
  J_match_of_delta_kappa Z3Omega.system (by norm_num) Z3Omega.pointed
    (fun _ _ _ _ => Z3Omega.J_eq_delta_kappa _ _ _)

/-! ## §5 — the honest `(Z/2)²` datum -/

/-- **WP3 Task 3.3 for the honest `(Z/2)²` datum**: `J_match` at the derived twist.
Its false-twist sibling `Z2SqH.system` has `J ≡ 1` and is `-1` off the unit on the
channel `1 ⊗ 2 ∋ 3`, so there `J_match` fails — the pair is the two-sided
statement of Task 1.5(b). -/
theorem Z2SqH.systemH_J_match :
    FusionCategory.J_match Z2SqH.systemH (derivedJGen Z2SqH.systemH) :=
  J_match_of_delta_kappa Z2SqH.systemH (by norm_num) pointed_Z2SqH_systemH
    (fun _ _ _ h => Z2SqH.J_match _ _ _ h)

/-! ## §6 — the same two `ℚ`-data read over `ℂ`, where the frozen targets live

`ENO823ExactC` and `WP2.DerivedJ_ne_zero` are `ℂ` statements, so the pointed
`J_match` facts above are moved to `ℂ` by scalar extension
(`DerivedJBridge.j_match_derived_mapSystem_iff`: the qualification is a property
of the datum and the computation, not of the field it is read in).  Nothing is
recomputed; these are the frozen-interface forms of §2 and §3. -/

namespace Transported

/-- `Vec_{Z/2}` with the trivial cocycle, over `ℂ`. -/
noncomputable abbrev VecZ2C : FusionSystem 2 ℂ :=
  Transport.mapSystem (algebraMap ℚ ℂ) VecZ2.system

/-- `Vec^ω_{Z/2}` with the non-trivial cocycle, over `ℂ`. -/
noncomputable abbrev VecZ2TwistedC : FusionSystem 2 ℂ :=
  Transport.mapSystem (algebraMap ℚ ℂ) VecZ2Twisted.system

/-- **`J_match` at `ℂ` for `Vec_{Z/2}`**, in the frozen form `J_match S (derivedJ S)`. -/
theorem VecZ2C_J_match : J_match VecZ2C (derivedJ VecZ2C) :=
  (j_match_derived_mapSystem_iff (algebraMap ℚ ℂ) VecZ2.system).mpr VecZ2.system_J_match

/-- **`J_match` at `ℂ` for `Vec^ω_{Z/2}`**, in the frozen form `J_match S (derivedJ S)`. -/
theorem VecZ2TwistedC_J_match : J_match VecZ2TwistedC (derivedJ VecZ2TwistedC) :=
  (j_match_derived_mapSystem_iff (algebraMap ℚ ℂ) VecZ2Twisted.system).mpr
    VecZ2Twisted.system_J_match

end Transported

end FusionCategory

/-! ## Axiom audit (budget `[propext, Classical.choice, Quot.sound]`) -/

#print axioms FusionCategory.J_match_of_delta_kappa
#print axioms FusionCategory.J_match_iff_delta_kappa
#print axioms FusionCategory.VecZ2.kappa_eq_one
#print axioms FusionCategory.VecZ2.J_eq_delta_kappa
#print axioms FusionCategory.VecZ2.system_J_match
#print axioms FusionCategory.VecZ2Twisted.kappa_eq
#print axioms FusionCategory.VecZ2Twisted.J_eq_delta_kappa
#print axioms FusionCategory.VecZ2Twisted.system_J_match
#print axioms FusionCategory.Z3Omega.J_eq_delta_kappa
#print axioms FusionCategory.Z3Omega.system_J_match
#print axioms FusionCategory.Z2SqH.systemH_J_match
#print axioms FusionCategory.Transported.VecZ2C_J_match
#print axioms FusionCategory.Transported.VecZ2TwistedC_J_match
#print axioms FusionCategory.Transported.VecZ2C
#print axioms FusionCategory.Transported.VecZ2TwistedC
