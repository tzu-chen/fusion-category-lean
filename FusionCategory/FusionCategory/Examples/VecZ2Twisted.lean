import FusionCategory.System
import FusionCategory.Pivotal

/-!
# `Vec^ω_{Z/2}` for the non-trivial cocycle: two pivotal structures

`VecZ2Twisted.system` is the same fusion ring as `Vec_{Z/2}` but with the
non-trivial associator (`F = -1` on the `g ⊗ g ⊗ g → g` block), and with the
duality normalisation `κ g = -1` forced by the snakes.

The point of this file is that such a system carries **more than one** pivotal
structure, and that the dimension function distinguishes them:

* `pTriv` (`p ≡ 1`): `dim g = κ g = -1`;
* `pSign` (`p g = -1`): `dim g = 1`, which is the FP-dimension, and it is
  spherical.

So `Vec^ω_{Z/2}` is an example where the conclusion of ENO 8.23 (`dim = FPdim`,
spherical) holds — but only for the *second* pivotal structure.  Which pivotal
structure a category "has" is not a property of the fusion ring, and
`pseudo-unitarity` is exactly the hypothesis that selects the one with positive
dimensions.  This category is not pseudo-unitary, which is why the trivial
pivotal structure gives `dim g = -1`.

Contrast with `Vec_{Z/2}` (trivial cocycle, `VecZ2.system`), where `κ ≡ 1` and
both pivotal structures give positive dimensions.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

namespace FusionCategory.Examples

open FusionCategory

namespace VecZ2Tw

abbrev S : FusionSystem 2 ℚ := VecZ2Twisted.system

/-- The trivial pivotal structure `p ≡ 1`. -/
def pTriv : PivotalStructure S where
  p := fun _ => 1
  p_unit := fun _ => rfl
  p_mon := by
    intro i j kk _
    simp [S, VecZ2Twisted.system]

/-- The other pivotal structure, `p g = -1`. -/
def pSign : PivotalStructure S where
  p := fun i => if i = 0 then (1 : ℚˣ) else -1
  p_unit := by
    intro hn
    show (if (⟨0, hn⟩ : Fin 2) = 0 then (1 : ℚˣ) else -1) = 1
    simp
  p_mon := by
    intro i j kk hN
    fin_cases i <;> fin_cases j <;> fin_cases kk <;>
      simp_all [S, VecZ2Twisted.system, VecZ2.ring, VecZ2.N]

theorem kappa_one : S.kappa 1 = -1 := VecZ2Twisted.kappa_g

theorem kappa_zero : S.kappa 0 = 1 := VecZ2Twisted.kappa_unit

/-- With the trivial pivotal structure the dimension of `g` is `-1`. -/
theorem pTriv_dim_one : dim pTriv 1 = -1 := by
  show ((pTriv.p 1 : ℚ)) * S.kappa 1 = -1
  simp [pTriv, kappa_one]

/-- With `p g = -1` the dimension of `g` is `1`, the FP-dimension. -/
theorem pSign_dim_one : dim pSign 1 = 1 := by
  show ((pSign.p 1 : ℚ)) * S.kappa 1 = 1
  simp [pSign, kappa_one]

theorem pSign_dim_zero : dim pSign 0 = 1 := by
  show ((pSign.p 0 : ℚ)) * S.kappa 0 = 1
  simp [pSign, kappa_zero]

/-- `p g = -1` is spherical: `g` is self-dual, so `dim (g*) = dim g`. -/
theorem pSign_spherical : pSign.IsSpherical := by
  intro i
  fin_cases i
  · rfl
  · rfl

end VecZ2Tw

end FusionCategory.Examples
