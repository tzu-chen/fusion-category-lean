import FusionCategory.ReconClosure
import FusionCategory.ReconSimpleSim
import FusionCategory.ReconBiprod
import FusionCategory.AssocNatural
import FusionCategory.SnakeCollapse

/-!
# The closure bridge: six of the seven `ClosureInputs` are theorems

`ClosureInputs S` (in `ReconClosure.lean`, the Round-3 assembly) takes exactly
seven inputs: the associator's naturality, the pentagon, the two snakes, the
finite-biproduct instance, and D1's two semisimplicity fields.  Round 3 proved
six of them — `associatorNatural` (m6, `AssocNatural.lean`),
`snakeLeft_holds`/`snakeRight_holds` (m4, `SnakeCollapse.lean`), and D1's
three (m2, `ReconSimpleSim.lean`/`ReconBiprod.lean`: `simples_fin`,
`decomposition`, and the `hasFiniteBiproducts` instance).  This file
discharges those six, so the reconstruction is a fusion category in the
library's own sense **one proof away**: any `PentagonShapeHom S` closes
`ReconIsFusionCanonical S hn`, and with it `ReconIsFusion`.

The pentagon's state (the record): the two-factor side is landed
(`PentagonUEntry.U_entry` — the composite `α_{A⊗B,C,D} ≫ α_{A,B,C⊗D}` at a
pair of refined indices is the two-`F` product on matched leaves, else `0`);
the three-factor side's collapse is the single open entry computation; the
independent re-derivation of the two-factor legs (m8's `PentagonLegs.lean`)
agrees.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

universe u

namespace FusionCategory

open FusionMat

variable {n : ℕ} {k : Type u} [Field k]

/-- **The closure inputs, discharged modulo the pentagon**: the naturality,
both snakes, the finite biproducts and both semisimplicity fields are theorems
of the tree; only the pentagon remains. -/
def closureInputsOfPentagon (S : FusionSystem n k) (hn : 0 < n)
    (pent : PentagonShapeHom S) : ClosureInputs S where
  hnat := associatorNatural S
  pent := pent
  snakeLeft := FusionMat.snakeLeft_holds S
  snakeRight := FusionMat.snakeRight_holds S
  simples_fin := FusionMat.simples_fin
  decomposition := FusionMat.decomposition

/-- **The reconstruction is a fusion category, one proof away**: any
`PentagonShapeHom S` — the pentagon, written about `associatorHom` — closes
`ReconIsFusionCanonical`.  Everything else is proved. -/
theorem reconIsFusionCanonical_of_pentagonHom (S : FusionSystem n k) (hn : 0 < n)
    (pent : PentagonShapeHom S) : ReconIsFusionCanonical S hn :=
  reconIsFusionCanonical S hn (closureInputsOfPentagon S hn pent)

end FusionCategory

#print axioms FusionCategory.closureInputsOfPentagon
#print axioms FusionCategory.reconIsFusionCanonical_of_pentagonHom

