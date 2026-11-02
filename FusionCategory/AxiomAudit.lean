import FusionCategory.DoubleDual
import FusionCategory.PFDim
import FusionCategory.PseudoUnitary
import FusionCategory.Examples.Fibonacci
import FusionCategory.Examples.Ising
import FusionCategory.Examples.Ostrik
import FusionCategory.Examples.PseudoUnitaryInstances

/-!
# Axiom audit — ENO 8.23

This file checks that the core theorems use only the allowed axiom
budget `[propext, Classical.choice, Quot.sound]`, matching
`haagerup-odd/AxiomAudit.lean`.

There are no `axiom` declarations left in the library: the three that stood in
`Grading.lean` are now a theorem (`torsor_p_dual`'s content is `pVal_dual`) and
two `def`s recording open targets.
-/

open FusionCategory
open FusionCategory.Examples

-- PF-uniqueness for examples is axiom-free
#print axioms FibonacciPFUnique
#print axioms IsingPFUnique
#print axioms K2210PFUnique
#print axioms phi_unique
#print axioms phi_sq
#print axioms fibonacci_pfUnique_instance
#print axioms ising_pfUnique_instance
#print axioms k2210_pfUnique_instance

-- The pivotal layer: `p_dual` is derived, sphericity is the kappa equation
#print axioms PivotalStructure.pVal_dual
#print axioms PivotalStructure.isSpherical_iff
#print axioms squaredNorm_eq

-- What the retired `pseudoUnitary_spherical` actually proved, and its cheap case
#print axioms exists_pivotal_of_trivial_twist
#print axioms exists_spherical_of_trivial_twist
#print axioms pfUnique_transport

-- The twist derived from the duality data (strict self-dual normalisation)
#print axioms DoubleDual.derivedTwist_coherent
#print axioms DoubleDual.derivedTwist_dual
#print axioms DoubleDual.vecZ2_twist_derived

-- Positivity and cover doubling are axiom-free
#print axioms globalDim_pos_of_fpdim
#print axioms coverGlobalDim_double
#print axioms cover_preserves_squaredReal
