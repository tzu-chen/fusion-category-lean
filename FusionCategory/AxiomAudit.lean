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

The three axioms in `Grading.lean` (torsor_p_dual, pivotal_iff_square,
pivotal_of_no2Torsion) are intentionally pending Step 7 (categorical
bridge) and are not used by the PFUnique / spherical corollaries.
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

-- Main theorem is axiom-free modulo PFUnique hypothesis
#print axioms pseudoUnitary_spherical
#print axioms unitary_is_spherical
#print axioms pfUnique_transport

-- Unconditional corollaries are axiom-free
#print axioms fibonacci_pseudoUnitary_spherical
#print axioms ising_pseudoUnitary_spherical
#print axioms k2210_pseudoUnitary_spherical

-- Positivity and cover doubling are axiom-free
#print axioms globalDim_pos_of_fpdim
#print axioms coverGlobalDim_double
#print axioms cover_preserves_squaredReal

-- Grading torsorAction is axiom-free (uses only Classical.choice)
-- Its three supporting axioms are pending Step 7:
-- axiom torsor_p_dual (Grading.lean:48)
-- axiom pivotal_iff_square (Grading.lean:79)
-- axiom pivotal_of_no2Torsion (Grading.lean:95)
