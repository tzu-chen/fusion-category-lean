import HaagerupIzumi

/-!
# Axiom audit

Run with `lake env lean AxiomAudit.lean` after `lake build`. Each line should
report exactly `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms HaagerupIzumi.GammaContinuation.hypGamma
#print axioms HaagerupIzumi.ruijsenaarsHypGamma
#print axioms HaagerupIzumi.EGEquations_ruijsenaars
#print axioms HaagerupIzumi.exists_EGEquations_odd

#check @HaagerupIzumi.exists_EGEquations_odd
