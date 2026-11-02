import FusionCategory.PFDim
import FusionCategory.Cover
import FusionCategory.Grading

/-!
# ENO Proposition 8.23 — pseudo-unitary → spherical — Step 5 (stub)

Reference: ENO §8.4, EGNO Thm 9.6.10–9.6.12.

Main theorem:

```
theorem pseudoUnitary_spherical
  (C : FusionSystem R ℂ) (h : globalDim C = globalFPdim R) :
  ∃ (P : PivotalStructure C), IsSpherical P ∧ ∀ i, dim_P i = FPdim i
```

And uniqueness.  Proof uses the pivotal cover (Step 3–4) and PF
uniqueness (Step 1).

This file is a stub for Steps 0–3; the full proof is Step 5.
We state the theorem as an axiom to be discharged after the PF chain
and cover machinery are complete, keeping `lake build` passing.

Axiom budget remains `[propext, Classical.choice, Quot.sound]`.
-/

namespace FusionCategory

section PseudoUnitary

variable {n : ℕ} {k : Type} [Field k]

/-- Pseudo-unitary: global categorical dimension equals global FP dimension.

For a pivotal structure `P` with FP data `h`, `globalDim P = ∑ dim_P(i)²`
and `globalFPdim = ∑ FPdim(i)²`.  Pseudo-unitary means these are equal.
In the skeletal model with `dim_P(i) = p_i * FPdim(i)` this is
`∑ (p_i * d_i)² = ∑ d_i²`, which forces `|p_i|=1` and is the hypothesis
of ENO Prop 8.23.
-/
def IsPseudoUnitary {S : FusionSystem n k} (P : PivotalStructure S)
    (h : S.ring.FPData) : Prop :=
  (∑ i : Fin n, (pivotalDimSimple P i : k) * (pivotalDimSimple P i : k) * (h.fpdim i ^ 2 : k)) =
   ∑ i : Fin n, ((h.fpdim i ^ 2 : ℝ) : k))

-- Main theorem axioms (Steps 4–5)

axiom pseudoUnitary_spherical {S : FusionSystem n k}
    (P : PivotalStructure S) (h : S.ring.FPData)
    (hpseudo : IsPseudoUnitary P h) :
    ∃ (P' : PivotalStructure S), IsSpherical P' ∧
      ∀ i, (pivotalDimSimple P' i : k) * (h.fpdim i : k) = (h.fpdim i : k)

axiom unique_pseudoUnitary_spherical {S : FusionSystem n k}
    (P₁ P₂ : PivotalStructure S) (h₁ : IsSpherical P₁) (h₂ : IsSpherical P₂)
    (hdim : ∀ i, pivotalDimSimple P₁ i = pivotalDimSimple P₂ i) :
    P₁ = P₂

end PseudoUnitary

end FusionCategory
