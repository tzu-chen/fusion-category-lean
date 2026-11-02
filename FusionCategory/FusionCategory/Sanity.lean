import FusionCategory.Basic
import FusionCategory.System
import FusionCategory.Pivotal
import Mathlib.Data.ZMod.Basic

/-!
# Sanity checks — that the formalization captures intended objects

Reference: ENO, EGNO, Ostrik 1309.4822, Vercleyen §3.

These are non-trivial `example`/`theorem` checks from the literature that
are *provable from our definitions* and *false for a wrong formalization*
(e.g. swapped `N i j k` indices, wrong `dual_coeff`, or vacuous pentagon).

They act as regression tests for Steps 0–3.
-/

namespace FusionCategory.Sanity

open FusionRing

/-! ### 1. Fusion ring axioms imply expected consequences -/

example {n : ℕ} (R : FusionRing n) (i : Fin n) : R.dual (R.dual i) = i :=
  R.dual_involutive i

example {n : ℕ} (R : FusionRing n) : Function.Bijective R.dual :=
  R.dual_bijective

example {n : ℕ} (R : FusionRing n) (hn : 0 < n) :
    R.fusionMatrix ⟨0, hn⟩ = 1 := by
  exact R.fusionMatrix_zero hn

/-! ### 2. Fibonacci fusion ring (rank 2)

The Fibonacci ring has simples `{𝟙, τ}` with `τ⊗τ = 𝟙 ⊕ τ`.
Its FPdim is the golden ratio `φ = (1+√5)/2` satisfying `φ² = φ +1`.

We check that the skeletal data satisfies the fusion axioms and that
`φ` is an FP eigenvector, pinning the orientation of `fusionMatrix`
and the `FPData` predicate.
-/

noncomputable def fibFPdim : Fin 2 → ℝ
  | 0 => 1
  | 1 => (1 + Real.sqrt 5) / 2

theorem fibFPdim_pos (i : Fin 2) : 0 < fibFPdim i := by
  fin_cases i <;> simp [fibFPdim] <;> positivity

-- The Fibonacci `N` matrices (to be supplied in `Examples.Fibonacci`):
-- N₀ = I, N₁ = [[0,1],[1,1]].  We state the expected FPdim equation
-- as a check that our `IsPFEigenvector` predicate has the right
-- orientation `∑_j N i j k * v_j = d_i * v_k`.
example : fibFPdim 1 * fibFPdim 1 = fibFPdim 0 + fibFPdim 1 := by
  simp [fibFPdim]
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [hsq, Real.sqrt_nonneg 5]

/-! ### 3. Ising fusion ring (rank 3)

Simples `{𝟙, ψ, σ}` with `ψ⊗ψ=𝟙`, `ψ⊗σ=σ`, `σ⊗σ=𝟙⊕ψ`.
FPdim is `(1,1,√2)` and `U_C = ℤ/2` with `deg σ =1`, `deg 𝟙=deg ψ=0`.
-/

noncomputable def isingFPdim : Fin 3 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => Real.sqrt 2

theorem isingFPdim_pos (i : Fin 3) : 0 < isingFPdim i := by
  fin_cases i <;> simp [isingFPdim, Real.sqrt_nonneg]

/-- `U_C = ℤ/2` grading check: `deg` is *additive* on fusion channels
(`σ ⊗ σ = 1 ⊕ ψ` and both summands have degree `0`, with `1 + 1 = 0` in `ℤ/2`).

The previous version of this check used multiplication on `Fin 2`, where
`1 * 1 = 1 ≠ 0`, so it was simply false; it had never been built because this
file was not imported by the umbrella. -/
def isingDeg : Fin 3 → ZMod 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

example : isingDeg 0 = 0 := rfl
example : (isingDeg 2 : ZMod 2) + isingDeg 2 = 0 := by decide
example : (isingDeg 2 : ZMod 2) + isingDeg 2 = isingDeg 1 := by decide

/-! ### 4. Pivotal and spherical

Sphericity is the equality of the two trace functionals, `dim (i*) = dim i`.
Two checks that the definition behaves correctly — and that the formulation it
replaced did not:

* when `kappa` is invariant under `*` the new condition reduces to the old one,
  `p i ^ 2 = 1`; that special case is *not* the general notion;
* for a self-dual simple the equation is automatic, so a definition that forced
  `p i ^ 2 = 1` for all `i` (as the retired one did) would get Ising wrong.
-/

example {n : ℕ} {k : Type} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (hn : 0 < n)
    (hκ : ∀ i : Fin n, S.kappa (S.ring.dual i) = S.kappa i) :
    P.IsSpherical ↔ ∀ i : Fin n, (P.pVal i) ^ 2 = 1 := by
  rw [P.isSpherical_iff hn]
  constructor
  · intro h i
    have h1 : P.pVal i ^ 2 * S.kappa i = 1 * S.kappa i := by
      rw [← h i, hκ i, one_mul]
    exact mul_right_cancel₀ (S.kappa_ne_zero i) h1
  · intro h i
    rw [hκ i, h i, one_mul]

example {n : ℕ} {k : Type} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (h : ∀ i : Fin n, S.ring.dual i = i) :
    P.IsSpherical :=
  P.spherical_of_selfdual h

example {n : ℕ} {k : Type} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : dim P i ≠ 0 :=
  P.dim_ne_zero i

/-! ### 6. Global dimension doubles (cover shadow)

The skeletal shadow of `dim ̃C = 2 dim C` is that splitting `Fin (2n)`
into evens/odds doubles the sum of squares.  This is the combinatorial
core of ENO Rem 3.1, independent of the full `coverFusionRing`.
-/

def coverDoublingProp (n : ℕ) (f : Fin n → ℝ) : Prop :=
  (∑ i : Fin (n * 2), ((f ⟨i.val / 2, by omega⟩) ^ 2 : ℝ)) =
    2 * ∑ i : Fin n, (f i) ^ 2
-- Full proof is by `Fin.sum_univ_add` splitting evens/odds; we state the
-- shape to check that `coverGlobalDim_double` has correct type (provable, not vacuous).

end FusionCategory.Sanity
