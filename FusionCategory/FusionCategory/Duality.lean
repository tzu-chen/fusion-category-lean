import FusionCategory.Statements
import FusionCategory.Coherence

/-!
# D1 — duality-agreement lemmas (WP1 Task 1.4 remainder + Task 1.3 assembly)

This file discharges the four frozen obligations of `FusionCategory.Statements`
belonging to the duality-agreement direction:

* `EvDual` is the signature field `FusionSystem.ev_dual` (a gauge fixing, not a
  restriction): `evDual`.
* under it the library's `dim P i = p i * κ i` and ENO's
  `dimENO P i = p i * coev i * ev (i*)` agree: `dimENO_eq_lib_dim`, which is the
  frozen `dimENO_eq_dim`.
* in the self-dual case the agreement needs no hypothesis at all:
  `dimENO_eq_lib_dim_selfdual`, which is the frozen
  `dimENO_eq_dim_of_selfdual`.
* the two forms of `J_coherent` agree: `J_coherent_forms_agree_iff`, which is
  the frozen `J_coherent_forms_agree`, assembled from the two directions proved
  at general `k` in `FusionCategory.Coherence`.

Two consequences are recorded because they are the point of Task 1.4 — that the
sphericity condition (K) and the target `ENO823` become statements about the
datum rather than about a choice of evaluations: `isSpherical_iff_dimENO` and
`eno823_iff_dimENO`.

Axiom budget of every declaration: `[propext, Classical.choice, Quot.sound]`,
checked with `#print axioms` at the end of the file.  Nothing here edits an
existing file; the `ℝ` originals are retained.
-/

universe u

open FusionCategory

namespace FusionCategory

/-! ## (a) The dual-evaluation normalisation, from the signature field -/

/-- Task 1.4's chosen gauge normalisation `ev_{i*} = ev_i`, read off the
signature field that landing added (`FusionSystem.ev_dual`). -/
theorem evDual {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) : EvDual S :=
  fun i => S.ev_dual i

/-! ## (b) The two dimension normalisations agree under the normalisation -/

/-- **Task 1.4, the frozen `dimENO_eq_dim`.**  Under `ev_{i*} = ev_i`, ENO's
`p i * coev i * ev (i*)` equals the library's `dim P i = p i * κ i`, since
`κ i = coev i * ev i`: the only difference between the two readings is the label
at which the evaluation is taken. -/
theorem dimENO_eq_lib_dim {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) : dimENO_eq_dim S h := by
  intro P i
  simp only [dimENO, dim, FusionSystem.kappa, h i, mul_assoc]

/-- The pointwise form of `dimENO_eq_lib_dim`, usable as a rewrite rule. -/
theorem dimENO_eq_lib_dim_apply {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) (P : PivotalStructure S) (i : Fin n) : dimENO P i = dim P i :=
  dimENO_eq_lib_dim S h P i

/-! ## (c) The self-dual case, with no hypothesis -/

/-- **Task 1.4, the frozen `dimENO_eq_dim_of_selfdual`.**  On a self-dual label
`i* = i` the two readings are the same expression, so the gauge normalisation of
Task 1.4 is a normalisation of the non-self-dual labels only — in particular it
is vacuous on every self-dual instance. -/
theorem dimENO_eq_lib_dim_selfdual {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : dimENO_eq_dim_of_selfdual S := by
  intro P i hd
  simp only [dimENO, dim, FusionSystem.kappa, hd, mul_assoc]

/-! ## (d) The two coherence forms agree -/

/-- **Task 1.3, the frozen `J_coherent_forms_agree`.**  The retained-`F` form
(the chosen replacement of the field) and the F-free qualified form are
equivalent; the two directions are `FusionCategory.Coherence`'s
`retained_of_qualified` and `qualified_of_retained`, whose `Retained`/`Qualified`
are the bodies of the frozen `J_coherent_retained`/`J_coherent_qualified`. -/
theorem J_coherent_forms_agree_iff {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : J_coherent_forms_agree S :=
  ⟨fun h => CoherenceCheck.retained_of_qualified S h,
   fun h => CoherenceCheck.qualified_of_retained S h⟩

/-! ## Consequences: (K) and the target are gauge-invariant

With `dimENO_eq_lib_dim` the sphericity condition `dim (i*) = dim i` can be read
in ENO's normalisation, and hence the target `ENO823` is a statement about the
datum and not about a choice of evaluations. -/

/-- **Sphericity in ENO's normalisation**: `dimENO P (i*) = dimENO P i` for all
`i` iff `P` is spherical.  (The definition of `IsSpherical` uses the library's
`dim`; this says the choice of normalisation does not matter once Task 1.4's
gauge fixing is in place.) -/
theorem isSpherical_iff_dimENO {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) (P : PivotalStructure S) :
    P.IsSpherical ↔ ∀ i : Fin n, dimENO P (S.ring.dual i) = dimENO P i := by
  constructor
  · intro hsph i
    rw [dimENO_eq_lib_dim_apply S h P (S.ring.dual i), dimENO_eq_lib_dim_apply S h P i]
    exact hsph i
  · intro hsph i
    rw [← dimENO_eq_lib_dim_apply S h P (S.ring.dual i), ← dimENO_eq_lib_dim_apply S h P i]
    exact hsph i

/-- **The target `ENO823` read in ENO's dimensions**: with the gauge
normalisation of Task 1.4, the bare target is equivalent to the same statement
with `dimENO` in place of `dim` in both conjuncts.  This is the precise sense in
which the normalisation makes the target gauge-invariant. -/
theorem eno823_iff_dimENO {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    (S : FusionSystem n k) (h : EvDual S) (hFP : S.ring.FPData) :
    ENO823 S hFP ↔
      ∃ P : PivotalStructure S,
        (∀ i : Fin n, dimENO P (S.ring.dual i) = dimENO P i) ∧
          ∀ i : Fin n, dimENO P i = algebraMap ℝ k (hFP.fpdim i) := by
  constructor
  · rintro ⟨P, hsph, hdim⟩
    exact ⟨P, (isSpherical_iff_dimENO S h P).1 hsph,
      fun i => by rw [dimENO_eq_lib_dim_apply S h P i]; exact hdim i⟩
  · rintro ⟨P, hsph, hdim⟩
    exact ⟨P, (isSpherical_iff_dimENO S h P).2 hsph,
      fun i => by rw [← dimENO_eq_lib_dim_apply S h P i]; exact hdim i⟩

#print axioms FusionCategory.evDual
#print axioms FusionCategory.dimENO_eq_lib_dim
#print axioms FusionCategory.dimENO_eq_lib_dim_apply
#print axioms FusionCategory.dimENO_eq_lib_dim_selfdual
#print axioms FusionCategory.J_coherent_forms_agree_iff
#print axioms FusionCategory.isSpherical_iff_dimENO
#print axioms FusionCategory.eno823_iff_dimENO

/-! ## The ℓ² bridge: ENO's `d_i d_{i*}` is the library's `κ_i κ_{i*}`

Task 1.4's normalisation does more than identify the two dimension functions: it
also identifies the two *squared* dimensions, so the ℂ pseudo-unitarity
predicate `IsPseudoUnitaryC` (stated with `κ`) is the source's condition
`Σ_i d_i d_{i*} = FPdim(C)` read in ENO's dimensions `d_i = dimENO P i`.  The
input is `p i * p (i*) = 1` (`pVal_inv`) and `ev_{i*} = ev_i` at `i` and at
`i*`. -/

/-- `d_i · d_{i*} = κ_i · κ_{i*}`: with `p_{i*} = p_i⁻¹` and
`ev_{i**} = ev_{i*} = ev_i`, both sides are `coev_i coev_{i*} ev_i²`. -/
theorem dimENO_mul_dimENO_dual {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) (hn : 0 < n) (P : PivotalStructure S) (i : Fin n) :
    dimENO P i * dimENO P (S.ring.dual i) = S.kappa i * S.kappa (S.ring.dual i) := by
  have hp : P.pVal i * P.pVal (S.ring.dual i) = 1 := P.pVal_inv hn i
  simp only [dimENO, FusionSystem.kappa, h i, h (S.ring.dual i)]
  calc (P.pVal i * S.coev i * S.ev i) *
        (P.pVal (S.ring.dual i) * S.coev (S.ring.dual i) * S.ev i)
      = (P.pVal i * P.pVal (S.ring.dual i)) *
          (S.coev i * S.ev i * (S.coev (S.ring.dual i) * S.ev i)) := by ring
    _ = S.coev i * S.ev i * (S.coev (S.ring.dual i) * S.ev i) := by rw [hp, one_mul]

/-- The same, summed: the ℓ² left-hand side of `IsPseudoUnitaryC` is
`Σ_i d_i d_{i*}` in ENO's dimensions. -/
theorem sum_dimENO_eq_sum_kappa {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : EvDual S) (hn : 0 < n) (P : PivotalStructure S) :
    (∑ i : Fin n, dimENO P i * dimENO P (S.ring.dual i))
      = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) :=
  Finset.sum_congr rfl fun i _ => dimENO_mul_dimENO_dual S h hn P i

/-- **`IsPseudoUnitaryC` is ENO's ℓ² condition in ENO's dimensions**: under the
Task 1.4 normalisation the frozen ℂ predicate is equivalent to
`Σ_i d_i d_{i*} = FPdim(C)` with `d = dimENO`.  (The condition does not depend on
`P`: `p` cancels against `p_{i*} = p_i⁻¹`.) -/
theorem isPseudoUnitaryC_iff_dimENO {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData)
    (h : EvDual S) (hn : 0 < n) (P : PivotalStructure S) :
    IsPseudoUnitaryC S hFP ↔
      (∑ i : Fin n, dimENO P i * dimENO P (S.ring.dual i)) = algebraMap ℝ ℂ hFP.globalDim := by
  simp only [IsPseudoUnitaryC]
  rw [sum_dimENO_eq_sum_kappa S h hn P]

#print axioms FusionCategory.dimENO_mul_dimENO_dual
#print axioms FusionCategory.sum_dimENO_eq_sum_kappa
#print axioms FusionCategory.isPseudoUnitaryC_iff_dimENO

/-! ## Positivity and the normalisation at `ℂ`

The two scalar-contract helpers WP1's other directions need (`Pos` of an
embedded real, and its converse), and the statement that positivity of a
dimension does not depend on which of the two normalisations is used. -/

/-- `Pos` holds of an embedded positive real. -/
theorem pos_ofReal {r : ℝ} (h : 0 < r) : Pos (algebraMap ℝ ℂ r) := ⟨r, h, rfl⟩

/-- Conversely: `Pos (algebraMap ℝ ℂ r)` is `0 < r`.  (`algebraMap ℝ ℂ` is
`Complex.ofReal`, so this is `Complex.ofReal_inj`.) -/
theorem pos_ofReal_iff {r : ℝ} : Pos (algebraMap ℝ ℂ r) ↔ 0 < r := by
  constructor
  · rintro ⟨r', hr', he⟩
    have h2 : r' = r := Complex.ofReal_inj.mp he.symm
    rwa [h2] at hr'
  · exact pos_ofReal

/-- The positivity conjunct of the target does not depend on the choice of
duality normalisation: ENO's `d_i` is positive iff the library's `dim i` is. -/
theorem pos_dimENO_iff {n : ℕ} {S : FusionSystem n ℂ} (h : EvDual S)
    (P : PivotalStructure S) (i : Fin n) : Pos (dimENO P i) ↔ Pos (dim P i) := by
  rw [dimENO_eq_lib_dim_apply S h P i]

#print axioms FusionCategory.pos_ofReal
#print axioms FusionCategory.pos_ofReal_iff
#print axioms FusionCategory.pos_dimENO_iff

end FusionCategory
