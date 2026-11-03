import FusionCategory.Statements
import FusionCategory.Triangle
import FusionCategory.Coherence

/-!
# Frozen-statement conformance: every `Prop`-valued definition of `Statements.lean`, discharged

Swarm `smw0zjsah`, member `m7`, direction `d7` (audit-and-fill).

The audit of `FusionCategory/Statements.lean` against the board (proposal WP1
Tasks 1.1-1.5, Appendix `app:statements`) found the frozen `Prop`s below with no
registered owner, or owned only inside another member's scratch file.  This file
discharges **all** of them in one place, depending only on modules of the package
(`FusionCategory.Statements`, `FusionCategory.Triangle`, and `CoherenceCheck`'s
two landed directions through them), so that the frozen-statement half of
milestone M2 is checkable as a single file:

* Task 1.1 -- `Cx.pivotal_ext`, `Cx.eno823_of_pseudoUnitary` (the conditional
  theorem at `ℂ`; no other direction registered it);
* Task 1.2 -- `TriangleLaw` (the landed proof `TriangleCheck.triangle` was never
  packaged as the frozen `Prop`);
* Task 1.3 -- `J_coherent_forms_agree`, from `CoherenceCheck`'s two landed
  directions (the frozen bodies are `CoherenceCheck.Retained`/`Qualified` up to
  definitional unfolding);
* Task 1.4 -- `EvDual`, `dimENO_eq_dim`, `dimENO_eq_dim_of_selfdual`;
* Task 1.5(a) -- `Cx.eno823_of_exact` and `Cx.eno823_of_bare` (the two
  directions of the bare/exact equivalence at `ℂ`).

Every theorem's conclusion is the frozen `def` *applied* (never a re-rendering);
the `example` marked "shape guard" checks the unrolling by `rfl`, so no proof
below can be of a weaker statement.

The frozen `ENO823ExactC` itself is not discharged here and cannot be at WP1:
its `derivedJ` parameter is WP2 Task 2.3's held definition, and
`Statements.lean`'s `eno823ExactC_collapse` shows the `∀ derivedJ` closure is
false at the carried twist.

Axiom budget of every theorem below: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedVariables false

universe u

open FusionCategory

namespace Coverage

/-! ## Task 1.4 -- the gauge normalisation, and its two consequences -/

/-- The frozen `EvDual`, which is a field of the signature. -/
theorem evDual {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.EvDual S :=
  S.ev_dual

/-- The frozen `dimENO_eq_dim`: under the gauge normalisation ENO's
`p_i coev_i ev_{i*}` is the library's `p_i κ_i`. -/
theorem dimENO_eq_dim {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : FusionCategory.EvDual S) : FusionCategory.dimENO_eq_dim S h := by
  intro P i
  simp only [FusionCategory.dimENO, FusionCategory.dim, FusionSystem.kappa, h i, mul_assoc]

/-- The frozen `dimENO_eq_dim_of_selfdual`: on a self-dual label no normalisation
is needed. -/
theorem dimENO_eq_dim_of_selfdual {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : FusionCategory.dimENO_eq_dim_of_selfdual S := by
  intro P i hi
  simp only [FusionCategory.dimENO, FusionCategory.dim, FusionSystem.kappa, hi, mul_assoc]

/-! ## Task 1.3 -- the two coherence forms agree -/

/-- The frozen `J_coherent_forms_agree`, assembled from `CoherenceCheck`'s two
landed directions (the frozen bodies are the `Retained`/`Qualified` bodies). -/
theorem J_coherent_forms_agree {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) : FusionCategory.J_coherent_forms_agree S :=
  ⟨fun h => CoherenceCheck.retained_of_qualified S h,
   fun h => CoherenceCheck.qualified_of_retained S h⟩

/-! ## Task 1.2 -- the triangle law, as the frozen statement -/

/-- The frozen `TriangleLaw`, discharged from the landed `TriangleCheck.triangle`. -/
theorem triangleLaw {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.TriangleLaw S :=
  TriangleCheck.triangle S

/-! ## The `ℂ` duality normalisation at the unit -/

/-- `κ` at the unit is `1`, at `ℂ`: the `ℝ` proof of `FusionCategory.kappa_unit`
is field-generic (kept here because the conditional theorem below uses it). -/
theorem kappa_unit_c {n : ℕ} (S : FusionSystem n ℂ) (hn : 0 < n) :
    S.kappa ⟨0, hn⟩ = 1 := by
  have hd : S.ring.dual ⟨0, hn⟩ = ⟨0, hn⟩ := S.ring.dual_zero hn
  have hN : 0 < S.ring.N ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [S.ring.left_unit hn ⟨0, hn⟩ ⟨0, hn⟩]
    simp
  have hunit := S.F_unit_left hn ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ hN
  simp only [if_true] at hunit
  have hsnake := S.snake_left hn ⟨0, hn⟩
  rw [hd, hunit, mul_one] at hsnake
  exact hsnake

/-! ## Task 1.1 -- `Cx.pivotal_ext` -/

/-- A pivotal structure over `ℂ` is determined by its dimension function
(field-generic copy of `FusionCategory.pivotal_ext`). -/
theorem cx_pivotal_ext : FusionCategory.Cx.pivotal_ext := by
  intro n S P P' h
  obtain ⟨p, pu, pm⟩ := P
  obtain ⟨p', pu', pm'⟩ := P'
  have hp : p = p' := by
    funext i
    apply Units.ext
    have hd := h i
    rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq] at hd
    exact mul_right_cancel₀ (S.kappa_ne_zero i) hd
  subst hp
  rfl

/-! ## Task 1.1 -- the conditional theorem at `ℂ` -/

/-- **The frozen `Cx.eno823_of_pseudoUnitary`**: a pivotal structure over `ℂ`
whose dimensions are positive (`Pos`) and multiplicative on the fusion ring is
spherical with the FP-dimensions, given `PFUnique`.  Port of
`FusionCategory.eno823_of_pseudoUnitary`: the `Pos` witnesses turn the `ℂ`
eigenvector equation into a real one by injectivity of `algebraMap ℝ ℂ`, so that
`PFUnique` (an `ℝ` statement) applies. -/
theorem cx_eno823_of_pseudoUnitary : FusionCategory.Cx.eno823_of_pseudoUnitary := by
  intro n S hn hFP huniq P hU
  classical
  choose r hrpos hdr using hU.pos
  -- `hdr : ∀ i, dim P i = ↑(r i)`
  have hdim0 : ∀ (hn' : 0 < n), r ⟨0, hn'⟩ = 1 := by
    intro hn'
    have h0 : (⟨0, hn'⟩ : Fin n) = ⟨0, hn⟩ := by simp
    have hdim : dim P ⟨0, hn'⟩ = 1 := by
      rw [PivotalStructure.dim_eq, h0, P.pVal_unit hn, kappa_unit_c S hn, mul_one]
    have h2 : ((r ⟨0, hn'⟩ : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [← hdr ⟨0, hn'⟩, hdim]
      simp
    exact Complex.ofReal_injective h2
  have hmul : ∀ i kk : Fin n,
      (∑ j : Fin n, (S.ring.N i j kk : ℝ) * r j) = r i * r kk := by
    intro i kk
    have h : (∑ j : Fin n, (S.ring.N i j kk : ℂ) * ((r j : ℝ) : ℂ))
        = ((r i : ℝ) : ℂ) * ((r kk : ℝ) : ℂ) := by
      simpa only [hdr] using hU.mult i kk
    apply Complex.ofReal_injective
    push_cast
    exact h
  have hrd : r = hFP.fpdim := huniq r hrpos hdim0 hmul
  refine ⟨P, ?_, ?_⟩
  · rw [P.isSpherical_iff hn]
    intro i
    have h1 : dim P (S.ring.dual i) = dim P i := by
      rw [hdr, hdr, congrFun hrd (S.ring.dual i), congrFun hrd i, hFP.dual_eq i]
    rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, P.pVal_dual hn i] at h1
    field_simp at h1
    rw [← h1]
  · intro i
    rw [hdr, congrFun hrd i]
    simp

/-- Shape guard: the proposition proved above is the frozen def, unrolled by
`rfl`. -/
example : FusionCategory.Cx.eno823_of_pseudoUnitary =
    (∀ {n : ℕ} {S : FusionSystem n ℂ}, 0 < n →
      ∀ (hFP : S.ring.FPData), PFUnique S.ring hFP →
        ∀ (P : PivotalStructure S), Cx.IsPseudoUnitaryPivotal P → ENO823 S hFP) := rfl

/-! ## Task 1.5(a) -- exact ⇒ bare at `ℂ` -/

/-- **The frozen `Cx.eno823_of_exact`**: the exact form implies the bare form
under the pseudo-unitarity and `J_match` antecedents; the unique witness' two
conjuncts are exactly `ENO823`'s. -/
theorem cx_eno823_of_exact
    (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    FusionCategory.Cx.eno823_of_exact derivedJ := by
  intro n S hFP h hPU hJ
  obtain ⟨P, ⟨hsp, hpos, hdim⟩, huniqP⟩ := h hPU hJ
  exact ⟨P, hsp, hdim⟩

/-! ## Task 1.5(a) -- bare ⇒ exact at `ℂ` -/

/-- **The frozen `Cx.eno823_of_bare`**: the bare form implies the exact form at
`ℂ`, with no side condition.  The `Pos` conjunct uses the real FP-dimension as
its witness; uniqueness is `Cx.pivotal_ext`. -/
theorem cx_eno823_of_bare
    (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    FusionCategory.Cx.eno823_of_bare derivedJ := by
  intro n S hFP hbare hPU hJm
  obtain ⟨P, hsp, hdim⟩ := hbare
  refine ⟨P, ⟨hsp, ?_, hdim⟩, ?_⟩
  · intro i
    exact ⟨hFP.fpdim i, hFP.pos i, by rw [hdim i]; simp⟩
  · intro P' hP'
    exact cx_pivotal_ext P' P (fun i => by rw [hP'.2.2 i, hdim i])

/-- **Task 1.5(a) at `ℂ`, as an equivalence**: the exact form holds iff the bare
form holds under its two antecedents. -/
theorem exact_iff_bare (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ)
    {n : ℕ} {S : FusionSystem n ℂ} (hFP : S.ring.FPData) :
    ENO823ExactC derivedJ S hFP ↔
      (IsPseudoUnitaryC S hFP → J_match S (derivedJ S) → ENO823 S hFP) :=
  ⟨fun h hPU hJ => cx_eno823_of_exact derivedJ hFP h hPU hJ,
   fun h hPU hJ => cx_eno823_of_bare derivedJ hFP (h hPU hJ) hPU hJ⟩

/-! ## Statement-fidelity guards (`rfl`)

Each frozen `def` is checked to be *definitionally* the `∀`-closure displayed in
`Statements.lean`'s docstring, so the theorems above are proofs of the frozen
statements and not of a re-rendering (proposal Appendix `app:statements`,
`sec:fidelity`). -/

section ShapeGuards

example {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.EvDual S = (∀ i : Fin n, S.ev (S.ring.dual i) = S.ev i) := rfl

example {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)
    (h : FusionCategory.EvDual S) :
    FusionCategory.dimENO_eq_dim S h =
      (∀ (P : PivotalStructure S) (i : Fin n), FusionCategory.dimENO P i = dim P i) := rfl

example {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.dimENO_eq_dim_of_selfdual S =
      (∀ (P : PivotalStructure S) (i : Fin n),
        S.ring.dual i = i → FusionCategory.dimENO P i = dim P i) := rfl

example {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.J_coherent_forms_agree S =
      (FusionCategory.J_coherent_qualified S ↔ FusionCategory.J_coherent_retained S) := rfl

example {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k) :
    FusionCategory.TriangleLaw S =
      (∀ (hn : 0 < n) (a c d : Fin n), 0 < S.ring.N a c d →
        S.F a ⟨0, hn⟩ c d a c = 1) := rfl

example :
    FusionCategory.Cx.pivotal_ext =
      (∀ {n : ℕ} {S : FusionSystem n ℂ} (P P' : PivotalStructure S),
        (∀ i : Fin n, dim P i = dim P' i) → P = P') := rfl

example (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    FusionCategory.Cx.eno823_of_exact derivedJ =
      (∀ {n : ℕ} {S : FusionSystem n ℂ} (hFP : S.ring.FPData),
        ENO823ExactC derivedJ S hFP → IsPseudoUnitaryC S hFP →
          J_match S (derivedJ S) → ENO823 S hFP) := rfl

example (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) :
    FusionCategory.Cx.eno823_of_bare derivedJ =
      (∀ {n : ℕ} {S : FusionSystem n ℂ} (hFP : S.ring.FPData),
        ENO823 S hFP → ENO823ExactC derivedJ S hFP) := rfl

end ShapeGuards

end Coverage

#print axioms Coverage.evDual
#print axioms Coverage.dimENO_eq_dim
#print axioms Coverage.dimENO_eq_dim_of_selfdual
#print axioms Coverage.J_coherent_forms_agree
#print axioms Coverage.triangleLaw
#print axioms Coverage.kappa_unit_c
#print axioms Coverage.cx_pivotal_ext
#print axioms Coverage.cx_eno823_of_pseudoUnitary
#print axioms Coverage.cx_eno823_of_exact
#print axioms Coverage.cx_eno823_of_bare
#print axioms Coverage.exact_iff_bare
