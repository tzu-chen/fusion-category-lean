import FusionCategory.Statements
import FusionCategory.DimMult

/-!
# D-gauge — the vertex gauge action on the signature (WP1 Task 1.4)

`FusionSystem` carries `ev : Fin n → k` (evaluation `X_{i*} ⊗ X_i → 1`) and
`coev : Fin n → k` (coevaluation `1 → X_i ⊗ X_{i*}`).  Only their product enters
the snake equations and `κ = coev * ev`, so the *vertex gauge*
`coev i ↦ λ i * coev i`, `ev i ↦ ev i / λ i` (every other field untouched)
sends a `FusionSystem` to a `FusionSystem` and fixes `κ`.  This file proves that,
characterises the gauge parameters that preserve the Task 1.4 normalisation
`EvDual` (exactly the dual-invariant ones), and proves that the categorical
dimension, sphericity, the ℂ pseudo-unitarity predicate and the bare target
`ENO823` are gauge-invariant — so that the target is a statement about the datum
and not about a choice of evaluations, which is what Task 1.4 is for.

Nothing here edits an existing file, and nothing is restated: the frozen
`EvDual` is proved *of the gauged system*, and the `ℝ` originals are untouched.

Axiom budget of every declaration: `[propext, Classical.choice, Quot.sound]`
(see the `#print axioms` lines at the end).
-/

universe u

open FusionCategory

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## The algebra the snakes see -/

/-- The gauge identity behind the snake equations: `(λ c) (e / λ) = c e`.  The
product `coev i * ev i = κ i` is what the snakes see, and the gauge preserves
it. -/
theorem gauge_coev_mul_ev (S : FusionSystem n k) (lam : Fin n → kˣ) (i : Fin n) :
    ((lam i : k) * S.coev i) * (S.ev i / (lam i : k)) = S.coev i * S.ev i := by
  rw [div_eq_mul_inv]
  calc ((lam i : k) * S.coev i) * (S.ev i * ((lam i : k))⁻¹)
      = S.coev i * S.ev i * ((lam i : k) * ((lam i : k))⁻¹) := by ring
    _ = S.coev i * S.ev i := by rw [mul_inv_cancel₀ (lam i).ne_zero, mul_one]

/-! ## The gauge on a `FusionSystem` -/

/-- **The vertex gauge on the corrected signature.**  `coev` is rescaled by
`λ`, `ev` by `λ⁻¹`, and every other field is kept: `F`, `Finv`, `J` and all
their laws do not mention `ev`/`coev`, and the snake equations see only the
product `coev i * ev i = κ i`, which the gauge fixes.

The gauge parameter must be *dual-invariant* (`hlam`): that is exactly the
condition under which the Task 1.4 normalisation `ev_{i*} = ev_i` survives the
gauge (`gauge_ev_dual_iff` below).  In other words the gauge group of the
corrected signature is the dual-invariant subgroup of `(kˣ)^n`. -/
def gauge (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) : FusionSystem n k where
  ring := S.ring
  mult_free := S.mult_free
  F := S.F
  F_support := S.F_support
  pentagon := S.pentagon
  F_unit_left := S.F_unit_left
  F_unit_right := S.F_unit_right
  Finv := S.Finv
  Finv_support := S.Finv_support
  Finv_comp := S.Finv_comp
  F_comp_inv := S.F_comp_inv
  ev := fun i => S.ev i / (lam i : k)
  coev := fun i => (lam i : k) * S.coev i
  ev_ne_zero := fun i => div_ne_zero (S.ev_ne_zero i) (lam i).ne_zero
  coev_ne_zero := fun i => mul_ne_zero (lam i).ne_zero (S.coev_ne_zero i)
  snake_left := by
    intro hn i
    rw [gauge_coev_mul_ev S lam i]
    exact S.snake_left hn i
  snake_right := by
    intro hn i
    rw [gauge_coev_mul_ev S lam i]
    exact S.snake_right hn i
  ev_dual := by
    intro i
    rw [hlam i, S.ev_dual i]
  J := S.J
  J_ne_zero := S.J_ne_zero
  J_unit_left := S.J_unit_left
  J_unit_right := S.J_unit_right
  J_dual := S.J_dual
  J_coherent := S.J_coherent

/-- The gauge does not move the fusion ring (nor `F`, `Finv`, `J`): only `ev`
and `coev` are rescaled. -/
theorem gauge_ring (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) : (gauge S lam hlam).ring = S.ring := rfl

/-- **The gauge fixes `κ`**: this is the whole content of "it preserves the
snakes and `κ`" — the gauged datum is the same fusion system with a different
choice of evaluation/coevaluation normalisation. -/
theorem gauge_kappa (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (i : Fin n) :
    (gauge S lam hlam).kappa i = S.kappa i := by
  have h : ((lam i : k) * S.coev i) * (S.ev i / (lam i : k)) = S.coev i * S.ev i :=
    gauge_coev_mul_ev S lam i
  simpa only [FusionSystem.kappa, gauge] using h

/-! ## Which gauge parameters preserve the Task 1.4 normalisation -/

/-- **The stabiliser of `ev_{i*} = ev_i` is exactly the dual-invariant gauges.**
A general vertex gauge sends the evaluation family to `ev i / λ i`; the gauged
family is again dual-invariant iff `λ` is.  (Proof: on the corrected signature
`ev_{i*} = ev_i ≠ 0`, so `ev i / λ_{i*} = ev i / λ i` forces `λ_{i*} = λ i`.)

This is the precise sense in which the Task 1.4 normalisation is a *gauge
slice*: the transverse gauge directions `λ_{i*}/λ_i` are what the `ev_dual`
field of the signature fixes. -/
theorem gauge_ev_dual_iff (S : FusionSystem n k) (lam : Fin n → kˣ) :
    (∀ i : Fin n, S.ev (S.ring.dual i) / (lam (S.ring.dual i) : k) = S.ev i / (lam i : k))
      ↔ ∀ i : Fin n, lam (S.ring.dual i) = lam i := by
  constructor
  · intro h i
    have hi := h i
    rw [S.ev_dual i] at hi
    have h1 : (lam (S.ring.dual i) : k) = (lam i : k) := by
      field_simp at hi
      exact (mul_left_cancel₀ (S.ev_ne_zero i) hi).symm
    exact Units.ext h1
  · intro h i
    rw [h i, S.ev_dual i]

/-! ## Gauge invariance of the dimensions and of the target

The gauge leaves `F`, `J`, the fusion ring and `κ` alone, so it leaves
`PivotalStructure S` alone too (a pivotal structure sees only `S.ring.N` and
`S.J`), and by `gauge_kappa` it leaves every `dim P i` alone.  Hence
sphericity, the ℂ pseudo-unitarity equation and the bare target are the same
statement at every point of the gauge orbit. -/

/-- **The gauge on pivotal structures**: a pivotal structure sees only
`S.ring.N` and `S.J` (`p_mon`), which the gauge does not touch, so it carries
over with the same `p`. -/
def gaugePivotal (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure S) :
    PivotalStructure (gauge S lam hlam) where
  p := P.p
  p_unit := P.p_unit
  p_mon := by
    intro i j kk hN
    exact P.p_mon i j kk hN

/-- The inverse transport of pivotal structures along the gauge. -/
def ungaugePivotal (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i)
    (P : PivotalStructure (gauge S lam hlam)) : PivotalStructure S where
  p := P.p
  p_unit := P.p_unit
  p_mon := by
    intro i j kk hN
    exact P.p_mon i j kk hN

/-- **The categorical dimension is gauge-invariant.** -/
theorem gauge_dim (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure S) (i : Fin n) :
    dim (gaugePivotal S lam hlam P) i = dim P i := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, gauge_kappa S lam hlam i]
  rfl

/-- The same in the other direction, for a pivotal structure of the gauged
datum. -/
theorem ungauge_dim (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i)
    (P : PivotalStructure (gauge S lam hlam)) (i : Fin n) :
    dim (ungaugePivotal S lam hlam P) i = dim P i := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, gauge_kappa S lam hlam i]
  rfl

/-- The two pivotal transports are mutually inverse on the nose: a pivotal
structure sees only `p`, and both maps keep it. -/
theorem ungaugePivotal_gaugePivotal (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure S) :
    ungaugePivotal S lam hlam (gaugePivotal S lam hlam P) = P := by
  cases P
  rfl

/-- The inverse round trip. -/
theorem gaugePivotal_ungaugePivotal (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure (gauge S lam hlam)) :
    gaugePivotal S lam hlam (ungaugePivotal S lam hlam P) = P := by
  cases P
  rfl

/-- **Sphericity is gauge-invariant.** -/
theorem gauge_isSpherical_iff (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure S) :
    PivotalStructure.IsSpherical (gaugePivotal S lam hlam P)
      ↔ PivotalStructure.IsSpherical P := by
  constructor
  · intro h i
    have hi : dim (gaugePivotal S lam hlam P) (S.ring.dual i)
        = dim (gaugePivotal S lam hlam P) i := h i
    rwa [gauge_dim S lam hlam P (S.ring.dual i), gauge_dim S lam hlam P i] at hi
  · intro h i
    have hi : dim (gaugePivotal S lam hlam P) (S.ring.dual i)
        = dim (gaugePivotal S lam hlam P) i := by
      rw [gauge_dim S lam hlam P (S.ring.dual i), gauge_dim S lam hlam P i]
      exact h i
    exact hi

/-- Sphericity of a pivotal structure of the gauged datum, read back on `S`. -/
theorem ungauge_isSpherical_iff (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i)
    (P : PivotalStructure (gauge S lam hlam)) :
    PivotalStructure.IsSpherical (ungaugePivotal S lam hlam P)
      ↔ PivotalStructure.IsSpherical P := by
  constructor
  · intro h i
    have hi : dim (ungaugePivotal S lam hlam P) (S.ring.dual i)
        = dim (ungaugePivotal S lam hlam P) i := h i
    rwa [ungauge_dim S lam hlam P (S.ring.dual i), ungauge_dim S lam hlam P i] at hi
  · intro h i
    have hi : dim (ungaugePivotal S lam hlam P) (S.ring.dual i)
        = dim (ungaugePivotal S lam hlam P) i := by
      rw [ungauge_dim S lam hlam P (S.ring.dual i), ungauge_dim S lam hlam P i]
      exact h i
    exact hi

/-- **The solution set of ENO 8.23 is gauge-invariant**: the three conjuncts the
target asks of its witness — spherical, positive dimensions, dimensions equal to
the `FP`-dimensions — hold of `ungaugePivotal P` exactly when they hold of `P`.
(`dim` is `ungauge_dim`, sphericity `ungauge_isSpherical_iff`.) -/
theorem ungauge_pivotal_solution_iff {n : ℕ} (S : FusionSystem n ℝ) (lam : Fin n → ℝˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (hFP : S.ring.FPData)
    (P : PivotalStructure (gauge S lam hlam)) :
    ((ungaugePivotal S lam hlam P).IsSpherical
        ∧ (∀ i, 0 < dim (ungaugePivotal S lam hlam P) i)
        ∧ (∀ i, dim (ungaugePivotal S lam hlam P) i = hFP.fpdim i))
      ↔ (P.IsSpherical ∧ (∀ i, 0 < dim P i) ∧ (∀ i, dim P i = hFP.fpdim i)) := by
  have hd : ∀ i, dim (ungaugePivotal S lam hlam P) i = dim P i :=
    fun i => ungauge_dim S lam hlam P i
  have hsp : (ungaugePivotal S lam hlam P).IsSpherical ↔ P.IsSpherical :=
    ungauge_isSpherical_iff S lam hlam P
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨hsp.mp a, fun i => by rw [← hd i]; exact b i,
      fun i => by rw [← hd i]; exact c i⟩
  · rintro ⟨a, b, c⟩
    exact ⟨hsp.mpr a, fun i => by rw [hd i]; exact b i,
      fun i => by rw [hd i]; exact c i⟩

/-- **The bare target is gauge-invariant**, in the form that avoids the
`FPData` bookkeeping: "there is a spherical pivotal structure with dimensions
`f`" is the same statement at every point of the gauge orbit.  Read at
`f = hFP.fpdim` this is `ENO823`; with `gauge_kappa` and `gauge_dim` it is Task
1.4's point — the target is a statement about the datum, not about the choice of
evaluations. -/
theorem gauge_exists_pivotal_iff (S : FusionSystem n k) [Algebra ℝ k] (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (f : Fin n → ℝ) :
    (∃ P : PivotalStructure (gauge S lam hlam),
        PivotalStructure.IsSpherical P ∧ ∀ i : Fin n, dim P i = algebraMap ℝ k (f i))
      ↔ ∃ P : PivotalStructure S,
        PivotalStructure.IsSpherical P ∧ ∀ i : Fin n, dim P i = algebraMap ℝ k (f i) := by
  constructor
  · rintro ⟨P, hsp, hdim⟩
    exact ⟨ungaugePivotal S lam hlam P, (ungauge_isSpherical_iff S lam hlam P).2 hsp,
      fun i => by rw [ungauge_dim S lam hlam P i]; exact hdim i⟩
  · rintro ⟨P, hsp, hdim⟩
    exact ⟨gaugePivotal S lam hlam P, (gauge_isSpherical_iff S lam hlam P).2 hsp,
      fun i => by rw [gauge_dim S lam hlam P i]; exact hdim i⟩

/-- **`ENO823` is gauge-invariant**: the bare target holds of the gauged datum
exactly when it holds of the datum.  (Read off `gauge_exists_pivotal_iff` at
`f = hFP.fpdim`.) -/
theorem gauge_eno823_iff (S : FusionSystem n k) [Algebra ℝ k] (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (hFP : S.ring.FPData) :
    ENO823 (gauge S lam hlam) hFP ↔ ENO823 S hFP :=
  gauge_exists_pivotal_iff S lam hlam hFP.fpdim

/-- **Pseudo-unitarity at `ℂ` is gauge-invariant**: the ℓ² sum `Σ_i κ_i κ_{i*}`
is untouched by the gauge. -/
theorem gauge_sum_kappa (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) :
    (∑ i : Fin n, (gauge S lam hlam).kappa i
        * (gauge S lam hlam).kappa ((gauge S lam hlam).ring.dual i))
      = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gauge_kappa S lam hlam i, gauge_kappa S lam hlam]
  rfl

/-- **`IsPseudoUnitaryC` is gauge-invariant** (it is stated with `κ`). -/
theorem gauge_isPseudoUnitaryC_iff {n : ℕ} (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (hFP : S.ring.FPData) :
    IsPseudoUnitaryC (gauge S lam hlam) hFP ↔ IsPseudoUnitaryC S hFP := by
  simp only [IsPseudoUnitaryC]
  rw [gauge_sum_kappa S lam hlam]
  exact Iff.rfl

/-- **(M) is gauge-invariant**: the vertex gauge fixes the fusion ring, the twist
`J` and `κ` (`gauge_ring`, `gauge_kappa`), and those three are the whole of
`DimMultiplicative`.  So the multiplicativity hypothesis of the analytic chain is
a property of the datum, not of the choice of evaluations — the companion of
`gauge_eno823_iff` for the hypothesis side of the conditional theorem. -/
theorem gauge_dimMult_iff (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) :
    DimMultiplicative (gauge S lam hlam) ↔ DimMultiplicative S := by
  have hsum : ∀ a b : Fin n,
      (∑ c : Fin n, (gauge S lam hlam).ring.N a b c * (gauge S lam hlam).J a b c
        * (gauge S lam hlam).kappa c)
      = ∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c := by
    intro a b
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [gauge_kappa S lam hlam c]
    rfl
  constructor
  · intro h a b
    rw [← hsum a b, h a b, gauge_kappa S lam hlam a, gauge_kappa S lam hlam b]
  · intro h a b
    rw [hsum a b, h a b, gauge_kappa S lam hlam a, gauge_kappa S lam hlam b]

/-- The `ℓ²` sum over the duality normalisation is gauge-invariant at any scalar
field — the field-generic form of `gauge_sum_kappa` below, which is what the `ℝ`
pseudo-unitarity equation `IsPseudoUnitary` of `DimMult.lean` needs. -/
theorem gauge_sum_kappa_of_field (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) :
    (∑ i : Fin n, (gauge S lam hlam).kappa i
        * (gauge S lam hlam).kappa ((gauge S lam hlam).ring.dual i))
      = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gauge_kappa S lam hlam i, gauge_kappa S lam hlam]
  rfl

/-- **The `ℝ` pseudo-unitarity equation is gauge-invariant.**  With
`gauge_dimMult_iff` and `gauge_exists_pivotal_iff` this says that all three
hypotheses of `DimMult.eno823Exact_of_dimMult_pseudoUnitary` — (M),
`IsPseudoUnitary`, and one pivotal structure — are properties of the datum at
every point of the gauge orbit, so the conditional theorem's conclusion is a
statement about the fusion system and not about the choice of evaluations. -/
theorem gauge_isPseudoUnitary_iff {n : ℕ} (S : FusionSystem n ℝ) (lam : Fin n → ℝˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (hFP : S.ring.FPData) :
    IsPseudoUnitary (gauge S lam hlam) hFP ↔ IsPseudoUnitary S hFP := by
  simp only [IsPseudoUnitary]
  rw [gauge_sum_kappa_of_field S lam hlam]
  exact Iff.rfl

/-- **ENO 8.23's exact statement is gauge-invariant.**  `ENO823Exact` is
`IsPseudoUnitary → ∃! P, (spherical ∧ positive ∧ dim = FPdim)`.  The hypothesis
is `gauge_isPseudoUnitary_iff`, and the solution sets correspond under the two
pivotal transports (`ungauge_pivotal_solution_iff`), which are mutually inverse
(`ungaugePivotal_gaugePivotal`, `gaugePivotal_ungaugePivotal`); so existence and
uniqueness transfer both ways.  The exact-form companion of `gauge_eno823_iff`:
the conditional theorem's conclusion is a statement about the datum, not about
the choice of evaluations. -/
theorem gauge_eno823Exact_iff {n : ℕ} (S : FusionSystem n ℝ) (lam : Fin n → ℝˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (hFP : S.ring.FPData) :
    ENO823Exact (gauge S lam hlam) hFP ↔ ENO823Exact S hFP := by
  have hp := gauge_isPseudoUnitary_iff S lam hlam hFP
  constructor
  · intro H hPU
    obtain ⟨P, hP, huniq⟩ := H (hp.mpr hPU)
    refine ⟨ungaugePivotal S lam hlam P, ?_, ?_⟩
    · exact (ungauge_pivotal_solution_iff S lam hlam hFP P).mpr hP
    · intro P' hP'
      have h1 : gaugePivotal S lam hlam P' = P := by
        refine huniq _ ?_
        exact (ungauge_pivotal_solution_iff S lam hlam hFP
          (gaugePivotal S lam hlam P')).mp (by rwa [ungaugePivotal_gaugePivotal S lam hlam P'])
      rw [← ungaugePivotal_gaugePivotal S lam hlam P', h1]
  · intro H hPU
    obtain ⟨P, hP, huniq⟩ := H (hp.mp hPU)
    refine ⟨gaugePivotal S lam hlam P, ?_, ?_⟩
    · exact (ungauge_pivotal_solution_iff S lam hlam hFP
        (gaugePivotal S lam hlam P)).mp (by rwa [ungaugePivotal_gaugePivotal S lam hlam P])
    · intro P' hP'
      have h1 : ungaugePivotal S lam hlam P' = P := by
        refine huniq _ ?_
        exact (ungauge_pivotal_solution_iff S lam hlam hFP P').mpr hP'
      rw [← gaugePivotal_ungaugePivotal S lam hlam P', h1]

/-! ## The gauge is a group action -/

/-- Pointwise: the gauge composes, `(gauge (gauge S λ) μ).ev = ev / (λ μ)`. -/
theorem gauge_ev_comp (S : FusionSystem n k) (lam mu : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i)
    (hmu : ∀ i, mu (S.ring.dual i) = mu i) (i : Fin n) :
    (gauge (gauge S lam hlam) mu hmu).ev i
      = S.ev i / ((lam i * mu i : kˣ) : k) := by
  simp only [gauge, Units.val_mul, div_div]

/-- Pointwise: the gauge composes on `coev`, `(gauge (gauge S λ) μ).coev = μ λ coev`. -/
theorem gauge_coev_comp (S : FusionSystem n k) (lam mu : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i)
    (hmu : ∀ i, mu (S.ring.dual i) = mu i) (i : Fin n) :
    (gauge (gauge S lam hlam) mu hmu).coev i
      = ((lam i * mu i : kˣ) : k) * S.coev i := by
  simp only [gauge, Units.val_mul]
  ring


/-- **The hypothesis of the conditional form is gauge-invariant too**: the ℂ
predicate `IsPseudoUnitaryPivotal` (positivity of `dim`, multiplicativity on the
fusion ring) is the same statement at every point of the gauge orbit, because
`dim` is (`gauge_dim`) and the structure constants are. -/
theorem gauge_isPseudoUnitaryPivotal_iff {n : ℕ} (S : FusionSystem n ℂ) (lam : Fin n → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (P : PivotalStructure S) :
    Cx.IsPseudoUnitaryPivotal (gaugePivotal S lam hlam P)
      ↔ Cx.IsPseudoUnitaryPivotal P := by
  constructor
  · intro h
    exact ⟨fun i => by rw [← gauge_dim S lam hlam P i]; exact h.pos i,
      fun i kk => by simpa only [gauge_ring, gauge_dim S lam hlam P] using h.mult i kk⟩
  · intro h
    exact ⟨fun i => by rw [gauge_dim S lam hlam P i]; exact h.pos i,
      fun i kk => by simpa only [gauge_ring, gauge_dim S lam hlam P] using h.mult i kk⟩

#print axioms FusionCategory.gauge_coev_mul_ev
#print axioms FusionCategory.gauge
#print axioms FusionCategory.gauge_kappa
#print axioms FusionCategory.gauge_ring
#print axioms FusionCategory.gauge_ev_dual_iff
#print axioms FusionCategory.gauge_dim
#print axioms FusionCategory.gauge_isSpherical_iff
#print axioms FusionCategory.gaugePivotal
#print axioms FusionCategory.ungaugePivotal
#print axioms FusionCategory.ungauge_dim
#print axioms FusionCategory.ungauge_isSpherical_iff
#print axioms FusionCategory.gauge_exists_pivotal_iff
#print axioms FusionCategory.gauge_sum_kappa
#print axioms FusionCategory.gauge_eno823_iff
#print axioms FusionCategory.gauge_isPseudoUnitaryC_iff
#print axioms FusionCategory.gauge_isPseudoUnitaryPivotal_iff
#print axioms FusionCategory.gauge_ev_comp
#print axioms FusionCategory.gauge_coev_comp
#print axioms FusionCategory.gauge_dimMult_iff
#print axioms FusionCategory.gauge_sum_kappa_of_field
#print axioms FusionCategory.gauge_isPseudoUnitary_iff
#print axioms FusionCategory.ungaugePivotal_gaugePivotal
#print axioms FusionCategory.gaugePivotal_ungaugePivotal
#print axioms FusionCategory.ungauge_pivotal_solution_iff
#print axioms FusionCategory.gauge_eno823Exact_iff

end FusionCategory
