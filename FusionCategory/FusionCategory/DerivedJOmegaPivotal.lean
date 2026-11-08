import FusionCategory.DerivedJCoherent

/-!
# The cohomological (pivotal) class for the associator-only coefficient `omegaCoeff`

`FusionMat.omegaCoeff S a b c` is the `(c,c)`-entry of the `(−)**` tensorator written in
`F`/`Finv` alone (`DoubleDualTensorator.lean`).  The fourth law for `derivedJGen` reduces to
the associator-only cocycle identity for it (`derivedJGen_coherent_iff_omegaCoeff_cocycle`).

This file records the *cohomological* part of that obligation:

* `omegaCoeff_ne_zero_of_omegaNe` — the `OmegaNe` bundle is exactly what makes the ratio
  `omegaCoeff` a nonzero scalar (so that the two sides of the identity may be cancelled).
* `omegaCocycle_rescale_iff` — **the cocycle identity is invariant under rescaling `ω` by a
  coboundary** `φ a * φ b / φ c`.  Consequently the truth of the identity depends only on
  the cohomology class of `ω`: `ω` may be normalised by any nowhere-zero `φ` before it is
  proved.
* `derivedJGen_qualified_of_omegaCoeff_coboundary` and
  `derivedJGen_coherent_of_omegaCoeff_coboundary` — if the associator-only coefficient is
  itself a coboundary then the two sides of the cocycle identity are *literally equal* on
  `OmegaNe` tuples, so the fourth law holds there.  These are the associator-only
  (`F`/`Finv`-only) forms of `DerivedJCoherent.coherent_free_of_coboundary`, which was
  stated for the `ev`/`coev`-built table `derivedJGen`: here the trivialising `φ` is read
  off the associator alone.

## Status of the class

`ω` a coboundary is not a hypothesis that can be discharged in general: for the honest
double-dual tensorator a trivialising `φ` *is* a pivotal structure, so the hypothesis holds
exactly on pivotal data (Ng–Schauenburg: `(−)**` is monoidally isomorphic to the identity
iff the category is pivotal).  The theorems here therefore cover the pivotal class, not the
general case; they are stated so that pivotal-ness of a datum can be checked from the
associator alone, without touching `ev`/`coev`.

Axiom budget: `[propext, Classical.choice, Quot.sound]` — see the `#print axioms` lines.
-/

namespace FusionCategory

set_option linter.unusedVariables false

open FusionMat

variable {n : ℕ} {k : Type*} [Field k]

/-- **`OmegaNe` makes `omegaCoeff` nonzero.**  The bundle carries precisely the two
nonvanishing facts of the two products in the ratio. -/
theorem omegaCoeff_ne_zero_of_omegaNe (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (h : OmegaNe S hn a b c) : FusionMat.omegaCoeff S a b c ≠ 0 := by
  rw [FusionMat.omegaCoeff, dif_pos hn]
  exact div_ne_zero h.2 h.1

/-- The two sides of the rescaled identity, with the `φ`-factors collected. -/
private theorem omega_rescale_lhs
    (ω : Fin n → Fin n → Fin n → k) (φ : Fin n → k) (hφ : ∀ i, φ i ≠ 0)
    (a b c d e : Fin n) :
    (ω a b e * (φ a * φ b / φ e)) * (ω e c d * (φ e * φ c / φ d))
      = (ω a b e * ω e c d) * ((φ a * φ b * φ c) / φ d) := by
  have ha := hφ a; have hb := hφ b; have hc := hφ c
  have hd := hφ d; have he := hφ e
  field_simp

private theorem omega_rescale_rhs
    (ω : Fin n → Fin n → Fin n → k) (φ : Fin n → k) (hφ : ∀ i, φ i ≠ 0)
    (a b c d f : Fin n) :
    (ω b c f * (φ b * φ c / φ f)) * (ω a f d * (φ a * φ f / φ d))
      = (ω b c f * ω a f d) * ((φ a * φ b * φ c) / φ d) := by
  have ha := hφ a; have hb := hφ b; have hc := hφ c
  have hd := hφ d; have hf := hφ f
  field_simp

/-- **The cocycle identity depends only on the cohomology class of `ω`.**

`ω` satisfies the associator cocycle identity iff `ω` rescaled by the coboundary
`φ a * φ b / φ c` of a nowhere-zero `φ` does.  No associator algebra enters: the
`φ`-factors cancel, so a datum may be gauge-normalised before the identity is proved. -/
theorem omegaCocycle_rescale_iff (S : FusionSystem n k)
    (ω : Fin n → Fin n → Fin n → k) (φ : Fin n → k) (hφ : ∀ i, φ i ≠ 0) :
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        (ω a b e * (φ a * φ b / φ e)) * (ω e c d * (φ e * φ c / φ d))
          = (ω b c f * (φ b * φ c / φ f)) * (ω a f d * (φ a * φ f / φ d))) ↔
      (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        ω a b e * ω e c d = ω b c f * ω a f d) := by
  have key : ∀ a b c d : Fin n, ((φ a * φ b * φ c) / φ d) ≠ 0 := by
    intro a b c d
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c)) (hφ d)
  constructor
  · intro h a b c d e f h1 h2 h3 h4
    have hh := h a b c d e f h1 h2 h3 h4
    rw [omega_rescale_lhs ω φ hφ a b c d e, omega_rescale_rhs ω φ hφ a b c d f] at hh
    exact mul_right_cancel₀ (key a b c d) hh
  · intro h a b c d e f h1 h2 h3 h4
    rw [omega_rescale_lhs ω φ hφ a b c d e, omega_rescale_rhs ω φ hφ a b c d f,
      h a b c d e f h1 h2 h3 h4]

/-- **The fourth law on the coboundary (pivotal) class** — `F`-free form, on `OmegaNe`
tuples.  The trivialising `φ` is read off the *associator only*:
`omegaCoeff S a b c = φ a * φ b / φ c`. -/
theorem derivedJGen_qualified_of_omegaCoeff_coboundary (S : FusionSystem n k) (hn : 0 < n)
    (φ : Fin n → k) (hφ : ∀ i, φ i ≠ 0)
    (hω : ∀ a b c : Fin n, 0 < S.ring.N a b c → FusionMat.omegaCoeff S a b c = φ a * φ b / φ c) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d = derivedJGen S b c f * derivedJGen S a f d := by
  intro a b c d e f h1 h2 h3 h4 h5 h6 h7 h8
  rw [derivedJGen_eq_omegaCoeff_of_omegaNe S hn h5, derivedJGen_eq_omegaCoeff_of_omegaNe S hn h6,
    derivedJGen_eq_omegaCoeff_of_omegaNe S hn h7, derivedJGen_eq_omegaCoeff_of_omegaNe S hn h8,
    hω a b e h1, hω e c d h2, hω b c f h3, hω a f d h4]
  have ha := hφ a; have hb := hφ b; have hc := hφ c
  have hd := hφ d; have he := hφ e; have hf := hφ f
  field_simp

/-- **The fourth law on the coboundary (pivotal) class** — `F`-retained form, on `OmegaNe`
tuples. -/
theorem derivedJGen_coherent_of_omegaCoeff_coboundary (S : FusionSystem n k) (hn : 0 < n)
    (φ : Fin n → k) (hφ : ∀ i, φ i ≠ 0)
    (hω : ∀ a b c : Fin n, 0 < S.ring.N a b c → FusionMat.omegaCoeff S a b c = φ a * φ b / φ c) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4 h5 h6 h7 h8
  rw [derivedJGen_qualified_of_omegaCoeff_coboundary S hn φ hφ hω a b c d e f h1 h2 h3 h4
    h5 h6 h7 h8]

/-! ### The class is non-empty: pointed data give an explicit `φ = κ`

The pointed `δ(κ)` theorem (`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed`) says
`derivedJGen S a b c = κ_a κ_b / κ_c`.  Under `OmegaNe` this is a statement about
`omegaCoeff`, i.e. the *associator-only* coefficient of every pointed datum is the
coboundary of the duality normalisation — the explicit pivotal structure of that class. -/

/-- On pointed data the associator-only coefficient is the coboundary of `κ`. -/
theorem omegaCoeff_eq_kappa_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (hN : 0 < S.ring.N a b c)
    (h : OmegaNe S hn a b c) :
    FusionMat.omegaCoeff S a b c = S.kappa a * S.kappa b / S.kappa c := by
  rw [← derivedJGen_eq_omegaCoeff_of_omegaNe S hn h,
    derivedJGen_eq_delta_kappa_of_pointed S hn hP hN]

/-- **Every pointed datum provides a nowhere-zero `φ` trivialising `omegaCoeff`** on the
channels where `OmegaNe` holds; hence the coboundary class of
`derivedJGen_qualified_of_omegaCoeff_coboundary` is inhabited in every `n`. -/
theorem exists_omegaCoeff_coboundary_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) :
    ∃ φ : Fin n → k, (∀ i, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → OmegaNe S hn a b c →
        FusionMat.omegaCoeff S a b c = φ a * φ b / φ c :=
  ⟨S.kappa, S.kappa_ne_zero, fun a b c hN h =>
    omegaCoeff_eq_kappa_of_pointed S hn hP hN h⟩

/-! ### Where the `OmegaNe` reduction loses information

`derivedJGen` is `ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}`, and `OmegaNe` bundles the two divisor
nonvanishing facts of those two comparison scalars.  Where `OmegaNe` fails, one of the two
comparison scalars is `0`, so the *derived* twist is `0` — while `omegaCoeff`, which is the
F/Finv-only reduction, need not be.  These two lemmas make the residual obligation of the
reduction chain exact: the associator-only cocycle identity plus `OmegaNe` on every supported
`F ≠ 0` tuple together give the fourth law; neither is implied by the other. -/

/-- **`OmegaNe` is necessary for `derivedJGen` to be the associator ratio.**  If either
divisor-nonvanishing fact fails, the comparison scalar resp. its counterpart vanishes and
`derivedJGen` is `0` (Lean's total division). -/
theorem derivedJGen_eq_zero_of_not_omegaNe (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (h : ¬ OmegaNe S hn a b c) : derivedJGen S a b c = 0 := by
  by_cases h1 : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
      S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ = 0
  · have hnum : comparisonScalar S a b c = 0 := by
      rw [comparisonScalar_def, dif_pos hn, h1]
      simp
    rw [derivedJGen_def, hnum, zero_div]
  · have h2 : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
          (S.ring.dual c) ⟨0, hn⟩ = 0 := by
      by_contra h2'
      exact h ⟨h1, h2'⟩
    have hden : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) = 0 := by
      rw [comparisonScalar_def, dif_pos hn]
      simp only [S.ring.dual_involutive, h2]
      simp
    rw [derivedJGen_def, hden, div_zero]

/-- **The fourth law from the associator-only identity plus the nonvanishing input.**

The two hypotheses are exactly what the reduction chain consumes:

* `hω` — the associator-only cocycle identity for `omegaCoeff` (the target of the boundary /
  block-matrix / mate / functor routes), in its `F`-free form;
* `hne` — every supported `F ≠ 0` tuple satisfies all four `OmegaNe` bundles, i.e. the two
  comparison scalars of `derivedJGen` are nonzero on the channels that matter.  This is *not*
  implied by the axioms (`omegaCoeff_ne_zero_of_omegaNe` shows it is consumed, not produced);
  it is the "`derivedJ_ne_zero`"-shaped input, carried explicitly.

Nothing else is needed: the `F`-vanishing tuples are handled by multiplying through. -/
theorem derivedJGen_coherent_of_omegaCocycle_of_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    (hω : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
          = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d)
    (hne : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d → S.F a b c d e f ≠ 0 →
        OmegaNe S hn a b e ∧ OmegaNe S hn e c d ∧ OmegaNe S hn b c f ∧ OmegaNe S hn a f d) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  by_cases hF : S.F a b c d e f = 0
  · rw [hF, mul_zero, mul_zero]
  · obtain ⟨h5, h6, h7, h8⟩ := hne a b c d e f h1 h2 h3 h4 hF
    rw [derivedJGen_eq_omegaCoeff_of_omegaNe S hn h5,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn h6,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn h7,
      derivedJGen_eq_omegaCoeff_of_omegaNe S hn h8,
      hω a b c d e f h1 h2 h3 h4]

/-! ### Audit -/

#print axioms omegaCoeff_ne_zero_of_omegaNe
#print axioms derivedJGen_eq_zero_of_not_omegaNe
#print axioms derivedJGen_coherent_of_omegaCocycle_of_omegaNe
#print axioms omegaCocycle_rescale_iff
#print axioms omegaCoeff_eq_kappa_of_pointed
#print axioms exists_omegaCoeff_coboundary_of_pointed
#print axioms derivedJGen_qualified_of_omegaCoeff_coboundary
#print axioms derivedJGen_coherent_of_omegaCoeff_coboundary

end FusionCategory
