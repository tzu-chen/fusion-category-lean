/-
# WP4 direction d5 — the functor route: the fourth law for `derivedJGen` from the
antimonoidal structure of the dual functor

`DerivedJScalar.derivedJGen` is the ratio of the *single-dual* comparison scalar
at the tuple and at its dual:

    derivedJGen S a b c = ψ(a,b;c) / ψ(b*,a*;c*),   ψ := `comparisonScalar S`

(`derivedJGen_def`, definitional).  So `derivedJGen` is the entry of the tensorator of
`(−)** = (−)* ∘ (−)*` on the generic factor `(−)*`, and the fourth law for it should
follow from the coherence of the *single* functor `(−)*` — the classical statement that
the dual functor of a rigid monoidal category is antimonoidal (tensor-reversing
monoidal) with structure `ψ : (x ⊗ y)* ⟶ y* ⊗ x*`.  That is the functor route: the
coherence of a composite of monoidal structures is a formal consequence of the
coherences of the factors, so nothing new is needed at the level of `(−)**`.

This file makes that precise at the coefficient level and proves it.

## §1 The field lemma

The reduction is the identity `(A/B)·(C/D) = (A'C')/(B'D')` when the two "defects"
`A·C/A'·C'` and `B·D/B'·D'` are *the same number*; §1 states the needed cross-multiplied
form, valid in any field with Lean's total division.

## §2 The hypothesis: antimonoidal coherence of `(−)*`

`SingleDualCoherent S` is the pentagon of the antimonoidal structure, in the channel
basis, with the associator factors *retained*:

    ψ(a,b;e)·ψ(e,c;d)·F(a,b,c,d,e,f) = ψ(b,c;f)·ψ(a,f;d)·F(c*,b*,a*,d*,f*,e*)

The associator factors are not decoration: on a genuine datum the *naive* form
`ψ(a,b;e)ψ(e,c;d) = ψ(b,c;f)ψ(a,f;d)` is **false**.  Machine check, exact arithmetic
(`.ultramath/smw7f657l/m3/verify_reduction.py`, `probe.py`):

* `Vec^ω_{Z/3}` (dual = negation, ω = ζ₉^{a(b+c-[b+c])}, every `FusionSystem` field
  verified on the finite data, exact group-ring `ℚ[ζ₉]`): the naive form fails on 6 of
  the 27 supported 6-tuples, while `omegaCoeff`-coherence and `derivedJGen`-coherence
  hold on all 27; the retained form above holds on all 27.
* `FibonacciSystem` (non-pointed: the block `F^{τττ}_τ = [[1/φ,1],[1/φ,-1/φ]]` is 2×2,
  every field verified in `ℝ(√5)`): the naive form fails on 2 of the 15 supported
  tuples, the retained form and the target hold on all 15.

So the honest single-dual coherence carries the associators, and with the factors
retained the two defects agree — which is exactly what §3 consumes.  Note the *opposite*
retained form (associator of the original tuple on the right) is also false: the
`F(c*,b*,a*,...)` side is forced.

`twistQualified_of_singleDual_naive` records what the naive form would give anyway: it
*does* imply the fourth law (the associator factors cancel pairwise), which is why the
failure above is a real refutation of the naive route rather than a bookkeeping slip.

## §3 The reduction (kernel-checked)

    SingleDualCoherent S → derivedJGen S a b e * derivedJGen S e c d
                            = derivedJGen S b c f * derivedJGen S a f d

on every tuple whose four channels are present, `F` is nonzero there, **and** the
corresponding dual entry `F(c*,b*,a*,d*,f*,e*)` is nonzero.  The dual-entry hypothesis
is what makes the two defects comparable; it is carried explicitly rather than assumed,
and `TwistQualified` (the `F`-free form) follows once the dual entry is known nonzero on
support (`twistQualified_of_singleDual`).

Under `OmegaNe` at the two triples `(a,b,e)`, `(e,c,d)` the comparison scalars there are
nonzero, which *forces* the dual entry to be nonzero — so on the tuples the law actually
needs, §3 needs no extra hypothesis at all (`singleDualQualified_of_omegaNe`).

Corollaries: the `F`-retained `J_coherent` shape (`derivedJGen_coherent_of_singleDual`),
the same reduction with no dual-entry hypothesis under `OmegaNe`, and — through
`derivedJGen_eq_omegaCoeff_of_omegaNe` — the swarm's associator-only cocycle identity for
`omegaCoeff` (`omegaCoeff_cocycle_of_singleDual_omegaNe`, `omegaCoeff_cocycle_of_pair`).

§5 rewrites the whole hypothesis in `ev`-free, division-free form (`SingleDualPairCoherent`,
ten `F`/`Finv` entries, four factors) and proves both transfers, so that is the smallest
attack surface this route offers: `PairCoherent → SingleDualCoherent → the fourth law`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the field lemma

`x·F₁ = y·F₂` and `z·F₂ = w·F₁` with `F₁, F₂ ≠ 0` force `x/w = y/z`: the two ratios
`x/y` and `w/z` are both `F₂/F₁`.  This is the whole of the "composite tensorator"
argument — the ratios are the defects of the two levels of the dual functor. -/
theorem div_eq_div_of_cross_mul {x y z w F1 F2 : k}
    (h1 : x * F1 = y * F2) (h2 : z * F2 = w * F1) (hF1 : F1 ≠ 0) (hF2 : F2 ≠ 0) :
    x / w = y / z := by
  have hx : x = y * (F2 / F1) := by
    have h := (eq_div_iff hF1).mpr h1
    rwa [mul_div_assoc] at h
  have hw : w = z * (F2 / F1) := by
    have h := (eq_div_iff hF1).mpr h2.symm
    rwa [mul_div_assoc] at h
  rw [hx, hw, mul_div_mul_right y z (div_ne_zero hF2 hF1)]


/-- The `ev`-bookkeeping of the comparison scalar, in the form the bridge needs: if the
two "pair defects" agree (with the associator entries crossed, which is what the `ev`-free
form of §6 says), then the two comparison-scalar products agree. -/
theorem pair_bridge {p1 p2 p3 p4 F1 F2 ea eb ec ed ee ef : k}
    (h : p1 * p2 * F2 = p3 * p4 * F1)
    (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0)
    (hea : ea ≠ 0) (heb : eb ≠ 0) (hec : ec ≠ 0) (hed : ed ≠ 0) (hee : ee ≠ 0)
    (hef : ef ≠ 0) :
    (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec)) * F1
      = (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef)) * F2 := by
  have h1 : p1 * ea * eb ≠ 0 := mul_ne_zero (mul_ne_zero hp1 hea) heb
  have h2 : p2 * ee * ec ≠ 0 := mul_ne_zero (mul_ne_zero hp2 hee) hec
  have h3 : p3 * eb * ec ≠ 0 := mul_ne_zero (mul_ne_zero hp3 heb) hec
  have h4 : p4 * ea * ef ≠ 0 := mul_ne_zero (mul_ne_zero hp4 hea) hef
  have hK : p1 * p2 * (ea * eb * ec) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp1 hp2) (mul_ne_zero (mul_ne_zero hea heb) hec)
  have hK' : p3 * p4 * (ea * eb * ec) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp3 hp4) (mul_ne_zero (mul_ne_zero hea heb) hec)
  have step1 : (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec))
      = ed / (p1 * p2 * (ea * eb * ec)) := by
    rw [div_mul_div_comm, mul_comm (p1 * ea * eb) (p2 * ee * ec)]
    rw [div_eq_div_iff (mul_ne_zero h2 h1) hK]
    ring
  have step2 : (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef))
      = ed / (p3 * p4 * (ea * eb * ec)) := by
    rw [div_mul_div_comm, mul_comm (p3 * eb * ec) (p4 * ea * ef)]
    rw [div_eq_div_iff (mul_ne_zero h4 h3) hK']
    ring
  have e1 : (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec)) * F1
      = ed * F1 / (p1 * p2 * (ea * eb * ec)) := by
    rw [step1, div_mul_eq_mul_div]
  have e2 : (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef)) * F2
      = ed * F2 / (p3 * p4 * (ea * eb * ec)) := by
    rw [step2, div_mul_eq_mul_div]
  rw [e1, e2]
  rw [div_eq_div_iff hK hK']
  linear_combination (-(ed * (ea * eb * ec))) * h

/-! ## §2 — the two forms of single-dual coherence -/

/-- **The antimonoidal coherence of `(−)*`**, associator retained: the two ways of
comparing `(a ⊗ b ⊗ c)*` with `c* ⊗ b* ⊗ a*` agree once the associators on both ends
are accounted for.  `ψ = comparisonScalar` is *the* comparison `(a⊗b)* ⟶ b*⊗a*`
(`comparisonScalar_spec`), so this is exactly "`(−)*` is a monoidal functor". -/
def SingleDualCoherent (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    comparisonScalar S a b e * comparisonScalar S e c d * S.F a b c d e f
      = comparisonScalar S b c f * comparisonScalar S a f d *
          S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a)
            (S.ring.dual d) (S.ring.dual f) (S.ring.dual e)

/-- The *naive* single-dual coherence — no associator factors.  **This is false** on
genuine data (see the module docstring: 6/27 on `Vec^ω_{Z/3}`, 2/15 on Fibonacci); it is
recorded because it is the natural first guess for the functor route, and because it
would have been sufficient (`twistQualified_of_singleDual_naive`). -/
def NaiveSingleDualCoherent (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    comparisonScalar S a b e * comparisonScalar S e c d
      = comparisonScalar S b c f * comparisonScalar S a f d

/-- The `F`-free fourth law with the dual entry retained as a hypothesis. -/
def SingleDualQualified (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    S.F a b c d e f ≠ 0 →
    S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
      (S.ring.dual f) (S.ring.dual e) ≠ 0 →
    J a b e * J e c d = J b c f * J a f d

/-! ## §3 — the reduction -/

/-- **The fourth law for `derivedJGen` from the antimonoidal coherence of `(−)*`.**

`derivedJGen` is `ψ/ψ̌`; the coherence at the tuple makes the numerator defect and the
coherence at the *dual* tuple makes the denominator defect the same associator ratio,
and §1 cancels it.  The dual tuple's four support hypotheses are `N_dual_symm` of the
given ones. -/
theorem singleDualQualified_derivedJGen (S : FusionSystem n k) (h : SingleDualCoherent S) :
    SingleDualQualified S (derivedJGen S) := by
  intro a b c d e f h1 h2 h3 h4 hF hFd
  -- the dual tuple's channels
  have hd1 : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) :=
    N_dual_symm S h1
  have hd2 : 0 < S.ring.N (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) :=
    N_dual_symm S h2
  have hd3 : 0 < S.ring.N (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) :=
    N_dual_symm S h3
  have hd4 : 0 < S.ring.N (S.ring.dual f) (S.ring.dual a) (S.ring.dual d) :=
    N_dual_symm S h4
  -- coherence at the tuple
  have hI := h a b c d e f h1 h2 h3 h4
  -- coherence at the dual tuple
  have hII := h (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
    (S.ring.dual f) (S.ring.dual e) hd3 hd4 hd1 hd2
  simp only [FusionRing.dual_dual] at hII
  show derivedJGen S a b e * derivedJGen S e c d
      = derivedJGen S b c f * derivedJGen S a f d
  simp only [derivedJGen_def]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_eq_div_of_cross_mul hI hII hF hFd

/-- **What the naive hypothesis would have given** (it is false, but the implication is
worth recording: it shows the associator factors cancel pairwise, so the retained form
above is the minimal correction). -/
theorem twistQualified_of_singleDual_naive (S : FusionSystem n k)
    (h : NaiveSingleDualCoherent S) : TwistQualified S (derivedJGen S) := by
  intro a b c d e f h1 h2 h3 h4 _hF
  have hd1 : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) :=
    N_dual_symm S h1
  have hd2 : 0 < S.ring.N (S.ring.dual c) (S.ring.dual e) (S.ring.dual d) :=
    N_dual_symm S h2
  have hd3 : 0 < S.ring.N (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) :=
    N_dual_symm S h3
  have hd4 : 0 < S.ring.N (S.ring.dual f) (S.ring.dual a) (S.ring.dual d) :=
    N_dual_symm S h4
  have hI := h a b c d e f h1 h2 h3 h4
  have hII := h (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
    (S.ring.dual f) (S.ring.dual e) hd3 hd4 hd1 hd2
  show derivedJGen S a b e * derivedJGen S e c d
      = derivedJGen S b c f * derivedJGen S a f d
  simp only [derivedJGen_def]
  rw [div_mul_div_comm, div_mul_div_comm, hI]
  rw [show comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual e) *
        comparisonScalar S (S.ring.dual c) (S.ring.dual e) (S.ring.dual d)
      = comparisonScalar S (S.ring.dual c) (S.ring.dual b) (S.ring.dual f) *
        comparisonScalar S (S.ring.dual f) (S.ring.dual a) (S.ring.dual d)
      from hII.symm]

/-- **The `F`-free fourth law for `derivedJGen`** from single-dual coherence, once the
dual entry is known nonzero on every supported tuple (true on every datum of the tree,
where all block entries on support are nonzero). -/
theorem twistQualified_of_singleDual (S : FusionSystem n k) (h : SingleDualCoherent S)
    (hd : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
        (S.ring.dual f) (S.ring.dual e) ≠ 0) :
    TwistQualified S (derivedJGen S) :=
  fun a b c d e f h1 h2 h3 h4 hF =>
    singleDualQualified_derivedJGen S h a b c d e f h1 h2 h3 h4 hF (hd a b c d e f h1 h2 h3 h4)

/-- **The `F`-retained `J_coherent` shape** (`DerivedJCoherent.coherent_of_qualified`'s
statement) for `derivedJGen`, from single-dual coherence.  On tuples where the entry
vanishes both sides vanish, so only the honest channels need the reduction. -/
theorem derivedJGen_coherent_of_singleDual (S : FusionSystem n k) (h : SingleDualCoherent S) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
        (S.ring.dual f) (S.ring.dual e) ≠ 0 →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4 hFd
  rcases eq_or_ne (S.F a b c d e f) 0 with h0 | h0
  · rw [h0, mul_zero, mul_zero]
  · rw [singleDualQualified_derivedJGen S h a b c d e f h1 h2 h3 h4 h0 hFd]

/-- **The swarm's target shape**: under `OmegaNe` the `F`-free law for `derivedJGen` is
the associator-only cocycle identity for `omegaCoeff`, so single-dual coherence gives
that cocycle identity. -/
theorem omegaCoeff_cocycle_of_singleDual (S : FusionSystem n k) (hn : 0 < n)
    (h : SingleDualCoherent S)
    (hd : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
        (S.ring.dual f) (S.ring.dual e) ≠ 0) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      S.F a b c d e f ≠ 0 →
      FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
        = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d := by
  intro a b c d e f h1 h2 h3 h4 hN1 hN2 hN3 hN4 hF
  have hq := twistQualified_of_singleDual S h hd a b c d e f h1 h2 h3 h4 hF
  rwa [derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN1,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN2,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN3,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN4] at hq


/-! ## §4 — removing the dual-entry hypothesis under `OmegaNe`

`SingleDualCoherent` gives the law on a tuple once *both* `F(tuple)` and `F(dual tuple)`
are nonzero.  Under `OmegaNe` at the two triples `(a,b,e)` and `(e,c,d)` the dual entry is
*forced* nonzero: the comparison scalars there are nonzero
(`comparisonScalar_ne_zero`), so their product is, while `SingleDualCoherent` at the tuple
makes that product times `F(dual tuple)` equal to something times `F(tuple)`.  Hence on
the tuples the fourth law actually needs (`F` nonzero), single-dual coherence suffices
with no extra hypothesis at all — `singleDualQualified_of_omegaNe`.

This is the sharp form: it removes the only hypothesis of §3 that is not already part of
the target statement. -/

/-- **`OmegaNe` at `(a,b,e)` and `(e,c,d)` makes the second comparison scalar nonzero**,
which is what the reduction of §3 needs beyond `F a b c d e f ≠ 0`. -/
theorem comparisonScalar_ne_zero_of_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (h : OmegaNe S hn a b c) : comparisonScalar S a b c ≠ 0 :=
  comparisonScalar_ne_zero S hn a b c
    (mul_ne_zero (mul_ne_zero h.1 (S.ev_ne_zero a)) (S.ev_ne_zero b)) (S.ev_ne_zero c)

/-- **The fourth law for `derivedJGen` from single-dual coherence, on `OmegaNe`
triples**: no hypothesis on the dual associator entry is needed. -/
theorem singleDualQualified_of_omegaNe (S : FusionSystem n k) (h : SingleDualCoherent S)
    (hn : 0 < n) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → S.F a b c d e f ≠ 0 →
      derivedJGen S a b e * derivedJGen S e c d
        = derivedJGen S b c f * derivedJGen S a f d := by
  intro a b c d e f h1 h2 h3 h4 hN1 hN2 hF
  have hp1 := comparisonScalar_ne_zero_of_omegaNe S hn hN1
  have hp2 := comparisonScalar_ne_zero_of_omegaNe S hn hN2
  have hAC : comparisonScalar S a b e * comparisonScalar S e c d ≠ 0 := mul_ne_zero hp1 hp2
  have hFd : S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
      (S.ring.dual f) (S.ring.dual e) ≠ 0 := by
    intro h0
    have hI := h a b c d e f h1 h2 h3 h4
    rw [h0, mul_zero] at hI
    exact hAC ((mul_eq_zero.mp hI).resolve_right hF)
  exact singleDualQualified_derivedJGen S h a b c d e f h1 h2 h3 h4 hF hFd

/-- **The swarm's target, sharp form**: single-dual coherence plus `OmegaNe` gives the
associator-only cocycle identity for `omegaCoeff` on every channel with `F ≠ 0`, with no
further hypothesis. -/
theorem omegaCoeff_cocycle_of_singleDual_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    (h : SingleDualCoherent S) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      S.F a b c d e f ≠ 0 →
      FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
        = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d := by
  intro a b c d e f h1 h2 h3 h4 hN1 hN2 hN3 hN4 hF
  have hq := singleDualQualified_of_omegaNe S h hn a b c d e f h1 h2 h3 h4 hN1 hN2 hF
  rwa [derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN1,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN2,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN3,
       derivedJGen_eq_omegaCoeff_of_omegaNe S hn hN4] at hq


/-! ## §5 — the `ev`-free, division-free form of the hypothesis

`ψ(x,y;z) = ev z / (singleDualPair x y z * ev x * ev y)` by definition, so the coherence
of §2 is *equivalent* (under the nonvanishing of the pair entries, which is `OmegaNe`'s
first component) to the product identity

    P(a,b;e)·P(e,c;d)·F(c*,b*,a*,d*,f*,e*) = P(b,c;f)·P(a,f;d)·F(a,b,c,d,e,f)

with `P := singleDualPair` — no `ev`, no `coev`, no division, ten entries, all of them
`F`/`Finv` entries with a unit composite slot or a unit channel.  That is the form a
block-matrix or pentagon-instance proof can attack, and `pair_bridge` / `pair_bridge_inv`
are the two directions of the transfer.

Machine check of this form (0 failures on all data sets, including the non-pointed
non-self-dual `Fib ⊠ Vec^ω_{Z/3}`): `.ultramath/smw7f657l/m3/uform.py`. -/

/-- The divisor of the comparison scalar with the `ev`-factors and the division removed. -/
noncomputable def singleDualPair (S : FusionSystem n k) (x y z : Fin n) : k :=
  if h : 0 < n then
    S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
      S.Finv (S.ring.dual x) x y y z ⟨0, h⟩
  else 0

/-- The comparison scalar in terms of the pair entry. -/
theorem comparisonScalar_eq_pair (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) :
    comparisonScalar S x y z
      = S.ev z / (singleDualPair S x y z * S.ev x * S.ev y) := by
  simp only [comparisonScalar_def, singleDualPair, dif_pos hn]

/-- The single-dual coherence in `ev`-free, division-free form. -/
def SingleDualPairCoherent (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    singleDualPair S a b e * singleDualPair S e c d *
        S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a)
          (S.ring.dual d) (S.ring.dual f) (S.ring.dual e)
      = singleDualPair S b c f * singleDualPair S a f d * S.F a b c d e f

/-- The reverse transfer: the comparison-scalar coherence gives the pair coherence. -/
theorem pair_bridge_inv {p1 p2 p3 p4 F1 F2 ea eb ec ed ee ef : k}
    (h : (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec)) * F1
      = (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef)) * F2)
    (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0)
    (hea : ea ≠ 0) (heb : eb ≠ 0) (hec : ec ≠ 0) (hed : ed ≠ 0) (hee : ee ≠ 0)
    (hef : ef ≠ 0) :
    p1 * p2 * F2 = p3 * p4 * F1 := by
  have h1 : p1 * ea * eb ≠ 0 := mul_ne_zero (mul_ne_zero hp1 hea) heb
  have h2 : p2 * ee * ec ≠ 0 := mul_ne_zero (mul_ne_zero hp2 hee) hec
  have h3 : p3 * eb * ec ≠ 0 := mul_ne_zero (mul_ne_zero hp3 heb) hec
  have h4 : p4 * ea * ef ≠ 0 := mul_ne_zero (mul_ne_zero hp4 hea) hef
  have hK : p1 * p2 * (ea * eb * ec) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp1 hp2) (mul_ne_zero (mul_ne_zero hea heb) hec)
  have hK' : p3 * p4 * (ea * eb * ec) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp3 hp4) (mul_ne_zero (mul_ne_zero hea heb) hec)
  have step1 : (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec))
      = ed / (p1 * p2 * (ea * eb * ec)) := by
    rw [div_mul_div_comm, mul_comm (p1 * ea * eb) (p2 * ee * ec)]
    rw [div_eq_div_iff (mul_ne_zero h2 h1) hK]
    ring
  have step2 : (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef))
      = ed / (p3 * p4 * (ea * eb * ec)) := by
    rw [div_mul_div_comm, mul_comm (p3 * eb * ec) (p4 * ea * ef)]
    rw [div_eq_div_iff (mul_ne_zero h4 h3) hK']
    ring
  have e1 : (ee / (p1 * ea * eb)) * (ed / (p2 * ee * ec)) * F1
      = ed * F1 / (p1 * p2 * (ea * eb * ec)) := by
    rw [step1, div_mul_eq_mul_div]
  have e2 : (ef / (p3 * eb * ec)) * (ed / (p4 * ea * ef)) * F2
      = ed * F2 / (p3 * p4 * (ea * eb * ec)) := by
    rw [step2, div_mul_eq_mul_div]
  rw [e1, e2] at h
  rw [div_eq_div_iff hK hK'] at h
  have hK0 : ea * eb * ec ≠ 0 := mul_ne_zero (mul_ne_zero hea heb) hec
  have hE : ed * (ea * eb * ec) * (F1 * (p3 * p4)) = ed * (ea * eb * ec) * (F2 * (p1 * p2)) := by
    linear_combination h
  have h'' := mul_left_cancel₀ (mul_ne_zero hed hK0) hE
  linear_combination (-1) * h''

/-- **The pair form implies the comparison-scalar form**: proving the `ev`-free identity
of §6 proves the antimonoidal coherence of `(−)*`. -/
theorem singleDualCoherent_of_pair (S : FusionSystem n k) (h : SingleDualPairCoherent S)
    (hP : ∀ x y z : Fin n, 0 < S.ring.N x y z → singleDualPair S x y z ≠ 0) :
    SingleDualCoherent S := by
  intro a b c d e f h1 h2 h3 h4
  have hn : 0 < n := a.pos
  have hm := h a b c d e f h1 h2 h3 h4
  rw [comparisonScalar_eq_pair S hn a b e, comparisonScalar_eq_pair S hn e c d,
    comparisonScalar_eq_pair S hn b c f, comparisonScalar_eq_pair S hn a f d]
  exact pair_bridge hm (hP a b e h1) (hP e c d h2) (hP b c f h3) (hP a f d h4)
    (S.ev_ne_zero a) (S.ev_ne_zero b) (S.ev_ne_zero c) (S.ev_ne_zero d)
    (S.ev_ne_zero e) (S.ev_ne_zero f)

/-- **The pair form is equivalent to the comparison-scalar form** (under the pair
nonvanishing): so §6's target is exactly as strong as §2's — a faithful, division-free
statement of "`(−)*` is monoidal". -/
theorem singleDualPairCoherent_iff (S : FusionSystem n k)
    (hP : ∀ x y z : Fin n, 0 < S.ring.N x y z → singleDualPair S x y z ≠ 0) :
    SingleDualPairCoherent S ↔ SingleDualCoherent S := by
  refine ⟨fun hp => singleDualCoherent_of_pair S hp hP, fun h => ?_⟩
  intro a b c d e f h1 h2 h3 h4
  have hn : 0 < n := a.pos
  have hm := h a b c d e f h1 h2 h3 h4
  rw [comparisonScalar_eq_pair S hn a b e, comparisonScalar_eq_pair S hn e c d,
    comparisonScalar_eq_pair S hn b c f, comparisonScalar_eq_pair S hn a f d] at hm
  exact pair_bridge_inv hm (hP a b e h1) (hP e c d h2) (hP b c f h3) (hP a f d h4)
    (S.ev_ne_zero a) (S.ev_ne_zero b) (S.ev_ne_zero c) (S.ev_ne_zero d)
    (S.ev_ne_zero e) (S.ev_ne_zero f)


/-- `OmegaNe`'s first component *is* the nonvanishing of the pair entry, so the pair
form's nonvanishing hypothesis is the one the target already carries. -/
theorem singleDualPair_ne_zero_of_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (h : OmegaNe S hn a b c) : singleDualPair S a b c ≠ 0 := by
  simp only [singleDualPair, dif_pos hn]
  exact h.1

/-- **The swarm's target from the `ev`-free form**: the pair coherence plus `OmegaNe` at
the supported triples gives the associator-only cocycle identity for `omegaCoeff`. -/
theorem omegaCoeff_cocycle_of_pair (S : FusionSystem n k) (hn : 0 < n)
    (h : SingleDualPairCoherent S)
    (hP : ∀ x y z : Fin n, 0 < S.ring.N x y z → singleDualPair S x y z ≠ 0) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      S.F a b c d e f ≠ 0 →
      FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
        = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d :=
  omegaCoeff_cocycle_of_singleDual_omegaNe S hn (singleDualCoherent_of_pair S h hP)


/-- **The fourth law in full** (the `F`-free form on *every* tuple with `F ≠ 0`) from
single-dual coherence plus the nonvanishing of the comparison scalar on channels — the
hypothesis `OmegaNe` encodes (`comparisonScalar_ne_zero_of_omegaNe`).  The dual entry
`F(c*,b*,a*,d*,f*,e*)` is then *forced* nonzero: if it vanished, `SingleDualCoherent` at
the tuple would make the nonzero product `ψ(a,b;e)·ψ(e,c;d)` zero. -/
theorem twistQualified_of_singleDual' (S : FusionSystem n k) (h : SingleDualCoherent S)
    (hne : ∀ x y z : Fin n, 0 < S.ring.N x y z → comparisonScalar S x y z ≠ 0) :
    TwistQualified S (derivedJGen S) := by
  intro a b c d e f h1 h2 h3 h4 hF
  have hFd : S.F (S.ring.dual c) (S.ring.dual b) (S.ring.dual a) (S.ring.dual d)
      (S.ring.dual f) (S.ring.dual e) ≠ 0 := by
    intro h0
    have hI := h a b c d e f h1 h2 h3 h4
    rw [h0, mul_zero] at hI
    have hAC : comparisonScalar S a b e * comparisonScalar S e c d = 0 :=
      (mul_eq_zero.mp hI).resolve_right hF
    rcases mul_eq_zero.mp hAC with h' | h'
    · exact hne a b e h1 h'
    · exact hne e c d h2 h'
  exact singleDualQualified_derivedJGen S h a b c d e f h1 h2 h3 h4 hF hFd

/-! ## §6 — axiom audit -/

#print axioms div_eq_div_of_cross_mul
#print axioms singleDualQualified_derivedJGen
#print axioms twistQualified_of_singleDual_naive
#print axioms twistQualified_of_singleDual
#print axioms derivedJGen_coherent_of_singleDual
#print axioms omegaCoeff_cocycle_of_singleDual
#print axioms comparisonScalar_ne_zero_of_omegaNe
#print axioms singleDualQualified_of_omegaNe
#print axioms twistQualified_of_singleDual'
#print axioms omegaCoeff_cocycle_of_singleDual_omegaNe
#print axioms pair_bridge
#print axioms pair_bridge_inv
#print axioms singleDualCoherent_of_pair
#print axioms singleDualPairCoherent_iff
#print axioms singleDualPair_ne_zero_of_omegaNe
#print axioms omegaCoeff_cocycle_of_pair

end FusionCategory
