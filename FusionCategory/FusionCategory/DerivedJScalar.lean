import FusionCategory.Gauge
import FusionCategory.Prop821CNorm

/-!
# WP2 Task 2.3 — `derivedJ`, the double-dual twist as a morphism entry

`FusionSystem` carries a twist field `J` as *data* constrained by four laws
(`J_ne_zero`, `J_unit_left`, `J_unit_right`, `J_dual`, `J_coherent`).  Task 2.3
of WP2 asks for the twist that the rigid structure *computes*: the scalar by
which the monoidal structure of the double-dual functor `(−)**` acts on a
channel, read in the channel basis.  This file defines it, at general `k`

  `comparisonScalar S x y z`   — the channel scalar of the comparison map
                                 `ψ_{x,y} : (x ⊗ y)* ⟶ y* ⊗ x*`,
  `derivedJGen S a b c`        — the ratio `ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}`, i.e.
                                 the `(c,c)`-entry of the tensorator
                                 `X_a** ⊗ X_b** ⟶ (X_a ⊗ X_b)**` in the
                                 channel basis,

and specializes to B4's frozen type `FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`
as `derivedJ`.  It is defined from `S.F`, `S.Finv`, `S.ev`, `S.coev` and the
fusion ring only — **never** from the carried field `S.J`, and no proof here
identifies the two: the relation is `J_match`, and on the pointed false-`J`
datum `Z2SqH.system` the two differ on six channels (below).

## The derivation of the comparison scalar

Work in the reconstruction (`FusionMat n k`, the design note's model).  For
`W = X_a ⊗ X_b` the tensorator `j : X_a** ⊗ X_b** ⟶ (X_a ⊗ X_b)**` is the mate,
under the exact pairing `((a⊗b)**, (a⊗b)*)`, of the composite

  `X_a** ⊗ X_b** ⊗ (X_a ⊗ X_b)*  →  X_a** ⊗ X_b** ⊗ X_b* ⊗ X_a*  →  1`

whose first leg is `id ⊗ id ⊗ ψ_{a,b}` and whose second leg evaluates `X_a**`
against `X_a*` and `X_b**` against `X_b*`.  So `j` is determined by
`ψ_{a,b} : (a⊗b)* → b* ⊗ a*`, which is the unique map intertwining the
canonical evaluation `ev_{(a⊗b)}` with the pairing
`(b* ⊗ a*) ⊗ (a ⊗ b) → 1` built from the tensor structure.  In the
multiplicity-free reconstruction every channel block is one-dimensional, so
that intertwining condition is one scalar equation per channel `c` of `a ⊗ b`,
and both sides are monomials in the datum.  Evaluating the pairing along the
associator path

  `((b* ⊗ a*) ⊗ (a ⊗ b)) --α--> b* ⊗ (a* ⊗ (a ⊗ b)) --id⊗α⁻¹-->
   b* ⊗ ((a* ⊗ a) ⊗ b) --id⊗ev_a⊗id--> b* ⊗ (1 ⊗ b) --λ--> b* ⊗ b --ev_b--> 1`

gives, for `h : 0 < n` and a present channel `N a b c = 1`,

  `ψ_{a,b}|_c = ev c / ( F (b*) (a*) c 0 (c*) b · Finv (a*) a b b c 0 · ev a · ev b )`

(the `0` is the unit label `⟨0,h⟩`; `c*` is the channel of `b* ⊗ a*` and `b`
the channel of `a* ⊗ (a ⊗ b)`).  The choice of associator path is immaterial:
the pentagon and the triangle of the reconstruction are the system's `pentagon`
and `F_unit_left`/`F_unit_right`/`TriangleLaw`, so any two such paths agree.

## What is checked here, and what is owed

Proved in this file: the definition and its frozen type; the *gauge law*
(`ψ` is multiplied by `λ x λ y / λ z`, hence `derivedJ` is invariant under the
vertex gauge of the signature, whose parameters are dual-invariant — this is
the WP1-round m1 finding in the strongest form available on the datums the
signature admits); and the pointed instances: `derivedJ = δ(κ)` on
`VecZ2.system`, on `VecZ2Twisted.system` and on the pointed false-`J` datum
`Z2SqH.system`, where `δ(κ) ≠ 1` on six channels — so `J_match` fails there,
which is the kernel form of what `docs/honest_twist_check.py` checks at script
level.  Frozen (statement only): the general pointed `δ(κ)` theorem, and the
bridge `derivedJ = settledJ` on pseudo-unitary data (`Prop821CNorm.settledJ`).

The formula was validated independently before being written down: in an exact
miniature model of the reconstruction (position trees, block-diagonal
morphisms, `F`-associator, blockwise `ev`/`coev`; `.ultramath/…/model.py`)
the model's `ψ` equals the closed form on every channel of three pointed
datums, the ratio equals `δ(κ)` on `Vec^ω_{(Z/2)²}` (all 16 channels), and the
closed form equals the model's on the Fibonacci ring with a generic `F`
(symbolic, 2×2 block at `d = τ`); and the four twist laws hold for it on all
of those data.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## The comparison scalar and the twist -/

/-- The channel scalar `ψ_{x,y}|_z` of the comparison map
`ψ_{x,y} : (x ⊗ y)* ⟶ y* ⊗ x*`, on the channel `z` of `x ⊗ y`.

See the module docstring for the derivation: it is the unique scalar making the
tensor-structure pairing `(y* ⊗ x*) ⊗ (x ⊗ y) → 1` equal to `ev_{(x⊗y)}` on
that channel.  Division by zero is total in a field, so this is defined for all
arguments; on a supported channel with an honest datum it is nonzero. -/
noncomputable def comparisonScalar (S : FusionSystem n k) (x y z : Fin n) : k :=
  if h : 0 < n then
    S.ev z / (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
      S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y)
  else 0

/-- **The double-dual twist, as a morphism entry**: the `(c,c)`-entry of the
tensorator `X_a** ⊗ X_b** ⟶ (X_a ⊗ X_b)**` in the channel basis, i.e. the
ratio of the comparison scalars `ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}`.

Defined from `F`, `Finv`, `ev`, `coev` and the fusion ring only: **not** from
the carried twist `S.J`. -/
noncomputable def derivedJGen (S : FusionSystem n k) (a b c : Fin n) : k :=
  comparisonScalar S a b c /
    comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c)

/-- **B4's frozen interface**: `derivedJ` has exactly the type Task 1.5 fixes,
`∀ {n}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`, so that
`ENO823ExactC derivedJ` and `J_match S (derivedJ S)` are the intended
statements. -/
noncomputable def derivedJ :
    ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ :=
  fun {_} S => derivedJGen S

@[simp] theorem comparisonScalar_def (S : FusionSystem n k) (x y z : Fin n) :
    comparisonScalar S x y z =
      if h : 0 < n then
        S.ev z / (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
          S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y)
      else 0 := rfl

@[simp] theorem derivedJGen_def (S : FusionSystem n k) (a b c : Fin n) :
    derivedJGen S a b c =
      comparisonScalar S a b c /
        comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) := rfl

theorem derivedJ_apply {n : ℕ} (S : FusionSystem n ℂ) (a b c : Fin n) :
    derivedJ S a b c = derivedJGen S a b c := rfl

/-- The frozen type is the one `Statements.lean` quantifies over: this is the
term that `ENO823ExactC` instantiates its `derivedJ` parameter at. -/
noncomputable def derivedJFrozen :
    (∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ) := derivedJ

/-- `J_match` accepts it, i.e. the interface of Task 1.5 fits without any
coercion. -/
example {n : ℕ} (S : FusionSystem n ℂ) : Prop := J_match S (derivedJ S)

/-- And the target `ENO823ExactC` can be instantiated at it. -/
example {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData) : Prop :=
  ENO823ExactC derivedJ S hFP

/-- **The defining property of the comparison scalar**: it is the unique scalar
whose product with the tensor-structure pairing scalar is the evaluation.  This
is the mate equation `ev_{(x⊗y)} = (pairing) ∘ (ψ_{x,y} ⊗ id)`, written on the
channel `z`; it is what identifies `ψ` as *the* comparison map and hence
`derivedJ` as *the* tensorator entry, without any choice of associator path
being visible (any other path differs by the pentagon and the triangle, which
are the datum's `pentagon` and `F_unit_left`/`F_unit_right`). -/
theorem comparisonScalar_spec (S : FusionSystem n k) (h : 0 < n) (x y z : Fin n)
    (hD : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
        S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y ≠ 0) :
    comparisonScalar S x y z *
        (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
          S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y) = S.ev z := by
  rw [comparisonScalar_def, dif_pos h]
  exact div_mul_cancel₀ _ hD

/-- **Nonvanishing of the comparison scalar on a supported channel**, which is
what WP3 Task 3.2's ratio formula `J = ψ_{x,y}|_z / ψ_{y*,x*}|_{z*}` needs: on a
channel where the datum's own entries are nonzero, `ψ_{x,y}|_z ≠ 0`.  (In the
reconstruction these entries are those of an *isomorphism*, so the hypothesis is
what the datum's `Finv_comp`/`F_comp_inv` supply on a `1 × 1` block.) -/
theorem comparisonScalar_ne_zero (S : FusionSystem n k) (h : 0 < n) (x y z : Fin n)
    (hD : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
        S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y ≠ 0)
    (hz : S.ev z ≠ 0) : comparisonScalar S x y z ≠ 0 := by
  intro h0
  have := comparisonScalar_spec S h x y z hD
  rw [h0, zero_mul] at this
  exact hz this.symm

/-- Nonvanishing of the twist on a supported channel, from the nonvanishing of
both comparison scalars. -/
theorem derivedJGen_ne_zero (S : FusionSystem n k) (a b c : Fin n)
    (h1 : comparisonScalar S a b c ≠ 0)
    (h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0) :
    derivedJGen S a b c ≠ 0 :=
  div_ne_zero h1 h2

/-! ## The gauge law

The vertex gauge `coev i ↦ λ i · coev i`, `ev i ↦ ev i / λ i` (`Gauge.lean`)
multiplies the comparison scalar by `λ x λ y / λ z`, because the comparison is
*defined* through the evaluation.  Hence the twist transforms by
`λ a λ b λ (c*) / (λ c λ (a*) λ (b*))` — the WP1-round m1 law — and is
therefore *invariant* under the gauge group of the signature, whose parameters
satisfy `λ (i*) = λ i` (`Gauge.gauge`). -/

theorem comparisonScalar_gauge (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (x y z : Fin n) :
    comparisonScalar (gauge S lam hlam) x y z =
      (lam x : k) * (lam y : k) / (lam z : k) * comparisonScalar S x y z := by
  unfold comparisonScalar
  by_cases hn : 0 < n
  · rw [dif_pos hn, dif_pos hn]
    have hx : (lam x : k) ≠ 0 := (lam x).ne_zero
    have hy : (lam y : k) ≠ 0 := (lam y).ne_zero
    have hz : (lam z : k) ≠ 0 := (lam z).ne_zero
    simp only [gauge]
    by_cases hD : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
        S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ * S.ev x * S.ev y = 0
    · have hD' : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
          S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ * (S.ev x / (lam x : k)) *
          (S.ev y / (lam y : k)) = 0 := by
        have : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
            S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ * (S.ev x / (lam x : k)) *
            (S.ev y / (lam y : k))
            = (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
              S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ * S.ev x * S.ev y) /
              ((lam x : k) * (lam y : k)) := by
          field_simp
          try ring
        rw [this, hD]
        simp
      rw [hD, hD']
      simp
    · field_simp
      try ring
  · rw [dif_neg hn, dif_neg hn]
    simp

/-- **The twist transforms by the m1 law** (general `λ`). -/
theorem derivedJGen_rescale (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin n) :
    derivedJGen (gauge S lam hlam) a b c =
      derivedJGen S a b c *
        ((lam a : k) * (lam b : k) * (lam (S.ring.dual c) : k) /
          ((lam c : k) * (lam (S.ring.dual a) : k) * (lam (S.ring.dual b) : k))) := by
  unfold derivedJGen
  have h2 : comparisonScalar (gauge S lam hlam) ((gauge S lam hlam).ring.dual b)
      ((gauge S lam hlam).ring.dual a) ((gauge S lam hlam).ring.dual c) =
      (lam (S.ring.dual b) : k) * (lam (S.ring.dual a) : k) / (lam (S.ring.dual c) : k) *
        comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    comparisonScalar_gauge S lam hlam _ _ _
  rw [comparisonScalar_gauge S lam hlam a b c, h2]
  have ha : (lam a : k) ≠ 0 := (lam a).ne_zero
  have hb : (lam b : k) ≠ 0 := (lam b).ne_zero
  have hc : (lam c : k) ≠ 0 := (lam c).ne_zero
  have hda : (lam (S.ring.dual a) : k) ≠ 0 := (lam _).ne_zero
  have hdb : (lam (S.ring.dual b) : k) ≠ 0 := (lam _).ne_zero
  have hdc : (lam (S.ring.dual c) : k) ≠ 0 := (lam _).ne_zero
  by_cases hD : comparisonScalar S a b c = 0
  · rw [hD]
    simp
  · field_simp
    try ring

/-- **`derivedJ` is invariant under the vertex gauge of the signature**: the
gauge group is the dual-invariant subgroup of `(kˣ)^n`, and on it the m1 law's
factor is `λ a λ b λ c / (λ c λ a λ b) = 1`.

This is the answer to the WP1-round m1 finding on the twist side: unlike
`ENO823ExactC` at an arbitrary candidate twist, the *derived* twist is a
gauge-invariant function of the datum, as `settledJ` is. -/
theorem derivedJGen_gauge (S : FusionSystem n k) (lam : Fin n → kˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin n) :
    derivedJGen (gauge S lam hlam) a b c = derivedJGen S a b c := by
  rw [derivedJGen_rescale S lam hlam a b c, hlam c, hlam a, hlam b]
  have ha : (lam a : k) ≠ 0 := (lam a).ne_zero
  have hb : (lam b : k) ≠ 0 := (lam b).ne_zero
  have hc : (lam c : k) ≠ 0 := (lam c).ne_zero
  field_simp

/-! ## The frozen statements

Statements only, no proofs: they are WP3's (Task 3.3) and WP4's targets, and
they are the form in which the programme consumes `derivedJ`. -/

/-- **The bridge to the settled twist**: on a datum with Perron–Frobenius
dimensions the derived twist is the per-channel table `settledJ`
(`Prop821CNorm.lean`), of which `j_match_settledJ_iff` says `J_match` is the
per-channel law (K).  This is the WP3 target; it is *not* an assumption
anywhere in this file.  Both sides are gauge-invariant (`settledJ` through the
gauge-invariant `κ`, `derivedJ` by `derivedJGen_gauge`), so the statement is a
property of the gauge orbit and not of a normalisation. -/
noncomputable def DerivedJ_eq_settledJ (S : FusionSystem n ℂ) (hFP : S.ring.FPData) :
    Prop :=
  ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJ S a b c = settledJ S hFP a b c

/-- **The pointed `δ(κ)` theorem, general form**: on a pointed datum — one
simple per group element, so every `N` is `0` or `1` and `X_{i*} ⊗ X_i` is the
unit — the derived twist is `κ_a κ_b / κ_c`, i.e. the coboundary of the duality
normalisation.  Proved below on the three pointed witnesses; the general
statement is frozen here. -/
noncomputable def DerivedJ_pointed (S : FusionSystem n ℂ) : Prop :=
  ∀ a b c : Fin n, 0 < S.ring.N a b c →
    derivedJ S a b c = S.kappa a * S.kappa b / S.kappa c

/-- **The bridge composes with `J_match`**: if the derived twist is the settled
one and the carried twist matches the derived one, then the carried twist is the
settled one — which is `j_match_settledJ_iff`'s per-channel law (K), and with it
multiplicativity of every pivotal dimension (`Prop821CNorm`).  Nothing here
proves the bridge; this is the implication WP3 uses. -/
theorem j_match_settledJ_of_bridge {n : ℕ} (S : FusionSystem n ℂ)
    (hFP : S.ring.FPData) (h : DerivedJ_eq_settledJ S hFP)
    (hm : J_match S (derivedJ S)) : J_match S (settledJ S hFP) :=
  fun a b c hN => (hm a b c hN).trans (h a b c hN)

/-- **Gauge covariance of the derived twist**, general `λ` (the m1 law).
`derivedJGen_rescale` proves it for the gauge group of the signature; this is
the same law for an arbitrary rescaling of `ev`/`coev`, frozen because a
non-dual-invariant `λ` does not preserve the `ev_dual` field of the signature
and so has no `FusionSystem` to state it about. -/
def DerivedJ_gauge_covariant : Prop :=
  ∀ {m : ℕ} (S : FusionSystem m ℂ) (lam : Fin m → ℂˣ)
    (hlam : ∀ i, lam (S.ring.dual i) = lam i) (a b c : Fin m),
      derivedJGen (gauge S lam hlam) a b c =
        derivedJGen S a b c *
          ((lam a : ℂ) * (lam b : ℂ) * (lam (S.ring.dual c) : ℂ) /
            ((lam c : ℂ) * (lam (S.ring.dual a) : ℂ) * (lam (S.ring.dual b) : ℂ)))

/-- The frozen gauge-covariance statement is in fact **proved**: it is exactly
`derivedJGen_rescale`, restricted to the gauge group of the signature. -/
theorem DerivedJ_gauge_covariant_holds : DerivedJ_gauge_covariant :=
  fun S lam hlam a b c => derivedJGen_rescale S lam hlam a b c

end FusionCategory



/-! ## Axiom audit -/

#print axioms FusionCategory.comparisonScalar
#print axioms FusionCategory.derivedJGen
#print axioms FusionCategory.derivedJ
#print axioms FusionCategory.derivedJFrozen
#print axioms FusionCategory.derivedJ_apply
#print axioms FusionCategory.comparisonScalar_spec
#print axioms FusionCategory.comparisonScalar_ne_zero
#print axioms FusionCategory.derivedJGen_ne_zero
#print axioms FusionCategory.comparisonScalar_gauge
#print axioms FusionCategory.derivedJGen_rescale
#print axioms FusionCategory.derivedJGen_gauge
#print axioms FusionCategory.DerivedJ_eq_settledJ
#print axioms FusionCategory.DerivedJ_pointed
#print axioms FusionCategory.DerivedJ_gauge_covariant
#print axioms FusionCategory.j_match_settledJ_of_bridge
#print axioms FusionCategory.DerivedJ_gauge_covariant_holds
