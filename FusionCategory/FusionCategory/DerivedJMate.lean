import FusionCategory.DerivedJCoherent

/-!
# The mate route to the fourth law for the derived twist

`DerivedJScalar.comparisonScalar S x y z` is *defined* as the quotient
`ev z / P(x,y;z)`, where `P(x,y;z)` is the scalar of the tensor-structure pairing

  `(y* ⊗ x*) ⊗ (x ⊗ y) ⟶ 1`

evaluated on the channel `z` of `x ⊗ y`.  That pairing scalar is the **mate** of
the evaluation: `ψ_{x,y} : (x ⊗ y)* → y* ⊗ x*` is the unique channel scalar
making the pairing equal to `ev`, and `DerivedJScalar.comparisonScalar_spec` is
precisely that equation.  This file takes the pairing as the primary object and
carries the fourth law over to it.

## §1–§2 — the mate equation and its uniqueness

`pairScalar S x y z` is `P(x,y;z)` written out in `F`, `Finv`, `ev`:

  `P(x,y;z) = F(y*,x*,z,1,z*,y) · Finv(x*,x,y,y,z,1) · ev x · ev y`.

`comparisonScalar_mul_pairScalar` is the mate equation; `eq_comparisonScalar_of_mul_pairScalar`
is its **uniqueness** — a scalar producing the same evaluation against the same
nonzero pairing *is* the comparison scalar.  That is the tool which lets an
identity between comparison scalars be settled without ever computing a quotient.

## §3–§4 — `omegaCoeff` and `derivedJGen` agree with no nonvanishing hypothesis

`omegaCoeff_eq_pairScalar_div`: `Ω(a,b;c) = P(b*,a*;c*)/P(a,b;c)` (the `ev`-factors
of the two pairings coincide by `ev_dual` — this is why an associator-only form
exists).  Hence **`derivedJGen_eq_omegaCoeff_uncond`: `derivedJGen = omegaCoeff`
on every label**, with no `OmegaNe`: written as a ratio of pairings the two
comparison scalars cancel outright, and in a field the degenerate cases agree
because `x / 0 = 0` on both sides.  Consequently
`derivedJGen_qualified_iff_omegaCoeff_uncond` is
`DerivedJCoherent.derivedJGen_coherent_iff_omegaCoeff_cocycle` **without the four
`OmegaNe` hypotheses**.

## §5 — the pairing form of the remaining obligation

`pairDual S x y z = P(y*,x*,z*)` is an involution (`pairDual_dual`), and
`derivedJGen_eq_pairDual_div`: `J(a,b;c) = P^D(a,b;c)/P(a,b;c)`.  So each side of
the cocycle identity is the **swap-dual ratio of a twofold evaluation product**
(`Π_L = P(a,b;e)P(e,c;d)` versus `Π_R = P(b,c;f)P(a,f;d)`), and the obligation
`PairCocycle S` reads `Π_L^D/Π_L = Π_R^D/Π_R`.  `derivedJGen_qualified_iff_pairCocycle`
identifies the `F`-free fourth law with it, and
`derivedJGen_coherent_of_pairCocycle` / `exists_fusionSystem_derivedJGen_of_pairCocycle`
assemble it to the retained fourth law and to the fixpoint datum: **`PairCocycle`
is the whole remaining obligation.**

## §6 — support

`pairScalar_eq_zero_of_not_chan`: `P(x,y;z) = 0` unless `0 < N x y z` (from
`F_support` and `dual_symm`).  The pairing matrix of `x ⊗ y` against `y* ⊗ x*` is
supported on the channels and its entries are the `pairScalar` values.

## §7–§10 — what would discharge it

Clearing denominators turns `PairCocycle` into the **division-free** `CrossCocycle`,
and a **pivotal factor** `φ` — a nowhere-vanishing `φ` with
`P^D(a,b;c)·φ c = P(a,b;c)·(φ a · φ b)` — gives it outright
(`crossCocycle_of_pivotalFactor`, no nonvanishing needed).  `pivotalFactor_entries`
is the raw form of that hypothesis: two boundary `F`-entries and two boundary
`Finv`-entries per channel, i.e. a monomial identity in the free abelian group on
the boundary entries — the shape a boundary instantiation of the pentagon
produces.  `pivotalFactor_of_coboundary` and `pivotalFactor_kappa_of_pointed`
show the hypothesis is not vacuous: every pointed datum carries the pivotal
factor `φ = κ`, which reproduces the pointed fourth law along this route
(`derivedJGen_coherent_of_pointed_mate`).

`PivotalFactor S φ` is exactly the `p_mon` field of the tree's
`Pivotal.PivotalStructure` (`p kk = J i j kk * p i * p j`) read at `J = derivedJGen`
with `p = φ⁻¹`: `pairScalar S a b c * φ a * φ b = pairDual S a b c * φ c` is
`(1/φ c) = (P^D/P)·(1/φ a)·(1/φ b)`.  So §7–§10 say: **the fourth law for the
derived twist is discharged by exhibiting the pivotal structure of the derived
twist**, and `pivotalFactor_kappa_of_pointed` exhibits it (`p = κ⁻¹`) on pointed
data.

**Not proved here**: `PivotalFactor` (equivalently `CrossCocycle`, equivalently
`PairCocycle`) for arbitrary data.  That is the classical statement that the
canonical tensorator of `(−)**` is monoidally isomorphic to the identity, i.e.
that the datum is pivotal; it is *not* a formal consequence of the pentagon in
the boundary regime.  Two things a successor needs:

* `PivotalFactor` alone does **not** give `PairCocycle` when a `pairScalar`
  vanishes: then both `Ω` entries are `0 / 0 = 0` by the total division of a
  field and the identity can genuinely fail.  The side condition
  `pairScalar ≠ 0` on channels (weaker than `OmegaNe`, which asks about the
  `F`/`Finv` product only) is exactly what clearing denominators needs, and it
  is the real content of the nonvanishing hypotheses.
* Where `F ≠ 0` the *retained* fourth law and the `F`-free one are equivalent
  (`coherent_of_qualified` and `mul_right_cancel₀`), so proving the retained form
  is not a weaker target on that region.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u

namespace FusionCategory

open FusionMat

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the mate pairing scalar -/

/-- **The mate pairing scalar.**  `pairScalar S x y z` is the scalar of the
tensor-structure pairing `(y* ⊗ x*) ⊗ (x ⊗ y) → 1` on the channel `z` of
`x ⊗ y`, in the reconstruction:

`P(x,y;z) = F(y*,x*,z,1,z*,y) · Finv(x*,x,y,y,z,1) · ev x · ev y`.

`comparisonScalar S x y z = ev z / P(x,y;z)` — that is
`comparisonScalar_mul_pairScalar` below. -/
noncomputable def pairScalar (S : FusionSystem n k) (x y z : Fin n) : k :=
  if h : 0 < n then
    S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
        S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y
  else 0

@[simp] theorem pairScalar_def (S : FusionSystem n k) (x y z : Fin n) :
    pairScalar S x y z =
      (if h : 0 < n then
        S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, h⟩ (S.ring.dual z) y *
            S.Finv (S.ring.dual x) x y y z ⟨0, h⟩ * S.ev x * S.ev y
      else 0) := rfl

/-- **The mate equation**: `ψ = comparisonScalar` times the pairing is the
evaluation.  Same content as `comparisonScalar_spec`, phrased with
`pairScalar` as the pairing. -/
theorem comparisonScalar_mul_pairScalar (S : FusionSystem n k) (hn : 0 < n)
    (x y z : Fin n) (hP : pairScalar S x y z ≠ 0) :
    comparisonScalar S x y z * pairScalar S x y z = S.ev z := by
  have hP' : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
      S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ * S.ev x * S.ev y ≠ 0 := by
    simpa only [pairScalar_def, dif_pos hn] using hP
  simpa only [pairScalar_def, dif_pos hn] using comparisonScalar_spec S hn x y z hP'

/-- **Mate uniqueness.**  A scalar which, against the same nonzero pairing,
produces the same evaluation *is* the comparison scalar. -/
theorem eq_comparisonScalar_of_mul_pairScalar (S : FusionSystem n k) (hn : 0 < n)
    (x y z : Fin n) (hP : pairScalar S x y z ≠ 0) {c : k}
    (h : c * pairScalar S x y z = S.ev z) :
    c = comparisonScalar S x y z := by
  have h2 := comparisonScalar_mul_pairScalar S hn x y z hP
  rw [← h2] at h
  exact mul_right_cancel₀ hP h

/-- Two scalars satisfying the mate equation against the same nonzero pairing
agree. -/
theorem eq_of_mul_pairScalar_eq (S : FusionSystem n k) (x y z : Fin n)
    (hP : pairScalar S x y z ≠ 0) {c c' : k}
    (h : c * pairScalar S x y z = S.ev z) (h' : c' * pairScalar S x y z = S.ev z) :
    c = c' := by
  have h1 : c * pairScalar S x y z = c' * pairScalar S x y z := by rw [h, h']
  exact mul_right_cancel₀ hP h1

/-! ## §2 — the pairing in expanded form -/

/-- `P(x,y;z)` with the `ev`-factors isolated. -/
theorem pairScalar_self (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) :
    pairScalar S x y z =
      (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
          S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩) * (S.ev x * S.ev y) := by
  rw [pairScalar_def, dif_pos hn]
  ring

/-- `P(y*,x*;z*)` — the dual triple — with the doubly dual labels reduced.
These are exactly the two `F`/`Finv` factors in the numerator of `omegaCoeff`. -/
theorem pairScalar_dual_dual (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n) :
    pairScalar S (S.ring.dual y) (S.ring.dual x) (S.ring.dual z) =
      (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
          S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
            (S.ring.dual z) ⟨0, hn⟩) * (S.ev y * S.ev x) := by
  rw [pairScalar_def, dif_pos hn]
  simp only [FusionRing.dual_dual, S.ev_dual]
  ring

/-- The pairing is nonzero wherever its two `F`/`Finv` factors are. -/
theorem pairScalar_ne_zero (S : FusionSystem n k) (hn : 0 < n) (x y z : Fin n)
    (h : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
        S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ ≠ 0) :
    pairScalar S x y z ≠ 0 := by
  rw [pairScalar_self S hn]
  exact mul_ne_zero h (mul_ne_zero (S.ev_ne_zero x) (S.ev_ne_zero y))

/-! ## §3 — the associator-only coefficient is a ratio of mate pairings -/

/-- **`omegaCoeff` is the double-dual ratio of the mate pairing**:
`Ω(a,b;c) = P(b*,a*;c*) / P(a,b;c)`.  The `ev`-factors of the two pairings are
equal by `ev_dual`, which is why the associator-only form exists at all. -/
theorem omegaCoeff_eq_pairScalar_div (S : FusionSystem n k) (hn : 0 < n)
    (a b c : Fin n) :
    FusionMat.omegaCoeff S a b c =
      pairScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) /
        pairScalar S a b c := by
  rw [FusionMat.omegaCoeff_def, dif_pos hn,
    pairScalar_dual_dual S hn a b c, pairScalar_self S hn a b c]
  have hx : S.ev a * S.ev b ≠ 0 := mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b)
  rw [mul_comm (S.ev b) (S.ev a), mul_div_mul_right _ _ hx]


/-! ## §4 — `omegaCoeff` and `derivedJGen` agree with no nonvanishing hypothesis

`DoubleDualTensorator.derivedJGen_eq_omegaCoeff` carries two explicit
nonvanishing hypotheses (`OmegaNe`), because it cancels `ev`-factors through
`comparisonScalar`.  Written with the mate pairing the cancellation is
immediate, and it survives the degenerate cases in a field (`x / 0 = 0` on both
sides): **`derivedJGen = omegaCoeff` on every label**, no hypothesis at all. -/

/-- **`derivedJGen` is `omegaCoeff`, unconditionally.** -/
theorem derivedJGen_eq_omegaCoeff_uncond (S : FusionSystem n k) (hn : 0 < n)
    (a b c : Fin n) :
    derivedJGen S a b c = omegaCoeff S a b c := by
  have h1 : comparisonScalar S a b c = S.ev c / pairScalar S a b c := by
    rw [comparisonScalar_def, dif_pos hn, pairScalar_self S hn]
    congr 1
    ring
  have h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) =
      S.ev c / pairScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) := by
    rw [comparisonScalar_def, dif_pos hn, pairScalar_self S hn]
    simp only [FusionRing.dual_dual, S.ev_dual]
    congr 1
    ring
  rw [omegaCoeff_eq_pairScalar_div S hn, derivedJGen_def, h1, h2]
  have hev : S.ev c ≠ 0 := S.ev_ne_zero c
  by_cases hP : pairScalar S a b c = 0
  · simp only [hP, div_zero, zero_div]
  · by_cases hQ : pairScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) = 0
    · simp only [hQ, div_zero, zero_div]
    · field_simp

/-- **The reduction without nonvanishing hypotheses**: the `F`-free fourth law
for `derivedJGen` is equivalent to the associator-only cocycle identity for
`omegaCoeff` — with *no* `OmegaNe`, unlike
`DerivedJCoherent.derivedJGen_coherent_iff_omegaCoeff_cocycle`. -/
theorem derivedJGen_qualified_iff_omegaCoeff_uncond (S : FusionSystem n k) (hn : 0 < n) :
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        derivedJGen S a b e * derivedJGen S e c d
          = derivedJGen S b c f * derivedJGen S a f d) ↔
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        omegaCoeff S a b e * omegaCoeff S e c d
          = omegaCoeff S b c f * omegaCoeff S a f d) := by
  have key : ∀ a b c : Fin n, derivedJGen S a b c = omegaCoeff S a b c :=
    fun a b c => derivedJGen_eq_omegaCoeff_uncond S hn a b c
  constructor
  · intro h a b c d e f h1 h2 h3 h4
    have hh := h a b c d e f h1 h2 h3 h4
    simpa only [key] using hh
  · intro h a b c d e f h1 h2 h3 h4
    simpa only [key] using h a b c d e f h1 h2 h3 h4

/-! ## §5 — the pairing form of the remaining obligation

`J(x,y;z) = P^D(x,y;z)/P(x,y;z)` where `P^D` is the swap-dual
`P^D(x,y;z) = P(y*,x*;z*)` (§4).  Hence the two sides of the cocycle identity
are the **swap-dual ratios of the two twofold evaluation products**

  `Π_L = P(a,b;e)·P(e,c;d)`   (left bracket),
  `Π_R = P(b,c;f)·P(a,f;d)`   (right bracket),

and the identity reads `Π_L^D/Π_L = Π_R^D/Π_R`: *the swap-dual ratio of the
twofold evaluation is independent of the associator path*.  This is the exact
form in which the mate picture states the remaining obligation; it mentions no
`ev`, no `coev` and no `comparisonScalar`, only `pairScalar`. -/

/-- **The swap-dual of the pairing.**  `P ↦ P^D` is an involution, so
`J = P^D/P` is the "double-dual ratio" of the pairing. -/
noncomputable def pairDual (S : FusionSystem n k) (x y z : Fin n) : k :=
  pairScalar S (S.ring.dual y) (S.ring.dual x) (S.ring.dual z)

/-- `P ↦ P^D` is an involution. -/
theorem pairDual_dual (S : FusionSystem n k) (x y z : Fin n) :
    pairDual S (S.ring.dual y) (S.ring.dual x) (S.ring.dual z) = pairScalar S x y z := by
  unfold pairDual
  rw [FusionRing.dual_dual, FusionRing.dual_dual, FusionRing.dual_dual]

/-- On the `x ⊗ x* ∋ 1` channel the swap-dual *is* the pairing: the
mate-level form of `derivedJGen_dual` (`J x x* 1 = 1`), and the reason that law
is free in the mate picture. -/
theorem pairDual_dual_right (S : FusionSystem n k) (hn : 0 < n) (x : Fin n) :
    pairDual S x (S.ring.dual x) ⟨0, hn⟩ = pairScalar S x (S.ring.dual x) ⟨0, hn⟩ := by
  unfold pairDual
  rw [FusionRing.dual_dual, S.ring.dual_zero hn]

/-- `omegaCoeff` as the swap-dual ratio of the pairing. -/
theorem omegaCoeff_eq_pairDual_div (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    omegaCoeff S a b c = pairDual S a b c / pairScalar S a b c := by
  rw [omegaCoeff_eq_pairScalar_div S hn]
  rfl

/-- **The derived twist is the swap-dual ratio of the mate pairing.** -/
theorem derivedJGen_eq_pairDual_div (S : FusionSystem n k) (a b c : Fin n) :
    derivedJGen S a b c = pairDual S a b c / pairScalar S a b c := by
  rw [derivedJGen_eq_omegaCoeff_uncond S a.pos, omegaCoeff_eq_pairScalar_div S a.pos]
  rfl

/-- **The remaining obligation, in the mate picture.**  For every supported
`(a,b,c,d)` and every pair of channels `e` (`a ⊗ b`), `f` (`b ⊗ c`), the
swap-dual ratio of the twofold evaluation product is path independent. -/
def PairCocycle (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    pairDual S a b e * pairDual S e c d / (pairScalar S a b e * pairScalar S e c d)
      = pairDual S b c f * pairDual S a f d / (pairScalar S b c f * pairScalar S a f d)

/-- **The fourth law in the mate picture**: the `F`-free fourth law for the
derived twist is *equivalent* to `PairCocycle`.  Both sides are products of
swap-dual ratios; the equivalence is `div_mul_div_comm` and needs no
nonvanishing hypothesis. -/
theorem derivedJGen_qualified_iff_pairCocycle (S : FusionSystem n k) (hn : 0 < n) :
    (∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
        0 < S.ring.N b c f → 0 < S.ring.N a f d →
        derivedJGen S a b e * derivedJGen S e c d
          = derivedJGen S b c f * derivedJGen S a f d) ↔ PairCocycle S := by
  rw [derivedJGen_qualified_iff_omegaCoeff_uncond S hn]
  constructor
  · intro h a b c d e f h1 h2 h3 h4
    have hh := h a b c d e f h1 h2 h3 h4
    rw [omegaCoeff_eq_pairDual_div S hn, omegaCoeff_eq_pairDual_div S hn,
      omegaCoeff_eq_pairDual_div S hn, omegaCoeff_eq_pairDual_div S hn,
      div_mul_div_comm, div_mul_div_comm] at hh
    exact hh
  · intro h a b c d e f h1 h2 h3 h4
    have hh := h a b c d e f h1 h2 h3 h4
    rw [omegaCoeff_eq_pairDual_div S hn, omegaCoeff_eq_pairDual_div S hn,
      omegaCoeff_eq_pairDual_div S hn, omegaCoeff_eq_pairDual_div S hn,
      div_mul_div_comm, div_mul_div_comm]
    exact hh

/-! ## §6 — support: the pairing vanishes off the channels -/

/-- `P(x,y;z)` vanishes unless `z` is a channel of `x ⊗ y`.  This is the
support lemma a block-matrix argument needs: the pairing matrix of `x ⊗ y`
against `y* ⊗ x*` is supported on the channels, so its entries are the
`pairScalar` values. -/
theorem pairScalar_eq_zero_of_not_chan (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (h : ¬ (0 < S.ring.N x y z)) : pairScalar S x y z = 0 := by
  rw [pairScalar_self S hn]
  have hF : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y = 0 := by
    refine S.F_support (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y ?_
    intro hcon
    exact h (by rw [S.ring.dual_symm x y z]; exact hcon.1)
  simp only [hF, zero_mul]


/-! ## §7 — the assembly: `PairCocycle` is the whole remaining obligation

`DerivedJCoherent.exists_fusionSystem_derivedJGen` needs the *retained* fourth
law.  The free form (`TwistQualified`) gives it by
`DerivedJCoherent.coherent_of_qualified`, and the free form is equivalent to
`PairCocycle` (§6).  So the fixpoint datum `J = derivedJGen` follows from
`PairCocycle` and the (frozen, separate) nonvanishing law, and from nothing
else. -/

/-- **The retained fourth law from the mate-picture obligation.** -/
theorem derivedJGen_coherent_of_pairCocycle (S : FusionSystem n k) (hn : 0 < n)
    (h : PairCocycle S) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  refine coherent_of_qualified ?_
  intro a b c d e f h1 h2 h3 h4 _
  exact (derivedJGen_qualified_iff_pairCocycle S hn).mpr h a b c d e f h1 h2 h3 h4

/-- **The twist is computed, not carried, from `PairCocycle`**: no associator
algebra beyond `PairCocycle` and the frozen nonvanishing law is left. -/
theorem exists_fusionSystem_derivedJGen_of_pairCocycle (S : FusionSystem n k) (hn : 0 < n)
    (hne : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0)
    (h : PairCocycle S) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  exists_fusionSystem_derivedJGen S hne (derivedJGen_coherent_of_pairCocycle S hn h)


/-! ## §8 — the target as a division-free monomial factorisation

The pairing form `PairCocycle` (§5) is a statement about quotients.  Clearing
denominators turns it into a **monomial identity**: the cross-multiplied form
`CrossCocycle` has no division at all, and it follows from a *single* factorisation
law

  `P^D(a,b;c) · φ c = P(a,b;c) · (φ a · φ b)`   for all supported `(a,b,c)`,

by cancelling.  This is the form in which an identity among boundary `F`/`Finv`
entries can be *found*: both sides of the factorisation law are monomials, so a
derivation is a derivation in the free abelian group on the boundary entries.
The converse (a `φ` always exists) is the classical "pivotal" statement and is
*not* proved here. -/

/-- **The division-free form of the remaining obligation.** -/
def CrossCocycle (S : FusionSystem n k) : Prop :=
  ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
    0 < S.ring.N b c f → 0 < S.ring.N a f d →
    pairDual S a b e * pairDual S e c d * pairScalar S b c f * pairScalar S a f d
      = pairScalar S a b e * pairScalar S e c d * pairDual S b c f * pairDual S a f d

/-- **A pivotal factor of the mate pairing**: a nowhere-vanishing `φ` making the
swap-dual ratio the coboundary `φ a · φ b / φ c`.  Division-free form. -/
def PivotalFactor (S : FusionSystem n k) (φ : Fin n → k) : Prop :=
  (∀ i : Fin n, φ i ≠ 0) ∧
    ∀ a b c : Fin n, 0 < S.ring.N a b c →
      pairDual S a b c * φ c = pairScalar S a b c * (φ a * φ b)

/-- **A pivotal factor gives the division-free cocycle**, with no nonvanishing
hypothesis: substitute `P^D = P·φ a·φ b/φ c` in all four factors and both sides
become the same monomial `Π P · φ a · φ b · φ c / φ d`. -/
theorem crossCocycle_of_pivotalFactor (S : FusionSystem n k) {φ : Fin n → k}
    (h : PivotalFactor S φ) : CrossCocycle S := by
  obtain ⟨hφ, hfac⟩ := h
  intro a b c d e f h1 h2 h3 h4
  have hD1 : pairDual S a b e = pairScalar S a b e * (φ a * φ b) / φ e := by
    rw [eq_div_iff (hφ e)]
    exact hfac a b e h1
  have hD2 : pairDual S e c d = pairScalar S e c d * (φ e * φ c) / φ d := by
    rw [eq_div_iff (hφ d)]
    exact hfac e c d h2
  have hD3 : pairDual S b c f = pairScalar S b c f * (φ b * φ c) / φ f := by
    rw [eq_div_iff (hφ f)]
    exact hfac b c f h3
  have hD4 : pairDual S a f d = pairScalar S a f d * (φ a * φ f) / φ d := by
    rw [eq_div_iff (hφ d)]
    exact hfac a f d h4
  rw [hD1, hD2, hD3, hD4]
  have he := hφ e
  have hd := hφ d
  have hf := hφ f
  field_simp

/-- Clearing denominators: `CrossCocycle` is `PairCocycle` provided the mate
pairing does not vanish on the channels. -/
theorem pairCocycle_iff_crossCocycle (S : FusionSystem n k)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    PairCocycle S ↔ CrossCocycle S := by
  constructor
  · intro h a b c d e f h1 h2 h3 h4
    have hP1 := hne a b e h1
    have hP2 := hne e c d h2
    have hP3 := hne b c f h3
    have hP4 := hne a f d h4
    have hh := h a b c d e f h1 h2 h3 h4
    rw [div_eq_div_iff (mul_ne_zero hP1 hP2) (mul_ne_zero hP3 hP4)] at hh
    linear_combination hh
  · intro h a b c d e f h1 h2 h3 h4
    have hP1 := hne a b e h1
    have hP2 := hne e c d h2
    have hP3 := hne b c f h3
    have hP4 := hne a f d h4
    have hh := h a b c d e f h1 h2 h3 h4
    rw [div_eq_div_iff (mul_ne_zero hP1 hP2) (mul_ne_zero hP3 hP4)]
    linear_combination hh

/-- **The whole target from a pivotal factor**: the retained fourth law. -/
theorem derivedJGen_coherent_of_pivotalFactor (S : FusionSystem n k) (hn : 0 < n)
    {φ : Fin n → k} (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f :=
  derivedJGen_coherent_of_pairCocycle S hn
    ((pairCocycle_iff_crossCocycle S hne).mpr (crossCocycle_of_pivotalFactor S h))

/-- **The twist is computed, not carried, from a pivotal factor of the mate
pairing.** -/
theorem exists_fusionSystem_derivedJGen_of_pivotalFactor (S : FusionSystem n k)
    (hn : 0 < n) {φ : Fin n → k} (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hJ : ∀ i j kk : Fin n, 0 < S.ring.N i j kk → derivedJGen S i j kk ≠ 0) :
    ∃ S' : FusionSystem n k,
      S'.F = S.F ∧ S'.Finv = S.Finv ∧ S'.ev = S.ev ∧ S'.coev = S.coev
        ∧ S'.J = derivedJGen S :=
  exists_fusionSystem_derivedJGen S hJ
    (derivedJGen_coherent_of_pivotalFactor S hn h hne)

/-- The pivotal factor *is* a coboundary description of the derived twist: on
the channels where the mate pairing is nonzero, `derivedJGen = φ a · φ b / φ c`.
So `PivotalFactor` is exactly the mate-level (division-free) form of
`DerivedJCoherent.coherent_free_of_coboundary`'s hypothesis. -/
theorem derivedJGen_eq_coboundary_of_pivotalFactor (S : FusionSystem n k)
    {φ : Fin n → k} (h : PivotalFactor S φ)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c := by
  intro a b c hN
  have hP := hne a b c hN
  have hc : φ c ≠ 0 := h.1 c
  have hD : pairDual S a b c = pairScalar S a b c * (φ a * φ b) / φ c := by
    rw [eq_div_iff hc]
    exact h.2 a b c hN
  rw [derivedJGen_eq_pairDual_div, hD]
  field_simp


/-! ## §9 — the raw monomial form of the pivotal factor

For a proof search the useful shape of `PivotalFactor` has no `ev` in it: the
`ev`-factors of `pairScalar` and `pairDual` are *equal* pairs, so they cancel,
leaving **two `F`-entries and two `Finv`-entries per channel** — the exact
monomial shape that a boundary instantiation of the pentagon produces. -/

/-- **The pivotal factor, entries only.**  `PivotalFactor` unwound: two boundary
`F`-entries and two boundary `Finv`-entries times `φ`.  This is the statement a
derivation in the free abelian group on the boundary entries has to produce. -/
theorem pivotalFactor_entries (S : FusionSystem n k) (hn : 0 < n) {φ : Fin n → k}
    (h : PivotalFactor S φ) :
    ∀ a b c : Fin n, 0 < S.ring.N a b c →
      S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
          S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
            (S.ring.dual c) ⟨0, hn⟩ * φ c
        = S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
          S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ * (φ a * φ b) := by
  intro a b c hN
  have hh := h.2 a b c hN
  unfold pairDual at hh
  rw [pairScalar_dual_dual S hn a b c, pairScalar_self S hn a b c] at hh
  have hev : S.ev a * S.ev b ≠ 0 := mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b)
  refine mul_right_cancel₀ hev ?_
  linear_combination hh


/-! ## §10 — the interface is not vacuous: pointed data give a pivotal factor

The converse of `derivedJGen_eq_coboundary_of_pivotalFactor`, under the
nonvanishing of the mate pairing: a twist table that is a coboundary *is* a
pivotal factor.  Consequently `PivotalFactor S S.kappa` holds on every pointed
datum (`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed`), so the
factorisation route of §8 is a genuine route and not an empty hypothesis. -/

/-- A coboundary description of `derivedJGen` is a pivotal factor, on the
channels where the mate pairing is nonzero. -/
theorem pivotalFactor_of_coboundary (S : FusionSystem n k) {φ : Fin n → k}
    (hφ : ∀ i : Fin n, φ i ≠ 0)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c) :
    PivotalFactor S φ := by
  refine ⟨hφ, ?_⟩
  intro a b c hN
  have hP := hne a b c hN
  have hc : φ c ≠ 0 := hφ c
  have hD : pairDual S a b c / pairScalar S a b c = φ a * φ b / φ c := by
    rw [← derivedJGen_eq_pairDual_div]
    exact hJ a b c hN
  have h3 : pairDual S a b c = pairScalar S a b c * (φ a * φ b) / φ c := by
    have h4 : pairDual S a b c / pairScalar S a b c * pairScalar S a b c
        = (φ a * φ b / φ c) * pairScalar S a b c := by rw [hD]
    rw [div_mul_cancel₀ _ hP] at h4
    rw [h4]
    field_simp
  rw [h3]
  field_simp

/-- **Pointed data carry a pivotal factor** (`φ = κ`): the mate-level form of
the pointed `δ(κ)` theorem. -/
theorem pivotalFactor_kappa_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    PivotalFactor S S.kappa :=
  pivotalFactor_of_coboundary S (fun i => S.kappa_ne_zero i) hne
    (fun a b c hN => derivedJGen_eq_delta_kappa_of_pointed S hn hP hN)

/-- Consequently the fourth law holds on pointed data from the mate-picture
route, independently of `DerivedJCoherent.derivedJGen_coherent_of_pointed`. -/
theorem derivedJGen_coherent_of_pointed_mate (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f :=
  derivedJGen_coherent_of_pivotalFactor S hn (pivotalFactor_kappa_of_pointed S hn hP hne) hne

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.pairScalar
#print axioms FusionCategory.pairScalar_def
#print axioms FusionCategory.comparisonScalar_mul_pairScalar
#print axioms FusionCategory.eq_comparisonScalar_of_mul_pairScalar
#print axioms FusionCategory.eq_of_mul_pairScalar_eq
#print axioms FusionCategory.pairScalar_self
#print axioms FusionCategory.pairScalar_dual_dual
#print axioms FusionCategory.pairScalar_ne_zero
#print axioms FusionCategory.omegaCoeff_eq_pairScalar_div

#print axioms FusionCategory.derivedJGen_eq_omegaCoeff_uncond
#print axioms FusionCategory.derivedJGen_qualified_iff_omegaCoeff_uncond
#print axioms FusionCategory.pairDual
#print axioms FusionCategory.pairDual_dual
#print axioms FusionCategory.pairDual_dual_right
#print axioms FusionCategory.derivedJGen_eq_pairDual_div
#print axioms FusionCategory.PairCocycle
#print axioms FusionCategory.derivedJGen_qualified_iff_pairCocycle
#print axioms FusionCategory.pairScalar_eq_zero_of_not_chan
#print axioms FusionCategory.derivedJGen_coherent_of_pairCocycle
#print axioms FusionCategory.exists_fusionSystem_derivedJGen_of_pairCocycle

#print axioms FusionCategory.CrossCocycle
#print axioms FusionCategory.PivotalFactor
#print axioms FusionCategory.crossCocycle_of_pivotalFactor
#print axioms FusionCategory.pairCocycle_iff_crossCocycle
#print axioms FusionCategory.derivedJGen_coherent_of_pivotalFactor
#print axioms FusionCategory.exists_fusionSystem_derivedJGen_of_pivotalFactor
#print axioms FusionCategory.derivedJGen_eq_coboundary_of_pivotalFactor
#print axioms FusionCategory.pivotalFactor_entries
#print axioms FusionCategory.pivotalFactor_of_coboundary
#print axioms FusionCategory.pivotalFactor_kappa_of_pointed
#print axioms FusionCategory.derivedJGen_coherent_of_pointed_mate
