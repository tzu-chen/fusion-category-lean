# FusionCategory — Plan for ENO Proposition 8.23

**Goal:** `pseudo-unitary → spherical` with `dim = FPdim`, unconditional in Lean 4.33.1.
This is the lemma that makes every recent classification/certification paper work,
and the only tractable piece of ENO Conjecture 2.8. Full `Id ≅ **` for arbitrary
fusion categories requires weak Hopf `S⁴` and is not attempted.

**Source theorem:** Etingof–Nikshych–Ostrik, *On fusion categories*, Annals 162 (2005),
§2.2, §3, §8.4, Prop. 8.23–8.26. Secondary: EGNO *Tensor Categories* Thm 9.6.10–9.6.12,
Bartlett 2009 PhD Prop 5.7 Lemma 6.2, Shimizu *Frobenius–Schur*.

## Status after the Step-2 rewrite

`System.lean` and `Pivotal.lean` were rewritten because the old signature could
not be inhabited and its pivotal axiom was vacuous:

* `FusionSystem`'s two unit axioms were mutually inconsistent for `n ≥ 2`
  (at `(0,b,0,d,b,0)` they force `1` and `0`), so the structure had **no
  inhabitants** and every theorem quantified over it vacuously.  `VecZ2.system`
  in `System.lean` is now a proved inhabitant, and the pentagon is checked on
  all 512 label tuples of `Vec_{Z/2}`.
* the identity called `pentagon` was not the pentagon: it had eight free labels
  where the F-matrix pentagon needs ten, and it fails on `Vec_{Z/2}^ω` for
  *every* `ω`, the trivial cocycle included.
* `PivotalStructure.p_fusion` assumed the double-dual twist `J ≡ 1`, where `J`
  is the monoidal structure of `(−)**`.  `J` is now carried by `FusionSystem`
  and read by `p_mon : p kk = J i j kk * p i * p j`.  `p_dual` is derived from
  the `i ⊗ i* ∋ 1` channel, not assumed.
* `IsSpherical` was `p i = p (i*)`, which never mentions `F` and is satisfied by
  `p ≡ 1` for every fusion-rule table.  Sphericity is now `dim (i*) = dim i`,
  with `dim i = p i * kappa i` and `kappa i = coev i * ev i`; equivalently
  `kappa (i*) = p i² * kappa i`.
* `pseudoUnitary_spherical` and the three corollaries in
  `Examples/PseudoUnitaryInstances.lean` are **retired**.  They were proved by
  exhibiting `p ≡ 1`, which satisfies the old axiom with no hypothesis at all.
  The genuine statement is `ENO823` in `PseudoUnitary.lean`, recorded as an open
  target.
* the three `axiom`s in `Grading.lean` are gone: `torsor_p_dual` is now
  `PivotalStructure.pVal_dual`, and `pivotal_iff_square` /
  `pivotal_of_no2Torsion` are `def`s recording open targets.  `AxiomAudit.lean`
  reports `[propext, Classical.choice, Quot.sound]` throughout, and the library
  contains no `sorry` and no `axiom`.

A second defect in the same sign was caught by the derivation swarm: the
`snake_right` axiom wrote the second snake with a factor of `F` instead of its
reciprocal, which forced `F^{i i* i}_i(1,1) = F^{i* i i*}_{i*}(1,1)` and so
excluded every pointed category whose cocycle is non-trivial in this
normalisation (`Vec^ω_{Z/3}`).  It was corrected to a reciprocal.  That
correction was *also* wrong, in the opposite direction, and it is corrected
again here; see the next section.  `snake_consistency` now records what the two
snakes actually force: the `(0,0)` entry of `F^{i i* i}_i` equals the `(0,0)`
entry of the inverse block `(F^{i* i i*}_{i*})⁻¹`.

`J` is **derived** from the duality data in the strict self-dual normalisation
(`DoubleDual.lean`).  The definition that file originally carried,
`J a b c = ev a * ev b / ev c`, is the ψ-scalar and *not* `J`; that was retracted
in `a168b32`, together with the coboundary gauge law.  The correct statement is
the ratio formula recorded under "The derived twist: result" below.  What is
still true from that file: `J`'s coherence for `Vec_{Z/2}` is verified rather
than chosen, and the twist is a genuine ratio of composites.

Still owed: an independent evaluation of the `J`-diagram (the non-self-dual
`F`-twisted case is now *checked* on nine data sets and *derived* only as a
reconstruction — see "The derived twist: result" below); a model with
`(−)** ≠ id` on labels, which `FusionSystem` cannot represent as it stands; the
multiplicity-free restriction (`N ≤ 1`) as a separate general-multiplicity
development; and the analytic input for `ENO823`.

## Prior art, checked

Searched before continuing; three bodies of work are adjacent and none is a
drop-in:

* **Mathlib** has `RigidCategory` (`CategoryTheory.Monoidal.Rigid.Basic`) but
  no pivotal or spherical categories. They are in flight: PR #42150
  (*pivotal categories*, blocked-by-other-PR), and PRs #42191 (*spherical
  categories*) and #42192 (*symmetric rigid categories are spherical*) build on
  it. This is exactly the layer vendored as `MathlibPatches/PivotalCategory.lean`
  (still a stub), and it is why the plan says to keep the patch
  byte-compatible: when #42150 lands, the bridge becomes an import. Nothing to
  reinvent here, only to track.
* **Alphabeta Math** (alphabetamath.cc) has a generated library page *Unitary
  Fusion Spaces, F/R Symbols, and Anyon Models* with multiplicity-aware fusion
  trees, the F-symbol as a recoupling matrix, the pentagon in fusion-tree
  coordinates, gauge covariance, and explicit Fibonacci and Ising carriers. It
  is pipeline-generated with provenance labels, and the page reports two
  results verified on it. Its target is unitary/braided anyon data, not
  pivotality, so it overlaps `System.lean` and the `DoubleDual` computation but
  not the question this project asks.
* **TNLean** (sirui-lu.com/TNLean) is a blueprint project on tensor networks
  whose anyon chapter treats quantum-double models. Different object (microscopic
  models rather than abstract fusion data).
* Data, not code: **AnyonWiki** supplies F/R/pivotal tables in a fixed gauge for
  the multiplicity-free categories up to rank 7; our Fibonacci and Ising
  conventions should follow it rather than be derived afresh.

Conclusion: no finished Lean formalization of pivotal fusion categories exists
to reuse; the categorical infrastructure is being landed in Mathlib right now,
so the cheap long-term move is to keep our skeletal layer aligned with
#42150/#42191 naming and stub out the bridge, as already planned.

## The duality normalisation: the right snake needs the inverse block

The Fibonacci and Ising instances were blocked by a third defect in the same
axiom, and the diagnosis recorded here previously (a missing mirror evaluation,
"`F² = ν`") was **wrong**.  What the two snake equations of a rigid skeletal
category actually say, with `κ i = coev i * ev i`, is

    snake_left  : κ i · F^{i i* i}_i(0,0) = 1,
    snake_right : κ i · (F^{i* i i*}_{i*})⁻¹(0,0) = 1,

where the second entry is the `(0,0)` entry of the **matrix inverse** of the
associator block at `(a,b,c,d) = (i*, i, i*, i*)` — not the reciprocal of the
single entry `F^{i* i i*}_{i*}(0,0)`.  The two agree exactly when that block is
`1 × 1`, which is the case for every pointed category (that is why the
`kappa / F` correction fixed `Vec^ω_{Z/3}`), and they differ as soon as the
block is bigger, which is exactly the self-dual case `i* = i` with
`N i i 0 = N i i i = 1`.

Checked numerically on honest linear models of the two examples (associator
blocks composed as matrices, `α⁻¹` inverted numerically, not by taking
reciprocals):

    Fibonacci, φ = (1+√5)/2, gauge F^{τττ}_τ = [[1/φ, 1], [1/φ, -1/φ]]:
        κ_τ = φ;  κ_τ · F(0,0) = 1  and  κ_τ · (F⁻¹)(0,0) = 1   (F is an involution)
        the reciprocal reading demands κ_τ = 1/φ instead, i.e. φ² = 1.
    Ising, F^{σσσ}_σ = (1/√2)[[1,1],[1,-1]]:
        κ_σ = √2; same phenomenon, κ_σ / F(0,0) = 2 ≠ 1.

So the fix is to carry the inverse associator `Finv` with its two inverse laws
(`α ∘ α⁻¹ = id`, `α⁻¹ ∘ α = id`, on the channel sets) and to state
`snake_right` with `Finv`.  `System.lean` does that; `Finv` is data because the
two channel index sets of a block are different subsets of `Fin n`, so there is
no canonical way to present the inverse block as a matrix indexed by `Fin n`.
`Vec_{Z/2}` still inhabits the structure (with `Finv a b c d f e = F a b c d e f`).

**The instances now exist.**  `Examples/FibonacciIsing.lean` builds
`FibonacciSystem : FusionSystem 2 ℝ` and `IsingSystem : FusionSystem 3 ℝ` with
every field proved — pentagon, both unit laws, both inverse laws, both snakes —
together with a pivotal structure `p ≡ 1` (`J ≡ 1`), sphericity and
`dim = FPdim` (`(1, φ)` and `(1, √2, 1)`).  The finite checks are done by
computation in `ℤ`: each entry is an integer pair `(p,q)` denoting
`(p + q√d)/2` in `ℚ(√d)` and `decide` verifies the identities exactly, so
there is no `norm_num` over the reals and no `native_decide`.  Ising needs the
gauge `F^{σψσ}_ψ = F^{ψσψ}_σ = -1` (with all `1 × 1` blocks `+1` the pentagon
fails at `(σ,σ,σ,ψ)` and `(σ,ψ,σ,σ)`), which is one of the two solutions of the
sign system (the other differs by the `λ_ψ = -1` gauge).  The cost is compile
time: the file takes about 100 s, so `lake build` now takes about 3 minutes
instead of 1.

## The coboundary reduction is a pointed-category statement

`Coboundary.lean`'s `KappaMultiplicative` — `κ c = κ a * κ b` on every fusion
channel — is *not* a theorem for a general fusion category, and it fails for
both new examples: Ising has `κ_1 = 1` but `κ_σ² = 2` on `σ ⊗ σ ∋ 1`, Fibonacci
the same with `φ²`.  It holds for pointed categories, where the dimension is a
character of the fusion ring.

Consequently `twist_eq_coboundary_of_pivotal` and `eno823_of_twist_coboundary`
are theorems about that situation only: a pivotal structure in general has
`J a b c = (dim c / (dim a * dim b)) · (κ a κ b / κ c)`, so `J` is the coboundary
of `dim` iff `κ` is multiplicative.  The claim in an earlier version of this
plan — that the open content of ENO 8.23 *is* that coboundary hypothesis — is
therefore too strong.  For non-pointed `C` the content is rather the sphericity
equation itself, `κ (i*) = (p i)² κ i` (`PivotalStructure.isSpherical_iff`), and
the examples realise it with `p ≡ 1` because they are self-dual, `κ (i*) = κ i`.
Both examples do satisfy the *conclusion*: a pivotal structure with
`dim = FPdim` that is spherical.

## The derived twist: result

`J` is the monoidal structure of `(−)** = (−)* ∘ (−)*`.  Since `(−)*` is
monoidal contravariant, `J` is a **ratio** of two cuspidal comparisons: with
`ψ_{a,b} : (a⊗b)* → b* ⊗ a*` the comparison between the two left duals
`(a⊗b)*` and `b* ⊗ a*` of `a⊗b`,

    J a b c = ψ_{a,b}|_c / ψ_{b*,a*}|_{c*} .

Evaluating `ψ` (two F-moves and one transported coevaluation) gives, in the
normalisation `ev_{i*} = ev_i`,

    Ω(a,b;c) = F^{b* a* c}_0(c*,b) · (M_b)^{-1}(0,c),    M_b(E,c') = F^{a* a b}_b(E,c'),
    J a b c  = Ω(b*,a*;c*) / Ω(a,b;c).

`M_b` is the block `F^{a* a b}_b` **restricted to its support** — rows `E`
channels of `a*⊗a` with `b ∈ E⊗b`, columns `c'` channels of `a⊗b` with
`b ∈ a*⊗c'`.  Unrestricted the matrix is rectangular (Ising at
`(a,b) = (σ,ψ)`: `2 × 1`) and the formula returns `0/0`; restricted it is
square and the formula is defined on every channel of every model tested.
`(M_b)^{-1}` is a genuine matrix inverse — a diagonal in `coev_b` is spread
over the whole channel space by the associator, so an entrywise reciprocal would
silently assume `M_b` were diagonal.

What is established, in order of strength:

* the two snakes in the matrix-inverse form of the previous section, verified on
  13–16 data sets, including non-self-dual objects and `2 × 2` blocks; the
  `i i* i` analogue of the second snake is **false** (`Vec^ω_{Z/3}` refutes it);
* the ratio structure of `J`, derived (m2, m7) and confirmed independently
  (m1, m3, m5, m6);
* `J ≡ 1` in the duality-compatible normalisation on all 16 data sets checked —
  Fibonacci, Ising, `Vec^ω_{Z/n}` for `n = 2,3,4,5`, and the products
  `Vec^ω_{Z/3} ⊠ Fib`, `Vec^ω_{Z/2} ⊠ Ising`, `Vec^ω_{Z/3} ⊠ Ising` — so
  `p ≡ 1` is pivotal with `dim = κ`.  This is *checked*, not proved: nobody
  produced an independent evaluation of the `J`-diagram from raw category data,
  so the formula is a reconstruction whose consequences are verified, not a
  derivation from first principles.  **The census cannot distinguish `J ≡ 1`
  from `J = δ(κ)`**: every pointed sample is cyclic (where `κ` is a character,
  so the two agree) and for Fibonacci and Ising `κ = FPdim`, which likewise
  makes the two right sides agree.  `(Z/2)²` separates them; see the correction
  under "Three further results" below.
* the gauge law `J ↦ J·(λ_a λ_b λ_{c*})/(λ_c λ_{a*} λ_{b*})`.  The invariant is
  `ν_i = κ_{i*}/κ_i`, not `κ` itself: under the vertex gauge
  `κ_i ↦ κ_i·v^{i i*}_0 v^{i* i}_0`, and `ν` is unchanged.  A channel gauge
  exists that makes both `J ≡ 1` and `κ_{i*} = κ_i` on the pointed examples, so
  `J ≡ 1` and sphericality are not in conflict — but they are different
  conditions, and `J ≡ 1` alone does not give `κ_{i*} = κ_i`;
* if `J ≡ 1` then `p ≡ 1` is pivotal and `κ` is a character of the fusion ring:
  `κ_a κ_b = Σ_c N^c_{ab} κ_c`.  So `κ` *is* a dimension function; the two
  examples have `κ = FPdim` (`φ`, `√2`), and `Vec^ω_{Z/2}` has the other
  character, `κ g = −1`.

**Correction to the coherence axiom.**  For a general `C` the `J`-pentagon
carries the associator on both sides,

    J a b e · J e c d · F^{abc}_d(e,f) = J b c f · J a f d · F^{a**b**c**}_{d**}(e**,f**),

and the F-free form `J a b e · J e c d = J b c f · J a f d` — which is
`FusionSystem.J_coherent` — is that equation only when `(−)**` is the identity
on labels.  The rest of `FusionSystem` fixes exactly that case: `J` has type
`Fin n → Fin n → Fin n → k` with no slot for a label transport, and `p_mon`
reads `p c = J a b c · p a · p b` with `c` the channel of `a ⊗ b`.  Every model
used has `a** = a`, so nothing is lost for the examples, but the general
statement is the displayed one and a `FusionSystem` with `i** ≠ i` is not
representable.

Three further results from the same swarm, worth keeping:

* **the pointed case is settled, and `J ≡ 1` is WRONG there.**  An earlier
  version of this bullet claimed that in a pointed category both dualities are
  canonical identifications of one-dimensional spaces, so the comparison
  `ν_{a,b} : (a⊗b)* → b* ⊗ a*` is `1` and hence `J ≡ 1` identically.  The
  conclusion is refuted (swarm `smvzybdp8`, m3, checked independently).  The
  correct value is

      J^c_{ab} = δ(κ)^c_{ab} = κ_a κ_b / κ_c,

  forced by multiplicativity of the categorical dimension: `dim = p·κ` with
  `p` pivotal gives `dim_a dim_b = Σ_c N^c_{ab} dim_c`, i.e. the *sum* identity
  **(M)** `Σ_c N^c_{ab} J^c_{ab} κ_c = κ_a κ_b`, which pins `J` per channel
  exactly when there is one channel.  `δ(κ)` satisfies the four `J`-axioms
  (`J^0_{ab} = J^{1}_{ii*} = 1` since `κ_g κ_{g*} = 1`), and `p_g = 1/κ_g` is
  then pivotal with `dim ≡ 1 = FPdim` and spherical.

  `δ(κ) = 1` iff `κ` is a character.  That holds for every cyclic group in the
  standard gauge — `Z/2,3,4,5,6` — which is why the census below saw `J ≡ 1`
  everywhere; the whole tested set was cyclic or built from Fibonacci and
  Ising, whose `κ = FPdim` makes `δ(κ) = FPdim_c κ_aκ_b/(κ_c FPdim_a FPdim_b)`
  the right side of (K) with `J = 1`.  It fails on `(Z/2)²`: with
  `ω = (-1)^{a₁b₂c₁}` one has `κ = (1,1,1,-1)`, not a character, `δ(κ) ≠ 1`,
  and the per-channel form of (K) is false for `J ≡ 1` while the sum form (M)
  survives.  Earlier versions of this plan asserted the per-channel identity
  as the general target; only (M) is general, and for non-pointed `C` the two
  genuinely differ (Ising: `J = 1`, `κ = FPdim`, `δ(κ) = 2` on `σ⊗σ ∋ 1`).
  The check is `docs/pointed_twist_check.py`, which recomputes every scalar
  above from the snake axioms (`python3 FusionCategory/docs/pointed_twist_check.py`).
* **what this does to the target.**  `ENO823` in `PseudoUnitary.lean` is stated
  for an arbitrary `FusionSystem`, and `J` there is data constrained only by
  the four laws, so a system with `J ≡ 1` on the `(Z/2)²` datum is
  representable and `ENO823` is *false* for it (no character `p` has
  `dim = FPdim = 1`; checked exhaustively).  The theorem therefore cannot be
  proved from the signature: `J` must be *defined* from `ev`, `coev` and `F`
  (and the definition must satisfy (M)), or (K)/(M) must be a hypothesis.
* **`ψ` and `θ` are not gauge-invariant objects.**  Rescaling the channel
  projections leaves every `F`-entry and every `ev`/`coev` unchanged but sends
  `θ(a,b;c) ↦ t^c_{ab} t^{c*}_{a*b*} θ(a,b;c)`, so only *ratios* such as `J`
  are meaningful.  A from-scratch diagram evaluator can therefore test the
  snake normalisation (it does: `κ_τ = φ` for Fibonacci in
  Temperley–Lieb(φ), with no `F`-data, against the naive `φ²`) but not the
  individual `Ω` values.
* **`FusionSystem` does not carry the triangle axiom** for a unit in the middle
  (`F^{a 1 c}_d(a,c) = δ`).  Neither example needs it — their middle-unit
  entries are `1` — but a signature that claims to be a skeletal monoidal
  category should carry it, and it is the one axiom of Mac Lane's list that is
  missing.

One claim from the swarm to *not* adopt: that `X** ≅ X` in any rigid monoidal
category, so a skeleton can always be chosen with `(−)** = id` on labels and
the F-free pentagon is therefore general.  The proof offered was "`X*` is both
a left and a right dual of `X`", which is precisely what a rigid category does
not give — identifying the left and right duals of an object is the content of
a pivotal structure, and `id ≅ (−)**` is exactly what need not exist.  So the
caveat above stands: the F-free form is the right statement for a skeleton in
which `i** = i`, which is the case for every model used here.

**Not derived:** the independent diagram evaluation of `J` itself (above); the
case `(−)** ≠ id` on labels; and the analytic input for `ENO823`.

## ENO 8.23: the sharp form

`Coboundary.lean` reduces the target to an equation.  With
`kappa i = coev i * ev i` the duality normalisation (which is *gauge
invariant*: `coev i ↦ lam i * coev i`, `ev i ↦ ev i / lam i` leaves it fixed and
preserves the snakes), and `kappa` multiplicative on fusion channels:

* a pivotal structure forces `J a b c = dim c / (dim a * dim b)` on every
  channel (`twist_eq_coboundary_of_pivotal`) — the twist of a pivotal structure
  is the coboundary of its dimension;
* conversely a character `d` of the fusion rules with `d c = J a b c * d a * d b`
  *is* a pivotal structure with `dim = d` (`exists_pivotal_of_coboundary`), and
  it is spherical when `d` is invariant under `*`
  (`exists_spherical_of_coboundary`);
* hence `ENO823` holds as soon as the twist is the coboundary of the
  FP-dimension (`eno823_of_twist_coboundary`).

So the open content of ENO Prop 8.23 is exactly the hypothesis of that last
theorem: pseudo-unitarity must produce `J a b c = FPdim c / (FPdim a * FPdim b)`.
That can only be proved once `J` is derived from `ev`, `coev` and `F` in
general, which is why the `F`-twisted case of `DoubleDual.lean` is the next
piece.  The `F`-twisted census for Fibonacci and Ising is the concrete test.

**The pointed hypothesis is now gone.**  `KappaMultiplicative` restricted the
reduction to pointed `C`; the general statement uses the twist in the duality
normalisation, `twistNorm a b c = J a b c * kappa c / (kappa a * kappa b)`,
which is `J` exactly when `kappa` is multiplicative.  In `Coboundary.lean`:

* `dim_eq_twistNorm` — for **every** pivotal structure,
  `dim P c = twistNorm a b c * dim P a * dim P b`, with no hypothesis on
  `kappa`; so a pivotal dimension is always a coboundary of `twistNorm`;
* `exists_pivotal_of_twistNorm`, `exists_spherical_of_twistNorm` — conversely a
  nonzero `d` with `d 1 = 1` and that equation *is* the dimension of a pivotal
  structure, spherical when `d` is `*`-invariant;
* `eno823_of_twistNorm` and its converse `twistNorm_eq_fpdim_ratio_of_dim_eq`.

Consequently, in this signature `ENO823` is **equivalent** to the single
per-channel identity

    FPdim c = twistNorm a b c * FPdim a * FPdim b,   i.e.
    J a b c = FPdim c * kappa a * kappa b / (kappa c * FPdim a * FPdim b),

and that identity is the whole of what remains.  It is not a consequence of the
axioms of `FusionSystem`: `J` is data there, constrained only by its unit, dual
and coherence laws, so a system may carry a coherent `J` admitting no pivotal
structure at all.  Pseudo-unitarity — a condition on Hom spaces and Hermitian
forms, invisible to a multiplicity-free skeleton where every Hom space is
one-dimensional — is what has to supply it.  `ENO823` still carries no
hypothesis expressing that, which is the substantive gap, not the algebra above.

**Upstream dependencies (pinned):**

* `leanprover/lean4:v4.33.1` with `mathlib` `0df444a3` — already pinned by `haagerup-odd/`
* `Mathlib.CategoryTheory.Monoidal.Rigid.Basic` — `RigidCategory` exists, lists
  `Future work: Define pivotal categories`. Do **not** re-define rigid.
* Open PR `leanprover-community/mathlib4#42145` `doubleRightDualFunctorMonoidal`
  and `#42150` `PivotalCategory` (+370/-13, blocked-by-other-PR). Until merged,
  vendor a minimal copy under `FusionCategory/MathlibPatches/` and keep it
  byte-compatible with those PRs. When they land, delete the patch.
* Open PF chain `#39914` `#39918` `#39919` `#39920` `#39922`
  (`PerronFrobenius.Irreducible`, `pft_irreducible`, `collatzWielandt`,
  `spectralRadius`). Same vendoring rule.

Axiom budget for all new theorems: `[propext, Classical.choice, Quot.sound]`
only — matching `haagerup-odd/`. No `sorry`.

---

## 0. Repository decisions (do first, ~30 min)

1. This project is **not** a submodule of `haagerup-odd`. It is a sibling
   Lake package `FusionCategory/` sharing the same toolchain (already done).
   Create `FusionCategory/lakefile.toml` with `defaultTargets = ["FusionCategory"]`
   and copy `lean-toolchain` + `lake-manifest.json` from `haagerup-odd/`
   verbatim. Do not bump `0df444a3` without updating both packages.
2. Add top-level `lakefile.toml` as workspace if desired, but keep
   `cd haagerup-odd && lake build` and `cd FusionCategory && lake build`
   working independently (CI builds each separately, as `safe_lean.py` does
   per-file).
3. Directory to create now:
   ```
   FusionCategory/
     lakefile.toml, lake-manifest.json, lean-toolchain
     FusionCategory.lean            # umbrella re-export
     FusionCategory/
       Basic.lean                   # fusion ring skeletal
       System.lean                  # F-symbols
       Pivotal.lean                 # p_i data
       Cover.lean                   # tilde construction
       Grading.lean                 # U_C and Aut^⊗(Id)
       PFDim.lean                   # FPdim via PF
       PseudoUnitary.lean           # Prop 8.23 main theorem
       Examples/
         Ising.lean, Fibonacci.lean  # certificates
     MathlibPatches/
       PivotalCategory.lean         # vendored #42150 until upstream
       PerronFrobenius.lean         # re-export or patch for #39922
   ```
4. Decide skeletal vs. abstract: **skeletal first** (finite F/p data),
   categorical second. This matches how `haagerup-odd/` verifies
   `CoeffData` → `EGEquations`, and how AnyonWiki/TensorCategories.jl
   store `F,R,p`. Abstract `MonoidalCategory` coherence is deferred to
   step 5.

## 1. Step 1 — Fusion rings and PF dimension (pure combinatorics)

**File:** `FusionCategory/Basic.lean`

* `structure FusionRing (n : ℕ)` with `N : Fin n → Fin n → Fin n → ℕ`,
  `dual : Fin n → Fin n`, axioms: `N i j 0 = if j=dual i then 1 else 0`,
  associativity `∑_k N i j k * N k l m = ∑_k N j l k * N i k m`,
  unit `0`, `dual` involution, `N i j k = N j* i* k*` etc.
  See `haagerup-odd/Analytic/Periods.lean` for `ZMod n` handling;
  reuse `ZMod n` lemmas where possible.
* `def FPdimMatrix (R : FusionRing n) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ`
  with entries `N i j k`.
* `def isIrreducible` via underlying quiver; prove `FPdimMatrix i` is
  non-negative irreducible when the ring is connected (true for all
  examples). Import `Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible`
  from PF chain — provides `pft_irreducible`, `exists_positive_eigenvector`.
* `noncomputable def FPdim (R) : Fin n → ℝ` as PF eigenvector normalized with
  `FPdim 0 = 1`. Prove `N i ⬝ᵥ v = FPdim i • v`, `FPdim i > 0`,
  `FPdim (dual i) = FPdim i`, uniqueness.
* `def globalFPdim (R) := ∑ i, (FPdim i)^2`.

**Checks:** `norm_num` examples for `Fibonacci` (golden ratio), `Ising`
(`√2`), `ℤ/3`. These are `rfl` after PF construction.

## 2. Step 2 — Skeletal fusion systems and pivotal data

**Files:** `System.lean`, `Pivotal.lean`

* `structure FusionSystem (R : FusionRing n) (k : Type) [Field k]` with
  `F : ∀ i j k l, Matrix ...` (or indexed family `F^{ijk}_l` as
  `F i j k l : (e : Fin n) → (f : Fin n) → k`), pentagon:
  `∑_e F^{ijc}_d(e,f) F^{a e d}_e ... = ∑_g ...` — write exactly as in
  Vercleyen thesis §3; keep it `decidable` for `k = ℂ` numerical.
* `structure PivotalStructure (S : FusionSystem R k)` with
  `p : Fin n → kˣ`, `p (dual i) = p i⁻¹`, monoidality:
  `p k • F = F • (p i * p j)` on each multiplicity factor.
  Show this is equivalent to `p : 𝟙 ≅ ** ` monoidal in skeletal model.
* Define `dim_p i := p i * ...` (trace) and `dim_p i = p_i * dim0`
  where `dim0` is formal dimension; prove `dim (dual i) = (p_i)⁻¹ ...`,
  `|V|² = dim V * dim V*`.
* `def IsSpherical (P) := ∀ i, dim_p i = dim_p (dual i)` ↔ totally real.
* **Bridge lemma:** provide `skeletalEquivCategory` sketch (not full proof
  yet) that `System + PivotalStructure` ↔ `PivotalCategory` instance on the
  semisimple `k`-linear category. State as `axiom` with `sorry` only here,
  to be discharged in step 5 after vendoring `PivotalCategory.lean`.

Reuse pattern from `haagerup-odd/Coefficients.lean` (`B, A=B/τ`, symmetries)
for packaging finite data.

## 3. Step 3 — Pivotal cover and torsor

**Files:** `Cover.lean`, `Grading.lean`

* Assume `g : 𝟙 ≅ ****` as monoidal iso (ENO Thm 2.6) — take as hypothesis,
  do not prove `S⁴`. Define
  ```
  structure CoverObj where
    orig : Fin n
    f : kˣ   -- f : X ≅ X** , with f** * f = g_X
  ```
  In skeletal terms this is `F : (X,f) ↦ X`, with two lifts per simple
  unless `g` already squares. Prove ENO Rem 3.1:
  * `Cover` is fusion, `ℤ/2`-graded, forgetful `F : Cover → C`
    preserves `|·|²`,
  * canonical pivotal `p_{(X,f)} = f` on `Cover`,
  * `dim Cover = 2 dim C`, `FPdim Cover = 2 FPdim C`.
* `Grading.lean`: universal grading group `U_C` — defined as `Fin n ↠ G`
  universal with `N i j k >0 → deg k = deg i * deg j`. Prove
  `Aut^⊗(Id_C) ≅ Hom(U_C, kˣ)` (Gelaki, ENO §3, Bartlett Prop 5.7).
  Pivotal structures form a torsor over this group; `[g] ∈ Hom(U_C,kˣ)`.
  Prove splitting criterion:
  ```
  theorem pivotal_iff_square : Nonempty (PivotalStructure C) ↔
    ∃ h, h^2 = classOf g
  ```
  If `U_C` has no 2-torsion, deduce pivotal automatically.

This is entirely algebraic; no analysis.

## 4. Step 4 — Positive dimensions on the cover (ENO §3)

**File:** `PseudoUnitary.lean` (first half)

* For pivotal categories define `d i = dim X_i`, `D = ∑ d_i²`,
  `|X_i|² = d_i * d_{i*}`. Prove pivotal case of Thm 2.3:
  * `T = N` (since `i` trivializes associator signs),
  * `|V|² >0`, `dim C ≠ 0`, all Galois conjugates of `dim C` are ≥1,
    `FPdim C ≥ dim C` etc.
  * All eigenvalues of integer matrix `N_i` are algebraic integers;
    use Galois argument as in ENO §3.
* Extend to general `C` via `Cover` descent already built in step 3.
  This reproduces the standard reduction used in `haagerup-odd/` to avoid
  proving `S⁴`.

## 5. Step 5 — ENO 8.23: pseudo-unitary ⇒ spherical

**File:** `PseudoUnitary.lean` (second half)

Main theorem:
```
theorem pseudoUnitary_spherical
  (C : FusionSystem R ℂ) (h : globalDim C = globalFPdim R) :
  ∃ (P : PivotalStructure C), IsSpherical P ∧ ∀ i, dim_P i = FPdim i
```
and uniqueness:
```
theorem unique_pseudoUnitary_spherical
  (P₁ P₂ : PivotalStructure C) (h₁ : IsSpherical P₁) (h₂ : IsSpherical P₂)
  (hdim : ∀ i, dim_P₁ i = FPdim i) (hdim₂ : ∀ i, dim_P₂ i = FPdim i) : P₁ = P₂
```

Proof plan (formalize exactly as ENO):

1. On `Cover`, `D = FPdim` implies `|d_i| = FPdim i` via PF uniqueness
   (`pft_irreducible` gives unique positive eigenvector; both `|d|` and
   `FPdim` satisfy `N_i v = λ v`). Use `spectralRadius` lemmas from PF chain.
2. Choose `f` with `d_i = FPdim i >0` (exists by `f** f = g` and sign
   adjustment). Construct `p_i = d_i⁻¹ * Tr(f)`.
3. Verify monoidality using positivity `D ≠ 0` + step 4.
4. Spherical follows because all `d_i` real positive.

All polynomial identities are `ring`/`norm_num` after PF eigenvector.

**Corollary:** every unitary fusion category (assumed `dim>0` Hermitian)
is spherical — state as `instance` if desired, but keep hypothesis explicit.

## 6. Step 6 — Concrete certificates (makes the library testable)

**Files:** `Examples/Ising.lean`, `Examples/Fibonacci.lean`

* Import `haagerup-odd` data as black box: `A = τ⁻¹ B` satisfies
  `EGEquations`. For one small `n` (e.g. `n=3` Haagerup, `n=5` extended),
  show its `FusionSystem` has `globalDim = globalFPdim` after applying
  Galois `σ(δ)=d` (Lemma 11.2 style, but cite as example — do not redo
  `ruijsenaarsHypGamma`). Conclude it is pseudo-unitary hence spherical
  via step 5.
* For pure skeletal test without importing `haagerup-odd`, hard-code
  Ising `F` from AnyonWiki (`FC^{3,1,0}_{1,1,1,1}`) and Fibonacci `F`,
  verify pentagon + `p` by `rfl`/`decide`, then `pseudoUnitary_spherical`
  gives `IsSpherical`.
* Negative test: certify one rank-3 ring `K(2,2,1,0)` violates Ostrik
  inequality (5) for spherical positive dimensions — `norm_num` + PF
  eigenvalue computation, replicating `1309.4822` §2 and `2210.13936`.

These files are the CI smoke test; they should build in <30s.

## 7. Step 7 — Categorical packaging and upstream

* Fill the `skeletalEquivCategory` bridge from step 2 by importing
  vendored `PivotalCategory.lean`. Show `PivotalStructure` skeletal ↔
  `PivotalCategory` as `MonoidalNatIso 𝟙 (doubleDualFunctor)`.
* Replace vendored patches with real Mathlib imports once `#42150`/`#39922`
  merge to `master` on `v4.33.1`+ (watch `leanprover-community/mathlib4`).
* Add `BLUEPRINT.md` or `docs/` entry mirroring this plan plus dependency
  graph (`lake exe mk_all` + `importGraph` as in `haagerup-odd/docs/`).
* Axiom audit: add `AxiomAudit.lean` mirroring `haagerup-odd/AxiomAudit.lean`
  that prints `[propext, Classical.choice, Quot.sound]` for
  `pseudoUnitary_spherical`.

---

## What is explicitly out of scope

* Weak Hopf algebras / Radford `S⁴` (ENO §4–5). Taken as `g : 𝟙 ≅ ****`.
* Evans–Gannon reconstruction Ch.10 (categorical realization from `A`).
  `haagerup-odd/` stops at Ch.9 for the same reason.
* General Conjecture 2.8 without pseudo-unitary hypothesis.
* Full classification of rank-3 pivotal categories (`1309.4822` Thm 1.1) —
  inequality (5) is the only piece reproduced here.

## Build and check commands (for the agent)

From repo root `fusion-category-lean/`:

```sh
cd FusionCategory && lake exe cache get   # first time
cd FusionCategory && lake build            # or per-file:
python ../haagerup-odd/safe_lean.py --build FusionCategory/PFDim.lean  # pattern
lake env lean AxiomAudit.lean
```

All files must pass `lake build` with linter warnings only, same as
`haagerup-odd/`. Keep `weakLeanArgs = ["-j2","-s8192"]` as in
`haagerup-odd/lakefile.toml` for CI memory limits.

## References to keep open

* ENO Annals 162 (2005) — §§2–5, 8.4
* EGNO *Tensor Categories* (2015) — Ch. 9
* Ostrik `1309.4822` — inequality (5)
* Vercleyen thesis `2405.20075` — `FusionSystem` conventions
* Mathlib PRs `#42145` `#42150` `#39914`–`#39922`
* `haagerup-odd/README.md`, `PLAN.md`, `docs/README.md` — packaging style
* Huang `2609.15986` — example instance (do not duplicate its analysis files)
