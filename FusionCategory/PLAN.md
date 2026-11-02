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

`J` is now **derived** from the duality data in the strict self-dual
normalisation (`DoubleDual.lean`): the chainmail composite `μ = ψ_{b*,a*} ∘ ψ*`
collapses to `J a b c = ev a * ev b / ev c`, its coherence holds identically,
its gauge law is the coboundary `J ↦ J · lam c / (lam a * lam b)`, and
`vecZ2_twist_derived` identifies it with the twist `VecZ2.system` carries.  So
for `Vec_{Z/2}` the carried `J` is verified rather than chosen.

Still owed: the `F`-twisted (non-strict) and non-self-dual cases of that
derivation, where the composite carries explicit associator factors; the
multiplicity-free restriction (`N ≤ 1`) as a separate general-multiplicity
development; and the analytic input for `ENO823`.

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
