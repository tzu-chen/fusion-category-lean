# WP2 design — the reconstruction (frozen for the first WP2 round)

Source of truth: `docs/research-proposal.tex`, WP2 (Tasks 2.1–2.3), deliverable D4,
milestone M3. This note records the architecture decisions for the reconstruction,
made by the coordinator before the first WP2 delegation round; members work against
it. A member who finds a concrete failure of a decision reports it as a finding —
decisions are falsifiable, not authority.

## What the pinned Mathlib gives, and does not give

Checked against the installed tree (`/opt/mathlib`, Lean 4.33.1, the pinned rev):

* **No fusion-category content at all.** `IsFusionCategory` is ours to define.
* `CategoryTheory.MonoidalCategoryStruct` / `MonoidalCategory` —
  `tensorObj`, `whiskerLeft`, `whiskerRight`, `tensorHom` (derived from the
  whiskers), `tensorUnit`, `leftUnitor`, `rightUnitor`, `associator`
  (`Mathlib/CategoryTheory/Monoidal/Category.lean`).
* `Preadditive C` (`CategoryTheory/Preadditive/Basic.lean`), `Linear R C`
  (`CategoryTheory/Linear/Basic.lean`), `MonoidalPreadditive C`
  (`CategoryTheory/Monoidal/Preadditive.lean` — bilinearity of the whiskers).
* `HasRightDual X` / `HasLeftDual X` (per object, via `ExactPairing`),
  `RightRigidCategory C`, `RigidCategory C`
  (`CategoryTheory/Monoidal/Rigid/Basic.lean`).
* `Simple X : Prop` (`CategoryTheory/Simple.lean`), Schur's lemma
  (`CategoryTheory/Preadditive/Schur.lean`).
* `CategoryTheory.Preadditive.Mat_` — the additive envelope (objects are finite
  labeled families, morphisms are `DMatrix` of base-category homs). **Not used**:
  its homs are dependent on the base category, which makes F-symbol entries
  painful; we go bespoke.
* **No categorical trace API for rigid categories** (`leftTrace`/`rightTrace`
  do not exist). Task 2.2 defines the trace itself.

## The model: `FusionMat n k` (multiplicity vectors, bespoke)

**Objects** are multiplicity vectors — formal finite direct sums of the `n`
simples, skeletal, matching the fusion ring's own skeletal philosophy:

```
structure FusionMat (n : ℕ) (k : Type u) [Field k] where
  m : Fin n → ℕ
```

**Morphisms** `X ⟶ Y` are block matrices, one block per simple label, since
`Hom(X_i, X_j) = 0` for `i ≠ j` and `End(X_i) = k` by construction (Schur holds
structurally):

```
X ⟶ Y  :=  ∀ i : Fin n, Matrix (Fin (X.m i)) (Fin (Y.m i)) k
```

Composition is per-block matrix multiplication; the identity is per-block `1`.
`Preadditive`, `Linear k` are entrywise. The simple `X_i` is the vector with
`m i = 1` at `i` and `0` elsewhere; `Simple` and Schur and `End(X_i) = k` are
immediate. `End(𝟙) = k` once `𝟙 := X₀`.

**Tensor on objects** — the fusion-ring convolution:

```
(X ⊗ Y).m c  =  ∑ a b, (N a b c) * X.m a * Y.m b
```

The index type of the `c`-block is `Σ (a b : Fin n), Fin (N a b c) × Fin (X.m a) × Fin (Y.m b)`
(and `Fin (N a b c)` is `Fin 0` or `Fin 1` by `mult_free` — the channel is
unique when it exists; this is where multiplicity-freeness earns its keep).

**Tensor on morphisms** — label-diagonal with the full Kronecker block inside:
for `f : X ⟶ Y` and `g : X' ⟶ Y'`, the `c`-block of `f ⊗ g` at row
`(a, b, _, i, j)` and column `(a', b', _, i', j')` is

```
if a = a' ∧ b = b' then (f a) i i' * (g b) j j' else 0
```

**[Corrected in-round; the original note was wrong, kernel-refuted by the
round's members]** The original formula here carried the extra conjuncts
`i = i'` and `j = j'`; they truncate every block to its diagonal and make the
assignment non-functorial (`(f₁ ≫ f₂) ⊗ (g₁ ≫ g₂) = (f₁ ⊗ g₁) ≫ (f₂ ⊗ g₂)`
fails — on a `2 × 2` multiplicity block with the transposition, the left side
is the identity and the right side is `0`; the counterexample is
`.ultramath/smw10qjp3/m3/NoteFormula.lean`, `noteBlock_not_mul`).  The correct
block is the Kronecker product `1 ⊗ₖ (f a) ⊗ₖ (g b)` — diagonal in the *labels*
only, full matrix inside the block.  The two readings coincide on simples
(all blocks `1 × 1`), which is why the channel-block analysis of the
associator below survives unchanged.

**[Model ruling, mid-round]** The round landed two viable object models: the
note's literal `structure FusionMat where m : Fin n → ℕ` (m4's
`ReconTensor.lean`: viable — the index transports are paid once in
`tensorBlockEquiv`), and the **block-carrying** generalization (m3's
`Recon.lean`/`ReconTensor.lean`): a structure with `m : Fin n → ℕ`,
`blk : Fin n → Type`, `[∀ i, Fintype (blk i)]` and
`card_blk : ∀ i, Fintype.card (blk i) = m i`, with `FusionMat.ofM m` giving
the note's model (`blk i := Fin (m i)`) definitionally.  **The block-carrying
model is the canonical model for the reconstruction** (ruled by the
coordinator, mid-round): the tensor's block index type is then *definitional*
(`TensorIdx S X Y c = Σ p, Fin (N p.1 p.2 c) × X.blk p.1 × Y.blk p.2`), and —
the decisive point — the associator is a *matrix between two different index
types*, which is legal, so the associativity cardinality computation never
enters any definition.  The note-literal model pays that transport at every
layer; the pentagon (the round's hardest proof) is meaningfully easier
without it.  Objects are no longer skeletal in the strict sense (two objects
with the same `m` and different `blk` are isomorphic, not equal) — immaterial:
every consumer (simples, trace, `derivedJ`) works with `sim i` and `ofM`, both
canonical.  m4's matrix lemmas (`reindex_mul`, `kron_mul`, the non-vacuity
checks) are model-independent and land with the round.

**The associator** is the F-data: `α_{X,Y,Z} : (X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)` has,
in the `d`-block, at row `((a,b)-channel e, then (e,c)-channel) with indices`
and column `((b,c)-channel f, then (a,f)-channel)`, the entry

```
F^{a b c}_d(e, f)   (times index-matching; 0 off the diagonal)
```

Both `(X ⊗ Y) ⊗ Z` and `X ⊗ (Y ⊗ Z)` have the same multiplicity vector (the
fusion ring's associativity), so `α` is an endomorphism-shaped block matrix, as
it must be.

**Key reduction (the reason this model works).** Every structural morphism is
diagonal in the multiplicity indices; so naturality, the pentagon, and the
triangle reduce *entrywise* to the corresponding label-level axiom of
`FusionSystem` at the labels carried by the row and column: the pentagon on
general objects is, entrywise, a single instance of the simple pentagon
(summed over the intermediate channel label, with the index bookkeeping
forced diagonal). No new coherence content appears at direct sums.

**Unit and unitors.** `𝟙 := X₀`. `𝟙 ⊗ X` has `c`-block `N 0 a c * X.m a`, and
`N 0 a c = δ_{ac}` (`left_unit`), so `𝟙 ⊗ X` is *canonically* `X` blockwise
(`Fin (δ * m) ≃ Fin m` by `Fin.fin_cast`-style equivalences); the unitors are
the identity matrices through these canonical block equivalences. The triangle
then reduces entrywise to `F_unit_left` / `F_unit_right`, and the
middle-unit entry that the triangle seems to need is `1` by
`TriangleCheck.triangle` (already landed, WP1 Task 1.2) — the reconstruction
consumes that theorem if the entrywise reduction demands it.

**Duals and rigidity.** `X* := (m ∘ ring.dual)` — the same vector with labels
dualized (`dual` is an involution, so `X** = X` *as objects*; the double-dual
*functor* is nevertheless not the identity — see Task 2.3 below).
`ev : X* ⊗ X ⟶ 𝟙` has, in the `0`-block, at row `((dual a, a)-channel 0, s, s')`
against the unique `𝟙`-index, the entry `if s = s' then S.ev a else 0`;
`coev : 𝟙 ⟶ X ⊗ X*` analogously with `S.coev a`. The two snake equations reduce
entrywise to `S.snake_left` (via the `F`-entry `F^{a a* a}_a(0,0)`) and
`S.snake_right` (via the `Finv`-entry — this is exactly why the signature
carries `Finv`): the system's snake axioms ARE the reconstruction's snakes.

## Task 2.3 — `derivedJ` (the definition is WP2's to give)

On the reconstruction, `X** = X` on objects; the double-dual *functor* acts by
adjoint mates on morphisms. Its monoidal structure — the tensorator
`X** ⊗ Y** ⟶ (X ⊗ Y)**`, i.e. an endomorphism-shaped block matrix of
`X ⊗ Y` — is the derived twist **as a morphism**. Define:

```
derivedJ S a b c := the ((a,b)-channel-c, (a,b)-channel-c) entry of the
  tensorator's c-block in the channel basis
```

Requirements, frozen from B4 and the WP1 round:

* its type must be `∀ {n}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ`
  (B4's frozen type, `Statements.lean`);
* it is defined **independently of the carried field `S.J`** — never an
  identification by fiat (the false-`J` datum `(Z/2)²` with `J ≡ 1` carries
  every law while its honest tensorator is `δ(κ)`);
* **gauge covariance** (the m1 finding of the WP1 round): `ENO823ExactC` at an
  arbitrary candidate twist is not gauge-invariant; `derivedJ` must transform
  with the vertex gauge so that `J_match S (derivedJ S)` is a statement about
  the datum. State the covariance; prove it if the round reaches it.
* The `settledJ` interface (`Prop821CNorm.lean`: `settledJ = f_c κ_a κ_b /
  (κ_c f_a f_b)`, whose `J_match` is the per-channel law (K)) is the bridge
  WP3 will consume: on pseudo-unitary data, `derivedJ = settledJ` is the
  expected theorem; on the pointed false-`J` datum, `derivedJ = δ(κ)` is the
  validation check (kernel-checking what `honest_twist_check.py` did at script
  level). Both are *targets*, not assumptions.

## The `IsFusionCategory` predicate (Task 2.1's "named predicate")

Over Mathlib's own classes, four properties as the proposal lists them:

```
class IsFusionCategory (C : Type*) [Category C] [Preadditive C]
    [MonoidalCategory C] [Linear k C] ... : Prop where
  -- monoidal: from Mathlib's MonoidalCategory instance (not a field)
  -- rigid:
  [rigid : RigidCategory C]            -- or per-object, decide at freeze
  -- k-linear finite semisimple: every object is a finite biproduct of simples,
  --   finitely many simples up to iso, Hom-spaces finite-dimensional
  -- End(𝟙) = k:
  [end_unit : ...]
```

The exact field list is D1's to freeze (a `Statements2.lean` for WP2, the B4
pattern): the predicate, the reconstruction theorem
("`FusionMat n k` of a `FusionSystem n k` is a fusion category"), the trace
correspondence statements, and the `derivedJ` definition + interface. Nothing
is proved in the freeze file; every statement is a `def`/`Prop` whose proof is
a later direction's.

## Round-1 scope (what this delegation round tries to land)

WP2 will not finish in one round. Round 1 lands, in priority order:
1. the frozen statements (`Statements2.lean`) and the predicate;
2. the base layer: `FusionMat` as `Category` + `Preadditive` + `Linear`, the
   simples, Schur, `End(X_i) = k`;
3. the monoidal scaffold: tensor obj/hom, bifunctoriality, associator,
   naturality;
4. the pentagon and/or the triangle (or a precise diagnosis of what the
   entrywise reduction needs);
5. the duals + snakes (or the same);
6. the trace correspondence (Task 2.2) as far as the scaffold allows;
7. `derivedJ`'s definition, its type-check against B4's frozen type, and the
   pointed-case validation (`derivedJ = δ(κ)` on pointed data).
