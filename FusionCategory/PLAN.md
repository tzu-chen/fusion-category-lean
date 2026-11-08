# FusionCategory — Plan for ENO Proposition 8.23

**Goal:** `pseudo-unitary → spherical` with `dim = FPdim`, in Lean 4.33.1 —
conditional on the quadruple-dual input `g` being supplied or discharged
(proposal S3), never silently assumed.
This is the lemma that makes every recent classification/certification paper work,
and the only tractable piece of ENO Conjecture 2.8. Full `Id ≅ **` for arbitrary
fusion categories requires weak Hopf `S⁴` and is not attempted.

**Source theorem:** Etingof–Nikshych–Ostrik, *On fusion categories*, Annals 162 (2005),
§2.2, §3, §8.4, Prop. 8.23–8.26.  Secondary: EGNO *Tensor Categories* Prop 9.5.1,
Bartlett 2009 PhD Prop 5.7 Lemma 6.2, Shimizu *Frobenius–Schur*.

**Source of truth (set by the second review).**  `docs/research-proposal.tex`
(proposal v1.2.1) is the controlling document for this programme: work packages,
theorem contracts, gates, and scope.  This file is the implementation-level
record; where the two conflict, **the proposal governs**.  The first delegation
batch is fixed there ("The first delegation batch, and the source of truth"):
reproduce the clean build, implement the enforcing axiom audit, repair the
cocycle census, and settle the corrected signature and theorem statement —
and **no dependent theorem work starts until that batch has passed review**.
The contradictory instructions named by the review are corrected in this
revision (see the paragraph after "Still owed" below for the withdrawn
label-permutation request); the original step list (§0–7 below) is retained
under a superseded banner that enumerates its retired instructions.

## WP1 proofs landed (the D3/M2 round, swarm `smw0zjsah`)

The first delegation batch passed review, so the holding rule on WP1's proofs
lifted.  A seven-solution delegation round landed the remaining WP1 proofs; every
artefact was re-elaborated by the coordinator before acceptance, and the chain is
green end to end (build 8743 jobs, audit 1216 declarations, Gate 4 and the
self-test green).  New modules, all with axiom budget
`[propext, Classical.choice, Quot.sound]`:

* **`PFUniqueAll.lean`** — **`PFUnique` is a theorem**: `pfUnique_unconditional`
  proves Perron–Frobenius uniqueness for *every* fusion ring with `FPData`, by an
  elementary Collatz–Wielandt argument (the row-sum matrix `M i j = Σ_k N i j k`
  is strictly positive by associativity at `(i,j,j*,i)`; two positive eigenvectors
  of a strictly positive matrix are proportional — no irreducibility, no spectral
  theory, no vendored PF chain).  Corollaries: `fpdim_unique` (`FPData` is a
  property of the ring, not data), `pfUnique_system` (discharges the hypothesis at
  any scalar field), `eno823_of_pseudoUnitary_noPF`.  The vendoring motivation of
  WP0 Task 0.1 shrinks to the `FPData` *existence* half; its uniqueness half is
  closed here.  The three hand-written instance proofs in
  `Examples/PseudoUnitaryInstances.lean` are now instances of the general theorem
  (consistency-checked in the swarm, not yet deleted from the tree).
* **`Coverage.lean`** — every provable frozen `Prop` of `Statements.lean`
  discharged in one file, conclusions being the frozen defs applied, pinned by
  `rfl` shape guards: `EvDual`, `dimENO_eq_dim`, `dimENO_eq_dim_of_selfdual`,
  `J_coherent_forms_agree`, `TriangleLaw` (Task 1.2's frozen form, previously
  proved only in the raw), and the four `Cx` statements — `Cx.pivotal_ext`,
  `Cx.eno823_of_exact`, `Cx.eno823_of_bare`, `Cx.eno823_of_pseudoUnitary`
  (the PFUnique route).  `exact_iff_bare` records Task 1.5(a) as an equivalence:
  at `ℂ` the exact form adds no content to the bare form gated on its antecedent.
* **`Prop821CNorm.lean`** — the ℂ analytic chain (Task 1.1's explicit port item):
  `norm_le_fpdim_of_eigenvector` lifts ENO 8.21 to any `NormedRing` (the ℝ
  original is the `K = ℝ` instance), `eq_abs_of_sum_sq_c`, the character form, the
  ℂ twist algebra (`mult_iff_twist_c`: multiplicativity ⟺ (M), per-channel (K) ⇒
  (M)), the **settled twist** `settledJ = f_c κ_a κ_b / (κ_c f_a f_b)` whose
  `J_match` is literally the per-channel law, and `κ = FPdim` / `dim = FPdim`
  from pseudo-unitarity with the honest extra hypotheses.
* **`Prop821CEq.lean`** — the ℓ²-equality chain: `eq_of_sum_mul` (the product
  form), `eq_norm_of_pseudoUnitary_c`, and — the highlight —
  `eno823_c_of_pseudoUnitaryPivotal`: **bare `ENO823` at `ℂ` from
  `IsPseudoUnitaryC` + `Pos` + multiplicativity via 8.21's bound and the ℓ²
  equality case, with no `PFUnique`** — ENO's own §8.4 route, the M5 skeleton
  pulled forward.  Two independent routes to the conditional theorem now exist.
* **`Duality.lean`** — the `dimENO` layer: the two normalisations agree, and
  `IsPseudoUnitaryC` ⟺ ENO's `Σ d_i d_{i*} = FPdim(C)` in ENO's own dimensions
  (the `dimENO`-level ℓ² bridge).
* **`Gauge.lean`** — Task 1.4's prose claim kernel-checked: the vertex gauge
  (`coev ↦ λ·coev`, `ev ↦ ev/λ`) is a `FusionSystem` endomorphism fixing `κ`;
  the `EvDual` stabiliser is exactly the dual-invariant subgroup, so `ev_dual` is
  a gauge slice, not a restriction; `dim`, sphericity, `IsPseudoUnitaryC`,
  `Cx.IsPseudoUnitaryPivotal` and `ENO823` are gauge-invariant.
* **`Transport.lean`** — Task 1.1's transport: `mapSystem f S` (scalar extension
  along any ring hom between fields, all 24 fields), `mapPivotal` (pivotal
  structures and `dim`/sphericity/`ENO823` transport), the ℂ copies
  `FibonacciC`/`IsingC`/`YangLeeC` and `VecZ2R`, and the battery:
  `IsPseudoUnitaryC` proved for Fibonacci and Ising at `ℂ`, **refuted** for
  Yang–Lee at `ℂ`, `ENO823` at both positive copies.  (Environment fact,
  kernel-checked by three members independently: `Complex.abs` does not exist in
  the pinned Mathlib — the modulus is the norm `‖·‖`; the ℂ files all use it.)

Still owed from WP1 (nothing new): the `ENO823ExactC` family is not a proof
target at WP1 (its `derivedJ` is WP2 Task 2.3's held definition; the collapse
guards in `Statements.lean` record why).  WP2 (reconstruction, `derivedJ`,
`J_match` discharge) is the next package; the `settledJ`/`J_match` interface in
`Prop821CNorm.lean` is its entry point.

## WP2 Round 1 landed (the reconstruction's foundation, swarm `smw10qjp3`)

WP2 started per the proposal's order (Task 2.1 first). The design was frozen in
`docs/wp2-design.md`, the swarm ran eight directions, and six solutions were
accepted — every artefact re-elaborated by the coordinator before acceptance.
Chain state after landing: build 8751 jobs, audit 1418 declarations (940
theorem-kind), Gate 4 and the self-test green.

**The round's record of falsified design decisions** (all kernel-checked by
members, all corrections pushed to the design note at `b0e83b5`):

* The note's tensor-on-morphisms entry was **wrong** — the `i = i'`, `j = j'`
  conjuncts truncate every block to its diagonal and destroy functoriality
  (three independent counterexamples; the smallest is `NoteFormula.lean`'s
  `noteBlock_not_mul`: the transposition on a `2 × 2` multiplicity block gives
  `1 ≠ 0`).  The correct entry is label-diagonal with the full Kronecker block
  inside.
* A `Prop`-valued `IsFusionCategory` cannot *carry* `MonoidalCategory` /
  `RigidCategory` (data-carrying classes); they are instance arguments.
* The unit is `sim 0`, **not** the empty direct sum; the trap is recorded.

**Landed (the canonical scaffold, m3's block-carrying model — the mid-round
ruling, recorded in the design note):**

* `Recon.lean` — `FusionMat` (`m`, abstract block types `blk` with
  `card_blk`, `ofM` embedding the literal model), `Category` / `Preadditive` /
  `Linear k`, and the `blockDiag` calculus (`blockDiag_mul_apply`,
  `mul_blockDiag_apply`, `blockDiag_mul_blockDiag`) — the engine that makes
  every entrywise argument a label-level computation.
* `ReconTensor.lean` + `ReconTensorApply.lean` — the tensor bifunctor, proved
  (`tensorHom_id`, `tensorHom_comp`, whiskers, `kroneckerMap_mul` — absent
  from this Mathlib), with the entrywise apply lemmas; `sim` and
  `tensorObj_sim_m` (the reconstruction reproduces the fusion rules).
* `ReconUnit.lean` — the unit object and the object-level unit laws.
* `ReconAssoc.lean` + `ReconAssocStatements.lean` — the associator and its
  inverse as **matrices between two different index types** (no cardinality
  transport in any definition — the model's decisive design win), with the
  three coherence statements **frozen but not proved**:
  `AssociatorIso`, `AssociatorNatural`, `ObjectAssociativity`.
* `Statements2.lean` (m1) — the WP2 freeze: `IsFusionCategory k C` (the four
  property fields over seven Mathlib classes), `ReconFusion` / `ReconIsFusion`,
  the trace's definition site (`trDual` — the classical trace into the double
  dual, no pivotal structure needed; **no `F`-entry enters the trace of a
  simple's endomorphism** — a real simplification of Task 2.2), the three trace
  statements parameterized in `trSimple` (the B4 device), and `derivedJ`'s
  interface with the `settledJ` bridge and gauge covariance.  Note:
  `WP2.FusionMat` inside it is the literal model (=`ofM`); the canonical
  scaffold is `FusionCategory.FusionMat`.  Round 2 connects them.
* `NoteFormula.lean` — the design-note refutation, landed as the regression
  record.

**Not landed this round — the other members' green content, recorded in
`.ultramath/smw10qjp3/` and porting to the canonical model in Round 2:**
m2's `Simple`/Schur/biproduct/decomposition layer (127 audited declarations;
`simple_iff_exists_sim` — the simples are exactly the `sim i` — and the
mono-based `Simple` proof are the highlights); m5's pentagon (the left side
proved entrywise, `pentagon_of_rhs_entry_all` reducing the whole pentagon to
the frozen right-side entry statement; numerically verified on `Vec_{Z/2}`
with both cocycles); m6's rigidity data (`dual`, `ev`/`coev` green, `homFun`
the round's cleanest formulation of index-diagonality, and the phantom-`k`
hazard finding); m4's lemma library (`reindex_*`, `kron_mul` — on the literal
model).  The **residual map** for Round 2: the associator's three Props (the
elaboration blocker is the nested-`Sigma` composite — `blockDiag2` or
`Matrix.reindex_mul`), the pentagon's right-side entry collapse (the *same*
blocker), the unitors and triangle, the two snakes (the surviving scalar is
exactly `S.snake_left` / `S.snake_right`), the trace correspondence, and
`derivedJ` itself (m8's partial files included).

## WP2 Round 2 landed (the reconstruction two proofs from monoidal, swarm `smw1222bv`)

Six accepted solutions, every artefact re-elaborated by the coordinator before
acceptance.  Chain state after landing: build 8764 jobs, audit 1666
declarations (1228 theorem-kind), Gate 4 and the self-test green.

**Landed modules** (all on the canonical scaffold, all axiom-clean):

* `ReconAssocObj.lean` + `ReconAssocIso.lean` (m2) — **two of the three frozen
  associator Props proved**: `ObjectAssociativity` and `AssociatorIso` (both
  conjuncts, the frozen def applied), plus the associator as a
  `CategoryTheory.Iso` ready for `MonoidalCategoryStruct`.  The **nested-Σ
  blocker is cracked** — the method (flatten with `Fintype.sum_sigma` /
`sum_prod_type` after `Matrix.mul_apply`, no `reindex`, no `Equiv`; never
  unfold a `dif`-ladder inside a sum; kill binders one at a time with
  `Finset.sum_eq_single` plus per-condition zero lemmas) is documented in
  `docs/wp2-composite-engine.md` and is the required reading for every
  remaining collapse.  Residual: `AssociatorNatural` (the two sides sum over
  different index types; the plan — a general `HEq` entry formula for
  `tensorHom (tensorHom f g) h` — is recorded in the member's RESULTS.md).
* `ReconUnitors.lean` (m5) — **D4 complete**: the unitors as `Iso`s with round
  trips, both naturality equations verbatim (Mathlib's field shapes), and the
  **triangle**, proved by the sum-free route (`assoc_eq_tensorHom_unit_mid`:
  the associator at the unit position is pointwise the tensor of the two
  unitors, since `X ◁ λ_Y` is invertible; the only nonzero value is
  `F e 0 c d e c = 1` by `TriangleCheck.triangle` — the WP1 Task 1.2 theorem
  consumed exactly as the design note predicted).  Non-vacuity at `VecZ2` and
  `VecZ2Twisted` over ℚ.
* `ReconMonoidalBilin.lean` + `ReconMonoidal.lean` + `ReconAssembly.lean` +
  `ReconFusionProps.lean` (m4) — **the monoidal assembly**: `MonoidalData`
  (3 Iso families + 5 coherence equations) with `toStruct` **unconditional**
  (tensor, whiskerings, unitors) and `toMonoidalCategory` via Mathlib's
  `MonoidalCategory.ofTensorHom`, the associator consuming m2's
  `AssociatorIso`, the triangle from m5's unitors, `MonoidalPreadditive`
  (tensor bilinearity), `hom_finite`, `End(𝟙) ≃+* k`, and the
  `IsFusionCategory` property pieces.  **The `MonoidalCategory` instance now
  depends on exactly two open items** (`AssociatorNatural`, `PentagonShape` —
  with `pentagonShape_iff` proving the two pentagon shapes agree).  Finding,
  kernel-checked: the frozen `WP2.ReconFusion` names the *literal* model and
  `tensorObj` provably leaves `ofM`'s image, so the freeze's reconstruction
  theorem must be restated on the canonical scaffold or connected by an
  explicit equivalence — a finding-driven statement revision for Round 3.
* `ReconRigid.lean` + `ReconSnake.lean` (m6) — the dual (`dual_dual : X** = X`
  on objects), `ev`/`coev` as unit-channel deltas with entry formulas, the
  unitors as `Iso`s (an independent copy in namespace `FusionMat` — a
  Round-3 dedupe with `Units`), the two middle collapses, and the frozen
  snake statements with the final double-sum collapse residual (surviving
  term identified: `coev c · F^{c c* c}_c(0,0) · ev c = 1`, i.e.
  `S.snake_left`; the resolution is the engine's next application).  The
  numeric regression `docs/snake_check.py` passes on `Vec_{Z/2}`, the twisted
  `κ_g = −1` case, **and Fibonacci** — the 2×2-block `Finv ≠ swapped F` case
  that separates the corrected snake normalisation from both earlier wrong
  versions.
* `ReconTraceCorrespondence.lean` (m7) — **Task 2.2 discharged**: all four
  frozen trace Props for the reconstruction's concrete trace
  (`TraceOfScalar`, `TraceOfPivotalComponent`, `TraceProduct_eq_kappa`,
  `TraceGlobalDim_eq_pseudoUnitary` at ℂ), three of them composed through the
  freeze's own glue theorems; no F-entry enters the trace of a simple's
  endomorphism (kernel-checked); Schur on the nose (`End(sim i) ≃+* k`), the
  non-vacuity iff, and gauge invariance of the trace.  Residual: the
  identification `trSimple = WP2.trDualScalar` is `rfl`-level once the
  monoidal/rigid instances satisfy three compatibility conditions (whisker =
  `tensorHom`, unit = `sim 0`, the pairing's coev/ev = the block matrices) —
  recorded as obligations on the assembly.
* `DerivedJScalar.lean` + `DerivedJLaws.lean` + `DerivedJPointed.lean` (m8) —
  **Task 2.3's obligations (i)–(iii)**: `derivedJGen` is the ψ-comparison ratio
  built from `F`/`Finv`/`ev` along one explicit associator path (never reading
  `S.J` — the J-blindness is `rfl`), with B4's frozen type;
  **the general pointed `δ(κ)` theorem** (arbitrary `n`, `k`, from the axioms
  alone — pointed Frobenius reciprocity, `F ≠ 0` on supported 1×1 blocks,
  `Finv = F⁻¹`, three pentagon instances, a cocycle identity), which
  kernel-checks what `honest_twist_check.py` did at script level; gauge
  covariance in the freeze's form; and the three unit laws at arbitrary data
  (three of the four twist laws are now theorems for `derivedJGen`;
  coherence is WP3's).  Residuals: the tensorator as a scaffold morphism
  (whose (c,c)-entry would *be* `derivedJGen`), general `DerivedJ_ne_zero`,
  and `DerivedJ_eq_settledJ` (WP3's).

**The round's open map** (Round 3's targets): `AssociatorNatural` (the `HEq`
entry formula plan), `PentagonShape` (Round 1's m5 left side is proved and the
engine is in place — the direction produced no submission this round),
the snake collapse (surviving term identified; the engine applies), the
`trSimple = trDualScalar` identification (three compatibility conditions),
the `WP2.ReconFusion` restatement on the canonical scaffold (the m4 finding),
and then the `ReconIsFusion` inhabitation itself.  m3's probe files are
recorded under `.ultramath/smw1222bv/m3/`.

## WP2 Round 3 landed (the reconstruction one proof away, swarm `smw1fs4cn`)

Six accepted solutions plus two members' unsubmitted-but-green work, every
artefact re-elaborated by the coordinator before acceptance.  Chain state
after landing: build 8779 jobs, audit 1860 declarations (1548 theorem-kind),
Gate 4 and the self-test green.

**The round's theorems** (all on the canonical scaffold, all axiom-clean):

* **`AssociatorNatural` PROVED** (`AssocNatural.lean`, m6) — the third and last
  frozen associator Prop.  Both sides of the naturality square reduce
  entrywise to the same scalar `f·g·h·F`, no reindex, no `Equiv`.  Engine
  lesson recorded: the Round-2 `HEq` plan was unnecessary — the channel `if`s
  are identities and `sum_eq_single` kills them.  **`monoidalCategoryOfPentagon`**:
  the `MonoidalCategory` now assembles from the pentagon ALONE.
* **BOTH SNAKES PROVED** (`SnakeCollapse.lean`, m4) — the frozen
  `SnakeLeft`/`SnakeRight` discharged: the system's snake axioms ARE the
  reconstruction's, exactly as the design note claimed (the left consuming
  `F^{c c* c}_c(0,0)` via `S.snake_left`, the right the `Finv` entry via
  `S.snake_right` at the dual label).  Plus the literature iso-forms for the
  rigidity packaging.  Engine lesson: do NOT flatten the inner sum in the
  outer proof; the channel subsingleton eliminates the channel kills.
* **The simple-object layer PROVED** (`ReconSimpleSim.lean`/`ReconBiprod.lean`,
  m2) — the twice-unsubmitted direction closed: mono-based `Simple (sim i)`,
  the honest iso-form converse, the FINITE biproduct (Round 1's gap) with
  `hasFiniteBiproducts`/`hasZeroObject` instances, the decomposition, and
  `isFusionCategory_of_instances` — `IsFusionCategory` from the instances
  plus `end_unit`, with both assembly hypotheses now theorems.
* **The rigidity packaging and the assembly** (`ReconClosure.lean`, m5) —
  `ClosureInputs` (the seven remaining inputs as one structure), the
  compatibility conditions (whisker = `tensorHom`, `tensorUnit = unitObj` =
  `sim 0`, the pairing's coev/ev ARE the block matrices), `ExactPairing`/
  `HasRightDual`/`HasLeftDual`/`RigidCategory` from the snakes (axiom-free),
  and `reconIsFusionCanonical (I : ClosureInputs S)`.
* **The freeze revision** (`ReconFusionCanonical.lean` + `UnitorDedupe.lean`,
  m7) — the canonical-scaffold reconstruction theorem (with `tensorObj_eq`
  as an OBJECT equality, pinning the block types), the honest resolution of
  the Round-2 finding (`ofM` is not strict monoidal; the literal freeze was
  unreachable, not refuted), and the unitor dedupe, whose key finding
  restructured rigidity: the frozen snakes ARE Mathlib's `ExactPairing`
  triangles up to one unitor (`snakeLeft_iff_triangleLeft`).
* **The `derivedJ` tensorator** (`DoubleDualTensorator.lean`, m1) — Task 2.3's
  capstone: the double-dual endofunctor and the tensorator
  `X** ⊗ Y** ⟶ (X⊗Y)**` as a block matrix; **the entry theorem**
  (`tensorator_entry_sim`: the (c,c)-channel entry IS `derivedJGen` — the
  path-independence kernel-checked); **the Ω-ratio theorem**
  (`derivedJGen_eq_omegaCoeff`: the ψ-comparison and the associator-only
  Ω-coefficient agree, the four `ev`-factors cancelling BY `ev_dual` — WP3
  Task 3.2's ratio formula, with explicit nonvanishing hypotheses); the
  pointed `δ(κ)` at morphism level; the false-`J` discrimination on
  `Z2SqH` (channel `1⊗2 ∋ 3` gives `−1`); gauge invariance.
* **The closure bridge** (`ReconClosureBridge.lean`, the coordinator) —
  `reconIsFusionCanonical_of_pentagonHom`: six of the seven `ClosureInputs`
  are theorems of the tree, so **any `PentagonShapeHom S` closes
  `ReconIsFusionCanonical S`**.  The reconstruction is one proof from a
  fusion category in the library's own sense.
* **The adversarial audit** (m8, unsubmitted, verified and salvaged) — the
  elaborated-environment census (10/24 obligations proved at its `01f41e7`
  snapshot; the round then closed five more), two statement-level defects
  both repaired in-round, one statement RISK correctly flagged
  (`WP2.DerivedJ_ne_zero` needs the comparison scalar's divisor nonzero — no
  counterexample on all six data sets, no proof; the conditional form is what
  exists — a WP3 item), and the numerical battery
  (`docs/wp2-battery.py` + `ReconDataBridge.lean`): **ALL CHECKS PASS** on
  six exact-arithmetic data sets — 7068 blocks, 8740 matrix entries, the
  frozen snakes, the unitors' dedupe, the trace Props, the pseudo-unitarity
  identity — with no mismatch anywhere.  `PentagonLegs.lean` (the independent
  re-derivation of the two-factor legs) agrees with m3's route.
* **The pentagon toolkit** (m3, unsubmitted, verified and salvaged:
  `PentagonAux/U/UEntry/NSmul.lean`) — the two-factor side's entry formula
  `U_entry` PROVED (the composite `α_{A⊗B,C,D} ≫ α_{A,B,C⊗D}` is the two-`F`
  product on matched leaves, else `0`), the transport machinery, and the
  multiplicity-collapse lemmas.  The three-factor side's collapse is the
  single open entry computation.

**The one open proof**: `PentagonShapeHom S` — the three-factor side of the
pentagon, entrywise the `S.pentagon` sum on matched leaves.  Round 1's m5
proved the left side and reduced the whole pentagon to the frozen right-side
entry statement (on the literal model); Round 3's toolkit has the two-factor
side on the canonical scaffold plus `tensorHom_blockDiag_apply` (the
general-left-factor entry tool, on the board from m6).  The engine method is
documented and twice-battle-tested.  This is WP2's last item.

## WP2 closed: the pentagon landed (`FusionCategory.PentagonLHS`, swarm `smw77hbfw`)

The last item is done, and with it WP2.  The WIP file
`WIP/PentagonLHS.lean` graduated to the package module
`FusionCategory/PentagonLHS.lean` (imported by the umbrella; the audit
manifest and `AxiomAudit.lean` regenerated; the `ci-chain` gates green).

* `LHS_entry` — the three-factor side, entrywise: the composite
  `(α_{A,B,C} ⊗ 𝟙_D) ≫ α_{A,B⊗C,D} ≫ (𝟙_A ⊗ α_{B,C,D})` at refined indices
  is the label-level pentagon sum `∑ kk, F a b Cc e g kk * F a kk Dw d e h *
  F b Cc Dw h kk f` on matched leaves and `0` off them.  The final cascade
  runs in the named-binder workbench `LHS_core`; the off-leaf case chains
  the three associator matches and four tensorHom deltas to `qlo = qhi`.
  Engine note: no nsmul bookkeeping — every free channel is disposed
  witness-free (`sum_channel` + `by_cases`; absent branches vanish by
  `F_support`), since `assocMatch` compares no channels.
* `pentagonShapeHom_holds : PentagonShapeHom S` — the capstone: entrywise
  `LHS_entry` + `U_entry`, and `S.pentagon` at `(a, b, Cc, Dw, g, f, h, d, e)`
  on the leaf match.
* `reconIsFusionCanonical_recon : ReconIsFusionCanonical S hn` — the
  `ReconClosureBridge` application: **the reconstruction from a
  `FusionSystem` is a fusion category**, for every system (Fibonacci, Ising,
  Yang–Lee, `Vec^ω`, …).

Verification: swarm `smw77hbfw` (8 members) produced three independent
kernel-checked solutions (m1 — landed; m6, m7 — verified post-hoc), each with
`LHS_entry`'s statement byte-identical to the frozen one and axiom budget
`[propext, Classical.choice, Quot.sound]`; the coordinator re-elaborated and
diff-audited every artefact before acceptance.


## The multiplicativity fork landed: `DimMultiplicative` (swarm `smw7b5fyh`)

The person directed work on the multiplicativity fork to open a route to
WP3/WP4.  It is landed, in the fork's second route — the proposal's own
fallback form, the theorem stated with the `J`-side content as an explicit
hypothesis — and it opens both packages.

* **`DimMult.lean`** — (M) `Σ_c N a b c · J a b c · κ_c = κ_a κ_b` as a named
  `Prop` on the system (`DimMultiplicative`), deliberately *not* a field of
  `FusionSystem`: a field would destroy `Z2SqH.system`, the kernel-checked
  witness that (M) is not derivable (`Z2SqH.not_dimMult`), and WP3's endgame
  (replacing the `J` field by the derived `J`) would force removing the field
  again.  The bridge network around it: `dimMult_iff_dimEigen` ((M) ⟺ the
  dimension of *every* pivotal structure is a character of the fusion ring —
  all-or-nothing; the field-generic `mult_iff_twist`),
  `dimMult_of_perChannel` ((K) ⟹ (M)), and `kappaD_eq_kappa` +
  `trace_iff_dimMult`: the `ev_dual` field makes `kappaD = kappa`, so ENO's
  trace identity for a `SqrtData` *is* `DimMultiplicative` — WP3's acceptance
  test, WP4's input and this hypothesis are one condition.
* **The analytic half** — `eno823Exact_of_dimMult_pseudoUnitary`: over `ℝ`,
  (M) + `IsPseudoUnitary` + one pivotal structure give ENO 8.23's *exact*
  statement (a unique spherical pivotal structure with positive dimensions
  equal to the FP-dimensions), with no `PFUnique`.  The route: (M) discharges
  `DimEigen` for every `P` at once (8.21's bound,
  `abs_dim_le_fpdim_of_dimMult`); the dual-paired equality case
  (`eq_abs_of_sum_mul_dual`, the form `IsPseudoUnitary` actually delivers via
  `dim_mul_dim_dual`) gives `|dim P i| = FPdim_i` for every `P`; the
  normalised twist is then pinned up to sign per channel
  (`twistNorm_sq_of_dimMult_pseudoUnitary` — WP4 Task 4.5(a)'s "only the
  squares of the ratios are determined"); and the sign is forced by (M)
  itself, read as the channel sum `Σ_c N a b c · twistNorm = 1` and compared
  with `fpdim_char` termwise — a single minus sign would drop the sum
  strictly below `FPdim_a · FPdim_b`
  (`twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary`, the per-channel
  identity (K)) — after which `exists_spherical_of_twistNorm` at
  `d = FPdim` plus `pivotal_ext` close the theorem.  Over `ℝ` this replaces
  ENO's σ/τ normalisation by one comparison.
* **`DimMultC.lean`** — the `ℂ` port (S2's scalar contract):
  `norm_le_fpdim_of_char` (8.21 from the character form over any normed
  ring, no dual-invariance), `eq_norm_of_sum_mul_dual` (the dual-paired
  equality case at `ℂ`, no `Pos`, no sphericity),
  `norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC` (`‖dim P i‖ = FPdim_i`),
  the deliverable `twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c` ((K)
  at `ℂ`, by the phase argument — `‖s_c‖ = 1` and real parts of the channel
  sum force `s_c = 1`), and `eno823ExactC_of_dimMult` (the `∃!` form under
  the frozen `Pos` contract).  Non-vacuity kernel-checked: instantiated at
  `FibonacciC`/`IsingC`, the predicted unique structure *is* the transported
  `p ≡ 1` witness.

**The instances** (exact arithmetic throughout — `ℤ[√d]` integer pairs or
`decide`, never floats): `DimMultiplicative` for Fibonacci, Ising, Yang–Lee
(the *non-PF* character `(1, -1/φ)`), `Vec_{Z/2}`, `Vec^ω_{Z/2}`, and the
honest-twist `Z2SqH.systemH`; `¬ DimMultiplicative` for the false-twist
`Z2SqH.system`; transported to every scalar copy (`FibonacciC`, `IsingC`,
`YangLeeC`, `VecZ2R`) through `mapSystem_dimMult_iff`; gauge-invariant
(`gauge_dimMult_iff`, `gauge_isPseudoUnitary_iff`, `gauge_eno823Exact_iff`).
The capstone's first end-to-end runs: `eno823Exact_FibonacciSystem` and
`eno823Exact_IsingSystem` (the first non-pointed instances of ENO 8.23's
exact statement — the round also discharges the old "instantiate on
Fibonacci/Ising" item) and `Z2SqH.eno823ExactH_via_dimMult`.  Sharpness of
both halves of the antecedent: `YangLee.dimMult_and_not_pseudoUnitary` and
`YangLee.dimMult_alone_insufficient` ((M) alone does not give `ENO823`);
`Z2SqH.pseudoUnitary_and_not_dimMult` (pseudo-unitarity alone does not give
(M)).  On the pointed `(Z/2)²` datum `Z2SqH.dimMult_iff_J_match`
kernel-checks that (M) *is* `J_match` (WP3 Task 3.3): the two systems differ
only in `J` (`same_datum_except_J`).

**The adversarial audit** (m5; `Audit.lean`/`AuditIndep.lean` under
`.ultramath/smw7b5fyh/`, scratch): the chain re-derived by an independent
route (through `twistNorm`, never `p_mon`; the equality case by
`2ab ≤ a² + b²`; `AuditIndep.lean` imports only `Prop821`+`Coboundary`, not
`DimMult`) — **no defect found**.  Three strength findings, kernel-checked
and recorded rather than landed (the landed signatures mirror the source's
hypothesis structure): `hfσ` in `eq_abs_of_sum_mul_dual` is removable
(`Bijective σ` and `0 ≤ f` suffice); `hPU` in the capstone is removable
(`ENO823Exact` is itself an implication, so `eno823Exact_of_dimMult_pivotal`
is strictly stronger); `hn : 0 < n` is removable (`n = 0` is vacuous).  The
slot-2/slot-3 convention clash is made precise: the character form and
`IsPseudoUnitaryPivotal.mult` agree exactly for `*`-invariant dimension
functions (`char_form_iff_mult_form_of_dual_invariant`).  The pivotal
structure in the antecedent is used only as `Nonempty (PivotalStructure S)`,
confirming the WP4 Tasks 4.1–4.2 boundary.

**A name-capture defect, caught by the global build and fixed at landing**:
m1's new `FibonacciFPData`/`IsingFPData` (at the `FusionCategory` root)
shadowed `FusionCategory.Examples.FibonacciFPData` for the bare name inside
`namespace FusionCategory`, breaking two pre-existing theorems of
`YangLee.lean` (`not_eno823`, `not_pseudoUnitary`) and one of m3's.  The
per-file `lake env lean` checks had all passed because they ran against
*stale* oleans, in which the new name was not yet visible — the shared-tree
hazard of parallel members, in the exact form the record warned about.  Fixed
by renaming to `FibonacciSystemFPData`/`IsingSystemFPData` (matching the
round's own `FibonacciSystem_*` convention); the "declaration uses `sorry`"
warnings in the failing build were Lean's error-recovery artifacts of those
three type mismatches, not real `sorry`s.

**What the fork leaves open, now cleanly separated** — the WP3/WP4 entry
points:

* (M) for the *derived* twist — WP3 Tasks 3.2/3.3/3.6: `J_match` per
  instance in the interim (on pointed data `J = δ(κ)` and (M) *is*
  `J_match`, `Z2SqH.dimMult_iff_J_match`; `DerivedJPointed` carries the
  pointed half), the closed form of `ψ` and (M) for it in general;
* the pivotal structure in the antecedent — WP4 Tasks 4.1–4.2 (`SqrtData`,
  the quadruple dual): `SqrtData.toPivotal` supplies it once the defect
  vanishes, ENO's rescaling `a ↦ a · FPdim/d` being what kills the defect;
* the `ℂ` side being now in place (`DimMultC.lean`), WP4's remaining analytic
  content is exactly the input side.

Verification: swarm `smw7b5fyh` (6 members, 6 accepted), every artefact
re-elaborated by the coordinator before acceptance; the tree builds green,
the audit regenerated, Gate 4 and the self-test pass.


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

`J` is **derived** from the duality data only in the strict self-dual
normalisation of `DoubleDual.lean` (and that file's original formula is
retracted — see below); in `FusionSystem` at large `J` is carried data.  The definition that file originally carried,
`J a b c = ev a * ev b / ev c`, is the ψ-scalar and *not* `J`; that was retracted
in `a168b32`, together with the coboundary gauge law.  The correct statement is
the ratio formula recorded under "The derived twist: result" below.  What is
still true from that file: `J`'s coherence for `Vec_{Z/2}` is verified rather
than chosen, and the twist is a genuine ratio of composites.

Still owed: an independent evaluation of the `J`-diagram (the non-self-dual
`F`-twisted case is now *checked* on nine data sets and *derived* only as a
reconstruction — see "The derived twist: result" below); the multiplicity-free
restriction (`N ≤ 1`) as a separate general-multiplicity development; and the
analytic input for `ENO823`.

**The label question is closed, and the earlier request for a
nontrivial-permutation model is withdrawn.**  By ENO Prop 2.1 every simple is
isomorphic to its double dual, so a skeleton always has `i** = i` on labels:
there is no nontrivial double-dual label permutation to model, and
`FusionSystem`'s lack of a label-transport slot is not a defect.  The item that
used to stand here asked for such a model and contradicted both the record
above and the proposal (Remark on the trap); it is removed.  The monoidal
content it was gesturing at is the twist `J` itself, which is carried as data
and derived in WP3 of the proposal.

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

**The construction is right; the formula as written here is not.**  On
`(Z/2)²` with `ω = (-1)^{a₁b₂c₁}` the honest twist is `J = δ(κ)`, i.e. `-1` on
six channels.  Read literally, the displayed `Ω` above — entry `(c*,b)`,
inverse-block index `(0,c)` — evaluates to `+1` there, so the transcription is
defective even though `ψ`'s construction is correct.  Implemented properly
(`swarm smvzybdp8` m6, three independent assemblies: the `Ω` coefficient form, a
`coev`-side assembly, and an `ev`-side assembly) the construction reproduces
`δ(κ)` on `(Z/2)²` channel by channel.

The honest value is confirmed independently by evaluating `φ` from its defining
property `ev ∘ (φ ⊗ id) = ev` with the full associator bookkeeping:
`λ(X,Y) = E_X E_Y ω(-(X+Y),X,Y)⁻¹ ω(-Y,-X,X)/E_{X+Y}`, `J = λ(b*,a*)/λ(a,b)`,
which agrees with `κ_aκ_b/κ_c` on all 16 channels of `(Z/2)²`
(`docs/honest_twist_check.py`).  So what is refuted is the *trivial-twist*
reading: `J ≡ 1` fails (K) on `(Z/2)²`, and `J ≡ 1` holds iff `κ` is a
character.  `m1`'s scalar `ψ` formula returns `1` on the same channels and is
wrong.  The `J ≡ 1` census below is still evidence of nothing on its pointed samples:
`δ(κ) = 1` on every cyclic group in the standard gauge (κ is a character
there).  Fibonacci and Ising are the *distinguishing* cases: there `κ = FPdim`
makes the right side of (K) equal to `1`, so the honest twist is `J ≡ 1`, while
`δ(κ) ≠ 1` (`φ²`, `2`) and is not even a legal twist there (it violates
`J_dual`).

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
  derivation from first principles.  **The pointed half of the census cannot distinguish `J ≡ 1`
  from `J = δ(κ)`**: every pointed sample is cyclic, where `κ` is a character
  and `δ(κ) = 1`.  Fibonacci and Ising *do* distinguish: there `κ = FPdim`,
  the right side of (K) is `1` and the honest twist is `J ≡ 1`, while `δ(κ) ≠ 1`
  (`φ²`, `2` — not even a legal twist, since it violates `J_dual`).  `(Z/2)²`
  separates the pointed readings; see the correction under "Three further
  results" below.
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
`FusionSystem.J_coherent` — follows from that equation only when `(−)**` is
the identity on labels **and** the common entry `F^{abc}_d(e,f)` is nonzero
(`h_F`); where the entry vanishes the displayed equation is vacuous (`0 = 0`)
and licenses nothing.  As it stands `J_coherent` is therefore *stronger* than
the monoidal-functor pentagon on channels with `F = 0`; WP1 Task 1.3 of the
proposal restates it in the qualified or retained-factor form.  The rest of `FusionSystem` fixes exactly that case: `J` has type
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
  Ising, whose `κ = FPdim` makes the right side of (K) equal to `1`, so the
  honest twist there is `J ≡ 1` — and `δ(κ) ≠ 1` on those data (`φ²`, `2`),
  `δ(κ)` not even being a legal twist there (it violates `J_dual`).  It fails on `(Z/2)²`: with
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
  [Superseded by the proposal, WP1 Task 1.2: the entry is *derivable* — the
  pentagon at `(a,1,1,c)` gives `t = t²`, and the block is `1 × 1` (the unit
  laws force `e = a`, `f = c`) so `Finv_comp` gives `t ≠ 0` — so it is proved
  as a lemma, not added as an axiom.]

One claim from the swarm to *not* adopt: that `X** ≅ X` in any rigid monoidal
category, so a skeleton can always be chosen with `(−)** = id` on labels and
the F-free pentagon is therefore general.  The proof offered was "`X*` is both
a left and a right dual of `X`", which is precisely what a rigid category does
not give — identifying the left and right duals of an object is the content of
a pivotal structure, and `id ≅ (−)**` is exactly what need not exist.  So the
caveat above stands: the F-free form is available to a skeleton in
which `i** = i` (the case for every model used here) **only on channels where
the cancelled `F`-entry is nonzero** (`h_F`); the retained-factor form is the
unconditional one.

**Not derived:** the independent diagram evaluation of `J` itself (above); and the
analytic input for `ENO823`.  (The case `(−)** ≠ id` on labels is not a case at
all: see the withdrawn request under "Still owed".)

## ENO's own proof, transplanted: `a`, `b`, and (M)

ENO's proof of 8.23 does not start from a pivotal structure — it produces one —
and the signature had no room for its input. What it uses (§3.1 of the arXiv
version, where the proposition is numbered 8.22) is a **tensor** isomorphism
`g : Id → ****` (their Thm 2.6, the Radford input we take as `S4Data`) and an
**additive** isomorphism `a : Id → **` with `a² = g`; `a` is *not* monoidal, and
the defect of its monoidality is the cochain `b^{ij}_c`. `ENOSqrt.lean` now
carries this: `SqrtData` is `a`, and `b`, `Tmat`, `d` are ENO's `b^{ij}_c`,
`T^{ij}_c` and `d_i = Tr(a_i)`.

Three things came out of it, all kernel-checked:

* **`b` carries `J` in the numerator**, `b = J i j c · a_i · a_j / a_c`, and
  `(b^{ij}_c)² = 1` follows from `a² = g` monoidal — *not* from `J² = 1`. The
  monoidality has to be stated against `J²`, because in a skeleton `(−)**` is
  the identity on labels and on morphisms, so the tensorator of
  `(−)**** = (−)** ∘ (−)**` is `J²`. `Cover.lean`'s `S4Data.g_fusion`, which
  reads `g c = g i · g j` on channels, is the `J = 1` special case and is wrong
  in general.
* **The trace identity is (M).** `d_i d_j = Σ_c T^{ij}_c d_c` is equivalent,
  after the `a`'s cancel, to `κ'_i κ'_j = Σ_c N i j c · J i j c · κ'_c` with
  `κ'_i = coev_i · ev_{i*}` (`SqrtData.trace_iff`). So ENO's "by the definition
  of `b`" step *is* the sum identity that `Prop821.mult_iff_twist` isolated:
  the fork between "derive `J`" and "assume multiplicativity" is not a fork,
  it is one theorem.
* **Do not add `J² = 1`.** It is false for honest pseudo-unitary data — with the
  corrected witness (delegation batch, B3c): `Vec^ω_{(Z/3)²}` with
  `ω = ζ^{a₁b₂c₁}` is a **coboundary** (kernel-checked,
  `Witnesses/Z3sqTwist.lean: om_is_coboundary`, with the explicit trivialising `μ`),
  so its `J² ≠ 1` is a gauge statement. The genuinely twisted family
  `ω = carry · carry · ζ^{a₁b₂c₁}` (`Witnesses/Z3sqTwisted.lean`,
  `no_trivialising_cochain`) has honest twist `δ(κ)` squaring to a
  primitive cube root of unity on 36 of the 81 channels, and the category is
  unitary, so adding `J² = 1` would exclude a category that ENO 8.23 applies to.

The duality normalisation is a second, independent defect. ENO's
`d_i = Tr(a_i)` is `a_i · coev_i · ev_{i*}`, not `a_i · κ_i` with
`κ_i = coev_i · ev_i`; the two agree exactly when `i* = i`, which holds for
every datum in `Examples/` but not in general. `FusionSystem.kappaD` is the
right normalisation and `SqrtData.d_eq_kappa` records the agreement.

What is left is unchanged in kind and smaller in extent: the *positivity half*
of the pseudo-unitarity input (positivity, hence `d = FPdim` by `PFUnique`) is
invisible in a multiplicity-free skeleton — the hypothesis itself,
`IsPseudoUnitary`, is the visible scalar equation — and `J` is still data
rather than derived — but the
condition it has to satisfy is now (M) itself, a statement about `(N, J, κ')`
that `mult_iff_twist`, `twist_sum_of_perChannel` and `SqrtData.trace_iff`
already surround. Checked on six data sets: (M) holds for Fibonacci, Ising,
Yang-Lee and `Vec^ω_{Z/2}` with `J = 1`; it fails on `Vec^ω_{(Z/2)²}` with
`J = 1` (`κ = (1,1,1,−1)` is not a character) and is repaired there by
`J = δ(κ) = κ_a κ_b / κ_c`; Yang-Lee satisfies (M) and its trace identity and
fails only at positivity (`|d_τ| = 1/φ < φ = FPdim_τ`), which is exactly the
sharpness that `YangLee.not_eno823` records.

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
structure at all.  What has to supply the identity is pseudo-unitarity — the
scalar equation `Σ_i κ_i κ_{i*} = Σ_i FPdim_i²`, which *is* visible in the
skeleton and is carried as `IsPseudoUnitary`.  The bare `ENO823` carried no
such hypothesis; it was restored after Yang–Lee refuted the unhypothesised
statement (see "The hypothesis, restored" below), and the substantive gap is
ENO's σ/τ normalisation itself — the passage from that equation to positivity
and multiplicativity — not the algebra above.

**The identity is `J`-free on the coevaluation channel.**  On the channel
`(i, i*; 1)` the axiom `J^{1}_{i i*} = 1` is used, so (K) there reads

    (C)   κ_i κ_{i*} = FPdim_i²     for every i,

with no `J` in it.  So (K) ⟹ (C) is a two-line theorem, and (C) is exactly the
statement that `p = FPdim/κ` is *spherical* (`isSpherical_iff`).  The converse,
(C) ⟹ (K), is ENO 8.23.  In other words, in this formalism

    (K) ⟺ ENO 8.23,   and   (K) ⟹ pseudo-unitarity of the datum,

and the residual mathematical content is `pseudo-unitarity ⟹ (C)` — a statement
about `κ` and `FPdim` only, *not* about `J`.  (The converse,
pseudo-unitarity ⟹ (K), *is* ENO 8.23; the chain above must not assume it.)  This retires the "derive the
`J`-diagram" programme as the route to ENO 8.23 (it stays necessary to make the
signature honest, since `p_mon` mentions `J`).

**The exact statement, checked against the source.**  ENO §8.4 says:

> Let us say that a fusion category `C` is *pseudo-unitary* if `dim(C) = FPdim(C)`.
> This property ... fails, for example, for the Yang-Lee category.
> **Proposition 8.23.** Any pseudo-unitary fusion category `C` admits a *unique*
> pivotal (in fact, spherical) structure, with respect to which the categorical
> dimensions of all simple objects are *positive*, and coincide with their
> Frobenius–Perron dimensions.

Three things were missing from `ENO823`: the hypothesis is one scalar equation
`dim C = FPdim C` (not positivity of a chosen dimension function), and both
positivity and uniqueness belong to the *conclusion*.  In the skeleton the
categorical global dimension is form-independent: `dim P i · dim P (i*) = κ_i κ_{i*}`
for every pivotal `P` (`dim_mul_dim_dual`), so

    IsPseudoUnitary S hFP  :=  Σ_i κ_i κ_{i*} = Σ_i FPdim_i²

has no `P` in it, exactly as in the source, and Yang-Lee fails it
(`YangLee.not_pseudoUnitary`) — the remark ENO make.  `ENO823Exact` then states
the conclusion with positivity and `∃!`, and `pivotal_ext` supplies uniqueness
(a pivotal structure is determined by its dimension function) so only existence
is left; `eno823_of_exact` recovers the bare `ENO823`.

What is *not* formalised is ENO's proof: Proposition 8.21 (`|V|² ≤ FPdim(V)²`,
via domination of the `T`-matrix by the fusion matrix) turns the sum equality
into a termwise one, and then the twisting argument --- by the *tensor*
automorphism `σ = d²/|d|²` and then the *natural, non-monoidal* automorphism
`τ = d/|d|` --- produces the pivotal structure with positive dimensions.  That is
the analytic heart and the next target.

**Step 1, done: Proposition 8.21's spectral bound.**  `Prop821.lean`:

* `cyclic`, `cyclic1`, `cyclic2` — the cyclic symmetry `N^k_{ij} = N^i_{j k*}`
  of the fusion coefficients, from associativity at `l = 1` and `dual_coeff`.
  The repo's axioms do not otherwise connect the second and third slots, and
  both index conventions occur below;
* `fpdim_char` — the FP-dimension is a character, `Σ_c N a b c f_c = f_a f_b`
  (the repo's `FPData.eigenvector` is the *middle*-slot form; `cyclic1`
  converts it);
* `abs_le_fpdim_of_eigenvector` — the bound itself: any `d` with
  `Σ_j N i j k d_j = d_i d_k` satisfies `|d_i| ≤ f_i`, by ENO's weighted norm
  `‖x‖ = Σ_j f_j|x_j|`, which `fpdim_char` bounds by `f_i`;
* `abs_dim_le_fpdim` — the same for the dimension of a pivotal structure, with
  the hypothesis `DimEigen S (dim P)` isolated;
* `eq_abs_of_sum_sq` — the equality case: `Σ_i |d_i|² = Σ_i f_i²` plus
  termwise `|d_i| ≤ f_i` forces `|d_i| = f_i`.

**What Proposition 8.21's hypothesis is, checked against the source.**  ENO
§3.1 construct `T_i` from the `b`-symbols: with `a_V : V → V**` chosen so that
`a_V² = g_V`, one has `a_V ⊗ a_W = ⊕_U b^{VW}_U ⊗ a_U` with `(b^{VW}_U)² = 1`, so
`T^{ik}_j := tr(b^{ik}_j) ∈ {0, ±1}`, `d_i d_k = Σ_j T^{ik}_j d_j`, and
`(T_i)_{kj} = T^{ik}_j`.  Remark 3.1 then says:

> in the pivotal case `ε_i` and `b^{ik}_j` **are 1**, so `T^{ik}_j` are equal to
> `N^{ik}_j`, the multiplicity of `X_j` in `X_i ⊗ X_k`.

So in a pivotal fusion system — which is exactly `FusionSystem` plus
`PivotalStructure` — ENO's `T`-matrix **is the fusion matrix**
(`tMatrix S i : fun k j => N i k j`), its domination
`|(T_i)_{kj}| ≤ N^{ik}_j` is an equality (`abs_tMatrix`), and the eigenvector
equation `T_i d = d_i · d` (`tMatrix_mulVec`) **is multiplicativity of the
dimension**, `d_a d_b = Σ_c N a b c d_c`.  The non-trivial `b`-symbols exist only
when no pivotal structure is fixed, and their role is to prove `dim(C) ≠ 0`
without one; they do not help with 8.23, where a pivotal structure is what we
must produce.

Consequently:

* `abs_le_fpdim_of_mult` — the bound for a multiplicative dimension
  (`DimEigen`, ENO's form), and `abs_dim_le_fpdim` for `dim P`;
* `abs_dim_le_fpdim_of_pseudoUnitary` — the bound for any `P` with
  `IsPseudoUnitaryPivotal P`, i.e. `DimEigen` discharged from `mult`, with no
  further input;
* `eq_abs_of_pseudoUnitary` — ENO's `|V|² = FPdim(V)²` from the total equality.

**Settling `J`, and why it cannot be done by defining it.**  `Prop821.lean` now
records the exact shape of the problem:

* `sum_dim_eq`, `dim_mul_dim`, `mult_iff_twist` — for a pivotal structure,
  multiplicativity of the dimension (`Σ_c N a b c d_c = d_a d_b`) is *equivalent*
  to the sum identity **(M)** `Σ_c N a b c · J a b c · κ_c = κ_a κ_b` on the
  twist.  So "settle `J`" = "prove (M)";
* `twist_sum_of_perChannel` — (K), the per-channel form, implies (M): sum (K)
  against the FP-dimensions, which by `fpdim_char` is a character.

So the honest `J` is characterised by (M), and (M) is not a definition: setting
`J := κ_aκ_b/κ_c` (or the FPdim-normalised coboundary) makes (M) true by
construction, and would then make `eno823_of_pseudoUnitary` apply to *every*
datum — which `YangLee.not_eno823` refutes.  A settlement has to derive `J` from
`(F, ev, coev)` as the monoidal structure of `(−)**`, i.e. the chainmail
`J = ψ_{b*,a*;c*}/ψ_{a,b;c}` with `ψ` the unique evaluation-intertwining
comparison, and then prove (M) for it.  What is known:

* pointed data: `J = δ(κ) = κ_aκ_b/κ_{a+b}`, proved (swarm `smvzybdp8`, m3) and
  verified independently — this is the one class where the settlement is done;
* every non-pointed example in the repo (Fibonacci, Ising, the Tambara-Yamagami
  family) has `κ = FPdim`, so the right side of (K) is `1` and the honest twist
  is `J ≡ 1`.  **`δ(κ) ≠ 1` there** (`φ²` on Fibonacci's `(τ,τ;1)` channel, `2`
  on Ising's), and `δ(κ)` is not even a legal twist on those data (it violates
  `J_dual`) — `J = δ(κ)` is a pointed-only statement, and the pointed
  `φ`-evaluation script does not touch these examples;
* general multiplicity-free data: the closed form of `ψ` is open.  The reason it
  is hard, stated precisely: through a channel the comparison `ψ` involves the
  associator at the *non-simple* object `a⊗b`, so evaluating it needs the
  F-blocks composed across the channel decomposition, and the index bookkeeping
  is where both `Ω` and m1's formula went wrong.

So the settlement is a real computation, not bookkeeping, and it is the last
piece of step 1.  **It has since been identified:** (M) is ENO's trace
identity, `d_i d_j = Σ_c T^{ij}_c d_c` after the `a`'s cancel — see "ENO's own
proof, transplanted" below.  What ENO compute is exactly the `b`-cochain of a
square root `a` of `g`, and `SqrtData.trace_iff` is the identification.

**The hypothesis, restored, and the theorem that follows from it.**  Since
`ENO823` is false without pseudo-unitarity, `PseudoUnitary.lean` now carries it:

    structure IsPseudoUnitaryPivotal (P : PivotalStructure S) : Prop where
      pos  : ∀ i, 0 < dim P i                              -- part of the source's conclusion, a hypothesis here
      mult : ∀ i kk, ∑ j, N i j kk * dim P j = dim P i * dim P kk   -- dim is a ring character

    theorem eno823_of_pseudoUnitary (hn) (hFP) (huniq : PFUnique S.ring hFP)
        (P) (hU : IsPseudoUnitaryPivotal P) : ENO823 S hFP

Both fields are needed and neither is automatic: **positivity** is what Yang-Lee
fails (`YangLee.not_eno823`), and **multiplicativity** is what
`Vec^ω_{(Z/2)²}` with `J ≡ 1` fails — in this signature multiplicativity of
`dim = p·κ` is equivalent to the sum identity (M) `Σ_c N^c_ab J^c_ab κ_c = κ_aκ_b`
on the twist, which a non-canonical `J` violates.  With both, `PFUnique` forces
`dim P = FPdim`, and sphericity then follows from `p_{i*} = p_i⁻¹` rather than
being assumed.  So what remains open is exactly the passage from the
pseudo-unitarity equation (`IsPseudoUnitary`) to those two conditions — ENO
8.23's own σ/τ argument — not the algebra.  (An earlier version of this
paragraph called it a passage from a Hermitian structure; removed.)

**The witness that (C) is not automatic is Yang-Lee, and it is kernel-checked.**
Rank 2 with `τ ⊗ τ = 1 ⊕ τ`, `F^{τττ}_τ = [[-φ, 1], [-φ, φ]]`, `FPdim_τ = φ`;
both snakes give `κ_τ = -1/φ` from both branches (the pentagon holds on all `2^9`
tuples), and `κ_τ κ_{τ*} = 1/φ² ≠ φ² = FPdim_τ²`.  So (K) fails on Yang-Lee for
*every* `J`, every other axiom of `FusionSystem` holds, and Yang-Lee is not
pseudo-unitary.  Fibonacci is the control: same check, `κ_τ = φ`, (C) holds.
`docs/yang_lee_check.py` recomputes both, and `Examples/YangLee.lean` carries the
formal statement:

    YangLee.system : FusionSystem 2 ℝ
    YangLee.not_eno823 : ¬ ENO823 YangLee.system FibonacciFPData

with the pentagon, the unit laws, both inverse laws and both snakes checked by
`decide` in `ℤ[√5]`, and `not_eno823` from `dim_eq_twistNorm`: a pivotal
structure with `dim = FPdim` would give `1 = twistNorm τ τ 1 · φ² = φ⁴`.  So
`ENO823` as stated is **false**, in a two-label model, and no hypothesis on `J`
can rescue it — the missing hypothesis is pseudo-unitarity, i.e. (C).

Two further results from the same swarm, both about constructions rather than
the identity:

* the defect `Δ^c_ab = J κ_c FPdim_a FPdim_b /(FPdim_c κ_a κ_b)` (so (K) ⟺ Δ = 1)
  is multiplicative: `Δ(C ⊠ D) = Δ_C Δ_D`, so no Deligne product cures a
  failure; `Δ(C̄) = conj Δ`; and on `C^op`,
  `Δ(a,b;c) = Δ(a,b;c)·(J(b,a;c)/J(a,b;c))·ν_aν_b/ν_c`;
* the vertex gauge `coev ↦ λ coev`, `ev ↦ ev/λ` fixes `κ` and multiplies `Δ` by
  `t_a t_b/t_c` with `t_i = λ_i/λ_{i*}`.  So (K), and hence `ENO823`, is *not*
  invariant under that gauge: it survives exactly the duality normalisation
  `λ_{i*} = λ_i`.  That is a defect of the signature, not of the mathematics —
  the fix is to add `ev (dual i) = ev i` as an axiom or to define
  `dim P i = p_i * coev_i * ev (dual i)` rather than `p_i * κ_i`.

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

> **Superseded (read the record above and the proposal first).**  The step
> list below (§0–7) is this project's original scaffold.  It predates the
> Step-2 rewrite, the results recorded above, and the proposal, and these
> instructions of it are retired: step 2's `skeletalEquivCategory` bridge was
> to be stated as an `axiom` with `sorry` (forbidden by the axiom budget and
> the audit); step 2's pivotal axiom `p k • F = F • (p i * p j)` is the
> retracted `p_fusion` (no twist factor — defect D3 of the proposal); step 3's
> square-root criterion `pivotal_iff_square` and its no-2-torsion corollary
> are withdrawn (proposal WP5 Task 5.3); step 5's `pseudoUnitary_spherical`
> and its corollaries are retired (see "Status after the Step-2 rewrite"),
> including the Hermitian-hypothesis corollary (no Hermitian structure enters
> the hypothesis or the proof).  The work-package structure, gates and theorem
> contracts now live in `docs/research-proposal.tex`.
> Retained for the record; where it conflicts with the sections above or with
> the proposal, those govern.

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
  **[Superseded: this is the retracted `p_fusion` (no twist factor); the
  current axiom is `p_mon` with the `J` factor — see "Status after the
  Step-2 rewrite".]**
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

**Corollary:** every unitary fusion category is spherical — state as
`instance` if desired, but keep the hypothesis explicit.  **[Superseded: the
Hermitian parenthetical is removed — no Hermitian structure enters the
hypothesis or the proof; see the proposal's WP4.]**

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
(cd FusionCategory && lake exe cache get)  # first time
(cd FusionCategory && lake build)         # whole package
sh FusionCategory/tools/audit-gate.sh      # Gate 4: enforcing axiom audit
# per-file FROM-SOURCE build (route (b) of the batch's B1), the actual loop:
#   priv=$PWD/.scratch/fromscratch; mkdir -p "$priv"
#   for M in Basic System Pivotal Cover Grading DoubleDual PFDim PseudoUnitary \
#            Coboundary Prop821 ENOSqrt; do
#     LEAN_PATH="$priv:$LEAN_PATH" lean -o "$priv/FusionCategory/$M.olean" \
#       FusionCategory/FusionCategory/$M.lean
#   done
# (the full 26-module spine, computed from the import graph, is
#  FusionCategory/tools/fromscratch-build.sh's job; see also
#  FusionCategory/tools/clean-build.sh, the batch's B1 deliverable)
```

All files must pass `lake build` with linter warnings only, same as
`haagerup-odd/`. Keep `weakLeanArgs = ["-j2","-s8192"]` as in
`haagerup-odd/lakefile.toml` for CI memory limits.

The axiom audit is a **gate, not a report** (proposal Gate 4): running
`lake env lean AxiomAudit.lean` and reading — or `grep`-ing — its output
cannot fail on a Lean error or on an out-of-budget dependency, and a
`grep -v` exit status says nothing usable.  `FusionCategory/tools/audit-gate.sh`
(now landed, with its self-test fixtures under `FusionCategory/tools/selftest/`)
exits non-zero on Lean errors, on any dependency outside
`[propext, Classical.choice, Quot.sound]`, on unrecognised output, on an empty
audit, and on any mismatch against the checked-in manifest of audited names;
batch item B2 wires it into CI and generates the audit list mechanically.

## References to keep open

* ENO Annals 162 (2005) — §§2–5, 8.4
* EGNO *Tensor Categories* (2015) — Ch. 9
* Ostrik `1309.4822` — inequality (5)
* Vercleyen thesis `2405.20075` — `FusionSystem` conventions
* Mathlib PRs `#42145` `#42150` `#39914`–`#39922`
* `haagerup-odd/README.md`, `PLAN.md`, `docs/README.md` — packaging style
* Huang `2609.15986` — example instance (do not duplicate its analysis files)
