# WIP: the pentagon's three-factor side (`PentagonLHS.lean`) — COMPLETE

**Status: proved.** Both `sorry`s are closed, the capstone
`pentagonShapeHom_holds : PentagonShapeHom S` is proved, and the endgame
`reconIsFusionCanonical_recon` closes WP2's last open item: the reconstruction
is a fusion category in the library's own sense. The file elaborates standalone
(zero warnings, ~5 s) but is NOT yet part of the package — not in the module
tree, not in the umbrella, not in the audit closure. Do not import it until the
integration landing.

## What is proved in the file

- The support lemmas: `chan_delta_one`, `sum_subsingleton_witness`,
  `sum_channel`, `idBlk_entry`, `pent_nsmul3` (kept though the final proof no
  longer needs it — the channel disposals went witness-free), the rfl-helper
  `associatorHom_apply`, and `LHS_core` — the named-binder workbench in which
  the leaf-case core computation runs.
- `LHS_entry` — the three-factor side, entrywise: the composite
  `(α_{A,B,C} ⊗ 𝟙_D) ≫ α_{A,B⊗C,D} ≫ (𝟙_A ⊗ α_{B,C,D})` at a pair of refined
  indices is the label-level pentagon sum
  `∑ kk, F a b Cc e g kk * F a kk Dw d e h * F b Cc Dw h kk f` on matched
  leaves and `0` off them.
- `pentagonShapeHom_holds` — `PentagonShapeHom S` for every `S`: entrywise
  (`funext d p q`), `LHS_entry` and `U_entry` put both sides in guarded form,
  and on the leaf match the label pentagon `S.pentagon` at
  `(a, b, Cc, Dw, g, f, h, d, e)` identifies the three-`F` sum with the
  two-`F` product (off the match both sides are `0`).
- `reconIsFusionCanonical_recon (S) (hn : 0 < n) : ReconIsFusionCanonical S hn`
  — the `ReconClosureBridge` application: with the pentagon in hand, WP2's
  reconstruction is a fusion category.

## Verification record (swarm `smw77hbfw`, member m1, accepted)

- `cd FusionCategory && lake env lean WIP/PentagonLHS.lean` — exit 0, zero
  warnings (coordinator re-ran it after landing).
- `#print axioms` on `LHS_entry`, `LHS_core`, `pentagonShapeHom_holds`,
  `reconIsFusionCanonical_recon` — `[propext, Classical.choice, Quot.sound]`.
- Diff vs `90cff28`: only the two helpers added and the two `sorry` regions
  replaced; `LHS_entry`'s statement and the seven committed green levels are
  byte-identical.

## The engine (for the next entry computation)

- **The hinner-technique** (third application, now at theorem level): the
  goal's inner sum binders are auto-named, so `rw`/`simp` cannot reference
  them. State the whole inner computation as a standalone lemma with YOUR OWN
  binder names (`LHS_core` here; `hleg1`/`hleg2` for the leg entries), prove
  it where the binders are referenceable, apply it from the outside via
  `Finset.sum_congr` / `simp only`.
- **Witness-free channel disposal beats nsmul bookkeeping.** `assocMatch`
  compares labels and elements but never channels, so a channel sum whose
  body does not mention it (none of the tensorHom deltas touch it) is disposed
  by `sum_channel` into `if 0 < N … then body-at-⟨0, _⟩ else 0`; the absent
  branch vanishes because the corresponding `F`-entry is `0` by `F_support`
  (`F_ne_zero_supp`). No multiplicity factor ever needs collapsing.
- **The kills**: label pairs by `Finset.sum_eq_single` + `Prod.ext` from the
  match's h1/h2/h3; elements by the match's h4/h5/h6 through
  `cast_eq_of_eq_self` / `heq_of_eq_cast'`; off-cases always
  `assocEntry_eq_zero_of_not` (expose `associatorHom` as `assocEntry` first —
  `associatorHom_apply` is `rfl`) or `tensorHom_apply_ne`, then `ring`.
- **The off-leaf case**: flatten BOTH middle indices, eight nested
  `Finset.sum_eq_zero`, then split on the two label pairs, the three
  `assocMatch`es and the four tensorHom deltas; the surviving case chains the
  matches into `qlo = qhi` (the `PentagonU` HEq helpers `heq_of_eq_cast'`,
  `cast_blk_fst/x/y`, `sigma_eq_mk`) and contradicts `hleaf`.
- `≫` is `infixr` (the composite is `leg1 ≫ (α₂ ≫ leg2)`); re-associate with
  `rw [← Matrix.mul_assoc]` to choose which index is the outer sum.
- `rw` and `simp only` disagree on which applications match — when one fails,
  try the other. `Finset.sum_eq_single` against a big goal needs the
  `(Finset.sum_eq_single w ?_ ?_).trans ?_` form. Write `∑ x in s, f x`.
  `if`-terms with different `Decidable` instances do not match syntactically —
  go through `if_pos (Subsingleton.elim …)`.

## What remains (the integration landing, not yet done)

- Bring the file into the package proper: module placement, umbrella import,
  regenerate the audit manifest (`tools/gen-audit.sh`), run
  `tools/ci-chain.sh`, and land as the WP2-closing commit. Until then this
  file is a verified but unpackaged artefact.
