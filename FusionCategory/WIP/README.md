# WIP: the pentagon's three-factor side (`PentagonLHS.lean`) — state record

**Status: blueprint complete and verified; the proof is blocked at one mechanical
step.  This file is WIP — it elaborates standalone (with `sorry`s) but is NOT
part of the package (not in the module tree, not in the umbrella, not in the
audit closure).  Do not import it.**

## What is proved in the file

- `chan_delta_one` — the channel delta is `1` (channels are subsingletons).
- `idBlk_entry` — the identity block entry.
- `pent_nsmul3` — the channel normalisation: the five per-`kk` factors
  (`(N e Dw d)`, `(N a h d)` witnessed-`1`; `(N a kk e)`, `(N b C kk)`,
  `(N kk Dw h)` — `1` in the nonzero case by the support facts of the first
  and third `F`-entries) collapse to the product.
- `LHS_entry` **scaffold**: the destructure + leaf-match case split (copied
  from `U_entry`), the composite as a triple matrix product (`≫` is
  right-associative: `leg1 ≫ (α₂ ≫ leg2)` — learned the hard way), both
  `Matrix.mul_apply`s, the `Finset.mul_sum` distribution, and the outer
  flattenings: **the `m1`-sum (`rw [flatBlk ...]`), the `m2`-sum
  (`simp only [flatBlk ...]` — `rw` does not match it, `simp only` does), and
  the `s`-flattening (`simp only [flatNest S A (tensorObj S B C)]`)** all
  fire, green.

## The verified blueprint (the coordinator's analysis, to be executed)

With `p = ⟨(e, Dw), (ν, (u, z))⟩`, `u = ⟨(g, Cc), (μ, (v, y))⟩`,
`v = ⟨(a, b), (l₀, (x, x₂))⟩`, and `q = ⟨(a, h), (ν', (x, w'))⟩`,
`w' = ⟨(b, f), (μ', (x₂, v'))⟩`, `v' = ⟨(Cc, Dw), (lq, (y, z))⟩`:

- **The kills** (each `Finset.sum_eq_single`, off-cases via
  `tensorHom_apply_ne` for the label pairs, `assocEntry_eq_zero_of_not` +
  component contradictions for the element structures):
  `m1`'s pair → `(e, Dw)`; `s`'s `(a₁, E)`-pair → `(a, E₂)` (α₂'s `h2`);
  `w₁` → `x`; `t₁` → `t₃` **as elements** (α₂'s `h5` — this pins `t₁`'s
  channel to `t₃`'s, so only ONE `(N b C kk)` factor survives);
  `z₁` → `z`; `m2`'s pair → `(a, h)`; `w₂` → `x`; `t₂`'s `Cw` → `Dw`
  (α₂'s `h3`); `t₃`'s labels → `(b, Cc)`; `z₃` → `z`.
- **The three F-values at the survivor**:
  `S.F a b Cc e g E₂` (leg1's α-entry),
  `S.F a E₂ Dw d e h` (α₂'s entry),
  `S.F b Cc Dw h E₂ f` (leg2's α-entry).
- **The free binders**: `E₂` (the sum), and the channels `λ` (s's),
  `λ₃` (t₃'s), `σ` (t₂'s) — plus `ν₁`, `ν₂` (witnessed-1).  The channel sums
  convert via `sum_fin_const_nsmul`; `pent_nsmul3` collapses the factors.
- **The conclusion**: `S.pentagon` at `(a, b, Cc, Dw, g, f, h, d, e)` equates
  the three-F sum with `U_entry`'s two-F product — `PentagonShapeHom`
  follows by matrix extensionality, and with `ReconClosureBridge` the
  reconstruction is a fusion category.

## The blocker, precisely

After the `s`-flattening, the inner `(B⊗C)`-blocks (`t₁` at the label
`s.1.2`, `t₃` at `t₂`'s label) must be flattened **at binder-dependent
labels**.  `simp only [flatNest S B C]` with a free label times out
(max steps); `rw` cannot reference the goal's auto-named binders
(`rename_i` does not reach term-level sum binders).

**Escape routes** (either should work):
1. `conv` + `enter` to navigate under the binders to the `t₃`-sum, then
   `rw [flatNest S B C _]` with the label unified against the in-scope
   binder.
2. Kill the outer pair-sums FIRST (m1's to `(e, Dw)`, m2's to `(a, h)` —
   both off-cases are `tensorHom_apply_ne`), making the `t₂`-flattening's
   label the CONCRETE `h`; split the `(E₂, Cw)`-pair-sum into `∑ E₂ ∑ Cw`
   (`Fintype.sum_prod_type`-style), kill `Cw` → `Dw`, and then only the
   `t₃`-sum (at the free label `E₂`) and the `t₁`-sum (at `s.1.2`) remain —
   handle `t₁` by killing its sum to `t₃` (α₂'s `h5` pins the whole element)
   and `t₃` by `conv`.

Also learned: `≫` is `infixr` (right-associative) — the composite is
`leg1 ≫ (α₂ ≫ leg2)` and `CategoryStruct.comp` unfolds to
`M1 * (M2 * M3)`, NOT `(M1 * M2) * M3`.
