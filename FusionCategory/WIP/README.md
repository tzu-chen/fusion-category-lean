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

## The blocker, precisely — and its SOLUTION (found this session)

The blocker was: the inner `(B⊗C)`-blocks must be flattened at binder-dependent
labels, `simp only [flatNest S B C]` with a free label times out, and `rw`
cannot reference the goal's auto-named term binders (`rename_i` does not reach
them).  **The solution is `U_entry`'s own `hinner`-technique**, which this
session identified as the general answer: *state each inner transformation as
an explicit `have : ∀ binders..., (hand-written body) = (hand-written new
body)` with ONE'S OWN binder names, prove it by the sum_eq_single/sum_eq_zero
machinery (where the binders are referenceable), and apply it from the
outside via `Finset.sum_congr`.*  No tactic ever needs to touch an
auto-named binder.

**The complete disposal order (m2-outer — verified green up to step 1):**

0. `simp only [CategoryStruct.comp]; rw [← Matrix.mul_assoc]` (the composite
   is `leg1 ≫ (α₂ ≫ leg2)`; re-associate so the m2-index is the OUTER sum),
   `rw [Matrix.mul_apply]; simp only [Matrix.mul_apply, Finset.sum_mul]`.
1. ✅ **GREEN**: `rw [flatBlk S A (tensorObj S (tensorObj S B C) D) d]`, kill
   the m2 pair to `(a, h)` via `(Finset.sum_eq_single (a, h) ?_ ?_).trans ?_`
   (off-case: `tensorHom_apply_ne` for leg2, then `mul_zero`; 4-level
   `Finset.sum_eq_zero` cascade).
2. The ν₂ channel: its body mentions ν₂ only through the element-arguments —
   rewrite the leg2 entry first (`tensorHom_apply` fires on hand-written
   shapes — verified in the scratch — but NOT on the goal's auto-named
   binder forms; use the hinner-technique), discharge the channel δ by
   `chan_delta_one`, then `sum_fin_const_nsmul`.
3. Kill w₂ → x (off: the A-δ via `idBlk_entry`).
4. Flatten t₂ at the CONCRETE label `h`; swap the (E₂, Cw)-pair-sum's
   components (`Equiv.sum_comp (Equiv.prodComm …)`), kill Cw → Dw (off:
   α₂'s h3-fail via `assocEntry_eq_zero_of_not`).
5. σ → nsmul; kill z₃ → z (off: α₂'s h6-fail).
6. Flatten t₃ at the free label E₂ — **the one free-label flattening**
   (works in isolation — verified in the scratch; do it inside a `have`
   whose body is hand-written).  Kill t₃'s (b₂, C₂)-pair → (b, Cc) and its
   raws → (x₂, y) (off: leg2's α-match fails); λ₃ stays free (nsmul).
7. Flatten the m1-sum (`flatBlk`), kill its pair → (e, Dw) (off:
   `tensorHom_apply_ne` for leg1), ν₁ → nsmul, flatten s at the CONCRETE
   label `e`, kill the s-pair → `(a, E₂)` (E₂ in scope — an outer binder!),
   λ → nsmul, kill w₁ → x, kill t₁ → `⟨(b, Cc), ⟨λ₃, (x₂, y)⟩⟩`
   (**the single term with λ₃ in scope** — this is why t₃ is flattened and
   t₁ is killed, not vice versa), kill z₁ → z.
8. The remaining goal is `∑ E₂, (five nsmul factors) • (F₁·F₂·F₃)` with the
   factors `(N e Dw d)`, `(N a h d)`, `(N a E₂ e)`, `(N b C E₂)`,
   `(N E₂ Dw h)` — collapse by `pent_nsmul3` (proved), then `S.pentagon`
   at `(a, b, Cc, Dw, g, f, h, d, e)` closes against `U_entry`'s matched
   value.

Also learned this session: `rw` and `simp` disagree on which applications
match (three separate cases where `rw` fails and `simp only` fires, and one
— the leg2 entry at auto-named binders — where both fail and only explicit
hand-written shapes work); `Finset.sum_eq_single` needs the
`(…).trans ?_`-form to elaborate against a big goal; `≫` is `infixr`.
