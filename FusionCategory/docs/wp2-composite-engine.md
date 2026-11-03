# The composite engine: collapsing nested-Σ matrix composites

**Status: kernel-checked.** `.ultramath/smw1222bv/m2/D2Iso.lean`, namespace `FusionCategory`,
section variables `(S : FusionSystem n k) (X Y Z : FusionMat n k) (d : Fin n)`, with

    abbrev blkL : Type := (tensorObj S (tensorObj S X Y) Z).blk d
    abbrev blkR : Type := (tensorObj S X (tensorObj S Y Z)).blk d

Axiom budget of every declaration: `[propext, Classical.choice, Quot.sound]`.

## Why this is the hard case

`associatorHom ≫ associatorInv` at block `d` is the matrix product
`∑ m : blkR, assocEntry d r m * assocInvEntry d m r'`, and `blkR` is the nested Σ

    blkR = Σ (p : Fin n × Fin n), Fin (N p.1 p.2 d) × (X.blk p.1 × (Σ (q : Fin n × Fin n), Fin (N q.1 q.2 p.2) × (Y.blk q.1 × Z.blk q.2)))

so the middle index carries the labels `(a₂, f)`, the channel `ν₂`, the multiplicity `x₂`, the
inner labels `(b₂, c₂)`, the inner channel `μ₂` and the inner multiplicities `(y₂, z₂)`.  The
`if`-ladder of `assocEntry` is written with dependent `dif`s and `▸`-transports, which do not
reduce while the labels are variables.

## The method

1. **Flatten, do not reindex.** `rw [Matrix.mul_apply]`, then

       simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

   turns the sum over the nested Σ into one iterated sum.  The binder order is
   `(a₂, f, ν₂, x₂, b₂, c₂, μ₂, y₂, z₂)` — label, then channel, then multiplicity at each
   level.  (No `Matrix.reindex`, no `Equiv`: `rw [← Fintype.sum_prod_type]` does NOT flatten,
   the match is syntactic.)

2. **Never unfold an entry inside the sum.**  Use the two families of lemmas below, which move
   the `dif`-ladder into plain equalities *before* any summation.

3. **Kill the sums one binder at a time** with `Finset.sum_eq_single`.  The off-value branch is
   closed uniformly by

       have hz : ∀ (rest of the binders), <summand> = 0 := by intro ...; rw [<zero lemma>]; simp
       simp only [hz, Finset.sum_const_zero]

   (`simp` rewrites under all the remaining binders, and the nested sums of zeros vanish by
   `Finset.sum_const_zero`).  The killed binder's own value is substituted automatically.

4. **Free pass-through binders** (here `f`, then `ν₂`, `μ₂`) are handled by peeling on the left
   with `Finset.sum_congr rfl (fun f _ => ...)` and *rewriting the right-hand side constant* `V`
   into `∑ _ : Fin m, V` with `sum_fin_const_eq`, which needs `m • V = V` (`nsmul_entry`:
   `mult_free` makes the channel multiplicity 0 or 1, and `F_support` kills the product off the
   channels).

## The lemmas

* `assocEntry_apply_matched`, `assocInvEntry_apply_matched`.  At labels shared by both indices
  the six-deep ladder collapses to

      if hx : x = x' then if hy : y = y' then if hz : z = z' then F a b c d e f else 0 else 0

  Proof: `simp only [assocEntry]` (the reflexive conditions `a = a` become `True` and the
  `▸`-transports vanish definitionally), then `simp only [dif_pos trivial]`.

* `assocEntry_exact`, `assocInvEntry_exact`: the fully matched entry is `S.F a b c d e f`
  resp. `S.Finv a b c d f e`.

* Zero lemmas: `assocEntry_zero_a`, `_b`, `_c` (general, hypotheses on the projections),
  `assocEntry_zero_x_gen` (the *middle* labels `b₂, c₂` still free — this is the one that lets
  the `x`-kill happen before the `b`/`c` kills), `assocEntry_zero_x`, `_y`, `_z` (matched
  labels), and the six mirrors for `assocInvEntry`.

* `collapse_matched`: for `r = ⟨⟨e,c⟩,⟨ν,⟨⟨⟨a,b⟩,⟨μ,x,y⟩⟩,z⟩⟩⟩` and
  `r' = ⟨⟨e',c⟩,⟨ν',⟨⟨⟨a,b⟩,⟨μ',x,y⟩⟩,z⟩⟩⟩`,

      ∑ a₂ f ν₂ x₂ b₂ c₂ μ₂ y₂ z₂, assocEntry d r m * assocInvEntry d m r'
        = ∑ f, S.F a b c d e f * S.Finv a b c d f e'

  and `S.F_comp_inv` (via `assocIso_label_right`) turns the right-hand side into
  `if e' = e then 1 else 0`.

* `nsmul_entry`, `sum_fin_const_eq`, `channel_pos`.

## Traps

* `assocEntry`/`assocInvEntry` are `abbrev`s, so `rw [assocEntry]` fails.  Use
  `simp only [assocEntry]`.
* A section variable that occurs only inside a *hypothesis* type stays explicit and comes
  FIRST in the binder list; call such lemmas with named arguments.
* `simp only [assocEntry]` turns the reflexive conditions into `True`, so the residue is
  `dif_pos trivial`, not `dif_pos rfl`.
* `split_ifs` with `cases` on a `▸`-transport fails (dependent elimination); use the
  `dif_pos`/`dif_neg` route instead.
