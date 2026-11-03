# WP2 round 2 — D4: the unitors and the triangle (member m5)

File: `.ultramath/smw1222bv/m5/Unitors.lean` (643 lines). Builds against the
landed Round-1 oleans (`FusionCategory.ReconUnit`, `ReconTensorApply`,
`ReconAssoc`, `Triangle`). `set_option autoImplicit false`; no `sorry`, no
`native_decide`, no new `axiom`. **All declarations have axioms exactly
`[propext, Classical.choice, Quot.sound]`** (`sigmaUniqueEquiv` and
`prodSubsingletonEquiv` use strictly less). An `.olean` is built
(`Unitors.olean`, module `Unitors`), so the results are importable:
put `.ultramath/smw1222bv/m5` on `LEAN_PATH` and `import Unitors`.

Build:
```
cd <repo>/FusionCategory
LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean <repo>/.ultramath/smw1222bv/m5/Unitors.lean
```

## What is proved

### The block identification of the unit channel

`left_unit : N 0 a c = if a = c then 1 else 0` forces *every* index of the
`c`-block of `𝟙 ⊗ X` to carry the label `(0, c)`, and `mult_free` makes its
channel coordinate a subsingleton; hence the block is canonically `X.blk c`.

* `fst_eq_unit_of_mem (hn) (r : (tensorObj S (unitObj hn) X).blk c) : r.1.1 = ⟨0,hn⟩`
* `snd_eq_of_mem (hn) (r : … ) : r.1.2 = c`
* `snd_eq_unit_of_mem (hn) (r : (tensorObj S X (unitObj hn)).blk c) : r.1.2 = ⟨0,hn⟩`
* `fst_eq_of_mem_unit_right (hn) (r : … ) : r.1.1 = c`
* `subsingleton_fin_N_unit_self`, `subsingleton_fin_N_self_unit`,
  `subsingleton_unitObj_blk_self`, `nonempty_fin_N_unit_self`,
  `nonempty_unitObj_blk_self`, `N_unit_self_pos`, `N_self_unit_pos`
* `unitPt`, `chanPt`, `chanPtRight` (the unique points, as `def`s — needed so
  that anonymous constructors elaborate against the *folded* block types)
* `leftIdxEquiv (hn) (X) (c) : (tensorObj S (unitObj hn) X).blk c ≃ X.blk c`
* `rightIdxEquiv (hn) (X) (c) : (tensorObj S X (unitObj hn)).blk c ≃ X.blk c`
* `leftIdxEquiv_apply : leftIdxEquiv … ⟨(0,c), ν, u, x⟩ = x` (and right)
* `leftIdxEquiv_symm_apply : (leftIdxEquiv …).symm x = ⟨(0,c), chanPt, unitPt, x⟩`
  (`@[simp]`, and the right analogue) — the inverse supplies the *canonical
  form* used everywhere below.

### The unitors

Generic transport lemmas (no `FusionSystem`):

* `sigmaUniqueEquiv (i₀) (γ) (e : β i₀ ≃ γ) (h : ∀ i ≠ i₀, IsEmpty (β i)) : (Σ i, β i) ≃ γ`
* `prodSubsingletonEquiv (α) (β) (γ) [Subsingleton α] [Nonempty α] [Subsingleton β] [Nonempty β] : α × β × γ ≃ γ`
* `graphMat (e) : Matrix α β k := fun a b => if e a = b then 1 else 0`, `graphMatInv`,
  `graphMat_mul_graphMatInv`, `graphMatInv_mul_graphMat` (the identity transported
  along an equivalence is invertible)

The unitors, and the two round trips:

* `leftUnitor (hn) (X) : tensorObj S (unitObj hn) X ⟶ X`
* `leftUnitorInv (hn) (X) : X ⟶ tensorObj S (unitObj hn) X`
* `rightUnitor`, `rightUnitorInv` (mirror images with `X ⊗ 𝟙`)
* `leftUnitor_comp_inv : leftUnitor ≫ leftUnitorInv = 𝟙 _`
* `leftUnitorInv_comp : leftUnitorInv ≫ leftUnitor = 𝟙 X`
* `rightUnitor_comp_inv`, `rightUnitorInv_comp`
* `leftUnitorIso : tensorObj S (unitObj hn) X ≅ X`, `rightUnitorIso : tensorObj S X (unitObj hn) ≅ X`
  (Iso-valued, ready for `MonoidalCategoryStruct`)

### Naturality

The key entry computation, in the form that avoids all dependent Σ-transport:

* `tensorHom_unit_left_apply (hn) (f : X ⟶ X') (c) (r) (y) (x') (hy : leftIdxEquiv … y = x') :
    tensorHom S (𝟙 (unitObj hn)) f c r y = f c (leftIdxEquiv … r) x'`
* `tensorHom_unit_right_apply` (mirror)

Naturality (`(𝟙 ◁ λ)`, `(ρ ▷ 𝟙)`):

* `whiskerLeft_leftUnitor (hn) (f : X ⟶ X') : whiskerLeft S (unitObj hn) f ≫ leftUnitor S hn X' = leftUnitor S hn X ≫ f`
* `whiskerRight_rightUnitor (hn) (f : X ⟶ X') : whiskerRight S f (unitObj hn) ≫ rightUnitor S hn X' = rightUnitor S hn X ≫ f`

These are exactly the `leftUnitor_naturality` / `rightUnitor_naturality`
fields of `CategoryTheory.MonoidalCategory`.

### The triangle

* `rightUnitor_canon (hn) (X) (e) (μ) (x) (u) (x') :
    rightUnitor S hn X e ⟨(e, ⟨0,hn⟩), μ, x, u⟩ x' = if x = x' then 1 else 0`
* `leftUnitorInv_canon (hn) (Y) (c) (y) (μ) (u) (y') :
    leftUnitorInv S hn Y c y ⟨(⟨0,hn⟩, c), μ, u, y'⟩ = if y' = y then 1 else 0`
* `assocEntry_mid_canon (hn) (X) (Y) (d) (e) (c) (ν) (μ) (x) (u) (y) (ν_s) (x_s) (μ_s) (u_s) (y_s) :
    assocEntry S X (unitObj hn) Y d ⟨(e,c), ν, ⟨(e,⟨0,hn⟩), μ, x, u⟩, y⟩
        ⟨(e,c), ν_s, x_s, ⟨(⟨0,hn⟩,c), μ_s, u_s, y_s⟩⟩
      = if x = x_s then (if y = y_s then S.F e ⟨0,hn⟩ c d e c else 0) else 0`
* `assocEntry_mid_ne_fst` / `assocEntry_mid_ne_snd` (the two vanishing cases)
* `assoc_eq_tensorHom_unit_mid (hn) (X) (Y) :
    associatorHom S X (unitObj hn) Y = tensorHom S (rightUnitor S hn X) (leftUnitorInv S hn Y)`
* **`triangle (hn) (X) (Y) :
    associatorHom S X (unitObj hn) Y ≫ whiskerLeft S X (leftUnitor S hn Y)
      = whiskerRight S (rightUnitor S hn X) Y`**
  i.e. `α_{X,𝟙,Y} ≫ (X ◁ λ_Y) = ρ_X ▷ Y`, Mathlib's `triangle` field.

## Notes on the proof of the triangle (useful for D5 and beyond)

The naive route — evaluate the sum `∑_s α_{X,𝟙,Y}(r,s) · (X ◁ λ_Y)(s,q)` —
needs the nested Σ-collapse that blocked Round 1. Instead the triangle is
reduced to the *pointwise* identity `α_{X,𝟙,Y} = (ρ_X ⊗ 1) ≫ (1 ⊗ λ_Y⁻¹)`
(valid because `X ◁ λ_Y` is invertible). At each index pair the two sides are
both a single `if`-cascade whose value is `F e 0 c d e c`; the label-forcing
lemmas make `a = e` and `b = 0` automatic, `mult_free` makes every channel
coordinate a subsingleton (so nothing has to be matched), and the surviving
`F`-entry is `1` by `TriangleCheck.triangle` (the middle-unit identity). Hence
the triangle holds with no F-entry cancellation and no nonzero hypothesis
beyond `0 < N e c d`, which is carried by the row channel `ν : Fin (N e c d)`.

Reusable ideas:

1. To compute a `tensorHom` entry whose index lies in a *unit block*, rewrite
   the index into the canonical form `e.symm (e r)` supplied by the inverse of
   the block equivalence. Then `tensorHom_apply` matches syntactically and no
   dependent transport on the Σ-label is needed. (Used for naturality.)
2. `graphMat e` is the identity transported along `e`; the unitors are exactly
   `graphMat (leftIdxEquiv …)`, which makes the iso laws one-line applications
   of `graphMat_mul_graphMatInv` / `graphMatInv_mul_graphMat`.
3. The label-forcing lemmas (`fst_eq_unit_of_mem`, `snd_eq_of_mem`, …) remove
   the `if`s of the definitions before any case analysis is attempted.

## Residual gaps

None for D4 as stated: unitors (as morphisms and as isos), their naturality,
and the triangle are all proved, with the frozen statement forms unchanged
(`TriangleCheck.triangle` is consumed, not re-proved). The `MonoidalCategory`
assembly itself is D5's direction; what is missing there from this file's side
is only the associator *iso* (D2's `AssociatorIso`) and the pentagon (D3).

## Non-vacuity and interface checks

* `triangle` applies at both genuine inhabitants of `FusionSystem` in
  `System.lean` (`VecZ2.system`, `VecZ2Twisted.system`, `FusionSystem 2 ℚ`)
  and at arbitrary `X Y : FusionMat 2 ℚ`; the `Iso` round trips apply too
  (checked in `.ultramath/smw1222bv/m5/.scratch/nonvac.lean`).
* The three statements are *literally* Mathlib's monoidal fields
  (`Mathlib/CategoryTheory/Monoidal/Category.lean`):
  `leftUnitor_naturality : 𝟙_ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f`,
  `rightUnitor_naturality : f ▷ 𝟙_ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f`,
  `triangle : (α_ X 𝟙_ Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y`,
  so D5 can fill `MonoidalCategory`'s fields verbatim from
  `whiskerLeft_leftUnitor`, `whiskerRight_rightUnitor`, `triangle`.
