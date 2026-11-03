/-
WP2 round 1, member m3, direction D4: the associator of the reconstruction.

`assocEntry` is the F-symbol as a block matrix: in the `d`-block, at a row
`((e,c)-channel ν, ((a,b)-channel μ, x, y), z)` and a column
`((a,f)-channel ν', x', ((b,c)-channel μ', y', z'))` the entry is
`F a b c d e f` when the labels `(a,b,c)` and the multiplicity indices
`(x,y,z)` match, `0` otherwise.  `assocInvEntry` is the same matrix with
`Finv a b c d f e` in place of `F` (the system carries the inverse associator
precisely for this).

The definitions are written with *projections* rather than pattern matching:
that keeps every application well typed without destructuring the index, which
is what the Σ-flexible collapse arguments need (`Matrix.mul_apply` followed by
`Fintype.sum_sigma` must be able to rewrite the middle index while the entry
function is still unapplied).

Index bookkeeping (all projections are structurally determined):
row `r`  : `r.1.1 = e`, `r.1.2 = c`, `r.2.2.1.1.1 = a`, `r.2.2.1.1.2 = b`,
           `r.2.2.1.2.2.1 = x`, `r.2.2.1.2.2.2 = y`, `r.2.2.2 = z`;
column `q` : `q.1.1 = a'`, `q.1.2 = f`, `q.2.2.1 = x'`, `q.2.2.2.1.1 = b'`,
           `q.2.2.2.1.2 = c'`, `q.2.2.2.2.2.1 = y'`, `q.2.2.2.2.2.2 = z'`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconTensor

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

variable (S : FusionSystem n k) (X Y Z : FusionMat n k)

/-- The `d`-block of the associator: `F a b c d e f` on the matched label
pattern, diagonal in the multiplicity indices, zero elsewhere. -/
abbrev assocEntry (d : Fin n) :
    (tensorObj S (tensorObj S X Y) Z).blk d → (tensorObj S X (tensorObj S Y Z)).blk d → k :=
  fun r q =>
    if h1 : r.2.2.1.1.1 = q.1.1 then
      if h2 : r.2.2.1.1.2 = q.2.2.2.1.1 then
        if h3 : r.1.2 = q.2.2.2.1.2 then
          if h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1) then
            if h5 : r.2.2.1.2.2.2 = (h2 ▸ q.2.2.2.2.2.1) then
              if h6 : r.2.2.2 = (h3 ▸ q.2.2.2.2.2.2) then
                S.F r.2.2.1.1.1 r.2.2.1.1.2 r.1.2 d r.1.1 q.1.2
              else 0
            else 0
          else 0
        else 0
      else 0
    else 0

/-- The associator of the reconstruction. -/
abbrev associatorHom : tensorObj S (tensorObj S X Y) Z ⟶ tensorObj S X (tensorObj S Y Z) :=
  fun d => Matrix.of (assocEntry S X Y Z d)

/-- The `d`-block of the inverse associator: `Finv a b c d f e` on the matched
label pattern, diagonal in the multiplicity indices. -/
abbrev assocInvEntry (d : Fin n) :
    (tensorObj S X (tensorObj S Y Z)).blk d → (tensorObj S (tensorObj S X Y) Z).blk d → k :=
  fun q r =>
    if h1 : r.2.2.1.1.1 = q.1.1 then
      if h2 : r.2.2.1.1.2 = q.2.2.2.1.1 then
        if h3 : r.1.2 = q.2.2.2.1.2 then
          if h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1) then
            if h5 : r.2.2.1.2.2.2 = (h2 ▸ q.2.2.2.2.2.1) then
              if h6 : r.2.2.2 = (h3 ▸ q.2.2.2.2.2.2) then
                S.Finv r.2.2.1.1.1 r.2.2.1.1.2 r.1.2 d q.1.2 r.1.1
              else 0
            else 0
          else 0
        else 0
      else 0
    else 0

/-- The inverse associator. -/
abbrev associatorInv : tensorObj S X (tensorObj S Y Z) ⟶ tensorObj S (tensorObj S X Y) Z :=
  fun d => Matrix.of (assocInvEntry S X Y Z d)

end FusionCategory
