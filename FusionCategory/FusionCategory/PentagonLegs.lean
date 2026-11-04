/-
WP2 round 3, member m8, direction D8: the pentagon's two-factor (left) side,
reduced kernel-side to a single middle sum.

# What this file is

The frozen `PentagonShapeHom` (D3's target) says

  `(a_{W,X,Y} (x) 1_Z) ; a_{W, X(x)Y, Z} ; (1_W (x) a_{X,Y,Z})
     = a_{W(x)X, Y, Z} ; a_{W, X, Y(x)Z}`.

Round 1's `ReconPentagon.lean` (m5) computes the left side entrywise with a
bespoke four-leaf refinement (`Quad`, `qlo`, `qhi`, `ppQ`, `pXY`, …).  On the
canonical scaffold most of that is *not needed*, because `tensorObj`'s block
index type is `Sigma (p : Fin n x Fin n), Fin (N p.1 p.2 c) x X.blk p.1 x Y.blk p.2`
and `tensorHom_apply` therefore reads the inner block index as opaque: the two
"two-factor legs" are instances of `tensorHom_apply`, not of a reindexing.

This file records that precisely, so that D3's remaining work is *only* the
middle sum:

* `leg_assoc_tensor_entry` / `leg_tensor_assoc_entry` — the entry of
  `tensorHom (associatorHom …) (1 …)` and of `tensorHom (1 …) (associatorHom …)`
  at a matched label pair: channel delta times the associator's entry times the
  identity's entry.  (`tensorHom_apply` instantiated; the actual work is naming
  the index types.)
* `leg_assoc_tensor_entry_F` — the same, with the associator's entry replaced by
  its *proved* leaf form (`assocEntry_apply_matched`), i.e. m5's `lhs_entry`
  first factor on the canonical scaffold.
* `pentagon_lhs_reduce` / `pentagon_rhs_reduce` — both sides of the pentagon,
  as one explicit `Finset.sum` over the middle block.  The only content left in
  the pentagon is that this sum has a single nonzero term.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconAssocIso

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-! ## The two-factor legs, entrywise -/

/-- **The left leg of the pentagon**, `a_{W,X,Y} (x) 1_Z`, at a matched label
pair: the channel delta times the associator's entry times the identity's. -/
theorem leg_assoc_tensor_entry (W X Y Z : FusionMat n k) (d : Fin n)
    (e c : Fin n) (ν ν' : Fin (S.ring.N e c d))
    (u : (tensorObj S (tensorObj S W X) Y).blk e)
    (u' : (tensorObj S W (tensorObj S X Y)).blk e)
    (z z' : Z.blk c) :
    tensorHom S (associatorHom S W X Y) (𝟙 Z) d
        ⟨(e, c), (ν, (u, z))⟩ ⟨(e, c), (ν', (u', z'))⟩
      = (if ν = ν' then 1 else 0)
          * (associatorHom S W X Y e u u' * (if z = z' then 1 else 0)) := by
  rw [tensorHom_apply]
  rfl

/-- **The right leg of the pentagon**, `1_W (x) a_{X,Y,Z}`, at a matched label
pair. -/
theorem leg_tensor_assoc_entry (W X Y Z : FusionMat n k) (d : Fin n)
    (e c : Fin n) (ν ν' : Fin (S.ring.N e c d))
    (w w' : W.blk e)
    (u : (tensorObj S (tensorObj S X Y) Z).blk c)
    (u' : (tensorObj S X (tensorObj S Y Z)).blk c) :
    tensorHom S (𝟙 W) (associatorHom S X Y Z) d
        ⟨(e, c), (ν, (w, u))⟩ ⟨(e, c), (ν', (w', u'))⟩
      = (if ν = ν' then 1 else 0)
          * ((if w = w' then 1 else 0) * associatorHom S X Y Z c u u') := by
  rw [tensorHom_apply]
  rfl

/-! ## The same, with the associator's leaf form

`assocEntry_apply_matched` is the proved leaf form of the associator: at
`r = ⟨⟨e,c⟩,⟨ν,⟨⟨⟨a,b⟩,⟨μ,x,y⟩⟩,z⟩⟩⟩` and
`q = ⟨⟨a,f⟩,⟨ν',⟨x',⟨⟨b,c'⟩,⟨μ',y',z'⟩⟩⟩⟩⟩` the entry is
`F a b c' d e f` when `x = x'`, `y = y'`, `z = z'`, else 0.

To state the leg's entry in that form I have to write the index at the *inner*
level too, which is where m5's `Quad` bookkeeping came from.  Below, the row of
`a_{W,X,Y}` is the (W(x)X)(x)Y-element `⟨(A,B),(μ,(⟨(a,b),(ν_ab,(x,y))⟩, zY))⟩`
and the column is the W(x)(X(x)Y)-element
`⟨(a,f),(ν_f,(x', ⟨(b,cY),(μ',(y',zY'))⟩))⟩`. -/

/-- **m5's `lhs_entry`, first factor, on the canonical scaffold.**

The row is `⟨(A,cZ),(ν,(u,z))⟩` with `u = ⟨(A,B),(μA,(v,yY))⟩`,
`v = ⟨(a,b),(μab,(x,yx))⟩`; the column is `⟨(A,cZ),(ν',(u',z'))⟩` with
`u' = ⟨(a,f),(ν_f,(x',⟨(b,B),(μ',(y',z'))⟩))⟩`.  The value is
`F a b B e A f` (`e` is the *inner* block label, i.e. the label of `(W(x)X)(x)Y`)
when `x = x'`, `y = y'`, `yY = z'`. -/
theorem leg_assoc_tensor_entry_F (W X Y Z : FusionMat n k) (d : Fin n)
    (e cZ : Fin n) (ν ν' : Fin (S.ring.N e cZ d))
    (A B : Fin n) (μA : Fin (S.ring.N A B e))
    (a b : Fin n) (μab : Fin (S.ring.N a b A)) (x : W.blk a) (yx : X.blk b)
    (yY : Y.blk B) (z : Z.blk cZ)
    (f : Fin n) (ν_f : Fin (S.ring.N a f e))
    (x' : W.blk a) (μ' : Fin (S.ring.N b B f)) (y' : X.blk b) (z' : Y.blk B)
    (zz' : Z.blk cZ) :
    tensorHom S (associatorHom S W X Y) (𝟙 Z) d
        ⟨(e, cZ), (ν, (⟨(A, B), (μA, (⟨(a, b), (μab, (x, yx))⟩, yY))⟩, z))⟩
        ⟨(e, cZ), (ν', (⟨(a, f), (ν_f, (x', ⟨(b, B), (μ', (y', z'))⟩))⟩, zz'))⟩
      = (if ν = ν' then 1 else 0)
          * ((if hx : x = x' then (if hy : yx = y' then
              (if hz : yY = z' then S.F a b B e A f else 0) else 0) else 0)
            * (if z = zz' then 1 else 0)) := by
  rw [leg_assoc_tensor_entry]
  have h := assocEntry_apply_matched S (X := W) (Y := X) (Z := Y) (d := e)
    (e := A) (c := B) (ν := μA) (a := a) (b := b) (μ := μab) (x := x) (y := yx)
    (z := yY) (f := f) (ν' := ν_f) (x' := x') (μ' := μ') (y' := y') (z' := z')
  simp only [associatorHom, Matrix.of_apply] at h ⊢
  rw [h]

/-! ## Both sides of the pentagon as one middle sum each -/

/-- **The pentagon's left side, reduced.**  `(a_{W,X,Y} (x) 1_Z) ; a_{W,X(x)Y,Z}`,
at a row `r` and a column `q`: a single sum over the middle block
`(W(x)(X(x)Y))(x)Z`.  Every summand is `leg_assoc_tensor_entry` times the second
associator's entry, so the only remaining content of the pentagon is that this
sum has one nonzero term. -/
theorem pentagon_lhs_reduce (W X Y Z : FusionMat n k) (d : Fin n)
    (r : (tensorObj S (tensorObj S (tensorObj S W X) Y) Z).blk d)
    (q : (tensorObj S W (tensorObj S (tensorObj S X Y) Z)).blk d) :
    (tensorHom S (associatorHom S W X Y) (𝟙 Z)
        ≫ associatorHom S W (tensorObj S X Y) Z) d r q
      = ∑ m : (tensorObj S (tensorObj S W (tensorObj S X Y)) Z).blk d,
          (tensorHom S (associatorHom S W X Y) (𝟙 Z) d r m
            * assocEntry S W (tensorObj S X Y) Z d m q) :=
  Matrix.mul_apply

/-- **The pentagon's right side, reduced**: `a_{W(x)X,Y,Z} ; a_{W,X,Y(x)Z}`. -/
theorem pentagon_rhs_reduce (W X Y Z : FusionMat n k) (d : Fin n)
    (r : (tensorObj S (tensorObj S (tensorObj S W X) Y) Z).blk d)
    (q : (tensorObj S W (tensorObj S X (tensorObj S Y Z))).blk d) :
    (associatorHom S (tensorObj S W X) Y Z
        ≫ associatorHom S W X (tensorObj S Y Z)) d r q
      = ∑ m : (tensorObj S (tensorObj S W X) (tensorObj S Y Z)).blk d,
          (assocEntry S (tensorObj S W X) Y Z d r m
            * assocEntry S W X (tensorObj S Y Z) d m q) :=
  Matrix.mul_apply

open FusionCategory in
#print axioms FusionCategory.leg_assoc_tensor_entry
open FusionCategory in
#print axioms FusionCategory.leg_assoc_tensor_entry_F
open FusionCategory in
#print axioms FusionCategory.pentagon_lhs_reduce
open FusionCategory in
#print axioms FusionCategory.pentagon_rhs_reduce

end FusionCategory
