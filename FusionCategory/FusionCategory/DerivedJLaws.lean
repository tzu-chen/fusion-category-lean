/-
WP2 round 2, member m8, direction D8: validations of `derivedJ`.

Round 1 (`D8Scalar.lean`, copied from `.ultramath/smw10qjp3/m8/DerivedJ.lean`)
defined the twist

  `comparisonScalar S x y z`  — the channel scalar of the comparison map
                                 `ψ_{x,y} : (x ⊗ y)* ⟶ y* ⊗ x*`,
  `derivedJGen S a b c`       — the ratio `ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}`, i.e. the
                                 `(c,c)`-entry of the tensorator `X_a** ⊗ X_b** ⟶ (X_a ⊗ X_b)**`,

and proved its defining property on a channel, its nonvanishing, and its gauge law.

This file adds what Task 2.3's validations need and Round 1 did not have:

* the **signature's own twist laws** for the derived twist, proved on arbitrary data:
  `derivedJGen_unit_left` (`J 1 j j = 1`), `derivedJGen_unit_right` (`J i 1 i = 1`),
  `derivedJGen_dual` (`J i i* 1 = 1`) — exactly `FusionSystem.J_unit_left`,
  `J_unit_right`, `J_dual`, which `J_match` demands.  They are consequences of the
  middle-unit entry `TriangleCheck.triangle`, the two unit normalisations, and the
  snake equations — no assumption on the datum beyond `FusionSystem`.
* the frozen gauge invariance of `Statements2` (`WP2.DerivedJ_gauge_invariant`)
  discharged for the derived twist, and its compatibility with `J_match`
  (`WP2.j_match_gauge_iff`).
* the kernel statement that `derivedJ` **does not see the carried field `S.J`**.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.Statements2
import FusionCategory.Triangle
import FusionCategory.DerivedJScalar

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the two block-collapse lemmas

`Finv_comp` sums over the `a ⊗ b`-channel `e`, `F_comp_inv` over the `b ⊗ c`-channel
`f`.  On every block met in the unit/duality normalisation one of the two channel
sets is a point (forced by `left_unit`, `right_unit` or `dual_coeff`), so the sum
collapses to a single product: `Finv = F⁻¹` there.  Nothing is cancelled without
being known nonzero: the product is *computed*, not divided. -/

/-- `Finv · F = 1` on a block whose `a ⊗ b`-channel is unique (`hu`). -/
theorem finv_mul_F_of_unique (S : FusionSystem n k) {a b c d e f : Fin n}
    (hu : ∀ e' : Fin n, 0 < S.ring.N a b e' → e' = e)
    (hf : 0 < S.ring.N b c f) (hafd : 0 < S.ring.N a f d)
    (hab : 0 < S.ring.N a b e) (hecd : 0 < S.ring.N e c d) :
    S.Finv a b c d f e * S.F a b c d e f = 1 := by
  have hcomp := S.Finv_comp a b c d f f hf hafd hf hafd
  have hsum : (∑ e' : Fin n, S.Finv a b c d f e' * S.F a b c d e' f)
      = S.Finv a b c d f e * S.F a b c d e f := by
    refine Finset.sum_eq_single e ?_ ?_
    · intro e' _ he'
      have hz : S.Finv a b c d f e' = 0 := by
        refine S.Finv_support a b c d f e' ?_
        intro hcon
        exact he' (hu e' hcon.2.2.1)
      rw [hz, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at hcomp
  simpa using hcomp

/-- `Finv · F = 1` in the commuted order, from `F_comp_inv` (sum over the `b ⊗ c`-channel). -/
theorem finv_mul_F_of_unique' (S : FusionSystem n k) {a b c d e f : Fin n}
    (hf' : ∀ f' : Fin n, 0 < S.ring.N b c f' → f' = f)
    (he : 0 < S.ring.N a b e) (hecd : 0 < S.ring.N e c d)
    (hbcf : 0 < S.ring.N b c f) (hafd : 0 < S.ring.N a f d) :
    S.Finv a b c d f e * S.F a b c d e f = 1 := by
  have hcomp := S.F_comp_inv a b c d e e he hecd he hecd
  have hsum : (∑ f' : Fin n, S.Finv a b c d f' e * S.F a b c d e f')
      = S.Finv a b c d f e * S.F a b c d e f := by
    refine Finset.sum_eq_single f ?_ ?_
    · intro f' _ hf''
      have hz : S.F a b c d e f' = 0 := by
        refine S.F_support a b c d e f' ?_
        intro hcon
        exact hf'' (hf' f' hcon.2.2.1)
      rw [hz, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at hcomp
  simpa using hcomp

/-! ## §2 — uniqueness of the channels forced by the unit and the duality -/

section Uniqueness

variable (S : FusionSystem n k) (hn : 0 < n)

/-- The only `e'` with `0 < N a 1 e'` is `a` (`right_unit`). -/
theorem unique_right_unit (a : Fin n) : ∀ e' : Fin n, 0 < S.ring.N a ⟨0, hn⟩ e' → e' = a := by
  intro e' h
  rw [S.ring.right_unit hn a e'] at h
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h
  exact lt_irrefl 0 h

/-- The only `f'` with `0 < N 1 b f'` is `b` (`left_unit`). -/
theorem unique_left_unit (b : Fin n) : ∀ f' : Fin n, 0 < S.ring.N ⟨0, hn⟩ b f' → f' = b := by
  intro f' h
  rw [S.ring.left_unit hn b f'] at h
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h
  exact lt_irrefl 0 h

/-- `0 < N i i* 1` (`dual_coeff`). -/
theorem pos_dual_coeff (i : Fin n) : 0 < S.ring.N i (S.ring.dual i) ⟨0, hn⟩ := by
  rw [S.ring.dual_coeff hn i]
  simp

/-- `0 < N i* i 1`. -/
theorem pos_dual_coeff' (i : Fin n) : 0 < S.ring.N (S.ring.dual i) i ⟨0, hn⟩ := by
  rw [S.ring.dual_coeff hn (S.ring.dual i)]
  simp [FusionRing.dual_dual]

/-- `0 < N i 1 i`. -/
theorem pos_right_unit (i : Fin n) : 0 < S.ring.N i ⟨0, hn⟩ i := by
  rw [S.ring.right_unit hn i i]
  simp

/-- `0 < N 1 i i`. -/
theorem pos_left_unit (i : Fin n) : 0 < S.ring.N ⟨0, hn⟩ i i := by
  rw [S.ring.left_unit hn i i]
  simp

end Uniqueness

end FusionCategory

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §3 — the signature's twist laws for the derived twist -/

/-- `J 1 j j = 1`: the left unit law `FusionSystem.J_unit_left` holds for the derived twist. -/
theorem derivedJGen_unit_left (S : FusionSystem n k) (hn : 0 < n) (b : Fin n) :
    derivedJGen S ⟨0, hn⟩ b b = 1 := by
  have hF1 : S.F (S.ring.dual b) ⟨0, hn⟩ b ⟨0, hn⟩ (S.ring.dual b) b = 1 :=
    TriangleCheck.triangle S hn (S.ring.dual b) b ⟨0, hn⟩ (pos_dual_coeff' S hn b)
  have hF2 : S.F ⟨0, hn⟩ b (S.ring.dual b) ⟨0, hn⟩ b ⟨0, hn⟩ = 1 := by
    have h := S.F_unit_left hn b (S.ring.dual b) ⟨0, hn⟩ ⟨0, hn⟩ (pos_dual_coeff S hn b)
    simpa using h
  have hFi1 : S.Finv ⟨0, hn⟩ ⟨0, hn⟩ b b b ⟨0, hn⟩ = 1 := by
    have hFuu : S.F ⟨0, hn⟩ ⟨0, hn⟩ b b ⟨0, hn⟩ b = 1 := by
      have h := S.F_unit_left hn ⟨0, hn⟩ b b b (pos_left_unit S hn b)
      simpa using h
    have h := finv_mul_F_of_unique' S (a := ⟨0, hn⟩) (b := ⟨0, hn⟩) (c := b) (d := b)
      (e := ⟨0, hn⟩) (f := b) (unique_left_unit S hn b) (pos_left_unit S hn ⟨0, hn⟩)
      (pos_left_unit S hn b) (pos_left_unit S hn b) (pos_left_unit S hn b)
    rw [hFuu, mul_one] at h
    exact h
  have hFi2 : S.Finv b (S.ring.dual b) ⟨0, hn⟩ ⟨0, hn⟩ (S.ring.dual b) ⟨0, hn⟩ = 1 := by
    have hFbb : S.F b (S.ring.dual b) ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ (S.ring.dual b) = 1 := by
      have h := S.F_unit_right hn b (S.ring.dual b) ⟨0, hn⟩ ⟨0, hn⟩ (pos_dual_coeff S hn b)
      simpa using h
    have h := finv_mul_F_of_unique' S (a := b) (b := S.ring.dual b) (c := ⟨0, hn⟩)
      (d := ⟨0, hn⟩) (e := ⟨0, hn⟩) (f := S.ring.dual b)
      (unique_right_unit S hn (S.ring.dual b)) (pos_dual_coeff S hn b)
      (pos_left_unit S hn ⟨0, hn⟩) (pos_right_unit S hn (S.ring.dual b)) (pos_dual_coeff S hn b)
    rw [hFbb, mul_one] at h
    exact h
  unfold derivedJGen comparisonScalar
  rw [dif_pos hn, dif_pos hn]
  simp only [S.ring.dual_zero hn, FusionRing.dual_dual, hF1, hF2, hFi1, hFi2, S.ev_dual b]
  have hb : S.ev b ≠ 0 := S.ev_ne_zero b
  have hu : S.ev ⟨0, hn⟩ ≠ 0 := S.ev_ne_zero _
  field_simp
  try ring

/-- `J i 1 i = 1`: the right unit law `FusionSystem.J_unit_right`. -/
theorem derivedJGen_unit_right (S : FusionSystem n k) (hn : 0 < n) (a : Fin n) :
    derivedJGen S a ⟨0, hn⟩ a = 1 := by
  have hF1 : S.F ⟨0, hn⟩ (S.ring.dual a) a ⟨0, hn⟩ (S.ring.dual a) ⟨0, hn⟩ = 1 := by
    have h := S.F_unit_left hn (S.ring.dual a) a ⟨0, hn⟩ ⟨0, hn⟩ (pos_dual_coeff' S hn a)
    simpa using h
  have hF2 : S.F a ⟨0, hn⟩ (S.ring.dual a) ⟨0, hn⟩ a (S.ring.dual a) = 1 :=
    TriangleCheck.triangle S hn a (S.ring.dual a) ⟨0, hn⟩ (pos_dual_coeff S hn a)
  have hFi1 : S.Finv (S.ring.dual a) a ⟨0, hn⟩ ⟨0, hn⟩ a ⟨0, hn⟩ = 1 := by
    have hFu : S.F (S.ring.dual a) a ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ a = 1 := by
      have h := S.F_unit_right hn (S.ring.dual a) a ⟨0, hn⟩ ⟨0, hn⟩ (pos_dual_coeff' S hn a)
      simpa using h
    have h := finv_mul_F_of_unique' S (a := S.ring.dual a) (b := a) (c := ⟨0, hn⟩)
      (d := ⟨0, hn⟩) (e := ⟨0, hn⟩) (f := a) (unique_right_unit S hn a) (pos_dual_coeff' S hn a)
      (pos_left_unit S hn ⟨0, hn⟩) (pos_right_unit S hn a) (pos_dual_coeff' S hn a)
    rw [hFu, mul_one] at h
    exact h
  have hFi2 : S.Finv ⟨0, hn⟩ ⟨0, hn⟩ (S.ring.dual a) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ = 1 := by
    have hFuu : S.F ⟨0, hn⟩ ⟨0, hn⟩ (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual a) = 1 := by
      have h := S.F_unit_left hn ⟨0, hn⟩ (S.ring.dual a) (S.ring.dual a) (S.ring.dual a)
        (pos_left_unit S hn (S.ring.dual a))
      simpa using h
    have h := finv_mul_F_of_unique' S (a := ⟨0, hn⟩) (b := ⟨0, hn⟩) (c := S.ring.dual a)
      (d := S.ring.dual a) (e := ⟨0, hn⟩) (f := S.ring.dual a)
      (unique_left_unit S hn (S.ring.dual a)) (pos_left_unit S hn ⟨0, hn⟩)
      (pos_left_unit S hn (S.ring.dual a)) (pos_left_unit S hn (S.ring.dual a))
      (pos_left_unit S hn (S.ring.dual a))
    rw [hFuu, mul_one] at h
    exact h
  unfold derivedJGen comparisonScalar
  rw [dif_pos hn, dif_pos hn]
  simp only [S.ring.dual_zero hn, FusionRing.dual_dual, hF1, hF2, hFi1, hFi2, S.ev_dual a]
  have ha : S.ev a ≠ 0 := S.ev_ne_zero a
  have hu : S.ev ⟨0, hn⟩ ≠ 0 := S.ev_ne_zero _
  field_simp
  try ring

/-- `J i i* 1 = 1`: the duality normalisation `FusionSystem.J_dual`. -/
theorem derivedJGen_dual (S : FusionSystem n k) (hn : 0 < n) (i : Fin n) :
    derivedJGen S i (S.ring.dual i) ⟨0, hn⟩ = 1 := by
  have hF : S.F i (S.ring.dual i) ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ (S.ring.dual i) = 1 := by
    have h := S.F_unit_right hn i (S.ring.dual i) ⟨0, hn⟩ ⟨0, hn⟩ (pos_dual_coeff S hn i)
    simpa using h
  have hFi : S.Finv (S.ring.dual i) i (S.ring.dual i) (S.ring.dual i) ⟨0, hn⟩ ⟨0, hn⟩
      = (S.kappa i)⁻¹ := by
    have h : S.kappa i * S.Finv (S.ring.dual i) i (S.ring.dual i) (S.ring.dual i)
        ⟨0, hn⟩ ⟨0, hn⟩ = 1 := S.snake_right hn i
    exact eq_inv_of_mul_eq_one_right h
  unfold derivedJGen comparisonScalar
  rw [dif_pos hn, dif_pos hn]
  simp only [S.ring.dual_zero hn, FusionRing.dual_dual, hF, hFi]
  have hk : S.kappa i ≠ 0 := S.kappa_ne_zero i
  have hev : S.ev ⟨0, hn⟩ ≠ 0 := S.ev_ne_zero _
  have hevi : S.ev i ≠ 0 := S.ev_ne_zero i
  have hevdi : S.ev (S.ring.dual i) ≠ 0 := S.ev_ne_zero _
  field_simp
  try ring

/-! ## §4 — `derivedJ` does not see the carried field `S.J`

The derived twist is a function of `(ring, F, Finv, ev, coev)` only.  Replacing the
carried twist by any other admissible table leaves it unchanged: this is the kernel
form of "`derivedJ` is never identified with `S.J`". -/

/-- **The datum with its carried twist replaced.**  Only the `J`-fields change. -/
def withJ (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f) :
    FusionSystem n k where
  ring := S.ring
  mult_free := S.mult_free
  F := S.F
  F_support := S.F_support
  pentagon := S.pentagon
  F_unit_left := S.F_unit_left
  F_unit_right := S.F_unit_right
  Finv := S.Finv
  Finv_support := S.Finv_support
  Finv_comp := S.Finv_comp
  F_comp_inv := S.F_comp_inv
  ev := S.ev
  coev := S.coev
  ev_ne_zero := S.ev_ne_zero
  coev_ne_zero := S.coev_ne_zero
  snake_left := S.snake_left
  snake_right := S.snake_right
  ev_dual := S.ev_dual
  J := J
  J_ne_zero := hne
  J_unit_left := h1
  J_unit_right := h2
  J_dual := h3
  J_coherent := h4

/-- **`derivedJ` is blind to `S.J`**: replacing the carried twist leaves the derived
twist untouched (`rfl`: the definition never mentions `S.J`). -/
theorem derivedJGen_withJ (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f)
    (a b c : Fin n) :
    derivedJGen (withJ S J hne h1 h2 h3 h4) a b c = derivedJGen S a b c := rfl

/-- The same for `derivedJ` itself (B4's frozen type at `ℂ`). -/
theorem derivedJ_withJ {n : ℕ} (S : FusionSystem n ℂ) (J : Fin n → Fin n → Fin n → ℂ)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f)
    (a b c : Fin n) :
    derivedJ (withJ S J hne h1 h2 h3 h4) a b c = derivedJ S a b c := rfl

/-! ## §5 — the ℂ-level twist laws and the frozen interface -/

/-- The derived twist's left unit law at B4's frozen type. -/
theorem derivedJ_unit_left {n : ℕ} (S : FusionSystem n ℂ) (hn : 0 < n) (b : Fin n) :
    derivedJ S ⟨0, hn⟩ b b = 1 :=
  derivedJGen_unit_left S hn b

/-- The derived twist's right unit law at B4's frozen type. -/
theorem derivedJ_unit_right {n : ℕ} (S : FusionSystem n ℂ) (hn : 0 < n) (a : Fin n) :
    derivedJ S a ⟨0, hn⟩ a = 1 :=
  derivedJGen_unit_right S hn a

/-- The derived twist's duality normalisation at B4's frozen type. -/
theorem derivedJ_dual {n : ℕ} (S : FusionSystem n ℂ) (hn : 0 < n) (i : Fin n) :
    derivedJ S i (S.ring.dual i) ⟨0, hn⟩ = 1 :=
  derivedJGen_dual S hn i

/-- **The frozen gauge invariance of `Statements2` is a theorem for the derived twist**:
`derivedJ` is invariant under the vertex gauge of the corrected signature (whose
parameters are dual-invariant), so `J_match S (derivedJ S)` is a property of the datum
and not of the chosen evaluations.  With `WP2.j_match_gauge_iff` this makes the
qualification gauge-invariant. -/
theorem WP2_DerivedJ_gauge_invariant :
    WP2.DerivedJ_gauge_invariant (fun {n : ℕ} (S : FusionSystem n ℂ) => derivedJGen S) :=
  fun {n} S lam hlam a b c _ => derivedJGen_gauge S lam hlam a b c

/-! ### The frozen type checks of `Statements2` §4 -/

example {n : ℕ} (S : FusionSystem n ℂ) : Prop :=
  WP2.J_match_at_derivedJ (fun {m : ℕ} (S : FusionSystem m ℂ) => derivedJGen S) S

example {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData) : Prop :=
  WP2.ENO823ExactC_at_derivedJ (fun {m : ℕ} (S : FusionSystem m ℂ) => derivedJGen S) S hFP

example {n : ℕ} (S : FusionSystem n ℂ) : Prop := J_match S (derivedJ S)

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.finv_mul_F_of_unique
#print axioms FusionCategory.finv_mul_F_of_unique'
#print axioms FusionCategory.unique_right_unit
#print axioms FusionCategory.unique_left_unit
#print axioms FusionCategory.pos_dual_coeff
#print axioms FusionCategory.pos_dual_coeff'
#print axioms FusionCategory.pos_right_unit
#print axioms FusionCategory.pos_left_unit
#print axioms FusionCategory.derivedJGen_unit_left
#print axioms FusionCategory.derivedJGen_unit_right
#print axioms FusionCategory.derivedJGen_dual
#print axioms FusionCategory.derivedJ_unit_left
#print axioms FusionCategory.derivedJ_unit_right
#print axioms FusionCategory.derivedJ_dual
#print axioms FusionCategory.withJ
#print axioms FusionCategory.derivedJGen_withJ
#print axioms FusionCategory.derivedJ_withJ
#print axioms FusionCategory.WP2_DerivedJ_gauge_invariant
