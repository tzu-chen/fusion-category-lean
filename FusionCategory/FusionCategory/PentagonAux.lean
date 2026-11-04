/-
WP2 round 3, member m3, direction D3: the pentagon of the reconstruction.

Auxiliary toolkit:
* `assocMatch` / `assocEntry_eq_F_of` / `assocEntry_eq_zero_of_not` — the associator
  entry as a match test with the `F`-symbol on the matching branch.  The block
  comparisons are equalities *after transport* along the label equalities the
  entry forces (this is the shape of the `dif`-ladder of `assocEntry`, and it is
  the shape from which the leaf data of the pentagon can be extracted);
* the projection lemmas `cast_blk_fst`/`cast_blk_x`/`cast_blk_y` recording that
  transporting a block along a *label* equality only changes its channel;
* support extraction from a non-zero `F`;
* the four-leaf data `Quad` of the pentagon, with `qlo`/`qhi`;
* the index-flattening lemmas `flatBlk`/`flatNest`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconAssembly
import FusionCategory.ReconAssocIso

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## 1. Support extraction -/

/-- A non-zero `F`-entry forces all four channels to be present. -/
theorem F_ne_zero_supp (S : FusionSystem n k) {a b c d e f : Fin n}
    (h : S.F a b c d e f ≠ 0) :
    0 < S.ring.N a b e ∧ 0 < S.ring.N e c d ∧ 0 < S.ring.N b c f ∧ 0 < S.ring.N a f d := by
  by_contra hc
  exact h (S.F_support a b c d e f hc)

/-- Multiplicity-freeness: a present channel has multiplicity one. -/
theorem N_eq_one (S : FusionSystem n k) {a b c : Fin n} (h : 0 < S.ring.N a b c) :
    S.ring.N a b c = 1 :=
  le_antisymm (S.mult_free a b c) h

/-! ## 2. Projections of a transported block

The block type of `P ⊗ Q` at `L` is `Σ (p : Fin n × Fin n), Fin (N p.1 p.2 L) × P.blk p.1 × Q.blk p.2`.
Transporting along an equality of the *label* `L` changes only the channel
component; the label pair and the two multiplicity indices are untouched. -/

theorem cast_blk_fst (S : FusionSystem n k) (P Q : FusionMat n k) {g g₁ : Fin n}
    (h : g = g₁) (s : (tensorObj S P Q).blk g₁) : (h ▸ s).1 = s.1 := by
  subst h
  rfl

theorem cast_blk_x (S : FusionSystem n k) (P Q : FusionMat n k) {g g₁ : Fin n}
    (h : g = g₁) (s : (tensorObj S P Q).blk g₁) : HEq ((h ▸ s).2.2.1) s.2.2.1 := by
  subst h
  exact HEq.rfl

theorem cast_blk_y (S : FusionSystem n k) (P Q : FusionMat n k) {g g₁ : Fin n}
    (h : g = g₁) (s : (tensorObj S P Q).blk g₁) : HEq ((h ▸ s).2.2.2) s.2.2.2 := by
  subst h
  exact HEq.rfl

/-! ## 3. The `if`-form of the associator entry -/

section AssocMatch

variable (S : FusionSystem n k) (X Y Z : FusionMat n k) (d : Fin n)

/-- The six conditions under which the associator entry at `(r, q)` is the
`F`-symbol `S.F (label X) (label Y) (label Z) d (label X⊗Y) (label Y⊗Z)`.
The block comparisons are equalities after transport along the label
equalities, exactly as in the `dif`-ladder of `assocEntry`. -/
def assocMatch (r : blkL S X Y Z d) (q : blkR S X Y Z d) : Prop :=
  ∃ (h1 : r.2.2.1.1.1 = q.1.1) (h2 : r.2.2.1.1.2 = q.2.2.2.1.1)
    (h3 : r.1.2 = q.2.2.2.1.2),
    r.2.2.1.2.2.1 = h1 ▸ q.2.2.1 ∧
    r.2.2.1.2.2.2 = h2 ▸ q.2.2.2.2.2.1 ∧
    r.2.2.2 = h3 ▸ q.2.2.2.2.2.2

/-- **The associator entry at a matching pair** is the `F`-symbol, with the
labels read off the row. -/
theorem assocEntry_eq_F_of (r : blkL S X Y Z d) (q : blkR S X Y Z d)
    (h : assocMatch S X Y Z d r q) :
    assocEntry S X Y Z d r q = S.F r.2.2.1.1.1 r.2.2.1.1.2 r.1.2 d r.1.1 q.1.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [assocEntry]
  rw [dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4, dif_pos h5, dif_pos h6]

/-- **The associator entry vanishes off a non-matching pair.** -/
theorem assocEntry_eq_zero_of_not (r : blkL S X Y Z d) (q : blkR S X Y Z d)
    (h : ¬ assocMatch S X Y Z d r q) : assocEntry S X Y Z d r q = 0 := by
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · by_cases h3 : r.1.2 = q.2.2.2.1.2
      · by_cases h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1)
        · by_cases h5 : r.2.2.1.2.2.2 = (h2 ▸ q.2.2.2.2.2.1)
          · by_cases h6 : r.2.2.2 = (h3 ▸ q.2.2.2.2.2.2)
            · exact absurd ⟨h1, h2, h3, h4, h5, h6⟩ h
            · simp only [assocEntry, dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4,
                dif_pos h5, dif_neg h6]
          · simp only [assocEntry, dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4, dif_neg h5]
        · simp only [assocEntry, dif_pos h1, dif_pos h2, dif_pos h3, dif_neg h4]
      · simp only [assocEntry, dif_pos h1, dif_pos h2, dif_neg h3]
    · simp only [assocEntry, dif_pos h1, dif_neg h2]
  · simp only [assocEntry, dif_neg h1]

end AssocMatch

/-! ## 4. Sum helpers -/

/-- A sum of a constant over `Fin m` is the `nsmul`. -/
theorem sum_fin_const_nsmul {M : Type*} [AddCommMonoid M] (m : ℕ) (x : M) :
    (∑ _ : Fin m, x) = m • x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-! ## 5. Flattening the block indices -/

theorem flatBlk (S : FusionSystem n k) (P Q : FusionMat n k) (d : Fin n)
    (f : (tensorObj S P Q).blk d → k) :
    (∑ m, f m) = ∑ (p : Fin n × Fin n), ∑ (ν : Fin (S.ring.N p.1 p.2 d)),
      ∑ (w : P.blk p.1), ∑ (t : Q.blk p.2), f ⟨p, ν, w, t⟩ := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

theorem flatNest (S : FusionSystem n k) (P Q : FusionMat n k) (g : Fin n)
    (G : (tensorObj S P Q).blk g → k) :
    (∑ w, G w) = ∑ (r : Fin n × Fin n), ∑ (l : Fin (S.ring.N r.1 r.2 g)),
      ∑ (x : P.blk r.1), ∑ (y : Q.blk r.2), G ⟨r, l, x, y⟩ := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

/-! ## 6. The four-leaf data of the pentagon -/

section Quad

variable (A B C D : FusionMat n k)

/-- Fully refined leaf data of the four factors. -/
abbrev Quad : Type :=
  (Σ a, A.blk a) × (Σ b, B.blk b) × (Σ c, C.blk c) × (Σ w, D.blk w)

/-- The four leaves of a source index `((A⊗B)⊗C)⊗D` of the pentagon. -/
def qlo (S : FusionSystem n k) (d : Fin n)
    (p : (tensorObj S (tensorObj S (tensorObj S A B) C) D).blk d) : Quad A B C D :=
  (⟨p.2.2.1.2.2.1.1.1, p.2.2.1.2.2.1.2.2.1⟩, ⟨p.2.2.1.2.2.1.1.2, p.2.2.1.2.2.1.2.2.2⟩,
   ⟨p.2.2.1.1.2, p.2.2.1.2.2.2⟩, ⟨p.1.2, p.2.2.2⟩)

/-- The four leaves of a target index `A⊗(B⊗(C⊗D))` of the pentagon. -/
def qhi (S : FusionSystem n k) (d : Fin n)
    (q : (tensorObj S A (tensorObj S B (tensorObj S C D))).blk d) : Quad A B C D :=
  (⟨q.1.1, q.2.2.1⟩, ⟨q.2.2.2.1.1, q.2.2.2.2.2.1⟩,
   ⟨q.2.2.2.2.2.2.1.1, q.2.2.2.2.2.2.2.2.1⟩,
   ⟨q.2.2.2.2.2.2.1.2, q.2.2.2.2.2.2.2.2.2⟩)

end Quad

/-! ## 7. Tensor entries with an identity factor

`tensorHom_apply` has all four objects implicit, and in the collapses the
elaborator cannot infer them from the *index* types when the indices are
variables; these two specialised forms are stated with the identity factor as an
explicit argument, so that matching them needs only first-order unification. -/

theorem tensorHom_id_left_apply (S : FusionSystem n k) {A Y Y' : FusionMat n k} (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c)) (x : A.blk p.1)
    (y : Y.blk p.2) (ν' : Fin (S.ring.N p.1 p.2 c)) (x' : A.blk p.1) (y' : Y'.blk p.2) :
    tensorHom S (𝟙 A) g c ⟨p, ν, x, y⟩ ⟨p, ν', x', y'⟩
      = (if ν = ν' then 1 else 0) * ((if x = x' then 1 else 0) * g p.2 y y') := by
  rw [tensorHom_apply S (𝟙 A) g c p ν x y ν' x' y']
  show (if ν = ν' then 1 else 0) * ((if x = x' then (1 : k) else 0) * g p.2 y y') = _
  rfl

theorem tensorHom_id_right_apply (S : FusionSystem n k) {X X' D : FusionMat n k} (f : X ⟶ X')
    (c : Fin n) (p : Fin n × Fin n) (ν : Fin (S.ring.N p.1 p.2 c)) (x : X.blk p.1)
    (y : D.blk p.2) (ν' : Fin (S.ring.N p.1 p.2 c)) (x' : X'.blk p.1) (y' : D.blk p.2) :
    tensorHom S f (𝟙 D) c ⟨p, ν, x, y⟩ ⟨p, ν', x', y'⟩
      = (if ν = ν' then 1 else 0) * (f p.1 x x' * (if y = y' then 1 else 0)) := by
  rw [tensorHom_apply S f (𝟙 D) c p ν x y ν' x' y']
  show (if ν = ν' then 1 else 0) * (f p.1 x x' * (if y = y' then (1 : k) else 0)) = _
  rfl

end FusionCategory
