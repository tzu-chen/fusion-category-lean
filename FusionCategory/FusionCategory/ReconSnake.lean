/-
# WP2 round 2, member m6, direction D6 — the snake equations

Entrywise collapse of the two snake composites of `ReconRigid2` onto the
label-level `FusionSystem.snake_left` / `snake_right`.

Conventions (repeated because they cost two debugging rounds):
`FusionHom X Y = ∀ i, Matrix (X.blk i) (Y.blk i)` — rows are the SOURCE.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconRigid
import FusionCategory.ReconTensorApply

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat

variable (S : FusionSystem n k)

/-! ## The canonical unit-channel elements -/

/-- The channel of `c ⊗ 𝟙 ∋ c`. -/
def unitChR (hn : 0 < n) (c : Fin n) : Fin (S.ring.N c ⟨0, hn⟩ c) :=
  ⟨0, by rw [S.ring.right_unit hn c c, if_pos rfl]; exact Nat.one_pos⟩

/-- The channel of `𝟙 ⊗ c ∋ c`. -/
def unitChL (hn : 0 < n) (c : Fin n) : Fin (S.ring.N ⟨0, hn⟩ c c) :=
  ⟨0, by rw [S.ring.left_unit hn c c, if_pos rfl]; exact Nat.one_pos⟩

/-- The unique index of the unit block. -/
def unitBlk (hn : 0 < n) : (unitObj (k := k) hn).blk ⟨0, hn⟩ :=
  ⟨0, by simp [unitObj]⟩

theorem unitBlk_unique (hn : 0 < n) (u : (unitObj (k := k) hn).blk ⟨0, hn⟩) :
    u = unitBlk hn := by
  have hu : u.val < 1 := by simpa [unitObj] using u.isLt
  have hu0 : u.val = 0 := by omega
  exact Fin.ext hu0

/-! ## Decomposing a tensor block into its coordinates -/

/-- A sum over the block of `A ⊗ B` decomposes into the label pair, the
(subsingleton-or-empty) channel, and the two block indices. -/
theorem sum_tensorBlk {M : Type*} [AddCommMonoid M] (A B : FusionMat n k) (c : Fin n)
    (φ : (tensorObj S A B).blk c → M) :
    (∑ r, φ r)
      = ∑ p : Fin n × Fin n, ∑ ν : Fin (S.ring.N p.1 p.2 c),
          ∑ x : A.blk p.1, ∑ y : B.blk p.2, φ ⟨p, ν, x, y⟩ := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [Fintype.sum_prod_type]

theorem tensorHomBlock_apply {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n)
    (ν : Fin (S.ring.N p.1 p.2 c)) (x : X.blk p.1) (y : Y.blk p.2)
    (ν' : Fin (S.ring.N p.1 p.2 c)) (x' : X'.blk p.1) (y' : Y'.blk p.2) :
    tensorHomBlock S f g c p ⟨ν, x, y⟩ ⟨ν', x', y'⟩
      = (if ν = ν' then 1 else 0) * ((f p.1) x x' * (g p.2) y y') := by
  simp only [tensorHomBlock, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `ev` whiskered on the left, with the right unitor absorbed. -/
def absorbedEv (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    Matrix ((tensorObj S X (tensorObj S (dual S X) X)).blk c) (X.blk c) k :=
  tensorHom S (𝟙 X) (ev S hn X) c * rightUnitor S hn X c

theorem absorbedEv_apply_of (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {b : (tensorObj S X (tensorObj S (dual S X) X)).blk c} (h : b.1 = (c, ⟨0, hn⟩))
    (j : X.blk c) :
    absorbedEv S hn X c b j
      = (if (h ▸ b.2).1 = unitChR S hn c then
          (if (h ▸ b.2).2.1 = j then (ev S hn X ⟨0, hn⟩) (h ▸ b.2).2.2 (unitBlk hn) else 0)
        else 0) := by
  obtain ⟨⟨q1, q2⟩, ν, x, y⟩ := b
  simp only at h
  cases h
  dsimp only
  rw [absorbedEv, mul_rightUnitor]
  have hidx : unitIdxR S hn X c j
      = ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, unitBlk hn)⟩ := rfl
  show (tensorHom S (𝟙 X) (ev S hn X) c) ⟨(c, ⟨0, hn⟩), (ν, x, y)⟩
      (unitIdxR S hn X c j) = _
  rw [hidx, tensorHom_apply]
  rw [show ((𝟙 X : X ⟶ X) c) x j = if x = j then 1 else 0 from Matrix.one_apply]
  by_cases hν : ν = unitChR S hn c
  · rw [if_pos hν]
    by_cases hx : x = j
    · rw [if_pos hx, if_pos hν, if_pos hx]; simp
    · rw [if_neg hx, if_pos hν, if_neg hx]; simp
  · rw [if_neg hν, if_neg hν]; simp

theorem absorbedEv_apply_ne (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {b : (tensorObj S X (tensorObj S (dual S X) X)).blk c} (h : b.1 ≠ (c, ⟨0, hn⟩))
    (j : X.blk c) : absorbedEv S hn X c b j = 0 := by
  rw [absorbedEv, mul_rightUnitor]
  show (tensorHom S (𝟙 X) (ev S hn X) c) b (unitIdxR S hn X c j) = 0
  rw [tensorHom, blockDiag]
  have h' : b.1 ≠ (unitIdxR S hn X c j).1 := h
  rw [dif_neg h']

theorem absorbedEv_apply_canon (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N c ⟨0, hn⟩ c)) (x : X.blk c)
    (w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩) (j : X.blk c) :
    absorbedEv S hn X c ⟨(c, ⟨0, hn⟩), (ν, x, w)⟩ j
      = (if ν = unitChR S hn c then
          (if x = j then (ev S hn X ⟨0, hn⟩) w (unitBlk hn) else 0) else 0) := by
  rw [absorbedEv_apply_of (h := rfl)]

/-- **Step 1 of the left snake**: the associator against the absorbed evaluation,
with the middle index of `X ⊗ (X*⊗X)` collapsed onto the canonical one
(`(c,0)`, its unique channel, the `X`-index `j`), leaving only the
`(X*⊗X)`-index `w`. -/
theorem assoc_mul_absorbedEv (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (a : (tensorObj S (tensorObj S X (dual S X)) X).blk c) (j : X.blk c) :
    (associatorHom S X (dual S X) X c * absorbedEv S hn X c) a j
      = ∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
          assocEntry S X (dual S X) X c a ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, w)⟩
            * ((ev S hn X ⟨0, hn⟩) w (unitBlk hn)) := by
  rw [Matrix.mul_apply]
  simp only [associatorHom, Matrix.of_apply]
  rw [sum_tensorBlk S X (tensorObj S (dual S X) X) c
    (fun b => assocEntry S X (dual S X) X c a b * absorbedEv S hn X c b j)]
  rw [Finset.sum_eq_single (c, ⟨0, hn⟩)]
  · rw [Finset.sum_eq_single (unitChR S hn c)]
    · rw [Finset.sum_eq_single j]
      · refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [absorbedEv_apply_canon, if_pos rfl, if_pos rfl]
      · intro x _ hx
        refine Finset.sum_eq_zero (fun w _ => ?_)
        rw [absorbedEv_apply_canon, if_pos rfl, if_neg hx, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ν _ hν
      refine Finset.sum_eq_zero (fun x _ => ?_)
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [absorbedEv_apply_canon, if_neg hν, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero (fun ν _ => ?_)
    refine Finset.sum_eq_zero (fun x _ => ?_)
    refine Finset.sum_eq_zero (fun w _ => ?_)
    have hne : (⟨p, (ν, x, w)⟩ :
        (tensorObj S X (tensorObj S (dual S X) X)).blk c).1 ≠ (c, ⟨0, hn⟩) := by
      simpa using hp
    rw [absorbedEv_apply_ne (h := hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The canonical form of an index of `𝟙 ⊗ X`

Every index of `𝟙 ⊗ X` over `c` has first label `0` (the unit block is `Fin 0`
elsewhere), second label `c` (`left_unit`), and then the only channel and the
only unit index — so it *is* `unitIdxL` of its `X`-index. -/

theorem unitObj_blk_eq (hn : 0 < n) {p : Fin n} (t : (unitObj (k := k) hn).blk p) :
    p = ⟨0, hn⟩ := by
  by_contra h
  have hz : (unitObj (k := k) hn).blk p = Fin 0 := by
    show Fin (if p = ⟨0, hn⟩ then 1 else 0) = Fin 0
    rw [if_neg h]
  rw [hz] at t
  exact Fin.elim0 t

theorem eq_unitIdxL_of (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S (unitObj hn) X).blk c) : ∃ j : X.blk c, r = unitIdxL S hn X c j := by
  obtain ⟨⟨r1, r2⟩, rν, ru, rx⟩ := r
  have hr1 : r1 = ⟨0, hn⟩ := unitObj_blk_eq hn ru
  cases hr1
  have hr2 : r2 = c := unit_label_of_left S hn rν
  cases hr2
  have hν : rν = unitChL S hn c := by
    have hN : S.ring.N ⟨0, hn⟩ c c = 1 := unit_channel_left S hn rν
    apply Fin.ext
    have h1 : rν.val < 1 := by
      have h := rν.isLt
      simpa [hN] using h
    show rν.val = (unitChL S hn c).val
    rw [show (unitChL S hn c).val = 0 from rfl]
    omega
  have hu : ru = unitBlk hn := by
    apply Fin.ext
    have h1 : ru.val < 1 := by
      have h := ru.isLt
      simpa [unitObj] using h
    show ru.val = (unitBlk hn).val
    rw [show (unitBlk hn).val = 0 from rfl]
    omega
  refine ⟨rx, ?_⟩
  show (⟨(⟨0, hn⟩, c), (rν, ru, rx)⟩ : (tensorObj S (unitObj hn) X).blk c) = unitIdxL S hn X c rx
  rw [hν, hu]
  simp [unitIdxL, unitChL, unitBlk]

theorem unitIdxL_injective (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {j j' : X.blk c} (h : unitIdxL S hn X c j = unitIdxL S hn X c j') : j = j' := by
  cases h
  rfl

/-! ## The entry of `coev ⊗ 𝟙` at the canonical index -/

theorem coev_tensor_apply_canon (hn : 0 < n) (X : FusionMat n k) (c : Fin n) (j : X.blk c)
    (ν : Fin (S.ring.N ⟨0, hn⟩ c c))
    (au : (tensorObj S X (dual S X)).blk ⟨0, hn⟩) (az : X.blk c) :
    (tensorHom S (coev S hn X) (𝟙 X) c) (unitIdxL S hn X c j) ⟨(⟨0, hn⟩, c), (ν, au, az)⟩
      = (if unitChL S hn c = ν then
          (if j = az then (coev S hn X ⟨0, hn⟩) (unitBlk hn) au else 0) else 0) := by
  have hidx : unitIdxL S hn X c j
      = ⟨(⟨0, hn⟩, c), (unitChL S hn c, unitBlk hn, j)⟩ := rfl
  rw [hidx, tensorHom_apply]
  rw [show ((𝟙 X : X ⟶ X) c) = (1 : Matrix (X.blk c) (X.blk c) k) from rfl, Matrix.one_apply]
  by_cases h1 : unitChL S hn c = ν <;> by_cases h2 : j = az <;> simp [h1, h2]

theorem coev_tensor_apply_ne (hn : 0 < n) (X : FusionMat n k) (c : Fin n) (j : X.blk c)
    {a : (tensorObj S (tensorObj S X (dual S X)) X).blk c} (h : a.1 ≠ (⟨0, hn⟩, c)) :
    (tensorHom S (coev S hn X) (𝟙 X) c) (unitIdxL S hn X c j) a = 0 := by
  rw [tensorHom]
  have h' : (unitIdxL S hn X c j).1 ≠ a.1 := by
    intro hc
    exact h hc.symm
  rw [blockDiag, dif_neg h']

/-- **Step 2 of the left snake**: the `coev ⊗ 𝟙` against the associator/ev
composite, with the outer index of `(X ⊗ X*) ⊗ X` collapsed onto the canonical
`((0,c), unit channel, j)`, leaving only the `(X ⊗ X*)`-index `au`. -/
theorem coevTensor_assoc_absorbedEv (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j j' : X.blk c) :
    (tensorHom S (coev S hn X) (𝟙 X) c
        * ((associatorHom S X (dual S X) X c) * absorbedEv S hn X c))
        (unitIdxL S hn X c j) j'
      = ∑ au : (tensorObj S X (dual S X)).blk ⟨0, hn⟩,
          ((coev S hn X ⟨0, hn⟩) (unitBlk hn) au)
            * ((associatorHom S X (dual S X) X c) * absorbedEv S hn X c)
                ⟨(⟨0, hn⟩, c), (unitChL S hn c, au, j)⟩ j' := by
  rw [Matrix.mul_apply]
  rw [sum_tensorBlk S (tensorObj S X (dual S X)) X c
    (fun a => (tensorHom S (coev S hn X) (𝟙 X) c) (unitIdxL S hn X c j) a
      * ((associatorHom S X (dual S X) X c) * absorbedEv S hn X c) a j')]
  rw [Finset.sum_eq_single (⟨0, hn⟩, c)]
  · rw [Finset.sum_eq_single (unitChL S hn c)]
    · refine Finset.sum_congr rfl (fun au _ => ?_)
      rw [Finset.sum_eq_single j]
      · rw [coev_tensor_apply_canon, if_pos rfl, if_pos rfl]
      · intro az _ hz
        rw [coev_tensor_apply_canon, if_pos rfl,
          if_neg (fun hc : j = az => hz hc.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ν _ hν
      refine Finset.sum_eq_zero (fun au _ => ?_)
      rw [Finset.sum_eq_zero (fun az _ => by
        rw [coev_tensor_apply_canon, if_neg (fun hc : unitChL S hn c = ν => hν hc.symm),
          zero_mul])]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero (fun ν _ => ?_)
    refine Finset.sum_eq_zero (fun au _ => ?_)
    refine Finset.sum_eq_zero (fun az _ => ?_)
    have hne : (⟨p, (ν, au, az)⟩ :
        (tensorObj S (tensorObj S X (dual S X)) X).blk c).1 ≠ (⟨0, hn⟩, c) := by
      simpa using hp
    rw [coev_tensor_apply_ne (h := hne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The unitors are isomorphisms

The inverse of the (delta-form) unitor is its transpose, and `eq_unitIdxL_of`
identifies the indices so the two inverse laws are single-sum collapses. -/

/-- The transpose of the left unitor: `X ⟶ 𝟙 ⊗ X`. -/
def leftUnitorInv (hn : 0 < n) (X : FusionMat n k) :
    X ⟶ tensorObj S (unitObj hn) X :=
  fun c => Matrix.of fun j r => if r = unitIdxL S hn X c j then 1 else 0

/-- The transpose of the right unitor: `X ⟶ X ⊗ 𝟙`. -/
def rightUnitorInv (hn : 0 < n) (X : FusionMat n k) :
    X ⟶ tensorObj S X (unitObj hn) :=
  fun c => Matrix.of fun j r => if r = unitIdxR S hn X c j then 1 else 0

theorem eq_unitIdxR_of (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (r : (tensorObj S X (unitObj hn)).blk c) : ∃ j : X.blk c, r = unitIdxR S hn X c j := by
  obtain ⟨⟨r1, r2⟩, rν, rx, ru⟩ := r
  have hr2 : r2 = ⟨0, hn⟩ := unitObj_blk_eq hn ru
  cases hr2
  have hr1 : r1 = c := unit_label_of_right S hn rν
  cases hr1
  have hν : rν = unitChR S hn c := by
    have hN : S.ring.N c ⟨0, hn⟩ c = 1 := unit_channel_right S hn rν
    apply Fin.ext
    have h1 : rν.val < 1 := by
      have h := rν.isLt
      simpa [hN] using h
    show rν.val = (unitChR S hn c).val
    rw [show (unitChR S hn c).val = 0 from rfl]
    omega
  have hu : ru = unitBlk hn := by
    apply Fin.ext
    have h1 : ru.val < 1 := by
      have h := ru.isLt
      simpa [unitObj] using h
    show ru.val = (unitBlk hn).val
    rw [show (unitBlk hn).val = 0 from rfl]
    omega
  refine ⟨rx, ?_⟩
  show (⟨(c, ⟨0, hn⟩), (rν, rx, ru)⟩ : (tensorObj S X (unitObj hn)).blk c)
      = unitIdxR S hn X c rx
  rw [hν, hu]
  simp [unitIdxR, unitChR, unitBlk]

theorem leftUnitor_comp_inv (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    leftUnitor S hn X c * leftUnitorInv S hn X c = 1 := by
  ext r r'
  obtain ⟨rx, rfl⟩ := eq_unitIdxL_of (S := S) hn X c r
  rw [Matrix.mul_apply, Finset.sum_eq_single rx]
  · rw [leftUnitor_eq, if_pos rfl, leftUnitorInv, Matrix.of_apply, one_mul]
    by_cases h : r' = unitIdxL S hn X c rx
    · rw [if_pos h]; simp [Matrix.one_apply, h]
    · rw [if_neg h]; simp [Matrix.one_apply, h, eq_comm]
  · intro j _ hj
    rw [leftUnitor_eq, leftUnitorInv, Matrix.of_apply,
      if_neg (fun hc => hj (by cases hc; rfl))]
    simp
  · simp

theorem leftUnitor_inv_comp (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    leftUnitorInv S hn X c * leftUnitor S hn X c = 1 := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (unitIdxL S hn X c j)]
  · rw [leftUnitorInv, Matrix.of_apply, if_pos rfl, leftUnitor_eq, one_mul]
    by_cases h : j = j'
    · rw [if_pos (by rw [h])]; simp [Matrix.one_apply, h]
    · rw [if_neg (fun hc => h (unitIdxL_injective (S := S) hn X c hc))]
      simp [Matrix.one_apply, h]
  · intro r _ hr
    rw [leftUnitorInv, Matrix.of_apply, if_neg hr]
    simp
  · simp

theorem rightUnitor_comp_inv (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    rightUnitor S hn X c * rightUnitorInv S hn X c = 1 := by
  ext r r'
  obtain ⟨rx, rfl⟩ := eq_unitIdxR_of (S := S) hn X c r
  rw [Matrix.mul_apply, Finset.sum_eq_single rx]
  · rw [rightUnitor_eq, if_pos rfl, rightUnitorInv, Matrix.of_apply, one_mul]
    by_cases h : r' = unitIdxR S hn X c rx
    · rw [if_pos h]; simp [Matrix.one_apply, h]
    · rw [if_neg h]; simp [Matrix.one_apply, h, eq_comm]
  · intro j _ hj
    rw [rightUnitor_eq, rightUnitorInv, Matrix.of_apply,
      if_neg (fun hc => hj (by cases hc; rfl))]
    simp
  · simp

theorem rightUnitor_inv_comp (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    rightUnitorInv S hn X c * rightUnitor S hn X c = 1 := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (unitIdxR S hn X c j)]
  · rw [rightUnitorInv, Matrix.of_apply, if_pos rfl, rightUnitor_eq, one_mul]
    by_cases h : j = j'
    · rw [if_pos (by rw [h])]; simp [Matrix.one_apply, h]
    · rw [if_neg (fun hc => h (by cases hc; rfl))]
      simp [Matrix.one_apply, h]
  · intro r _ hr
    rw [rightUnitorInv, Matrix.of_apply, if_neg hr]
    simp
  · simp

/-- The left unitor as an isomorphism `𝟙 ⊗ X ≅ X`. -/
def leftUnitorIso (hn : 0 < n) (X : FusionMat n k) : tensorObj S (unitObj hn) X ≅ X where
  hom := leftUnitor S hn X
  inv := leftUnitorInv S hn X
  hom_inv_id := by
    funext c; exact leftUnitor_comp_inv S hn X c
  inv_hom_id := by
    funext c; exact leftUnitor_inv_comp S hn X c

/-- The right unitor as an isomorphism `X ⊗ 𝟙 ≅ X`. -/
def rightUnitorIso (hn : 0 < n) (X : FusionMat n k) : tensorObj S X (unitObj hn) ≅ X where
  hom := rightUnitor S hn X
  inv := rightUnitorInv S hn X
  hom_inv_id := by
    funext c; exact rightUnitor_comp_inv S hn X c
  inv_hom_id := by
    funext c; exact rightUnitor_inv_comp S hn X c


/-! ## The snake in iso form (the literature form) -/

/-- **The left snake, iso form**: `λ⁻¹ ≫ (coev ⊗ 1) ≫ α ≫ (1 ⊗ ev) ≫ ρ = 𝟙`,
the honest snake equation of the dual pair `(X, X*)` with the unitors as
isomorphisms. -/
def SnakeLeftIso : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    (leftUnitorIso S hn X).inv ≫ whiskerRight S (coev S hn X) X
        ≫ associatorHom S X (dual S X) X ≫ whiskerLeft S X (ev S hn X)
        ≫ (rightUnitorIso S hn X).hom = 𝟙 X

theorem snakeLeft_iff_iso : SnakeLeft S ↔ SnakeLeftIso S := by
  constructor
  · intro h hn X
    have hS := h hn X
    show (leftUnitorIso S hn X).inv ≫ _ = 𝟙 X
    rw [leftUnitorIso, rightUnitorIso]
    simp only
    rw [hS]
    exact Iso.inv_hom_id (leftUnitorIso S hn X)
  · intro h hn X
    have hS := h hn X
    rw [leftUnitorIso, rightUnitorIso] at hS
    simp only at hS
    have h2 := congrArg (fun t => leftUnitor S hn X ≫ t) hS
    simp only [Category.assoc, Category.comp_id] at h2
    rw [← Category.assoc, show leftUnitor S hn X ≫ leftUnitorInv S hn X = 𝟙 _ from
      Iso.hom_inv_id (leftUnitorIso S hn X), Category.id_comp] at h2
    exact h2

end FusionMat

end FusionCategory

open FusionCategory in
#print axioms FusionCategory.FusionMat.sum_tensorBlk
open FusionCategory in
#print axioms FusionCategory.FusionMat.absorbedEv_apply_canon
open FusionCategory in
#print axioms FusionCategory.FusionMat.assoc_mul_absorbedEv
open FusionCategory in
#print axioms FusionCategory.FusionMat.eq_unitIdxL_of
open FusionCategory in
#print axioms FusionCategory.FusionMat.eq_unitIdxR_of
open FusionCategory in
#print axioms FusionCategory.FusionMat.coev_tensor_apply_canon
open FusionCategory in
#print axioms FusionCategory.FusionMat.coevTensor_assoc_absorbedEv
open FusionCategory in
#print axioms FusionCategory.FusionMat.leftUnitor_comp_inv
open FusionCategory in
#print axioms FusionCategory.FusionMat.leftUnitor_inv_comp
open FusionCategory in
#print axioms FusionCategory.FusionMat.rightUnitor_comp_inv
open FusionCategory in
#print axioms FusionCategory.FusionMat.rightUnitor_inv_comp
open FusionCategory in
#print axioms FusionCategory.FusionMat.leftUnitorIso
open FusionCategory in
#print axioms FusionCategory.FusionMat.rightUnitorIso
open FusionCategory in
#print axioms FusionCategory.FusionMat.SnakeLeftIso
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeLeft_iff_iso
