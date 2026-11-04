/-
WP2 round 3, member m6, direction D2: **`AssociatorNatural`** — the first of the two
monoidal proofs, and the last thing (with D3's pentagon) between the scaffold and a
`MonoidalCategory` instance.

The frozen statement (`ReconAssocStatements.AssociatorNatural`) is

    tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z'
      = associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)

at every block `d` and every index pair `r : (X⊗Y)⊗Z` / `q : X'⊗(Y'⊗Z)`.  The two sides
sum over *different* index types (`blkL S X' Y' Z' d` on the left, `blkR S X Y Z d` on the
right), which is why the entrywise reduction cannot be a single reindexing: the multiplicity
kills are ill-typed before the label case split.

The route taken here (no reindex, no `Equiv`):

1. **The double-tensor entry formula.**  `tensorHom_blockDiag_apply` gives the entry of
   `tensorHom S F h` at a *matched* outer label, and `tensorHomBlock_apply` the entry of a
   single block; together (`tensorHom_tensorHom_apply`) the entry of `tensorHom (tensorHom f g) h`
   at a doubly refined index pair is the plain scalar
   `(if ν = ν' then 1 else 0) * ((if μ = μ' then 1 else 0) * (f·g·h))`.  The `if`s are the
   channel identities; because `Fin (N a b c)` is a subsingleton they are the *only* channel
   bookkeeping, and no `nsmul` trick is needed anywhere in this file.
2. **Compose with the associator by `blockDiag_mul_apply` / `mul_blockDiag_apply`** (the
   block-diagonal composition lemmas of `Recon`).  On the left this fixes the middle index's
   outer label to the row's, on the right to the column's, and each channel sum is then killed
   by the identity `if`.  What remains is a three-fold sum over the multiplicity indices
   (`lhs_sum_eq`, `rhs_sum_eq`).
3. **Kill the multiplicities** with `assocEntry_zero_x/_y/_z` (and `_x_gen` for the middle
   index of the right side, whose `b,c` labels are still free at that point), and evaluate the
   survivor with `assocEntry_exact`.
4. The label mismatches are `lhs_eq_zero` / `rhs_eq_zero`; the matched case is
   `lhs_eq_matched` / `rhs_eq_matched`.  Both matched values are
   `f a x x' · g b y y' · h c z z' · F a b c d e f'` (up to one associativity of `*`), so the
   square commutes.

Consequences: `associatorNatural : AssociatorNatural S` is proved, and
`monoidalCategoryOfPentagon` builds the `MonoidalCategory` from **`PentagonShapeHom S`
alone** (`associatorIso` and `associatorNatural` are theorems now).

Axiom budget of every declaration: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconAssocIso
import FusionCategory.ReconAssembly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option warn.classDefReducibility false

universe u

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- The entry of `tensorHomBlock` at matched labels: the channel acts as an
identity and the block is the Kronecker product of the two blocks. -/
theorem tensorHomBlock_apply {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n)
    (ν : Fin (S.ring.N p.1 p.2 c)) (x : X.blk p.1) (y : Y.blk p.2)
    (ν' : Fin (S.ring.N p.1 p.2 c)) (x' : X'.blk p.1) (y' : Y'.blk p.2) :
    tensorHomBlock S f g c p ⟨ν, x, y⟩ ⟨ν', x', y'⟩
      = (if ν = ν' then 1 else 0) * (f p.1 x x' * g p.2 y y') := by
  simp [tensorHomBlock, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The entry of a tensor with a general left factor, at matched outer labels. -/
theorem tensorHom_blockDiag_apply {A A' Y Y' : FusionMat n k}
    (F : A ⟶ A') (h : Y ⟶ Y') (d : Fin n) (p : Fin n × Fin n)
    (ν : Fin (S.ring.N p.1 p.2 d)) (u : A.blk p.1) (z : Y.blk p.2)
    (ν' : Fin (S.ring.N p.1 p.2 d)) (u' : A'.blk p.1) (z' : Y'.blk p.2) :
    tensorHom S F h d ⟨p, ν, u, z⟩ ⟨p, ν', u', z'⟩
      = (if ν = ν' then 1 else 0) * (F p.1 u u' * h p.2 z z') := by
  rw [tensorHom, blockDiag_mk]
  simp [tensorHomBlock, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The entry of a tensor with a general left factor, at differing outer labels. -/
theorem tensorHom_blockDiag_apply_ne {A A' Y Y' : FusionMat n k}
    (F : A ⟶ A') (h : Y ⟶ Y') (d : Fin n) {p p' : Fin n × Fin n} (hp : p ≠ p')
    (ν : Fin (S.ring.N p.1 p.2 d)) (u : A.blk p.1) (z : Y.blk p.2)
    (ν' : Fin (S.ring.N p'.1 p'.2 d)) (u' : A'.blk p'.1) (z' : Y'.blk p'.2) :
    tensorHom S F h d ⟨p, ν, u, z⟩ ⟨p', ν', u', z'⟩ = 0 := by
  rw [tensorHom]
  simp only [blockDiag, dif_neg hp]

/-- The entry of a double-tensored morphism at matched (doubly refined) labels. -/
theorem tensorHom_tensorHom_apply {X X' Y Y' Z Z' : FusionMat n k}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n) (e c : Fin n)
    (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (ν' : Fin (S.ring.N e c d)) (μ' : Fin (S.ring.N a b e))
    (x' : X'.blk a) (y' : Y'.blk b) (z' : Z'.blk c) :
    tensorHom S (tensorHom S f g) h d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩
      = (if ν = ν' then 1 else 0) *
          ((if μ = μ' then 1 else 0) * (f a x x' * g b y y' * h c z z')) := by
  rw [tensorHom_blockDiag_apply S (tensorHom S f g) h d (e, c) ν ⟨⟨a, b⟩, ⟨μ, x, y⟩⟩ z
    ν' ⟨⟨a, b⟩, ⟨μ', x', y'⟩⟩ z']
  rw [tensorHom_apply S f g e (a, b) μ x y μ' x' y']
  ring

end FusionCategory

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

section LHS

variable {X X' Y Y' Z Z' : FusionMat n k}

/-- **The left side of the naturality square, reduced.** -/
theorem lhs_sum_eq (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (q : (tensorObj S X' (tensorObj S Y' Z')).blk d) :
    (tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z') d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ q
      = ∑ x₂ : X'.blk a, ∑ y₂ : Y'.blk b, ∑ z₂ : Z'.blk c,
          (f a x x₂ * g b y y₂ * h c z z₂) *
            assocEntry S X' Y' Z' d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x₂, y₂⟩⟩, z₂⟩⟩⟩ q := by
  rw [show (tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z') d
      = blockDiag (fun p : Fin n × Fin n => tensorHomBlock S (tensorHom S f g) h d p)
        * Matrix.of (assocEntry S X' Y' Z' d) from rfl]
  rw [blockDiag_mul_apply]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single ν ?_ ?_).trans ?_
  · -- the channel of the middle index is forced
    intro ν₂ _ hν₂
    have hz : ∀ (a₂ : Fin n) (b₂ : Fin n) (μ₂ : Fin (S.ring.N a₂ b₂ e))
        (x₂ : X'.blk a₂) (y₂ : Y'.blk b₂) (z₂ : Z'.blk c),
        (tensorHomBlock S (tensorHom S f g) h d (e, c) (ν, ⟨(a, b), (μ, x, y)⟩, z)
            (ν₂, ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩, z₂) *
          Matrix.of (assocEntry S X' Y' Z' d)
            ⟨(e, c), (ν₂, ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩, z₂)⟩ q) = 0 := by
      intro a₂ b₂ μ₂ x₂ y₂ z₂
      rw [tensorHomBlock_apply S (tensorHom S f g) h d (e, c) ν ⟨(a, b), (μ, x, y)⟩ z
        ν₂ ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩ z₂, if_neg (Ne.symm hν₂), zero_mul, zero_mul]
    simp only [hz, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · refine (Finset.sum_eq_single a ?_ ?_).trans ?_
    · -- the label of the middle `X`-summand is forced
      intro a₂ _ ha₂
      have hz : ∀ (b₂ : Fin n) (μ₂ : Fin (S.ring.N a₂ b₂ e))
          (x₂ : X'.blk a₂) (y₂ : Y'.blk b₂) (z₂ : Z'.blk c),
          (tensorHomBlock S (tensorHom S f g) h d (e, c) (ν, ⟨(a, b), (μ, x, y)⟩, z)
              (ν, ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩, z₂) *
            Matrix.of (assocEntry S X' Y' Z' d)
              ⟨(e, c), (ν, ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩, z₂)⟩ q) = 0 := by
        intro b₂ μ₂ x₂ y₂ z₂
        rw [tensorHomBlock_apply S (tensorHom S f g) h d (e, c) ν ⟨(a, b), (μ, x, y)⟩ z
          ν ⟨(a₂, b₂), (μ₂, x₂, y₂)⟩ z₂, if_pos rfl, one_mul,
          tensorHom_apply_ne S f g e (p := (a, b)) (q := (a₂, b₂))
            (fun hh => ha₂ (Prod.mk.injEq a b a₂ b₂ |>.mp hh).1.symm) μ x y μ₂ x₂ y₂,
          zero_mul, zero_mul]
      simp only [hz, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
      · -- the label of the middle `Y`-summand is forced
        intro b₂ _ hb₂
        have hz : ∀ (μ₂ : Fin (S.ring.N a b₂ e))
            (x₂ : X'.blk a) (y₂ : Y'.blk b₂) (z₂ : Z'.blk c),
            (tensorHomBlock S (tensorHom S f g) h d (e, c) (ν, ⟨(a, b), (μ, x, y)⟩, z)
                (ν, ⟨(a, b₂), (μ₂, x₂, y₂)⟩, z₂) *
              Matrix.of (assocEntry S X' Y' Z' d)
                ⟨(e, c), (ν, ⟨(a, b₂), (μ₂, x₂, y₂)⟩, z₂)⟩ q) = 0 := by
          intro μ₂ x₂ y₂ z₂
          rw [tensorHomBlock_apply S (tensorHom S f g) h d (e, c) ν ⟨(a, b), (μ, x, y)⟩ z
            ν ⟨(a, b₂), (μ₂, x₂, y₂)⟩ z₂, if_pos rfl, one_mul,
            tensorHom_apply_ne S f g e (p := (a, b)) (q := (a, b₂))
              (fun hh => hb₂ (Prod.mk.injEq a b a b₂ |>.mp hh).2.symm) μ x y μ₂ x₂ y₂,
            zero_mul, zero_mul]
        simp only [hz, Finset.sum_const_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
      · refine (Finset.sum_eq_single μ ?_ ?_).trans ?_
        · -- the channel of the two-factor summand is forced
          intro μ₂ _ hμ₂
          have hz : ∀ (x₂ : X'.blk a) (y₂ : Y'.blk b) (z₂ : Z'.blk c),
              (tensorHomBlock S (tensorHom S f g) h d (e, c) (ν, ⟨(a, b), (μ, x, y)⟩, z)
                  (ν, ⟨(a, b), (μ₂, x₂, y₂)⟩, z₂) *
                Matrix.of (assocEntry S X' Y' Z' d)
                  ⟨(e, c), (ν, ⟨(a, b), (μ₂, x₂, y₂)⟩, z₂)⟩ q) = 0 := by
            intro x₂ y₂ z₂
            rw [tensorHomBlock_apply S (tensorHom S f g) h d (e, c) ν ⟨(a, b), (μ, x, y)⟩ z
              ν ⟨(a, b), (μ₂, x₂, y₂)⟩ z₂, if_pos rfl, one_mul,
              tensorHom_apply S f g e (a, b) μ x y μ₂ x₂ y₂, if_neg (Ne.symm hμ₂),
              zero_mul, zero_mul, zero_mul]
          simp only [hz, Finset.sum_const_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · refine Finset.sum_congr rfl (fun x₂ _ => Finset.sum_congr rfl
            (fun y₂ _ => Finset.sum_congr rfl (fun z₂ _ => ?_)))
          rw [tensorHomBlock_apply S (tensorHom S f g) h d (e, c) ν ⟨(a, b), (μ, x, y)⟩ z
            ν ⟨(a, b), (μ, x₂, y₂)⟩ z₂, if_pos rfl, one_mul,
            tensorHom_apply S f g e (a, b) μ x y μ x₂ y₂, if_pos rfl, one_mul]
          rfl

end LHS

section RHS

variable {X X' Y Y' Z Z' : FusionMat n k}

/-- **The right side of the naturality square, reduced.**  The outer label of the
middle index is forced (to the column's label) and its channel is forced; the
inner tensor factor is left as a matrix entry, and the middle `X`-index is kept
as a single variable (its block type is opaque). -/
theorem rhs_sum_eq (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (a' f' : Fin n) (ν' : Fin (S.ring.N a' f' d)) (x' : X'.blk a')
    (b' c' : Fin n) (μ' : Fin (S.ring.N b' c' f')) (y' : Y'.blk b') (z' : Z'.blk c') :
    (associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)) d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
      = ∑ u : X.blk a',
          ∑ b₁ : Fin n, ∑ c₁ : Fin n, ∑ μ₁ : Fin (S.ring.N b₁ c₁ f'),
          ∑ y₁ : Y.blk b₁, ∑ z₁ : Z.blk c₁,
          (f a' u x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
              ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩) *
            assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
              ⟨⟨a', f'⟩, ⟨ν', ⟨u, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩ := by
  rw [show (associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)) d
      = Matrix.of (assocEntry S X Y Z d)
        * blockDiag (fun p : Fin n × Fin n => tensorHomBlock S f (tensorHom S g h) d p)
        from rfl]
  rw [mul_blockDiag_apply]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single ν' ?_ ?_).trans ?_
  · intro ν₁ _ hν₁
    have hz : ∀ (u : X.blk a') (b₁ : Fin n) (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
        (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
        (Matrix.of (assocEntry S X Y Z d) ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
            ⟨(a', f'), (ν₁, u, ⟨(b₁, c₁), (μ₁, y₁, z₁)⟩)⟩ *
          tensorHomBlock S f (tensorHom S g h) d (a', f')
            (ν₁, u, ⟨(b₁, c₁), (μ₁, y₁, z₁)⟩) (ν', x', ⟨(b', c'), (μ', y', z')⟩)) = 0 := by
      intro u b₁ c₁ μ₁ y₁ z₁
      rw [tensorHomBlock_apply S f (tensorHom S g h) d (a', f') ν₁ u ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
        ν' x' ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩, if_neg hν₁, zero_mul, mul_zero]
    simp only [hz, Finset.sum_const_zero]
  · intro hzz
    exact absurd (Finset.mem_univ _) hzz
  · refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun b₁ _ => ?_)
    refine Finset.sum_congr rfl (fun c₁ _ => ?_)
    refine Finset.sum_congr rfl (fun μ₁ _ => ?_)
    refine Finset.sum_congr rfl (fun y₁ _ => ?_)
    refine Finset.sum_congr rfl (fun z₁ _ => ?_)
    rw [tensorHomBlock_apply S f (tensorHom S g h) d (a', f') ν' u
      ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩ ν' x' ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩, if_pos rfl, one_mul]
    exact mul_comm _ _

end RHS

section Matched

variable {X X' Y Y' Z Z' : FusionMat n k}

/-- **The left side at fully matched labels is the scalar `(f ⊗ g) ⊗ h`-entry
times the `F`-symbol.** -/
theorem lhs_eq_matched (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f' : Fin n) (ν' : Fin (S.ring.N a f' d)) (x' : X'.blk a)
    (μ' : Fin (S.ring.N b c f')) (y' : Y'.blk b) (z' : Z'.blk c) :
    (tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z') d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f'⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
      = f a x x' * g b y y' * h c z z' * S.F a b c d e f' := by
  rw [lhs_sum_eq S f g h d e c ν a b μ x y z ⟨⟨a, f'⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩]
  refine (Finset.sum_eq_single x' ?_ ?_).trans ?_
  · intro x₂ _ hx₂
    have hz : ∀ (y₂ : Y'.blk b) (z₂ : Z'.blk c),
        ((f a x x₂ * g b y y₂ * h c z z₂) *
          assocEntry S X' Y' Z' d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x₂, y₂⟩⟩, z₂⟩⟩⟩
            ⟨⟨a, f'⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩) = 0 := by
      intro y₂ z₂
      rw [assocEntry_zero_x (X := X') (Y := Y') (Z := Z') (e := e) (c := c) (ν := ν)
        (a := a) (b := b) (μ := μ) (x := x₂) (y := y₂) (z := z₂) (f := f') (ν' := ν')
        (x' := x') (μ' := μ') (y' := y') (z' := z') (h := hx₂), mul_zero]
    simp only [hz, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · refine (Finset.sum_eq_single y' ?_ ?_).trans ?_
    · intro y₂ _ hy₂
      have hz : ∀ (z₂ : Z'.blk c),
          ((f a x x' * g b y y₂ * h c z z₂) *
            assocEntry S X' Y' Z' d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x', y₂⟩⟩, z₂⟩⟩⟩
              ⟨⟨a, f'⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩) = 0 := by
        intro z₂
        rw [assocEntry_zero_y (X := X') (Y := Y') (Z := Z') (e := e) (c := c) (ν := ν)
          (a := a) (b := b) (μ := μ) (x := x') (y := y₂) (z := z₂) (f := f') (ν' := ν')
          (x' := x') (μ' := μ') (y' := y') (z' := z') (h := hy₂), mul_zero]
      simp only [hz, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · refine (Finset.sum_eq_single z' ?_ ?_).trans ?_
      · intro z₂ _ hz₂
        rw [assocEntry_zero_z (X := X') (Y := Y') (Z := Z') (e := e) (c := c) (ν := ν)
          (a := a) (b := b) (μ := μ) (x := x') (y := y') (z := z₂) (f := f') (ν' := ν')
          (x' := x') (μ' := μ') (y' := y') (z' := z') (h := hz₂), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
      · rw [assocEntry_exact S X' Y' Z' d e c ν a b μ x' y' z' f' ν' μ']

end Matched

end FusionCategory

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

section MatchedR

variable {X X' Y Y' Z Z' : FusionMat n k}

set_option maxHeartbeats 2000000 in
/-- **The right side at fully matched labels.** -/
theorem rhs_eq_matched (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f' : Fin n) (ν' : Fin (S.ring.N a f' d)) (x' : X'.blk a)
    (μ' : Fin (S.ring.N b c f')) (y' : Y'.blk b) (z' : Z'.blk c) :
    (associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)) d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f'⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
      = f a x x' * (g b y y' * h c z z') * S.F a b c d e f' := by
  rw [rhs_sum_eq S f g h d e c ν a b μ x y z a f' ν' x' b c μ' y' z']
  refine (Finset.sum_eq_single x ?_ ?_).trans ?_
  · intro u _ hu
    have hz : ∀ (b₁ : Fin n) (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
        (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
        ((f a u x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩ ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩) *
          assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
            ⟨⟨a, f'⟩, ⟨ν', ⟨u, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
      intro b₁ c₁ μ₁ y₁ z₁
      rw [assocEntry_zero_x_gen (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e)
        (c := c) (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z) (f := f')
        (ν₂ := ν') (x₂ := u) (b₂ := b₁) (c₂ := c₁) (μ₂ := μ₁) (y₂ := y₁) (z₂ := z₁)
        (h := Ne.symm hu), mul_zero]
    simp only [hz, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
    · intro b₁ _ hb₁
      have hz : ∀ (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
          (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
          ((f a x x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩ ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩) *
            assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
              ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
        intro c₁ μ₁ y₁ z₁
        rw [assocEntry_zero_b (h1 := rfl) (h := Ne.symm hb₁), mul_zero]
      simp only [hz, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · refine (Finset.sum_eq_single c ?_ ?_).trans ?_
      · intro c₁ _ hc₁
        have hz : ∀ (μ₁ : Fin (S.ring.N b c₁ f'))
            (y₁ : Y.blk b) (z₁ : Z.blk c₁),
            ((f a x x' * (tensorHom S g h) f' ⟨⟨b, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩ ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩) *
              assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
          intro μ₁ y₁ z₁
          rw [assocEntry_zero_c (h1 := rfl) (h2 := rfl) (h := Ne.symm hc₁), mul_zero]
        simp only [hz, Finset.sum_const_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
      · refine (Finset.sum_eq_single μ' ?_ ?_).trans ?_
        · intro μ₁ _ hμ₁
          have hz : ∀ (y₁ : Y.blk b) (z₁ : Z.blk c),
              ((f a x x' * (tensorHom S g h) f' ⟨⟨b, c⟩, ⟨μ₁, y₁, z₁⟩⟩
                  ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩) *
                assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                  ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
            intro y₁ z₁
            rw [tensorHom_apply S g h f' (b, c) μ₁ y₁ z₁ μ' y' z', if_neg hμ₁,
              zero_mul, mul_zero, zero_mul]
          simp only [hz, Finset.sum_const_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · refine (Finset.sum_eq_single y ?_ ?_).trans ?_
          · intro y₁ _ hy₁
            have hz : ∀ (z₁ : Z.blk c),
                ((f a x x' * (tensorHom S g h) f' ⟨⟨b, c⟩, ⟨μ', y₁, z₁⟩⟩
                    ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩) *
                  assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                    ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
              intro z₁
              rw [assocEntry_zero_y (e := e) (c := c) (ν := ν) (a := a) (b := b) (μ := μ)
                (x := x) (y := y) (z := z) (f := f') (ν' := ν') (x' := x) (μ' := μ')
                (y' := y₁) (z' := z₁) (h := Ne.symm hy₁), mul_zero]
            simp only [hz, Finset.sum_const_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
          · refine (Finset.sum_eq_single z ?_ ?_).trans ?_
            · intro z₁ _ hz₁
              rw [assocEntry_zero_z (e := e) (c := c) (ν := ν) (a := a) (b := b) (μ := μ)
                (x := x) (y := y) (z := z) (f := f') (ν' := ν') (x' := x) (μ' := μ')
                (y' := y) (z' := z₁) (h := Ne.symm hz₁), mul_zero]
            · intro h
              exact absurd (Finset.mem_univ _) h
            · rw [tensorHom_apply S g h f' (b, c) μ' y z μ' y' z', if_pos rfl, one_mul,
                assocEntry_exact S X Y Z d e c ν a b μ x y z f' ν' μ']

end MatchedR

end FusionCategory

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

section Zeros

variable {X X' Y Y' Z Z' : FusionMat n k}

/-- **The left side vanishes off the matched labels.** -/
theorem lhs_eq_zero (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (a' b' c' f' : Fin n) (ν' : Fin (S.ring.N a' f' d)) (x' : X'.blk a')
    (μ' : Fin (S.ring.N b' c' f')) (y' : Y'.blk b') (z' : Z'.blk c')
    (hne : ¬ ((a, b) = (a', b') ∧ c = c')) :
    (tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z') d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ = 0 := by
  rw [lhs_sum_eq S f g h d e c ν a b μ x y z
    ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩]
  by_cases ha : a = a'
  · subst ha
    by_cases hb : b = b'
    · subst hb
      have hc : c ≠ c' := fun hh => hne ⟨rfl, hh⟩
      refine Finset.sum_eq_zero fun x₂ _ => Finset.sum_eq_zero fun y₂ _ =>
        Finset.sum_eq_zero fun z₂ _ => ?_
      rw [assocEntry_zero_c (X := X') (Y := Y') (Z := Z') (h1 := rfl) (h2 := rfl)
        (h := hc), mul_zero]
    · have hb' : b ≠ b' := hb
      refine Finset.sum_eq_zero fun x₂ _ => Finset.sum_eq_zero fun y₂ _ =>
        Finset.sum_eq_zero fun z₂ _ => ?_
      rw [assocEntry_zero_b (X := X') (Y := Y') (Z := Z') (h1 := rfl) (h := hb'), mul_zero]
  · have ha' : a ≠ a' := ha
    refine Finset.sum_eq_zero fun x₂ _ => Finset.sum_eq_zero fun y₂ _ =>
      Finset.sum_eq_zero fun z₂ _ => ?_
    rw [assocEntry_zero_a (X := X') (Y := Y') (Z := Z') (h := ha'), mul_zero]

end Zeros

end FusionCategory

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

section ZeroR

variable {X X' Y Y' Z Z' : FusionMat n k}

set_option maxHeartbeats 2000000 in
/-- **The right side vanishes off the matched labels.** -/
theorem rhs_eq_zero (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (a' f' : Fin n) (ν' : Fin (S.ring.N a' f' d)) (x' : X'.blk a')
    (b' c' : Fin n) (μ' : Fin (S.ring.N b' c' f')) (y' : Y'.blk b') (z' : Z'.blk c')
    (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    (associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)) d
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ = 0 := by
  rw [rhs_sum_eq S f g h d e c ν a b μ x y z a' f' ν' x' b' c' μ' y' z']
  by_cases ha : a = a'
  · subst ha
    by_cases hb : b = b'
    · subst hb
      have hc : c ≠ c' := fun hh => hne ⟨rfl, rfl, hh⟩
      refine (Finset.sum_eq_single x ?_ ?_).trans ?_
      · intro u _ hu
        have hz : ∀ (b₁ : Fin n) (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
            (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
            ((f a u x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
                ⟨⟨b, c'⟩, ⟨μ', y', z'⟩⟩) *
              assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                ⟨⟨a, f'⟩, ⟨ν', ⟨u, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
          intro b₁ c₁ μ₁ y₁ z₁
          rw [assocEntry_zero_x_gen (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e)
            (c := c) (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z)
            (f := f') (ν₂ := ν') (x₂ := u) (b₂ := b₁) (c₂ := c₁) (μ₂ := μ₁) (y₂ := y₁)
            (z₂ := z₁) (h := Ne.symm hu), mul_zero]
        simp only [hz, Finset.sum_const_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
      · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
        · intro b₁ _ hb₁
          have hz : ∀ (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
              (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
              ((f a x x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
                  ⟨⟨b, c'⟩, ⟨μ', y', z'⟩⟩) *
                assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                  ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
            intro c₁ μ₁ y₁ z₁
            rw [assocEntry_zero_b (h1 := rfl) (h := Ne.symm hb₁), mul_zero]
          simp only [hz, Finset.sum_const_zero]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
        · refine (Finset.sum_eq_single c ?_ ?_).trans ?_
          · intro c₁ _ hc₁
            have hz : ∀ (μ₁ : Fin (S.ring.N b c₁ f')) (y₁ : Y.blk b) (z₁ : Z.blk c₁),
                ((f a x x' * (tensorHom S g h) f' ⟨⟨b, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
                    ⟨⟨b, c'⟩, ⟨μ', y', z'⟩⟩) *
                  assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                    ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
              intro μ₁ y₁ z₁
              rw [assocEntry_zero_c (h1 := rfl) (h2 := rfl) (h := Ne.symm hc₁), mul_zero]
            simp only [hz, Finset.sum_const_zero]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
          · refine Finset.sum_eq_zero fun μ₁ _ => Finset.sum_eq_zero fun y₁ _ =>
              Finset.sum_eq_zero fun z₁ _ => ?_
            rw [tensorHom_apply_ne S g h f' (p := (b, c)) (q := (b, c'))
              (fun hh => hc (Prod.mk.injEq b c b c' |>.mp hh).2) μ₁ y₁ z₁ μ' y' z']
            simp
    · have hb' : b ≠ b' := hb
      refine (Finset.sum_eq_single x ?_ ?_).trans ?_
      · intro u _ hu
        have hz : ∀ (b₁ : Fin n) (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
            (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
            ((f a u x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
                ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩) *
              assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                ⟨⟨a, f'⟩, ⟨ν', ⟨u, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
          intro b₁ c₁ μ₁ y₁ z₁
          rw [assocEntry_zero_x_gen (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e)
            (c := c) (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z)
            (f := f') (ν₂ := ν') (x₂ := u) (b₂ := b₁) (c₂ := c₁) (μ₂ := μ₁) (y₂ := y₁)
            (z₂ := z₁) (h := Ne.symm hu), mul_zero]
        simp only [hz, Finset.sum_const_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
      · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
        · intro b₁ _ hb₁
          have hz : ∀ (c₁ : Fin n) (μ₁ : Fin (S.ring.N b₁ c₁ f'))
              (y₁ : Y.blk b₁) (z₁ : Z.blk c₁),
              ((f a x x' * (tensorHom S g h) f' ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩
                  ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩) *
                assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                  ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b₁, c₁⟩, ⟨μ₁, y₁, z₁⟩⟩⟩⟩⟩) = 0 := by
            intro c₁ μ₁ y₁ z₁
            rw [assocEntry_zero_b (h1 := rfl) (h := Ne.symm hb₁), mul_zero]
          simp only [hz, Finset.sum_const_zero]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
        · refine Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun μ₁ _ =>
            Finset.sum_eq_zero fun y₁ _ => Finset.sum_eq_zero fun z₁ _ => ?_
          rw [tensorHom_apply_ne S g h f' (p := (b, c₁)) (q := (b', c'))
            (fun hh => hb' (Prod.mk.injEq b c₁ b' c' |>.mp hh).1) μ₁ y₁ z₁ μ' y' z']
          simp
  · have ha' : a ≠ a' := ha
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun b₁ _ =>
      Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun μ₁ _ =>
      Finset.sum_eq_zero fun y₁ _ => Finset.sum_eq_zero fun z₁ _ => ?_
    rw [assocEntry_zero_a (h := ha'), mul_zero]

end ZeroR

end FusionCategory

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

section Assembly

variable {X X' Y Y' Z Z' : FusionMat n k}

set_option maxHeartbeats 1000000 in
/-- **The naturality square, entrywise.** -/
theorem associatorNatural_apply (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : Fin n)
    (r : (tensorObj S (tensorObj S X Y) Z).blk d)
    (q : (tensorObj S X' (tensorObj S Y' Z')).blk d) :
    ((tensorHom S (tensorHom S f g) h ≫ associatorHom S X' Y' Z') d) r q
      = ((associatorHom S X Y Z ≫ tensorHom S f (tensorHom S g h)) d) r q := by
  obtain ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ := r
  obtain ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ := q
  by_cases ha : a = a'
  · subst ha
    by_cases hb : b = b'
    · subst hb
      by_cases hc : c = c'
      · subst hc
        rw [lhs_eq_matched S f g h d e c ν a b μ x y z f' ν' x' μ' y' z',
          rhs_eq_matched S f g h d e c ν a b μ x y z f' ν' x' μ' y' z']
        ring
      · rw [lhs_eq_zero S f g h d e c ν a b μ x y z a b c' f' ν' x' μ' y' z'
            (fun hh => hc hh.2),
          rhs_eq_zero S f g h d e c ν a b μ x y z a f' ν' x' b c' μ' y' z'
            (fun hh => hc hh.2.2)]
    · rw [lhs_eq_zero S f g h d e c ν a b μ x y z a b' c' f' ν' x' μ' y' z'
            (fun hh => hb (Prod.mk.injEq a b a b' |>.mp hh.1).2),
          rhs_eq_zero S f g h d e c ν a b μ x y z a f' ν' x' b' c' μ' y' z'
            (fun hh => hb hh.2.1)]
  · rw [lhs_eq_zero S f g h d e c ν a b μ x y z a' b' c' f' ν' x' μ' y' z'
          (fun hh => ha (Prod.mk.injEq a b a' b' |>.mp hh.1).1),
        rhs_eq_zero S f g h d e c ν a b μ x y z a' f' ν' x' b' c' μ' y' z'
          (fun hh => ha hh.1)]

end Assembly

/-- **`AssociatorNatural`** — the first of the two frozen statements of
`ReconAssocStatements`, proved. -/
theorem associatorNatural : AssociatorNatural S := by
  intro X Y Z X' Y' Z' f g h
  funext d
  ext r q
  exact associatorNatural_apply S f g h d r q

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.tensorHomBlock_apply
#print axioms FusionCategory.tensorHom_blockDiag_apply
#print axioms FusionCategory.tensorHom_tensorHom_apply
#print axioms FusionCategory.lhs_sum_eq
#print axioms FusionCategory.rhs_sum_eq
#print axioms FusionCategory.lhs_eq_matched
#print axioms FusionCategory.rhs_eq_matched
#print axioms FusionCategory.lhs_eq_zero
#print axioms FusionCategory.rhs_eq_zero
#print axioms FusionCategory.associatorNatural_apply
#print axioms FusionCategory.associatorNatural

/-! ## What this closes: the monoidal structure now waits only on the pentagon -/

namespace FusionCategory
open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- **The monoidal coherence data**, from the *proved* associator laws and the pentagon. -/
noncomputable def monoidalDataOfPentagon (hn : 0 < n) (pent : PentagonShapeHom S) :
    MonoidalData S hn :=
  monoidalDataOfAssoc S hn (associatorIso S) (associatorNatural S) pent

/-- **The monoidal category**, with the associator laws discharged: the only remaining
input is D3's pentagon `PentagonShapeHom S`. -/
noncomputable def monoidalCategoryOfPentagon (hn : 0 < n) (pent : PentagonShapeHom S) :
    MonoidalCategory (FusionMat n k) :=
  monoidalCategoryOfAssoc S hn (associatorIso S) (associatorNatural S) pent

/-- The additivity of the tensor for that structure. -/
theorem monoidalPreadditiveOfPentagon (hn : 0 < n) (pent : PentagonShapeHom S) :
    @MonoidalPreadditive (FusionMat n k) _ _ (monoidalCategoryOfPentagon S hn pent) :=
  monoidalPreadditiveOfAssoc S hn (associatorIso S) (associatorNatural S) pent

/-- The assembled associator is the F-symbol block matrix. -/
theorem monoidalDataOfPentagon_associator_hom (hn : 0 < n) (pent : PentagonShapeHom S)
    (X Y Z : FusionMat n k) :
    ((monoidalDataOfPentagon S hn pent).associator X Y Z).hom = associatorHom S X Y Z := rfl

#print axioms FusionCategory.monoidalDataOfPentagon
#print axioms FusionCategory.monoidalCategoryOfPentagon
#print axioms FusionCategory.monoidalPreadditiveOfPentagon

end FusionCategory
