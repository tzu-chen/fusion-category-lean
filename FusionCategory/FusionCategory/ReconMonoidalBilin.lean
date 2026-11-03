/-
WP2 round 2, member m4, direction D5 (monoidal assembly), part (a):
bilinearity of the reconstruction's tensor on morphisms.

`MonoidalPreadditive` (Mathlib) asks exactly four things of the whiskerings:
`X ◁ 0 = 0`, `0 ▷ X = 0`, `X ◁ (f + g) = X ◁ f + X ◁ g`, `(f + g) ▷ X = f ▷ X + g ▷ X`.
On the canonical scaffold the whiskerings are `tensorHom` with an identity, so these are
bilinearity of `tensorHom`; entrywise, `tensorHomBlock` is an iterated Kronecker product, and
the Kronecker product is bilinear because it is entrywise multiplication.

Everything here is unconditional: no associator, no unitor, no pentagon.  It only uses the
landed `FusionCategory.Recon` block calculus and the landed `tensorHom` (Round 1).

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconTensorApply

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## The block calculus, additively -/

section BlockDiagAdd

variable {L : Type} {ι κ : L → Type}
variable [Fintype L] [DecidableEq L]
variable [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
variable [∀ l, DecidableEq (ι l)] [∀ l, DecidableEq (κ l)]

/-- `blockDiag` is additive in its blocks. -/
theorem blockDiag_add (A B : ∀ l, Matrix (ι l) (κ l) k) :
    blockDiag A + blockDiag B = blockDiag (fun l => A l + B l) := by
  classical
  ext r q
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  by_cases h : l = l'
  · subst h
    simp [blockDiag, Matrix.add_apply]
  · simp [blockDiag, h]

/-- `blockDiag` is `k`-linear in its blocks. -/
theorem blockDiag_smul (r : k) (A : ∀ l, Matrix (ι l) (κ l) k) :
    r • blockDiag A = blockDiag (fun l => r • A l) := by
  classical
  ext a b
  obtain ⟨l, i⟩ := a
  obtain ⟨l', j⟩ := b
  by_cases h : l = l'
  · subst h; simp [blockDiag, Matrix.smul_apply]
  · simp [blockDiag, h]

/-- `blockDiag` of a pointwise zero family is zero. -/
theorem blockDiag_zero :
    blockDiag (fun l => (0 : Matrix (ι l) (κ l) k)) = 0 := by
  classical
  ext r q
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  by_cases h : l = l'
  · subst h; simp [blockDiag]
  · simp [blockDiag, h]

end BlockDiagAdd

/-! ## The Kronecker product, bilinearly

`tensorHomBlock` is `1 ⊗ₖ (f ⊗ₖ g)`; both factors are entrywise products, so additivity in
either slot of either factor is `add_mul`/`mul_add`.  These are the `kroneckerMap`-shaped
versions of Mathlib's `Matrix.add_kronecker`/`Matrix.kronecker_add`, stated for the exact
shape `FusionCategory` uses (so that no notation is needed). -/

section KroneckerBilin

variable {l m p l' m' p' : Type}

/-- The Kronecker product is additive in the left factor. -/
theorem kroneckerMap_add_left (A A' : Matrix l m k) (B : Matrix l' m' k) :
    Matrix.kroneckerMap (fun a b : k => a * b) (A + A') B
      = Matrix.kroneckerMap (fun a b : k => a * b) A B
        + Matrix.kroneckerMap (fun a b : k => a * b) A' B := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, add_mul]

/-- The Kronecker product is additive in the right factor. -/
theorem kroneckerMap_add_right (A : Matrix l m k) (B B' : Matrix l' m' k) :
    Matrix.kroneckerMap (fun a b : k => a * b) A (B + B')
      = Matrix.kroneckerMap (fun a b : k => a * b) A B
        + Matrix.kroneckerMap (fun a b : k => a * b) A B' := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, mul_add]

/-- The Kronecker product vanishes with a zero left factor. -/
theorem kroneckerMap_zero_left (B : Matrix l' m' k) :
    Matrix.kroneckerMap (fun a b : k => a * b) (0 : Matrix l m k) B = 0 := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp [Matrix.kroneckerMap_apply]

/-- The Kronecker product vanishes with a zero right factor. -/
theorem kroneckerMap_zero_right (A : Matrix l m k) :
    Matrix.kroneckerMap (fun a b : k => a * b) A (0 : Matrix l' m' k) = 0 := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp [Matrix.kroneckerMap_apply]

/-- The Kronecker product is `k`-linear in the left factor. -/
theorem kroneckerMap_smul_left (r : k) (A : Matrix l m k) (B : Matrix l' m' k) :
    Matrix.kroneckerMap (fun a b : k => a * b) (r • A) B
      = r • Matrix.kroneckerMap (fun a b : k => a * b) A B := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The Kronecker product is `k`-linear in the right factor. -/
theorem kroneckerMap_smul_right (r : k) (A : Matrix l m k) (B : Matrix l' m' k) :
    Matrix.kroneckerMap (fun a b : k => a * b) A (r • B)
      = r • Matrix.kroneckerMap (fun a b : k => a * b) A B := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end KroneckerBilin

/-! ## Bilinearity of `tensorHom` -/

variable (S : FusionSystem n k)

section Blocks

variable {X X' Y Y' : FusionMat n k}

/-- `tensorHomBlock` is `k`-linear in the second factor. -/
theorem tensorHomBlock_smul_right (r : k) (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S f (r • g) c p = r • tensorHomBlock S f g c p := by
  have hg : (r • g) p.2 = r • g p.2 := rfl
  simp only [tensorHomBlock, hg, kroneckerMap_smul_right]

/-- `tensorHomBlock` is `k`-linear in the first factor. -/
theorem tensorHomBlock_smul_left (r : k) (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S (r • f) g c p = r • tensorHomBlock S f g c p := by
  have hf : (r • f) p.1 = r • f p.1 := rfl
  simp only [tensorHomBlock, hf, kroneckerMap_smul_right, kroneckerMap_smul_left]

/-- `tensorHomBlock` is additive in the second factor. -/
theorem tensorHomBlock_add_right (f : X ⟶ X') (g h : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S f (g + h) c p
      = tensorHomBlock S f g c p + tensorHomBlock S f h c p := by
  have hg : (g + h) p.2 = g p.2 + h p.2 := rfl
  simp only [tensorHomBlock, hg, kroneckerMap_add_right]

/-- `tensorHomBlock` is additive in the first factor. -/
theorem tensorHomBlock_add_left (f f' : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S (f + f') g c p
      = tensorHomBlock S f g c p + tensorHomBlock S f' g c p := by
  have hf : (f + f') p.1 = f p.1 + f' p.1 := rfl
  simp only [tensorHomBlock, hf, kroneckerMap_add_right, kroneckerMap_add_left]

/-- `tensorHomBlock` vanishes on a zero second factor. -/
theorem tensorHomBlock_zero_right (f : X ⟶ X') (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S f (0 : Y ⟶ Y') c p = 0 := by
  have hg : (0 : Y ⟶ Y') p.2 = (0 : Matrix (Y.blk p.2) (Y'.blk p.2) k) := rfl
  simp only [tensorHomBlock, hg, kroneckerMap_zero_right]

/-- `tensorHomBlock` vanishes on a zero first factor. -/
theorem tensorHomBlock_zero_left (g : Y ⟶ Y') (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S (0 : X ⟶ X') g c p = 0 := by
  have hf : (0 : X ⟶ X') p.1 = (0 : Matrix (X.blk p.1) (X'.blk p.1) k) := rfl
  simp only [tensorHomBlock, hf, kroneckerMap_zero_right, kroneckerMap_zero_left]

end Blocks

/-- `tensorHom` is additive in the second factor. -/
theorem tensorHom_add_right {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g h : Y ⟶ Y') :
    tensorHom S f (g + h) = tensorHom S f g + tensorHom S f h := by
  funext c
  show blockDiag (fun p => tensorHomBlock S f (g + h) c p)
    = blockDiag (fun p => tensorHomBlock S f g c p)
      + blockDiag (fun p => tensorHomBlock S f h c p)
  rw [blockDiag_add]
  congr 1
  funext p
  exact tensorHomBlock_add_right S f g h c p

/-- `tensorHom` is additive in the first factor. -/
theorem tensorHom_add_left {X X' Y Y' : FusionMat n k} (f f' : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom S (f + f') g = tensorHom S f g + tensorHom S f' g := by
  funext c
  show blockDiag (fun p => tensorHomBlock S (f + f') g c p)
    = blockDiag (fun p => tensorHomBlock S f g c p)
      + blockDiag (fun p => tensorHomBlock S f' g c p)
  rw [blockDiag_add]
  congr 1
  funext p
  exact tensorHomBlock_add_left S f f' g c p

/-- `tensorHom` vanishes on a zero second factor. -/
theorem tensorHom_zero_right {X X' Y Y' : FusionMat n k} (f : X ⟶ X') :
    tensorHom S f (0 : Y ⟶ Y') = 0 := by
  funext c
  show blockDiag (fun p => tensorHomBlock S f (0 : Y ⟶ Y') c p) = (0 : Matrix _ _ k)
  simp only [tensorHomBlock_zero_right S f]
  exact blockDiag_zero

/-- `tensorHom` vanishes on a zero first factor. -/
theorem tensorHom_zero_left {X X' Y Y' : FusionMat n k} (g : Y ⟶ Y') :
    tensorHom S (0 : X ⟶ X') g = 0 := by
  funext c
  show blockDiag (fun p => tensorHomBlock S (0 : X ⟶ X') g c p) = (0 : Matrix _ _ k)
  simp only [tensorHomBlock_zero_left S g]
  exact blockDiag_zero

/-- `tensorHom` is `k`-linear in the second factor. -/
theorem tensorHom_smul_right {X X' Y Y' : FusionMat n k} (r : k) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom S f (r • g) = r • tensorHom S f g := by
  funext c
  show blockDiag (fun p => tensorHomBlock S f (r • g) c p)
    = r • blockDiag (fun p => tensorHomBlock S f g c p)
  rw [blockDiag_smul]
  congr 1
  funext p
  exact tensorHomBlock_smul_right S r f g c p

/-- `tensorHom` is `k`-linear in the first factor. -/
theorem tensorHom_smul_left {X X' Y Y' : FusionMat n k} (r : k) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom S (r • f) g = r • tensorHom S f g := by
  funext c
  show blockDiag (fun p => tensorHomBlock S (r • f) g c p)
    = r • blockDiag (fun p => tensorHomBlock S f g c p)
  rw [blockDiag_smul]
  congr 1
  funext p
  exact tensorHomBlock_smul_left S r f g c p

/-! ## Whiskerings on the scaffold

The whiskerings of the `MonoidalCategoryStruct` assembled in `ReconMonoidal.lean` are
`tensorHom` with an identity, so the four `MonoidalPreadditive` fields are the four lemmas
above.  Recorded in whiskering shape here. -/

/-- Left whiskering, on the canonical scaffold. -/
abbrev wl (X : FusionMat n k) {Y Y' : FusionMat n k} (g : Y ⟶ Y') :
    tensorObj S X Y ⟶ tensorObj S X Y' :=
  tensorHom S (𝟙 X) g

/-- Right whiskering, on the canonical scaffold. -/
abbrev wr {X X' : FusionMat n k} (f : X ⟶ X') (Y : FusionMat n k) :
    tensorObj S X Y ⟶ tensorObj S X' Y :=
  tensorHom S f (𝟙 Y)

theorem wl_zero (X : FusionMat n k) {Y Y' : FusionMat n k} :
    wl S X (0 : Y ⟶ Y') = 0 :=
  tensorHom_zero_right S (𝟙 X)

theorem wr_zero {X X' : FusionMat n k} (Y : FusionMat n k) :
    wr S (0 : X ⟶ X') Y = 0 :=
  tensorHom_zero_left S (𝟙 Y)

theorem wl_add (X : FusionMat n k) {Y Y' : FusionMat n k} (f g : Y ⟶ Y') :
    wl S X (f + g) = wl S X f + wl S X g :=
  tensorHom_add_right S (𝟙 X) f g

theorem wr_add {X X' : FusionMat n k} (Y : FusionMat n k) (f g : X ⟶ X') :
    wr S (f + g) Y = wr S f Y + wr S g Y :=
  tensorHom_add_left S f g (𝟙 Y)

theorem wl_smul (r : k) (X : FusionMat n k) {Y Y' : FusionMat n k} (g : Y ⟶ Y') :
    wl S X (r • g) = r • wl S X g :=
  tensorHom_smul_right S r (𝟙 X) g

theorem wr_smul (r : k) {X X' : FusionMat n k} (g : X ⟶ X') (Y : FusionMat n k) :
    wr S (r • g) Y = r • wr S g Y :=
  tensorHom_smul_left S r g (𝟙 Y)

/-- The exchange law of the two whiskerings: `tensorHom_comp` read backwards, and the reason
`tensorHom` (not the factorised form) is the primary datum of the struct. -/
theorem wl_wr_exchange {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y') :
    wr S f Y ≫ wl S X' g = wl S X g ≫ wr S f Y' := by
  simp only [wr, wl, ← tensorHom_comp, Category.comp_id, Category.id_comp]

end FusionCategory
