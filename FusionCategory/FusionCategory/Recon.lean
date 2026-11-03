import Mathlib
import FusionCategory.System

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## The reconstruction's objects and morphisms -/

/-- Objects of the reconstruction: a multiplicity vector together with block
index types realising it.

The design note's object is the multiplicity vector `m : Fin n → ℕ`
(`FusionMat.ofM` below recovers that model with `blk i := Fin (m i)`); the
block types are carried as data so that the tensor product's block index type
(`Σ (a b), Fin (N a b c) × blk a × blk b`) is *definitionally* the block of the
tensor object. -/
structure FusionMat (n : ℕ) (k : Type u) [Field k] where
  /-- The multiplicity of the `i`-th simple. -/
  m : Fin n → ℕ
  /-- The block index type of the `i`-th simple summand. -/
  blk : Fin n → Type
  /-- Each block is finite. -/
  fintype_blk : ∀ i, Fintype (blk i)
  /-- Each block has decidable equality (needed for identity matrices). -/
  decidableEq_blk : ∀ i, DecidableEq (blk i)
  /-- The block type realises the multiplicity. -/
  card_blk : ∀ i, Fintype.card (blk i) = m i

namespace FusionMat

instance instFintypeBlk (X : FusionMat n k) (i : Fin n) : Fintype (X.blk i) :=
  X.fintype_blk i

instance instDecidableEqBlk (X : FusionMat n k) (i : Fin n) : DecidableEq (X.blk i) :=
  X.decidableEq_blk i

/-- The design note's model: `m ↦ (fun i => Fin (m i))`. -/
def ofM (m : Fin n → ℕ) : FusionMat n k where
  m := m
  blk := fun i => Fin (m i)
  fintype_blk := fun _ => inferInstance
  decidableEq_blk := fun _ => inferInstance
  card_blk := fun _ => by simp

@[simp] theorem ofM_m (m : Fin n → ℕ) : (ofM (k := k) m).m = m := rfl
theorem ofM_blk (m : Fin n → ℕ) (i : Fin n) : (ofM (k := k) m).blk i = Fin (m i) := rfl

end FusionMat

/-- Morphisms: one matrix block per simple label (Schur is structural). -/
abbrev FusionHom (X Y : FusionMat n k) : Type u := ∀ i, Matrix (X.blk i) (Y.blk i) k

instance instCategory : Category (FusionMat n k) where
  Hom := FusionHom
  id _ := fun _ => 1
  comp f g := fun i => f i * g i
  id_comp f := by funext i; exact Matrix.one_mul (f i)
  comp_id f := by funext i; exact Matrix.mul_one (f i)
  assoc f g h := by funext i; exact Matrix.mul_assoc (f i) (g i) (h i)

instance instPreadditive : Preadditive (FusionMat n k) where
  homGroup X Y := inferInstanceAs (AddCommGroup (FusionHom X Y))
  add_comp _ _ _ _ _ _ := by funext i; exact Matrix.add_mul _ _ _
  comp_add _ _ _ _ _ _ := by funext i; exact Matrix.mul_add _ _ _

instance instLinear : Linear k (FusionMat n k) where
  homModule X Y := inferInstanceAs (Module k (FusionHom X Y))
  smul_comp _ _ _ r _ _ := by funext i; exact Matrix.smul_mul r _ _
  comp_smul _ _ _ _ r _ := by funext i; exact Matrix.mul_smul _ r _

/-! ## The block-diagonal calculus -/

section BlockDiag

variable {L : Type} {ι κ ι' : L → Type}
variable [Fintype L] [DecidableEq L]
variable [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)] [∀ l, Fintype (ι' l)]
variable [∀ l, DecidableEq (ι l)] [∀ l, DecidableEq (κ l)] [∀ l, DecidableEq (ι' l)]

/-- Two sigma elements over the same label are equal iff their fibres are. -/
theorem sigma_mk_eq_iff {l : L} {i j : ι l} : (⟨l, i⟩ : Sigma ι) = ⟨l, j⟩ ↔ i = j := by
  constructor
  · intro h
    exact eq_of_heq ((Sigma.mk.injEq l i l j).mp h).2
  · intro h
    rw [h]

/-- A matrix which is block diagonal over the label type `L`: the `(l, l)`-block
is `A l`, every off-diagonal block is zero. -/
def blockDiag (A : ∀ l, Matrix (ι l) (κ l) k) : Matrix (Σ l, ι l) (Σ l, κ l) k :=
  fun r q => if h : r.1 = q.1 then A r.1 r.2 (h ▸ q.2) else 0

@[simp] theorem blockDiag_mk (A : ∀ l, Matrix (ι l) (κ l) k) (l : L) (i : ι l) (j : κ l) :
    blockDiag A ⟨l, i⟩ ⟨l, j⟩ = A l i j := by
  simp [blockDiag]

theorem blockDiag_one :
    blockDiag (fun l => (1 : Matrix (ι l) (ι l) k))
      = (1 : Matrix (Σ l, ι l) (Σ l, ι l) k) := by
  classical
  ext r q
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  by_cases h : l = l'
  · subst h
    rw [blockDiag_mk]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (⟨l, i⟩ : Sigma ι) ≠ ⟨l, j⟩ := fun hc => hij (sigma_mk_eq_iff.mp hc)
      show (if i = j then (1 : k) else 0)
        = (if (⟨l, i⟩ : Sigma ι) = ⟨l, j⟩ then (1 : k) else 0)
      rw [if_neg hij, if_neg hne]
  · have hne : (⟨l, i⟩ : Sigma ι) ≠ ⟨l', j⟩ := fun hc => h (congrArg Sigma.fst hc)
    simp [blockDiag, h, hne]

/-- Composition against a general matrix on the right: the label of the middle
index is forced to be the row label, and the sum runs over the remaining block
index only. -/
theorem blockDiag_mul_apply (A : ∀ l, Matrix (ι l) (κ l) k)
    (B : Matrix (Σ l, κ l) (Σ l, ι' l) k) (r : Σ l, ι l) (q : Σ l, ι' l) :
    (blockDiag A * B) r q = ∑ y : κ r.1, A r.1 r.2 y * B ⟨r.1, y⟩ q := by
  classical
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  refine (Finset.sum_eq_single (a := l) ?_ ?_).trans ?_
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have h : ¬ (l = x) := fun hc => hx hc.symm
    simp [blockDiag, h]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · simp only [blockDiag_mk]

/-- Composition against a general matrix on the left: here the label of the
middle index is forced to be the *column* label. -/
theorem mul_blockDiag_apply (A : Matrix (Σ l, ι l) (Σ l, κ l) k)
    (B : ∀ l, Matrix (κ l) (ι' l) k) (r : Σ l, ι l) (q : Σ l, ι' l) :
    (A * blockDiag B) r q = ∑ y : κ q.1, A r ⟨q.1, y⟩ * B q.1 y q.2 := by
  classical
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  refine (Finset.sum_eq_single (a := l') ?_ ?_).trans ?_
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have h : ¬ (x = l') := hx
    simp [blockDiag, h]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [blockDiag_mk]

/-- Composition of two block-diagonal matrices is block diagonal, with the
composed blocks. -/
theorem blockDiag_mul_blockDiag (A : ∀ l, Matrix (ι l) (κ l) k)
    (B : ∀ l, Matrix (κ l) (ι' l) k) :
    blockDiag A * blockDiag B = blockDiag (fun l => A l * B l) := by
  classical
  ext r q
  rw [blockDiag_mul_apply]
  obtain ⟨l, i⟩ := r
  obtain ⟨l', j⟩ := q
  by_cases h : l = l'
  · subst h
    simp only [blockDiag_mk]
    exact (Matrix.mul_apply).symm
  · simp [blockDiag, h]

end BlockDiag

end FusionCategory
