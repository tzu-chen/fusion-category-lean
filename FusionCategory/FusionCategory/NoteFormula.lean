/-
WP2 round 1, member m3, direction D4: a kernel check of a DESIGN-NOTE SLIP.

`docs/wp2-design.md` (Tensor on morphisms) writes the `c`-block of `f ⊗ g` at a
row `(a, b, _, i, j)` and a column `(a', b', _, i', j')` as

  `if a = a' ∧ b = b' ∧ i = i' ∧ j = j' then (f a) i i' * (g b) j j' else 0`.

The two conjuncts `i = i'`, `j = j'` must go: they truncate each block to its
diagonal, and the truncated assignment is not functorial.  The correct entry is
block-diagonal in the LABEL only, carrying the full block:

  `if a = a' ∧ b = b' then (f a) i i' * (g b) j j' else 0`

(`FusionCategory.tensorHomBlock` in `ReconTensor.lean`, which is
`1 ⊗ₖ ((f a) ⊗ₖ (g b))` and satisfies `tensorHom_comp`).

Below is the failure, with no category theory needed: on a block whose channel
coordainate is unique (`Fin 1`, e.g. any label with `N a b c = 1`) and whose
multiplicity indices are `Fin 2`, the note's formula is the matrix
`noteBlock f g` below, and `noteBlock (f₁ * f₂) (g₁ * g₂) = noteBlock f₁ g₁ *
noteBlock f₂ g₂` fails.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconTensor

set_option autoImplicit false

namespace FusionCategory

/-- The design note's tensor entry, on a block with a unique channel and
`2 × 2` multiplicity indices: `i = i'` and `j = j'` are kept. -/
def noteBlock (f g : Matrix (Fin 2) (Fin 2) ℚ) :
    Matrix (Fin 1 × Fin 2 × Fin 2) (Fin 1 × Fin 2 × Fin 2) ℚ :=
  Matrix.of fun ⟨_, i, j⟩ ⟨_, i', j'⟩ => if i = i' ∧ j = j' then f i i' * g j j' else 0

/-- The correction: label-diagonal only (the channel index stays, the block is
the full Kronecker product). -/
def fixedBlock (f g : Matrix (Fin 2) (Fin 2) ℚ) :
    Matrix (Fin 1 × Fin 2 × Fin 2) (Fin 1 × Fin 2 × Fin 2) ℚ :=
  Matrix.of fun ⟨_, i, j⟩ ⟨_, i', j'⟩ => f i i' * g j j'

/-- The transposition, used as the test morphism. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

theorem swap2_mul_swap2 : swap2 * swap2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The design note's formula is not functorial**: with `f₁ = f₂ = swap2`,
`g₁ = g₂ = 1`, the left side is the identity matrix (`swap2 * swap2 = 1`) while
the right side is `0` (`swap2` has zero diagonal). -/
theorem noteBlock_not_mul (i j : Fin 2) :
    noteBlock (swap2 * swap2) (1 * 1) ⟨0, i, j⟩ ⟨0, i, j⟩
      ≠ (noteBlock swap2 1 * noteBlock swap2 1) ⟨0, i, j⟩ ⟨0, i, j⟩ := by
  rw [swap2_mul_swap2, Matrix.one_mul]
  have h0 : noteBlock swap2 (1 : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
    ext ⟨ν, a, b⟩ ⟨ν', a', b'⟩
    by_cases h : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := h
      have : swap2 a a = 0 := by fin_cases a <;> simp [swap2]
      simp [noteBlock, this]
    · simp [noteBlock, h]
  rw [h0, Matrix.zero_mul]
  simp [noteBlock, Matrix.one_apply]

/-- The corrected formula is the Kronecker product block of `tensorHom`. -/
theorem fixedBlock_eq_kron (f g : Matrix (Fin 2) (Fin 2) ℚ) :
    fixedBlock f g
      = Matrix.kroneckerMap (fun a b : ℚ => a * b) (1 : Matrix (Fin 1) (Fin 1) ℚ)
          (Matrix.kroneckerMap (fun a b : ℚ => a * b) f g) := by
  ext ⟨ν, i, j⟩ ⟨ν', i', j'⟩
  have hν : ν = ν' := Subsingleton.elim _ _
  subst hν
  simp [fixedBlock, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The corrected formula IS multiplicative (this is `kroneckerMap_mul` in
disguise, and it is the block of `tensorHom`). -/
theorem fixedBlock_mul (f₁ f₂ g₁ g₂ : Matrix (Fin 2) (Fin 2) ℚ) :
    fixedBlock (f₁ * f₂) (g₁ * g₂) = fixedBlock f₁ g₁ * fixedBlock f₂ g₂ := by
  rw [fixedBlock_eq_kron (f₁ * f₂) (g₁ * g₂), fixedBlock_eq_kron f₁ g₁,
    fixedBlock_eq_kron f₂ g₂, kroneckerMap_mul, kroneckerMap_mul, Matrix.one_mul]

end FusionCategory
