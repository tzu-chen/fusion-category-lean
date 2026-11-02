import FusionCategory.Basic

/-!
# PF-dimension via Perron–Frobenius — Step 1 (analysis half)

Reference: ENO §2.5, §8.4; Perron–Frobenius `pft_irreducible`,
`exists_positive_eigenvector`, `spectralRadius`.

This file will import the vendored `PerronFrobenius` patches
(`MathlibPatches/PerronFrobenius.lean`) once the upstream PRs
`#39914`–`#39922` are available.  For Step 1 we only declare the
interface: FPdim as the PF eigenvector of `N_i`.

For now `FusionRing.FPData` in `Basic.lean` carries the data
axiomatically.  This file proves elementary consequences that do not
require the full PF theorem.
-/

namespace FusionCategory

section PFDim

variable {n : ℕ} {R : FusionRing n} (h : R.FPData)

/-- FPdim is positive. -/
theorem fpdim_pos (i : Fin n) : 0 < h.fpdim i := h.pos i

/-- FPdim of the unit is 1. -/
theorem fpdim_unit (hn : 0 < n) : h.fpdim ⟨0, hn⟩ = 1 := h.unit_one hn

/-- FPdim respects duals. -/
theorem fpdim_dual (i : Fin n) : h.fpdim (R.dual i) = h.fpdim i := h.dual_eq i

/-- Global FP dimension is positive when `n>0`. -/
theorem globalFPdim_pos (hn : 0 < n) : 0 < h.globalDim := h.globalDim_pos hn

/-- FPdim eigenvector equation in `mulVec` form. -/
theorem fpdim_eigenvector_mulVec (i : Fin n) :
    (R.fusionMatrix i)ᵀ *ᵥ h.fpdim = (h.fpdim i) • h.fpdim := by
  have heig := h.eigenvector i
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, FusionRing.fusionMatrix_apply,
    Pi.smul_apply, smul_eq_mul]
  exact heig k

end PFDim

end FusionCategory
