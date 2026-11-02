
import FusionCategory.Basic


/-!
# PF-dimension via Perron–Frobenius — Step 1 (analysis half)

Reference: ENO §2.5, §8.4; Perron–Frobenius `pft_irreducible`,
`exists_positive_eigenvector`, `spectralRadius`.

This file will import the vendored `PerronFrobenius` patches
(`MathlibPatches/PerronFrobenius.lean`) once the upstream PRs
`#39914`–`#39922` are available.  For Step 1 we only declare the
interface: FPdim as the PF eigenvector of `N_i`.

Stub for Step 0/1.
-/

namespace FusionCategory

-- PFDim existence, uniqueness, spectral radius lemmas — to be proved in Step 1 PFDim.lean
-- using vendored PF chain.  For now `FusionRing.FPData` in `Basic.lean`
-- carries the data axiomatically.

end FusionCategory