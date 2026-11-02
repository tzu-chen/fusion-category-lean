
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs


/-!
# Mathlib patch: Perron–Frobenius — vendored from PF chain #39914–#39922

Until the PF chain merges, this file re-exports the available
`Matrix.IsIrreducible` API and declares the intended PF interface.

See `PLAN.md` §0.
-/

namespace FusionCategory.MathlibPatches

-- Placeholder: the intended exports are
-- `pft_irreducible`, `exists_positive_eigenvector`, `collatzWielandt`,
-- `spectralRadius` from the PF chain.
-- When `#39922` lands, delete this file and replace imports with
-- `Mathlib.LinearAlgebra.Matrix.PerronFrobenius.*`.

end FusionCategory.MathlibPatches