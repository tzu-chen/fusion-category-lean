
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic


/-!
# Mathlib patch: PivotalCategory — vendored from PR #42150

Until `leanprover-community/mathlib4#42150` (`PivotalCategory`) merges to
`master`, a byte-compatible copy lives here.  Currently a stub that
re-exports `RigidCategory` and declares the intended interface.

See `PLAN.md` §0.
-/

/-!
Vendor note: the real `PivotalCategory` is

```
class PivotalCategory (C : Type u) [Category C] [MonoidalCategory C]
  extends RigidCategory C where
  pivotalIso : (𝟭 C) ≅ doubleDualFunctor C
  -- + monoidality
```

We do not redefine `RigidCategory`.  When `#42150` lands, delete this
file and replace imports with `Mathlib.CategoryTheory.Monoidal.Rigid.Pivotal`.
-/

namespace FusionCategory.MathlibPatches

-- Placeholder: no definitions yet.  Importing this file is a no-op.

end FusionCategory.MathlibPatches