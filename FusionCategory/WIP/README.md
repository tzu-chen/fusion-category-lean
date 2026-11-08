# WIP — graduated: the pentagon landed as `FusionCategory.PentagonLHS`

**This directory's file is gone by design.** `WIP/PentagonLHS.lean` passed its
review gates and graduated to the package module
`FusionCategory/FusionCategory/PentagonLHS.lean` (imported by the umbrella,
in the audit manifest, `tools/ci-chain.sh` green). What it proved:

- `LHS_entry` — the three-factor side of the pentagon, entrywise;
- `pentagonShapeHom_holds : PentagonShapeHom S` — the capstone, via
  `LHS_entry` + `U_entry` + `S.pentagon` at `(a, b, Cc, Dw, g, f, h, d, e)`;
- `reconIsFusionCanonical_recon` — WP2 closes: the reconstruction from a
  `FusionSystem` is a fusion category.

The state record (verification, corroboration by three independent
solutions, and the engine notes) moved to `PLAN.md`'s "WP2 closed" section.
This directory is empty of code; a future WIP file would come with its own
README in the same style as the one this replaced.
