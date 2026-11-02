# fusion-category-lean

Lean 4 formalizations for fusion categories and related constructions.

This repository is pinned to **Lean v4.33.1 / Mathlib v4.33.1** (`0df444a3`).

## Projects

### 1. `haagerup-odd/` — Cyclic Haagerup–Izumi at every odd order

Standalone Lake project extracted from [`tzu-chen/haagerup`](https://github.com/tzu-chen/haagerup) at `b4b618f` (checkpoint `c8-checkpoint-20260927`).

- Umbrella: `haagerup-odd/HaagerupIzumi.lean` → `exists_EGEquations_odd` (all odd `n`)
- 115 modules, ~24k lines, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`s
- Build: `cd haagerup-odd && lake exe cache get && lake build && lake env lean AxiomAudit.lean`
- Source manuscript: `hi_infinitude_expanded.tex` Ch.1–9 (Ch.10 reconstruction not formalized)
- See `haagerup-odd/README.md` and `haagerup-odd/PLAN.md` for layout and proof plan

Lean toolchain: `haagerup-odd/lean-toolchain` (`leanprover/lean4:v4.33.1`).

### 2. `FusionCategory/` — (planned) pivotal / spherical structures

Placeholder for the small project discussed in this workspace:
pivotal cover $\tilde{\cal C}=\{(X,f\mid f^{**}f=g)\}$, ${\rm Aut}^\otimes({\rm Id})\cong{\rm Hom}(U_{\cal C},k^\times)$ torsor, and ENO Prop.8.23 `pseudo-unitary → spherical`.
Intended to build on Mathlib PRs `#42150` (PivotalCategory) and `#39914-39922` (Perron-Frobenius).

## Repository layout

```
.
├── README.md                # this file
├── haagerup-odd/            # standalone odd-order Haagerup–Izumi Lake project
│   ├── HaagerupIzumi.lean
│   ├── HaagerupIzumi/
│   ├── lakefile.toml
│   └── docs/
├── FusionCategory/          # future work
└── docs/                    # umbrella docs
```

## Checking

Each subproject is independent. From repo root:

```sh
cd haagerup-odd && lake exe cache get && lake build
```

All projects share `v4.33.1` - do not bump `lean-toolchain` without updating `lake-manifest.json`.

## Citation

If using `haagerup-odd`, cite Huang, *Cyclic Haagerup–Izumi fusion categories at every odd order*, arXiv:2609.15986, and the commit `b4b618f`.
