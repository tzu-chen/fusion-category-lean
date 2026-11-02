import FusionCategory.Basic

/-!
# Skeletal fusion systems (F-symbols) — Step 2

Reference: Vercleyen thesis §3; EGNO Ch. 7; `haagerup-odd/Coefficients.lean`.

A `FusionSystem` is the skeletal data of a fusion category over a field `k`:
a fusion ring `R` plus F-symbols satisfying the pentagon.  We keep the
multiplicity-free case first (`N i j k ∈ {0,1}`) and allow general
multiplicities via indexed families.

This file is a stub for Step 0/1.  The full pentagon with `F^{ijk}_l`
matrices is defined in Step 2 of `PLAN.md`.
-/

universe u

namespace FusionCategory

/-- Skeletal fusion system over a field `k` with underlying fusion ring `R`.

For Step 2 we record the underlying ring and the field together with
F-symbols.  In the multiplicity-free case `F^{a b c}_d(e,f) ∈ k` is
defined when `N a b e >0`, `N e c d >0`, `N b c f >0`, `N a f d >0`,
and is zero otherwise.  The pentagon axiom is

```
∑_h F^{a b c}_{g}(e,h) * F^{a h d}_{k}(f,i) * F^{b c d}_{h}(g,j)
  = ∑_h F^{a b f}_{k}(e,h) * F^{h c d}_{k}(g,i)
```

in Vercleyen §3.  We state a simplified version that is `decide`-able
for `k = ℂ` and trivial for group-theoretical examples.

The structure is intentionally minimal to keep `Basic.lean` the first
file to type-check; full F-matrix pentagon will be refined in Step 5
bridge to `PivotalCategory`.
-/
structure FusionSystem (n : ℕ) (k : Type u) [Field k] where
  ring : FusionRing n
  F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → k
  -- Pentagon axiom (simplified Vercleyen form).  For multiplicity-free
  -- rings the sums over intermediate `h` are finite and `decide`-able.
  pentagon : ∀ (a b c d e f g h : Fin n),
    (∑ i : Fin n, F a b c d e i * F a i d g h f * F b c g h i e) =
    (∑ i : Fin n, F a b f g e i * F i c d g h f)
  -- Normalization: F^{0 b c}_d = id and F^{a 0 c}_d = id etc.
  F_unit_left : ∀ (hn : 0 < n) (b c d e f : Fin n),
    F ⟨0, hn⟩ b c d e f = if e = b ∧ f = c then 1 else 0
  F_unit_right : ∀ (hn : 0 < n) (a b c d e f : Fin n),
    F a b ⟨0, hn⟩ d e f = if e = a ∧ f = b then 1 else 0

namespace FusionSystem

variable {n : ℕ} {k : Type u} [Field k] (S : FusionSystem n k)

/-- Underlying fusion ring. -/
abbrev toFusionRing : FusionRing n := S.ring

/-- F-symbol evaluated at given labels. -/
def FSymbol (a b c d e f : Fin n) : k := S.F a b c d e f

theorem pentagon_eq (a b c d e f g h : Fin n) :
    (∑ i : Fin n, S.F a b c d e i * S.F a i d g h f * S.F b c g h i e) =
    (∑ i : Fin n, S.F a b f g e i * S.F i c d g h f) :=
  S.pentagon a b c d e f g h

end FusionSystem

end FusionCategory
