import FusionCategory.System
import Mathlib.Data.ZMod.Basic

/-!
# `Vec^ω_{Z/3}`: a witness with `i* ≠ i` and a non-trivial associator

The two witnesses in `System.lean` are `Vec_{Z/2}` with the trivial cocycle
(`F ≡ 1`) and with the non-trivial one (`F = -1` on the all-`g` block).  Both
have `i* = i` for every simple, so neither can see the difference between the
two associator entries `F^{i i* i}_i(0,0)` and `F^{i* i i*}_{i*}(0,0)` that the
right snake involves.  This file supplies a witness with `g* = g² ≠ g` and
`F ≠ 1` everywhere it can be: the pointed category `Vec^ω_{Z/3}` for the
non-trivial 3-cocycle `ω(a,b,c) = ζ^(a·⌊(b+c)/3⌋)`, where `ζ` is a primitive
cube root of unity.

The field is `ZMod 7`, where `ζ = 2` is a primitive cube root of unity
(`2^3 = 1`, `1 + 2 + 4 = 0`).  Nothing in the axioms asks for characteristic
zero, and working over a finite field makes every axiom a *closed* decidable
statement, so the whole instance is checked by the kernel (`decide`) rather
than by `norm_num` over the reals.  The duality normalisation is forced by the
snakes: `κ g = ω(g²,g,g²) = ζ² = 4` and `κ g² = ω(g,g²,g) = ζ = 2`, which is
the general formula `κ i = ω(i*,i,i*)` and satisfies the left snake because
`ω(i,i*,i)·ω(i*,i,i*) = 1` is the cocycle identity.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

namespace FusionCategory.Examples

namespace Z3Pointed

/-- `ZMod 7` is a field; its primality is proved rather than assumed. -/
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive cube root of unity in `ZMod 7`. -/
def zeta : ZMod 7 := 2

theorem zeta_sq : zeta ^ 2 = 4 := by decide

theorem zeta_add_self_add_one : zeta * zeta + zeta + 1 = 0 := by decide

theorem zeta_ne_zero : zeta ≠ 0 := by decide

/-- `N a b c = 1` iff `c = a + b` in `Z/3`. -/
def N (a b c : Fin 3) : ℕ := if (a.val + b.val) % 3 = c.val then 1 else 0

/-- Duality is negation in `Z/3`, so `g* = g² ≠ g`. -/
def dual (a : Fin 3) : Fin 3 := ⟨(3 - a.val) % 3, Nat.mod_lt _ (by decide)⟩

theorem dual_involutive : ∀ i : Fin 3, dual (dual i) = i := by decide

theorem dual_zero : ∀ (hn : 0 < 3), dual ⟨0, hn⟩ = ⟨0, hn⟩ := fun _ => rfl

theorem left_unit : ∀ (hn : 0 < 3) (i j : Fin 3),
    N ⟨0, hn⟩ i j = if i = j then 1 else 0 := by
  intro _ i j
  fin_cases i <;> fin_cases j <;> decide

theorem right_unit : ∀ (hn : 0 < 3) (i j : Fin 3),
    N i ⟨0, hn⟩ j = if i = j then 1 else 0 := by
  intro _ i j
  fin_cases i <;> fin_cases j <;> decide

theorem dual_coeff : ∀ (hn : 0 < 3) (i j : Fin 3),
    N i j ⟨0, hn⟩ = if j = dual i then 1 else 0 := by
  intro _ i j
  fin_cases i <;> fin_cases j <;> decide

theorem associativity : ∀ i j k l : Fin 3,
    (∑ p : Fin 3, (N i j p : ℕ) * N p k l) =
      (∑ q : Fin 3, (N j k q : ℕ) * N i q l) := by decide

theorem dual_symm : ∀ i j k : Fin 3, N i j k = N (dual j) (dual i) (dual k) := by
  decide

/-- The fusion ring of `Z/3`. -/
def ring : FusionRing 3 where
  N := N
  dual := dual
  dual_involutive := dual_involutive
  dual_zero := dual_zero
  left_unit := left_unit
  right_unit := right_unit
  dual_coeff := dual_coeff
  associativity := associativity
  dual_symm := dual_symm

/-- The non-trivial 3-cocycle `ω(a,b,c) = ζ^(a·⌊(b+c)/3⌋)`, extended by zero off
the fusion channels.  On a supported entry the exponent is `0`, `1` or `2`. -/
def F (a b c d e f : Fin 3) : ZMod 7 :=
  if 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d then
    zeta ^ (a.val * ((b.val + c.val) / 3))
  else 0

/-- The inverse associator: every block is `1 × 1`, so this is the reciprocal
of the corresponding `F` entry. -/
def Finv (a b c d f e : Fin 3) : ZMod 7 :=
  if 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d then
    (zeta ^ (a.val * ((b.val + c.val) / 3)))⁻¹
  else 0

/-- `Vec^ω_{Z/3}` as a skeletal fusion system over `ZMod 7`. -/
def system : FusionSystem 3 (ZMod 7) where
  ring := ring
  mult_free := by
    intro i j kk
    fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide
  F := F
  F_support := by
    intro a b c d e f h
    simp only [F]
    exact if_neg h
  pentagon := by
    intro a b c d e i j r x
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases e <;> fin_cases i <;> fin_cases j <;> fin_cases r <;>
      fin_cases x <;> decide
  F_unit_left := by
    intro _ b c d f _
    fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases f <;>
      decide
  F_unit_right := by
    intro _ a b d e _
    fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
      decide
  Finv := Finv
  Finv_support := by
    intro a b c d f e h
    simp only [Finv]
    exact if_neg (fun hc => h ⟨hc.2.2.1, hc.2.2.2, hc.1, hc.2.1⟩)
  Finv_comp := by
    intro a b c d f' f _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases f' <;> fin_cases f <;> decide
  F_comp_inv := by
    intro a b c d e' e _ _ _ _
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      fin_cases e' <;> fin_cases e <;> decide
  ev := fun _ => 1
  coev := fun i => if i = 0 then 1 else if i = 1 then 4 else 2
  ev_ne_zero := fun _ => one_ne_zero
  coev_ne_zero := by
    intro i
    fin_cases i <;> decide
  snake_left := by
    intro _ i
    fin_cases i <;> decide
  snake_right := by
    intro _ i
    fin_cases i <;> decide
  J := fun _ _ _ => 1
  J_ne_zero := fun _ _ _ _ => one_ne_zero
  J_unit_left := fun _ _ => rfl
  J_unit_right := fun _ _ => rfl
  J_dual := fun _ _ => rfl
  J_coherent := by
    intro a b c d e f _ _ _ _
    simp

/-- The duality normalisation on the non-unit simples: `κ g = ζ²`, `κ g² = ζ`.
This is the general formula `κ i = ω(i*,i,i*)`, and it differs from
`1/ω(i,i*,i)` by the cocycle identity — the two factors are `ζ²` and `ζ`. -/
theorem kappa_g : system.kappa 1 = 4 := by
  simp [FusionSystem.kappa, system]

theorem kappa_g_sq : system.kappa 2 = 2 := by
  simp [FusionSystem.kappa, system]

/-- The two associator entries that a `Vec_{Z/2}` witness cannot separate do
differ here: `F^{g g² g}_g(0,0) = ω(g,g²,g) = ζ` while
`F^{g² g g²}_{g²}(0,0) = ω(g²,g,g²) = ζ² = ζ⁻¹`. -/
theorem fits_differ :
    F 1 2 1 1 0 0 = zeta ∧ F 2 1 2 2 0 0 = zeta ^ 2 := by
  constructor <;> decide

end Z3Pointed

end FusionCategory.Examples
