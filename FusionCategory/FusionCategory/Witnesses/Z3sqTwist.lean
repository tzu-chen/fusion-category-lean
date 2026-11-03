/-
Census, `(Z/3)^2` row: kernel-checked arithmetic (delegation batch B3c).

This file kernel-checks the arithmetic of the `Vec^omega_(Z/3)^2` row of
`pointed_census.py`, the row on which the honest twist satisfies `J^2 != 1`.
Nothing here is a theorem about fusion categories: it is the finite arithmetic
of the datum, checked exactly with `decide` (no `sorry`, no `native_decide`).

The datum.  `G = (Z/3)^2`, written additively, `omega(a,b,c) = zeta^{a1 b2 c1}`
with `zeta` a primitive cube root of unity.  Values are carried as exponents in
`ZMod 3`, so that `omega` is the function `om` below and multiplication of
values is addition of exponents.  The pentagon of `System.lean` on a pointed
datum reads, in exponents,

  `om x y z + om x (y+z) w + om y z w = om (x+y) z w + om x y (z+w)`   (`(R)`)

and that is `pentagon` below, on all `9^4 = 6561` quadruples.

Why the exponents and not complex numbers.  The map `e : ZMod 3 -> mu_3`,
`e k = zeta^k`, is an isomorphism of groups, so an exponent identity is a value
identity; the one place where the value matters (the order of `J^2`) is
discharged at the end in `C` itself, for the single channel that witnesses it.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace CensusZ3sq

/-- The group `(Z/3)^2`, additively. -/
abbrev G : Type := ZMod 3 × ZMod 3

/-- Addition in `(Z/3)^2`. -/
def add (a b : G) : G := (a.1 + b.1, a.2 + b.2)

/-- The inverse (negation) in `(Z/3)^2`. -/
def neg (a : G) : G := (-a.1, -a.2)

/-- `omega(a,b,c) = zeta^{a1 b2 c1}`, as an exponent in `ZMod 3`. -/
def om (a b c : G) : ZMod 3 := a.1 * b.2 * c.1

/-- `kappa_g = 1 / omega(g, g*, g)`, the duality normalisation fixed by the
left snake (`System.lean`'s `snake_left`). -/
def kap (g : G) : ZMod 3 := - om g (neg g) g

/-- The honest double-dual twist `J = delta(kappa)` on the channel `(a,b)`,
as an exponent. -/
def J (a b : G) : ZMod 3 := kap a + kap b - kap (add a b)

/-- The trivial twist `J = 1`, as an exponent. -/
def J1 (_ _ : G) : ZMod 3 := 0

/-! ## The associator: the pentagon, in the convention of `System.lean` -/

/-- **The pentagon.**  On all `6561` quadruples. -/
theorem pentagon : ∀ a b c d : G,
    om a b c + om a (add b c) d + om b c d
      = om (add a b) c d + om a b (add c d) := by
  decide

/-- The old census script checked the *inverse* associator's cocycle condition;
on a genuine `mu_3`-valued cocycle that condition is **false**.  Recorded so
that the repair cannot silently revert. -/
theorem old_convention_fails : ∃ a b c d : G,
    om b c d + om a (add b c) d + om a b (add c d)
      ≠ om (add a b) c d + om a b c := by
  decide

/-! ## The duality normalisation `kappa` -/

/-- The left snake: `kappa_g omega(g,g*,g) = 1`. -/
theorem snake_left : ∀ g : G, kap g + om g (neg g) g = 0 := by
  decide

/-- The right snake: `kappa_g = omega(g*,g,g*)` for a `1 x 1` block. -/
theorem snake_right : ∀ g : G, kap g - om (neg g) g (neg g) = 0 := by
  decide

/-- `kappa_g kappa_{g*} = 1`. -/
theorem kappa_neg : ∀ g : G, kap g + kap (neg g) = 0 := by
  decide

/-- Closed form of `kappa`: `kappa_{(a1,a2)} = zeta^{a1^2 a2}`. -/
theorem kappa_formula : ∀ g : G, kap g = g.1 * g.1 * g.2 := by
  decide

/-- `kappa` is **not** a character of `(Z/3)^2`, which is exactly why the honest
twist `delta(kappa)` is not `1`. -/
theorem kappa_not_character : ∃ a b : G, kap (add a b) ≠ kap a + kap b := by
  decide

/-- Consequently `delta(kappa)` is not the trivial twist. -/
theorem honest_ne_trivial : ∃ a b : G, J a b ≠ J1 a b := by
  decide

/-! ## The four `J` laws -/

theorem J_unit_left : ∀ b : G, J (0, 0) b = 0 := by decide

theorem J_unit_right : ∀ a : G, J a (0, 0) = 0 := by decide

/-- `J_dual`: `J i i* 1 = 1` on the coevaluation channel. -/
theorem J_dual : ∀ a : G, J a (neg a) = 0 := by decide

/-- `J_coherent`, with all support conditions automatic for a pointed datum. -/
theorem J_coherent : ∀ a b c : G,
    J a b + J (add a b) c = J b c + J a (add b c) := by
  decide

/-- The trivial twist satisfies the same four laws: they do not determine `J`. -/
theorem J1_laws : (∀ b : G, J1 (0, 0) b = 0) ∧ (∀ a : G, J1 a (0, 0) = 0)
    ∧ (∀ a : G, J1 a (neg a) = 0)
    ∧ (∀ a b c : G, J1 a b + J1 (add a b) c = J1 b c + J1 a (add b c)) := by
  decide

/-- And (M)/(K) fails for the trivial twist: no `p` repairs it, since `(M)` does
not involve `p` at all -- `J a b = kappa_a kappa_b / kappa_{a+b}` is false there. -/
theorem trivial_fails_K : ∃ a b : G, J1 a b ≠ kap a + kap b - kap (add a b) := by
  decide

/-- The honest twist satisfies (M)/(K) on every channel, by construction. -/
theorem honest_satisfies_K : ∀ a b : G, J a b = kap a + kap b - kap (add a b) :=
  fun _ _ => rfl

/-! ## The pivotal structure `p = 1/kappa` -/

/-- `p_mon`: `p_{a+b} = J(a,b) p_a p_b` with `p = 1/kappa`. -/
theorem p_pivotal : ∀ a b : G,
    (-kap (add a b)) = J a b + (-kap a) + (-kap b) := by
  decide

/-- Sphericity: `dim g* = dim g` for `dim g = p_g kappa_g`. -/
theorem spherical : ∀ g : G, kap (neg g) = 2 * (-kap g) + kap g := by
  decide

/-- `dim = FPdim = 1` on every simple. -/
theorem dim_eq_one : ∀ g : G, (-kap g) + kap g = 0 := by
  decide

/-! ## `J^2 != 1`: the witness -/

/-- The honest twist takes the value `zeta^2` on the channel `((0,1),(1,0))`. -/
theorem J_value : J ((0, 1) : G) ((1, 0) : G) = 2 := by
  decide

/-- `J^2` is not trivial on that channel: the value there is `zeta^2`, whose
square is `zeta^4 = zeta != 1` for any primitive cube root of unity `zeta`. -/
theorem J_sq_ne_one (zeta : ℂ) (h3 : zeta ^ 3 = 1) (h1 : zeta ≠ 1) :
    (zeta ^ (J ((0, 1) : G) ((1, 0) : G)).val) ^ 2 ≠ 1 := by
  have h2 : (J ((0, 1) : G) ((1, 0) : G)).val = 2 := by decide
  rw [h2]
  intro h
  have h4 : zeta ^ 4 = 1 := by
    have : (zeta ^ 2) ^ 2 = zeta ^ 4 := by ring
    rwa [this] at h
  have hsplit : zeta ^ 4 = zeta ^ 3 * zeta := by ring
  rw [hsplit, h3, one_mul] at h4
  exact h1 h4

/-- The values of `J^2` are not confined to `1`: `2 * J` is non-zero somewhere,
i.e. `J^2` is a cube root of unity of order `3` on some channel. -/
theorem Jsq_nontrivial : ∃ a b : G, 2 * J a b ≠ 0 := by
  decide

/-! ## The proposal's example is a *coboundary*

`omega = zeta^{a1 b2 c1}` on `(Z/3)^2` is gauge-trivial: here is an explicit
normalised 2-cochain `mu` with `delta mu = omega`.  It depends only on `(a, b.1)`,
so it is tabulated.  Consequence: as a pointed category this datum is
`Vec_(Z/3)^2` in a gauge in which `kappa` is *not* a character, so its `J^2 != 1`
is a statement about that datum and not about the category -- the genuinely
twisted witness is in `Z3sqTwisted.lean`. -/

/-- An explicit `mu` with `delta mu = omega`, tabulated by `(a.1.val, a.2.val, b.1.val)`. -/
def mu (a b : G) : ZMod 3 :=
  match a.1.val, a.2.val, b.1.val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 0, 2, 0 => 0
  | 0, 2, 1 => 2
  | 0, 2, 2 => 2
  | 1, 0, 0 => 0
  | 1, 0, 1 => 2
  | 1, 0, 2 => 2
  | 1, 1, 0 => 0
  | 1, 1, 1 => 2
  | 1, 1, 2 => 1
  | 1, 2, 0 => 0
  | 1, 2, 1 => 2
  | 1, 2, 2 => 0
  | 2, 0, 0 => 0
  | 2, 0, 1 => 2
  | 2, 0, 2 => 0
  | 2, 1, 0 => 0
  | 2, 1, 1 => 1
  | 2, 1, 2 => 0
  | 2, 2, 0 => 0
  | 2, 2, 1 => 0
  | 2, 2, 2 => 0
  | _, _, _ => 0

/-- `omega = delta mu`: the class of `omega` is zero. -/
theorem om_is_coboundary : ∀ x y z : G,
    om x y z = mu y z - mu (add x y) z + mu x (add y z) - mu x y := by
  decide

/-- `mu` is normalised, which is what makes it a legitimate gauge. -/
theorem mu_normalised : ∀ a b : G, mu a (0, 0) = 0 ∧ mu (0, 0) b = 0 := by
  decide

end CensusZ3sq

#print axioms CensusZ3sq.pentagon
#print axioms CensusZ3sq.old_convention_fails
#print axioms CensusZ3sq.kappa_formula
#print axioms CensusZ3sq.kappa_not_character
#print axioms CensusZ3sq.J_coherent
#print axioms CensusZ3sq.p_pivotal
#print axioms CensusZ3sq.spherical
#print axioms CensusZ3sq.J_value
#print axioms CensusZ3sq.J_sq_ne_one
#print axioms CensusZ3sq.Jsq_nontrivial
#print axioms CensusZ3sq.om_is_coboundary
#print axioms CensusZ3sq.mu_normalised
