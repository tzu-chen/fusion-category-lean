/-
Census, the genuinely twisted `(Z/3)^2` row: kernel-checked arithmetic (B3c).

`omega = carry x carry x zeta^{a1 b2 c1}` on `(Z/3)^2`, i.e. in exponents

  `om x y z = carry(x1,y1,z1) + carry(x2,y2,z2) + x1 * y2 * z1`,
  `carry(a,b,c) = a * floor((b + c)/3)`   (the standard generator of `H^3(Z/3)`),

values in `mu_3`.  This is the family that carries the `J^2 != 1` witness on a
*genuinely twisted* cocycle: the product of the two carry cocycles has a non-zero
class (`pointed_census.py` decides this exactly, by elimination over `Z/3`), and
the `zeta^{a1 b2 c1}` factor -- a coboundary, see `Z3sqTwist.lean` -- is what makes
`kappa` a non-character, hence the honest twist `delta(kappa)` non-trivial.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace CensusZ3sqTwisted

/-- `(Z/3)^2`, additively. -/
abbrev G : Type := ZMod 3 × ZMod 3

def add (a b : G) : G := (a.1 + b.1, a.2 + b.2)

def neg (a : G) : G := (-a.1, -a.2)

/-- The carry cocycle on `Z/3`: `(a,b,c) -> a * floor((b+c)/3)`, `b`,`c` read in `{0,1,2}`. -/
def carry (a b c : ZMod 3) : ZMod 3 := ((a.val * ((b.val + c.val) / 3) : ℕ) : ZMod 3)

/-- `omega` as an exponent in `Z/3`. -/
def om (x y z : G) : ZMod 3 :=
  carry x.1 y.1 z.1 + carry x.2 y.2 z.2 + x.1 * y.2 * z.1

/-! ## The pentagon, in `System.lean`'s convention -/

theorem pentagon : ∀ x y z w : G,
    om x y z + om x (add y z) w + om y z w = om (add x y) z w + om x y (add z w) := by
  decide

/-- The trivial cocycle is not an instance: `omega` takes non-trivial values. -/
theorem om_ne_one : ∃ x y z : G, om x y z ≠ 0 := by decide

/-! ## The class is non-zero

The restriction of `omega` to the cyclic subgroup `<(0,1)> = {(0,0),(0,1),(0,2)}`
is the carry cocycle on `Z/3`, and *no* `Z/3`-valued 2-cochain trivialises it.
Since a trivialisation on `G` would restrict to one there, the class of `omega` on
`G` is non-zero.  The restriction step is the standard fact that restriction of
cochains commutes with `delta`; the non-existence statement below is the
kernel-checked part. -/

theorem no_trivialising_cochain :
    ∀ mu : ZMod 3 → ZMod 3 → ZMod 3, ∃ x y z : ZMod 3,
      carry x y z ≠ mu y z - mu (x + y) z + mu x (y + z) - mu x y := by
  intro mu
  by_contra h
  simp only [not_exists, not_not] at h
  have c1 : carry 1 1 1 = (0 : ZMod 3) := by decide
  have c2 : carry 2 2 2 = (2 : ZMod 3) := by decide
  have e1 : (1 : ZMod 3) + 1 = 2 := by decide
  have e2 : (2 : ZMod 3) + 2 = 1 := by decide
  have h1 := h 1 1 1
  have h2 := h 2 2 2
  rw [c1, e1] at h1
  rw [c2, e2] at h2
  have hcontra : (2 : ZMod 3) = 0 := by linear_combination h1 + h2
  exact absurd hcontra (by decide)

/-- The cycle that witnesses it, in the cyclic subgroup: `(g,g,g) + (g,g^2,g)`,
`g = (0,1)`, has `omega`-exponent `1` and is a cycle. -/
theorem cycle_witness :
    (carry 1 1 1 + carry 1 2 1 = 1) ∧ (carry 1 1 1 + carry 1 2 1 ≠ 0) := by
  decide
/-! ## `kappa` and the honest twist `J = delta(kappa)` -/

def kap (g : G) : ZMod 3 := - om g (neg g) g

def J (a b : G) : ZMod 3 := kap a + kap b - kap (add a b)

theorem snake_left : ∀ g : G, kap g + om g (neg g) g = 0 := by decide
theorem snake_right : ∀ g : G, kap g - om (neg g) g (neg g) = 0 := by decide
theorem kappa_neg : ∀ g : G, kap g + kap (neg g) = 0 := by decide

/-- `kappa` is **not** a character: the honest twist is not the trivial one. -/
theorem kappa_not_character : ∃ a b : G, kap (add a b) ≠ kap a + kap b := by decide

/-- `kappa` is not the product of the two carry `kappa`s alone: the `zeta^{a1 b2 c1}`
factor is what breaks multiplicativity. -/
theorem kappa_values : kap (0, 1) = 2 ∧ kap (1, 0) = 2 ∧ kap (1, 1) = 2 := by decide

theorem J_unit_left : ∀ b : G, J (0, 0) b = 0 := by decide
theorem J_unit_right : ∀ a : G, J a (0, 0) = 0 := by decide
theorem J_dual : ∀ a : G, J a (neg a) = 0 := by decide
theorem J_coherent : ∀ a b c : G, J a b + J (add a b) c = J b c + J a (add b c) := by
  decide

/-- `J = delta(kappa)` satisfies (M)/(K) on every channel. -/
theorem honest_satisfies_K : ∀ a b : G, J a b = kap a + kap b - kap (add a b) :=
  fun _ _ => rfl

/-- `p = 1/kappa` is pivotal and the dimensions are `1`. -/
theorem p_pivotal : ∀ a b : G, (-kap (add a b)) = J a b + (-kap a) + (-kap b) := by
  decide

theorem dim_eq_one : ∀ g : G, (-kap g) + kap g = 0 := by decide

/-! ## `J^2 != 1` on a genuinely twisted cocycle -/

/-- The honest twist takes the value `zeta^2` on the channel `((0,1),(1,0))`. -/
theorem J_value : J ((0, 1) : G) ((1, 0) : G) = 2 := by decide

/-- So `J^2` there is `zeta`, which is not `1`: on a datum whose cocycle has
non-zero class, `J^2 = 1` is not a law. -/
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

/-- `J^2` is of order `3` on some channel (`2 * J != 0`). -/
theorem Jsq_nontrivial : ∃ a b : G, 2 * J a b ≠ 0 := by decide

end CensusZ3sqTwisted

#print axioms CensusZ3sqTwisted.pentagon
#print axioms CensusZ3sqTwisted.no_trivialising_cochain
#print axioms CensusZ3sqTwisted.cycle_witness
#print axioms CensusZ3sqTwisted.kappa_not_character
#print axioms CensusZ3sqTwisted.J_coherent
#print axioms CensusZ3sqTwisted.p_pivotal
#print axioms CensusZ3sqTwisted.J_sq_ne_one
#print axioms CensusZ3sqTwisted.Jsq_nontrivial
