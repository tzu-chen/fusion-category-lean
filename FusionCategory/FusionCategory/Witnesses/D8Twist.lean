/-
Census, `D8` row: kernel-checked arithmetic (delegation batch B3c).

The non-abelian row of `pointed_census.py`.  `D8 = <r,s | r^4 = s^2 = 1, s r s = r^-1>`,
written `r^i s^j`, so that `(r^i s^j)(r^k s^l) = r^{i + (-1)^j k} s^{j+l}`; and

  `omega(x,y,z) = (-1)^{i(x) j(y) i(z)}`   (the cup product `alpha u beta u alpha`,
                                            `alpha = r`-exponent mod 2, `beta = s`-exponent)

with values in `mu_2`, carried as exponents in `ZMod 2`.  Unlike the `S3` family (where
`kappa` is the sign character and the honest twist is therefore trivial) this datum has
`kappa_g = -1` exactly at `r^2` and `r^3 s`, i.e. `kappa` is *not* a character: `J = 1`
fails (M)/(K) there and `J = delta(kappa)` does not.

The pentagon is the repo's (`System.lean`) convention, as in `Z3sqTwist.lean`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace CensusD8

/-- The underlying set of `D8`, as pairs `r^i s^j`. -/
abbrev G : Type := ZMod 4 × ZMod 2

/-- Multiplication: `(r^i s^j)(r^k s^l) = r^{i + (-1)^j k} s^{j+l}`. -/
def mul (x y : G) : G := (x.1 + (if x.2 = 0 then y.1 else -y.1), x.2 + y.2)

/-- Inversion. -/
def inv (x : G) : G := (if x.2 = 0 then -x.1 else x.1, x.2)

/-- The identity `1 = r^0 s^0`. -/
def e : G := (0, 0)

/-- The `r`-exponent read in `Z/2`. -/
def ii (x : G) : ZMod 2 := (x.1.val : ZMod 2)

/-! ## It is a group (needed only so that the statements mean what they say) -/

theorem mul_assoc : ∀ x y z : G, mul (mul x y) z = mul x (mul y z) := by decide
theorem mul_e_left : ∀ x : G, mul e x = x := by decide
theorem mul_e_right : ∀ x : G, mul x e = x := by decide
theorem mul_inv : ∀ x : G, mul x (inv x) = e := by decide
theorem inv_mul : ∀ x : G, mul (inv x) x = e := by decide

/-! ## The associator -/

/-- `omega = (-1)^{i(x) j(y) i(z)}`, as an exponent in `ZMod 2`. -/
def om (x y z : G) : ZMod 2 := ii x * y.2 * ii z

/-- **The pentagon** in `System.lean`'s convention, on all `4096` quadruples. -/
theorem pentagon : ∀ x y z w : G,
    om x y z + om x (mul y z) w + om y z w = om (mul x y) z w + om x y (mul z w) := by
  decide

/-- `omega` is not identically `1`. -/
theorem om_ne_one : ∃ x y z : G, om x y z ≠ 0 := by decide

/-! ## The duality normalisation -/

def kap (g : G) : ZMod 2 := - om g (inv g) g

theorem snake_left : ∀ g : G, kap g + om g (inv g) g = 0 := by decide
theorem snake_right : ∀ g : G, kap g - om (inv g) g (inv g) = 0 := by decide
theorem kappa_neg : ∀ g : G, kap g + kap (inv g) = 0 := by decide

/-- Closed form: `kappa_g = -1` exactly when `g` is a reflection with odd `r`-exponent,
i.e. at `r s` and `r^3 s`. -/
theorem kappa_formula : ∀ g : G, kap g = ii g * g.2 := by decide

/-- `kappa` is **not** a character of `D8`. -/
theorem kappa_not_character : ∃ a b : G, kap (mul a b) ≠ kap a + kap b := by decide

/-! ## The four `J` laws and the two candidate twists -/

def J (a b : G) : ZMod 2 := kap a + kap b - kap (mul a b)
def J1 (_ _ : G) : ZMod 2 := 0

theorem J_unit_left : ∀ b : G, J e b = 0 := by decide
theorem J_unit_right : ∀ a : G, J a e = 0 := by decide
theorem J_dual : ∀ a : G, J a (inv a) = 0 := by decide
theorem J_coherent : ∀ a b c : G, J a b + J (mul a b) c = J b c + J a (mul b c) := by
  decide

theorem J1_laws : (∀ b : G, J1 e b = 0) ∧ (∀ a : G, J1 a e = 0)
    ∧ (∀ a : G, J1 a (inv a) = 0)
    ∧ (∀ a b c : G, J1 a b + J1 (mul a b) c = J1 b c + J1 a (mul b c)) := by
  decide

/-- The honest twist is not the trivial one. -/
theorem honest_ne_trivial : ∃ a b : G, J a b ≠ J1 a b := by decide

/-- `J = 1` fails (M)/(K) on some channel. -/
theorem trivial_fails_K : ∃ a b : G, J1 a b ≠ kap a + kap b - kap (mul a b) := by
  decide

theorem honest_satisfies_K : ∀ a b : G, J a b = kap a + kap b - kap (mul a b) :=
  fun _ _ => rfl

/-! ## The pivotal structure `p = 1/kappa` -/

theorem p_pivotal : ∀ a b : G, (-kap (mul a b)) = J a b + (-kap a) + (-kap b) := by
  decide

/-- Over `mu_2` sphericity is automatic, so every pivotal structure is spherical. -/
theorem spherical : ∀ g : G, kap (inv g) = 2 * (-kap g) + kap g := by decide

theorem dim_eq_one : ∀ g : G, (-kap g) + kap g = 0 := by decide

end CensusD8

#print axioms CensusD8.mul_assoc
#print axioms CensusD8.pentagon
#print axioms CensusD8.kappa_formula
#print axioms CensusD8.kappa_not_character
#print axioms CensusD8.J_coherent
#print axioms CensusD8.trivial_fails_K
#print axioms CensusD8.p_pivotal
#print axioms CensusD8.spherical
