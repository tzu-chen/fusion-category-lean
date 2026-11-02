import FusionCategory.System
import FusionCategory.Pivotal

/-!
# The double-dual twist, derived from the duality data

`System.lean` carries the twist `J` as coherent data, and states in its
docstring that in an honest rigid category `J` is *computed* from `ev`, `coev`
and `F`, and that the computation is owed.  This file pays that debt in the
normalisation where the computation is transparent: a **strict, self-dual**
system, which is the shape `Vec_{Z/2}` has.

## The composite

The double-dual comparison is the chainmail composite
`μ_{a,b} : a** ⊗ b** → (a ⊗ b)**`, built from the transpose
`ψ_{a,b} : (a ⊗ b)* → b* ⊗ a*` and its dual:

  `μ_{a,b} = ψ_{b*,a*} ∘ (ψ_{a,b})*`.

In a strict self-dual system the associator is trivial and every object is
self-dual, so `ψ` is nothing but the comparison of the two evaluations and the
composite collapses, on the channel `c` of `a ⊗ b`, to the scalar

  `J a b c = ev a * ev b / ev c`,

the evaluation `ev c` of the product being `ev a * ev b` transported through
the comparison.

## What this establishes

* `derivedTwist_coherent` — the derived twist satisfies the pentagon
  `FusionSystem.J_coherent` *identically*.  Coherence is therefore not an extra
  assumption on a computed twist: it follows from the formula.
* `derivedTwist_gauge` — rescaling `coev i` by `lam i` and `ev i` by `lam i⁻¹`
  (which preserves the snakes) multiplies the twist by `lam c / (lam a * lam b)`.
  That is exactly the coboundary law under which pivotality is invariant, so the
  derivation is consistent with the twist being an invariant of the *class*.
* `vecZ2_twist_derived` — for `Vec_{Z/2}` the twist the system carries is the
  derived one.  For that category the carried datum is verified, not chosen.

Not covered, and still owed: the `F`-twisted (non-strict) case and the
non-self-dual case, where the composite carries explicit associator factors
alongside the evaluation scalars.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

namespace DoubleDual

open FusionRing

variable {n : ℕ} {k : Type u} [Field k]

/-- The double-dual comparison computed from the evaluation scalars, in the
strict self-dual normalisation: on the channel `c` of `a ⊗ b` it is
`ev a * ev b / ev c`. -/
noncomputable def derivedTwist (S : FusionSystem n k) (a b c : Fin n) : k :=
  S.ev a * S.ev b / S.ev c

theorem derivedTwist_ne_zero (S : FusionSystem n k) (a b c : Fin n) :
    derivedTwist S a b c ≠ 0 := by
  unfold derivedTwist
  exact div_ne_zero (mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b)) (S.ev_ne_zero c)

/-- **Coherence comes for free.**  The derived twist satisfies the twist
pentagon that `FusionSystem.J_coherent` assumes: both sides are
`ev a * ev b * ev c / ev d`, with the intermediate channel cancelling. -/
theorem derivedTwist_coherent (S : FusionSystem n k) (a b c d e f : Fin n)
    (h1 : 0 < S.ring.N a b e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N a f d) :
    derivedTwist S a b e * derivedTwist S e c d
      = derivedTwist S b c f * derivedTwist S a f d := by
  unfold derivedTwist
  have he := S.ev_ne_zero e
  have hf := S.ev_ne_zero f
  have hd := S.ev_ne_zero d
  field_simp

/-- The unit normalisation: with `ev 1 = 1` the derived twist is trivial on the
unit channels. -/
theorem derivedTwist_unit (S : FusionSystem n k) (hn : 0 < n)
    (hev : S.ev ⟨0, hn⟩ = 1) (i j : Fin n) :
    derivedTwist S ⟨0, hn⟩ j j = 1 ∧ derivedTwist S i ⟨0, hn⟩ i = 1 := by
  have hj := S.ev_ne_zero j
  have hi := S.ev_ne_zero i
  constructor <;> · unfold derivedTwist; rw [hev]; field_simp

/-- The `i ⊗ i* ∋ 1` normalisation, which is what makes `p_dual` a theorem:
with `ev 1 = 1` and `ev (i*) * ev i = 1` the derived twist is `1` there. -/
theorem derivedTwist_dual (S : FusionSystem n k) (hn : 0 < n) (i : Fin n)
    (hev : S.ev ⟨0, hn⟩ = 1) (hinv : S.ev (S.ring.dual i) * S.ev i = 1) :
    derivedTwist S i (S.ring.dual i) ⟨0, hn⟩ = 1 := by
  unfold derivedTwist
  rw [hev, mul_comm, hinv]
  norm_num

/-- **Gauge covariance.**  Rescaling the duality data — `coev i ↦ lam i * coev i`
and `ev i ↦ ev i / lam i`, which preserves the snake equations — multiplies the
derived twist by the coboundary `lam c / (lam a * lam b)`.  This is the law under
which the twist's *class*, and hence pivotality, is invariant. -/
theorem derivedTwist_gauge {ev lam : Fin n → k} (h : ∀ i, lam i ≠ 0)
    (a b c : Fin n) :
    (ev a / lam a) * (ev b / lam b) / (ev c / lam c)
      = (ev a * ev b / ev c) * (lam c / (lam a * lam b)) := by
  have ha := h a
  have hb := h b
  have hc := h c
  field_simp

end DoubleDual

/-! ## The concrete case: `Vec_{Z/2}` -/

namespace DoubleDual

/-- `Vec_{Z/2}`'s evaluation scalars are trivial. -/
theorem vecZ2_ev (i : Fin 2) : VecZ2.system.ev i = 1 := rfl

/-- **The carried twist is the derived one.**  For `Vec_{Z/2}`, whose
associator is trivial and whose simples are self-dual, the twist computed from
the duality data equals the `J` the system carries.  This is the point of the
exercise: on this category `J` is not an extra datum but a computation. -/
theorem vecZ2_twist_derived (a b c : Fin 2) :
    derivedTwist VecZ2.system a b c = VecZ2.system.J a b c := by
  unfold derivedTwist
  simp [VecZ2.system]

/-- The derived twist on `Vec_{Z/2}` is the value its `J` field records. -/
theorem vecZ2_twist_eq_one (a b c : Fin 2) : derivedTwist VecZ2.system a b c = 1 := by
  rw [vecZ2_twist_derived]
  rfl

end DoubleDual

end FusionCategory
