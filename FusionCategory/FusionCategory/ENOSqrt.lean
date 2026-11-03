import FusionCategory.System
import FusionCategory.Pivotal
import Mathlib.Tactic

/-!
# ENO's square root `a` of `g`, and the `b`-cochain

Reference: Etingof–Nikshych–Ostrik, arXiv:math/0203060 §3.1 and §8.4
(Annals 162 (2005), Prop. 8.23).  This file carries the part of their proof of
8.23 that the signature of `System.lean` was missing.

## What ENO start from, and what the skeleton was missing

ENO's proof starts from a **tensor** isomorphism `g : Id → (−)****` (their
Thm 2.6, the Radford `S⁴` input) and an **additive** isomorphism
`a : Id → (−)**` with `a² = g`.  `a` need *not* be monoidal; the defect of its
monoidality is the cochain `b`, and the content of the proof is that a twist of
`a` has trivial defect.

`System.lean` carries `J` (the monoidal structure of `(−)**`) but neither `a`
nor `g`, so ENO's argument could not be stated, let alone run.  `SqrtData`
below is `a`; the monoidality of `g = a²` is `a_mon`, and it is stated against
`J ^ 2` because in a skeleton `(−)**` is the identity on labels and on
morphisms, so the tensorator of `(−)**** = (−)** ∘ (−)**` is `J²`.

This is the correction to `Cover.lean`'s `S4Data.g_fusion`, which reads
`g c = g i * g j` on channels — that is the tensorator of `(−)****` only when
`J = 1`.  The correct equation is `g c = J² · g i · g j`, and it is exactly
`a_mon` with `a · a = g`.

## What is proved here

* `b_sq` — ENO's `(b^{ij}_c)² = 1`, from `a_mon` alone.  No hypothesis
  `J² = 1` is used, and none may be added: it is false for honest
  pseudo-unitary data (see `PLAN.md` and the `Vec^ω_{(Z/3)²}` datum, where the
  honest twist squares to a primitive cube root of unity).
* `trace_iff` — ENO's trace identity `d_i d_j = Σ_c T^{ij}_c d_c` is
  **equivalent**, after the `a`'s cancel, to the sum identity

      (M)   κ'_i κ'_j = Σ_c N i j c · J i j c · κ'_c ,   κ'_i = coev_i · ev_{i*}

  a condition on `(N, J, κ')` alone, independent of `a` and of `F`.  So the
  question left open in `PLAN.md` — "settle `J`" — is exactly "prove (M)",
  which is what ENO's `b`-symbol computation does.
* `toPivotal` — if the defect vanishes, `a` itself is a pivotal structure.
* `d_mult` — with the defect gone and (M), `d` is a character of the fusion
  ring: the dimension function `dim P = d` is multiplicative.

## The duality normalisation

ENO's `d_i = Tr(a_i)` is `a_i · coev_i · ev_{i*}`, **not** `a_i · κ_i` with
`κ_i = coev_i · ev_i`: the trace uses `ev` at the dual, and the two differ as
soon as `i* ≠ i`.  `kappaD` is that normalisation.  For the self-dual data the
repo carries (Fibonacci, Ising, Yang-Lee, `Vec^ω_{Z/2}`) they agree, and
`d_eq_kappa` records it.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

section KappaDual

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionSystem

variable (S : FusionSystem n k)

/-- The duality normalisation the quantum trace actually uses: `coev_i · ev_{i*}`.
ENO's `d_i = Tr(a_i)` is `a_i` times this, and it agrees with `S.kappa` exactly
when `i* = i`. -/
def kappaD (i : Fin n) : k := S.coev i * S.ev (S.ring.dual i)

theorem kappaD_ne_zero (i : Fin n) : S.kappaD i ≠ 0 :=
  mul_ne_zero (S.coev_ne_zero i) (S.ev_ne_zero (S.ring.dual i))

end FusionSystem

end KappaDual

section Sqrt

variable {n : ℕ} {k : Type u} [Field k]

/-- ENO's `a : Id → (−)**`, as a non-zero scalar at each simple, with `a² = g`
monoidal for `(−)****`.

`a` is *not* required to be monoidal — that is the whole content of ENO 8.23 —
and the condition on `a²` is stated against `J ^ 2` because the tensorator of
`(−)****` is the square of the tensorator of `(−)**` in a skeleton. -/
structure SqrtData (S : FusionSystem n k) where
  /-- The scalar of `a : X_i → X_i**` at the simple `i`. -/
  a : Fin n → k
  a_ne_zero : ∀ i, a i ≠ 0
  /-- `a` is a natural isomorphism `Id → (−)**`, so its value at the unit is
  the canonical identification `1 → 1**`, i.e. `1`. -/
  a_unit : ∀ (hn : 0 < n), a ⟨0, hn⟩ = 1
  /-- `g = a²` is a tensor isomorphism `Id → (−)****`. -/
  a_mon : ∀ (i j c : Fin n), 0 < S.ring.N i j c →
    a c ^ 2 = (S.J i j c) ^ 2 * a i ^ 2 * a j ^ 2

namespace SqrtData

variable {S : FusionSystem n k} (A : SqrtData S)

/-- ENO's `b^{ij}_c`: the defect of the monoidality of `a` on the channel `c`
of `i ⊗ j`.  `J` enters in the numerator because `J` is the scalar of
`i** ⊗ j** → (i ⊗ j)**`, while `a_i ⊗ a_j` lands in `i** ⊗ j**`. -/
def b (i j c : Fin n) : k := S.J i j c * A.a i * A.a j / A.a c

/-- ENO's `T^{ij}_c = tr(b^{ij}_c)`.  The channel space is one-dimensional
(`mult_free`), so the trace of `b` is `b`, and `T` is `N · b` off the support. -/
def Tmat (i j c : Fin n) : k := (S.ring.N i j c : k) * A.b i j c

/-- ENO's `d_i = Tr(a_i) = ev_{i*} ∘ (a_i ⊗ 1) ∘ coev_i`. -/
def d (i : Fin n) : k := A.a i * S.kappaD i

theorem d_eq (i : Fin n) : A.d i = A.a i * S.kappaD i := rfl

/-- For self-dual data the trace normalisation is `S.kappa`, and then `d` is
the repo's dimension of the pivotal structure `a`. -/
theorem d_eq_kappa (hself : ∀ i, S.ring.dual i = i) (i : Fin n) :
    A.d i = A.a i * S.kappa i := by
  simp only [d, FusionSystem.kappaD, FusionSystem.kappa, hself]

/-- **ENO's `(b^{ij}_c)² = 1`.**  From `a² = g` monoidal for `(−)****`.
No hypothesis `J² = 1` is used; adding one would exclude every pseudo-unitary
category whose honest twist squares to a non-trivial root of unity. -/
theorem b_sq {i j c : Fin n} (hN : 0 < S.ring.N i j c) : A.b i j c ^ 2 = 1 := by
  have hac : A.a c ≠ 0 := A.a_ne_zero c
  have hnum : (S.J i j c * A.a i * A.a j) ^ 2
      = S.J i j c ^ 2 * A.a i ^ 2 * A.a j ^ 2 := by ring
  rw [b, div_pow, hnum, ← A.a_mon i j c hN]
  exact div_self (pow_ne_zero 2 hac)

/-- **The trace identity is (M).**  ENO's `d_i d_j = Σ_c T^{ij}_c d_c` holds if
and only if the sum identity

  `κ'_i κ'_j = Σ_c N i j c · J i j c · κ'_c`,  `κ'_i = coev_i · ev_{i*}`

holds.  The `a`'s cancel: the trace identity carries no information about `a`,
only about `(N, J, κ')`. -/
theorem trace_iff (i j : Fin n) :
    (A.d i * A.d j = ∑ c : Fin n, (S.ring.N i j c : k) * A.b i j c * A.d c)
      ↔ (S.kappaD i * S.kappaD j
          = ∑ c : Fin n, (S.ring.N i j c : k) * S.J i j c * S.kappaD c) := by
  have hai : A.a i ≠ 0 := A.a_ne_zero i
  have haj : A.a j ≠ 0 := A.a_ne_zero j
  have hterm : ∀ c : Fin n,
      (S.ring.N i j c : k) * A.b i j c * A.d c
        = (A.a i * A.a j) * ((S.ring.N i j c : k) * S.J i j c * S.kappaD c) := by
    intro c
    have hc : A.a c ≠ 0 := A.a_ne_zero c
    rw [b, d_eq]
    field_simp
  have hd : A.d i * A.d j = (A.a i * A.a j) * (S.kappaD i * S.kappaD j) := by
    rw [d_eq, d_eq]; ring
  have hsum : (∑ c : Fin n, (S.ring.N i j c : k) * A.b i j c * A.d c)
      = (A.a i * A.a j)
        * (∑ c : Fin n, (S.ring.N i j c : k) * S.J i j c * S.kappaD c) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => hterm c)
  have hprod : A.a i * A.a j ≠ 0 := mul_ne_zero hai haj
  rw [hd, hsum]
  exact ⟨fun h => mul_left_cancel₀ hprod h, fun h => by rw [h]⟩

/-- **If the defect vanishes, `a` is pivotal.**  This is the last step of
ENO's argument: `b = 1` is exactly `p_mon` for `p = a`. -/
noncomputable def toPivotal
    (hb : ∀ i j c : Fin n, 0 < S.ring.N i j c → A.b i j c = 1) :
    PivotalStructure S where
  p i := Units.mk0 (A.a i) (A.a_ne_zero i)
  p_unit hn := by
    apply Units.ext
    simpa using A.a_unit hn
  p_mon i j c hN := by
    have h := hb i j c hN
    rw [b] at h
    field_simp [A.a_ne_zero c] at h
    exact h.symm

/-- On self-dual data the dimension of the pivotal structure `a` is ENO's `d`. -/
theorem dim_toPivotal (hb : ∀ i j c : Fin n, 0 < S.ring.N i j c → A.b i j c = 1)
    (hself : ∀ i, S.ring.dual i = i) (i : Fin n) :
    dim (A.toPivotal hb) i = A.d i := by
  rw [PivotalStructure.dim_eq, A.d_eq_kappa hself i]
  rfl

/-- **ENO's conclusion, algebraically.**  If the defect vanishes and (M) holds,
then `d` is a character of the fusion ring — the dimension function of a
pivotal structure is multiplicative.  (Positivity, and hence
`d = FPdim` by Perron–Frobenius uniqueness, is the separate pseudo-unitarity
input; it is not available in a multiplicity-free skeleton over an arbitrary
field.) -/
theorem d_mult
    (hb : ∀ i j c : Fin n, 0 < S.ring.N i j c → A.b i j c = 1)
    (hM : ∀ p q : Fin n,
      (∑ c : Fin n, (S.ring.N p q c : k) * S.J p q c * S.kappaD c)
        = S.kappaD p * S.kappaD q)
    (x y : Fin n) :
    (∑ c : Fin n, (S.ring.N x y c : k) * A.d c) = A.d x * A.d y := by
  have hterm : ∀ c : Fin n,
      (S.ring.N x y c : k) * A.d c
        = (A.a x * A.a y) * ((S.ring.N x y c : k) * S.J x y c * S.kappaD c) := by
    intro c
    rcases Nat.eq_zero_or_pos (S.ring.N x y c) with h0 | hpos
    · rw [h0]; simp
    · have h := hb x y c hpos
      rw [SqrtData.b] at h
      field_simp [A.a_ne_zero c] at h
      rw [d_eq, ← h]
      ring
  have hd : A.d x * A.d y = (A.a x * A.a y) * (S.kappaD x * S.kappaD y) := by
    rw [d_eq, d_eq]; ring
  calc (∑ c : Fin n, (S.ring.N x y c : k) * A.d c)
      = ∑ c : Fin n,
          (A.a x * A.a y) * ((S.ring.N x y c : k) * S.J x y c * S.kappaD c) :=
        Finset.sum_congr rfl (fun c _ => hterm c)
    _ = (A.a x * A.a y)
          * (∑ c : Fin n, (S.ring.N x y c : k) * S.J x y c * S.kappaD c) := by
        rw [Finset.mul_sum]
    _ = (A.a x * A.a y) * (S.kappaD x * S.kappaD y) := by rw [hM x y]
    _ = A.d x * A.d y := hd.symm

end SqrtData

end Sqrt

end FusionCategory
