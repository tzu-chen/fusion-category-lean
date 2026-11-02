import FusionCategory.Pivotal
import FusionCategory.PseudoUnitary

/-!
# ENO 8.23 reduces to a coboundary condition on the twist

`Pivotal.lean` makes a pivotal structure a family of scalars `p` with
`p c = J a b c * p a * p b`, and defines the categorical dimension as
`dim i = p i * kappa i`.  This file proves the two halves of the resulting
reformulation.

**The twist of a pivotal structure is the coboundary of its dimension** — up to
the duality normalisation.  Concretely, with `kappa` multiplicative on fusion
channels,

  `J a b c = dim c / (dim a * dim b)`

on every channel (`twist_eq_coboundary_of_pivotal`).  So `J` is not independent
of the dimension once a pivotal structure exists.

**Conversely**, a character `d` of the fusion rules which is a coboundary for
the twist is a pivotal structure, normalised by `kappa`
(`exists_pivotal_of_coboundary`), and it is spherical when `d` is invariant
under `*` (`exists_spherical_of_coboundary`).

`eno823_of_twist_coboundary` is then the payoff: ENO 8.23 holds as soon as the
twist is the coboundary of the FP-dimension in the `kappa`-normalisation.  That
is the equation the theorem is *about*; what remains open is producing it from
pseudo-unitarity.

`kappa_gauge_invariant` records why the hypothesis on `kappa` is legitimate: it
is unchanged by `coev i ↦ lam i * coev i`, `ev i ↦ ev i / lam i`, the
rescaling that preserves the snake equations.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

open PivotalStructure

variable {n : ℕ} {k : Type u} [Field k]

/-- The duality normalisation `kappa` is multiplicative on fusion channels.

This is gauge invariant: `coev i ↦ lam i * coev i` together with
`ev i ↦ ev i / lam i` preserves the snakes and leaves `kappa` untouched, so the
condition is a condition on the rigid structure and not on its normalisation. -/
def KappaMultiplicative (S : FusionSystem n k) : Prop :=
  ∀ a b c : Fin n, 0 < S.ring.N a b c → S.kappa c = S.kappa a * S.kappa b

theorem kappa_gauge_invariant (S : FusionSystem n k) (lam : Fin n → k)
    (h : ∀ i, lam i ≠ 0) (i : Fin n) :
    (lam i * S.coev i) * (S.ev i / lam i) = S.kappa i := by
  unfold FusionSystem.kappa
  field_simp [h i]

/-- **The twist of a pivotal structure is the coboundary of its dimension**,
in the normalisation where `kappa` is multiplicative. -/
theorem twist_eq_coboundary_of_pivotal (S : FusionSystem n k) (P : PivotalStructure S)
    (hκ : KappaMultiplicative S) (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    S.J a b c = dim P c / (dim P a * dim P b) := by
  have hp : P.pVal c = S.J a b c * P.pVal a * P.pVal b := P.p_mon a b c hN
  have hk := hκ a b c hN
  have hmain : S.J a b c * (dim P a * dim P b) = dim P c := by
    rw [dim_eq, dim_eq, dim_eq, hk, hp]
    ring
  refine (eq_div_iff (mul_ne_zero (dim_ne_zero P a) (dim_ne_zero P b))).mpr ?_
  exact hmain

/-- **Conversely**: a character of the fusion rules whose values are a
coboundary for the twist gives a pivotal structure with those dimensions. -/
theorem exists_pivotal_of_coboundary (S : FusionSystem n k) (d : Fin n → k)
    (hκ : KappaMultiplicative S) (hd : ∀ i, d i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → d c = S.J a b c * d a * d b)
    (hn : 0 < n) (hd0 : d ⟨0, hn⟩ = 1) (hκ0 : S.kappa ⟨0, hn⟩ = 1) :
    ∃ P : PivotalStructure S, ∀ i, dim P i = d i := by
  have hne : ∀ i, d i / S.kappa i ≠ 0 :=
    fun i => div_ne_zero (hd i) (S.kappa_ne_zero i)
  let p : Fin n → kˣ := fun i => Units.mk0 (d i / S.kappa i) (hne i)
  have hval : ∀ i, (p i : k) = d i / S.kappa i := fun _ => rfl
  refine ⟨⟨p, ?_, ?_⟩, ?_⟩
  · intro hn'
    apply Units.ext
    have h0 : (⟨0, hn'⟩ : Fin n) = ⟨0, hn⟩ := by simp
    show (p ⟨0, hn'⟩ : k) = ((1 : kˣ) : k)
    rw [hval, h0, hd0, hκ0]
    norm_num
  · intro a b c hN
    rw [hval, hval, hval, hJ a b c hN, hκ a b c hN]
    have ha := S.kappa_ne_zero a
    have hb := S.kappa_ne_zero b
    have hc := S.kappa_ne_zero c
    field_simp
  · intro i
    show (p i : k) * S.kappa i = d i
    rw [hval, div_mul_cancel₀ _ (S.kappa_ne_zero i)]

/-- The spherical case: `d` invariant under `*`. -/
theorem exists_spherical_of_coboundary (S : FusionSystem n k) (d : Fin n → k)
    (hκ : KappaMultiplicative S) (hd : ∀ i, d i ≠ 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → d c = S.J a b c * d a * d b)
    (hn : 0 < n) (hd0 : d ⟨0, hn⟩ = 1) (hκ0 : S.kappa ⟨0, hn⟩ = 1)
    (hdual : ∀ i, d (S.ring.dual i) = d i) :
    ∃ P : PivotalStructure S, P.IsSpherical ∧ ∀ i, dim P i = d i := by
  obtain ⟨P, hP⟩ := exists_pivotal_of_coboundary S d hκ hd hJ hn hd0 hκ0
  refine ⟨P, ?_, hP⟩
  intro i
  rw [hP (S.ring.dual i), hP i, hdual i]

section Eno

variable [Algebra ℝ k]

/-- **ENO 8.23, reduced to the equation it is about.**  If the double-dual twist
is the coboundary of the FP-dimension, in the normalisation where `kappa` is
multiplicative and normalised at the unit, then a spherical pivotal structure
with `dim = FPdim` exists.

The remaining open content of ENO Prop 8.23 is exactly the hypothesis `hJ`:
pseudo-unitarity has to produce that equation, which it can only do once the
twist is *derived* from `ev`, `coev` and `F` rather than carried. -/
theorem eno823_of_twist_coboundary (S : FusionSystem n k) (hFP : S.ring.FPData)
    (hκ : KappaMultiplicative S) (hn : 0 < n) (hκ0 : S.kappa ⟨0, hn⟩ = 1)
    (hmap : ∀ r : ℝ, algebraMap ℝ k r = 0 → r = 0)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = algebraMap ℝ k (hFP.fpdim c) /
        (algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b))) :
    ENO823 S hFP := by
  have hd : ∀ i, algebraMap ℝ k (hFP.fpdim i) ≠ 0 := by
    intro i h
    exact (ne_of_gt (hFP.pos i)) (hmap _ h)
  have hJ' : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      algebraMap ℝ k (hFP.fpdim c) =
        S.J a b c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b) := by
    intro a b c hN
    rw [hJ a b c hN]
    have ha := hd a
    have hb := hd b
    field_simp
  have hd0 : algebraMap ℝ k (hFP.fpdim ⟨0, hn⟩) = 1 := by
    rw [hFP.unit_one hn, map_one]
  have hdual : ∀ i, algebraMap ℝ k (hFP.fpdim (S.ring.dual i))
      = algebraMap ℝ k (hFP.fpdim i) := by
    intro i
    rw [hFP.dual_eq i]
  obtain ⟨P, hsp, hdim⟩ :=
    exists_spherical_of_coboundary S (fun i => algebraMap ℝ k (hFP.fpdim i))
      hκ hd hJ' hn hd0 hκ0 hdual
  exact ⟨P, hsp, hdim⟩

end Eno

end FusionCategory
