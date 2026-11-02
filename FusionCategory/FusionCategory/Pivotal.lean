import FusionCategory.System
import Mathlib.Tactic

/-!
# Pivotal structures on skeletal fusion systems — Step 2 (rewritten)

Reference: EGNO Ch. 4 (pivotal categories), ENO §2.2 and §3.

A pivotal structure on a rigid monoidal category is a *monoidal* natural
isomorphism `p : 𝟙 ⇒ (−)**`.  In a skeleton `(−)**` is the identity on objects
and on scalar morphisms, so `p` is a family of scalars `p i ∈ kˣ` and the whole
content of monoidality is the per-channel equation

  `p kk = J i j kk * p i * p j`   whenever `N i j kk > 0`,

where `J` is the double-dual twist carried by `FusionSystem`.  This is
`p_mon` below.

## What the previous version got wrong

It had `p_fusion : p kk = p i * p j` with no twist factor, i.e. it assumed
`J ≡ 1`.  Since `p ≡ 1` satisfies that equation for *every* fusion ring, the
theorem `pseudoUnitary_spherical` of `PseudoUnitary.lean` was provable without
using any of its hypotheses.  `p_fusion` also cannot be repaired by an
`F`-only formula: the twist is not a function of `(N, F)` but of the rigid
structure, which is why `J` is carried by `FusionSystem`.

Two consequences, both recorded here:

* `p_dual` is no longer a field.  It follows from `p_mon` on the `i ⊗ i* ∋ 1`
  channel together with the normalisation `J i i* 1 = 1`.
* sphericality is *not* the equation `p i = p (i*)`.  It is the equality of
  the two trace functionals, `dim (i*) = dim i`, which uses the duality
  normalisation `kappa i = coev i * ev i` as well.  See `IsSpherical` and
  `isSpherical_iff`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

/-- A pivotal structure on a skeletal fusion system: a family of nonzero
scalars whose monoidal defect is exactly the double-dual twist. -/
structure PivotalStructure {n : ℕ} {k : Type u} [Field k]
    (S : FusionSystem n k) where
  p : Fin n → kˣ
  p_unit : ∀ (hn : 0 < n), p ⟨0, hn⟩ = 1
  /-- Monoidality of `p : 𝟙 ⇒ (−)**`, channel by channel. -/
  p_mon : ∀ i j kk : Fin n,
    0 < S.ring.N i j kk → (p kk : k) = S.J i j kk * (p i : k) * (p j : k)

namespace PivotalStructure

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}

/-- The scalar of the pivotal structure at a simple. -/
abbrev pVal (P : PivotalStructure S) (i : Fin n) : k := (P.p i : k)

theorem pVal_unit (P : PivotalStructure S) (hn : 0 < n) :
    P.pVal ⟨0, hn⟩ = 1 := by
  simp [pVal, P.p_unit hn]

theorem pVal_ne_zero (P : PivotalStructure S) (i : Fin n) : P.pVal i ≠ 0 :=
  (P.p i).ne_zero

/-- The `i ⊗ i* ∋ 1` channel is present. -/
theorem dual_channel_pos (hn : 0 < n) (i : Fin n) :
    0 < S.ring.N i (S.ring.dual i) ⟨0, hn⟩ := by
  have h := S.ring.dual_coeff hn i (S.ring.dual i)
  rw [h]
  simp

/-- **`p_dual` is a theorem, not an axiom.**  Monoidality on the
`i ⊗ i* ∋ 1` channel, together with the normalisation `J i i* 1 = 1`, gives
`p (i*) = (p i)⁻¹`. -/
theorem pVal_dual (P : PivotalStructure S) (hn : 0 < n) (i : Fin n) :
    P.pVal (S.ring.dual i) = (P.pVal i)⁻¹ := by
  have hN : 0 < S.ring.N i (S.ring.dual i) ⟨0, hn⟩ := dual_channel_pos hn i
  have h := P.p_mon i (S.ring.dual i) ⟨0, hn⟩ hN
  rw [P.p_unit hn, S.J_dual hn i, one_mul] at h
  have h1 : P.pVal i * P.pVal (S.ring.dual i) = 1 := h.symm
  have h2 : P.p i * P.p (S.ring.dual i) = 1 := by
    apply Units.ext
    simpa [Units.val_mul] using h1
  have h3 : P.p (S.ring.dual i) = (P.p i)⁻¹ := by
    calc P.p (S.ring.dual i) = 1 * P.p (S.ring.dual i) := (one_mul _).symm
      _ = (P.p i)⁻¹ * P.p i * P.p (S.ring.dual i) := by rw [inv_mul_cancel]
      _ = (P.p i)⁻¹ * (P.p i * P.p (S.ring.dual i)) := by rw [mul_assoc]
      _ = (P.p i)⁻¹ * 1 := by rw [h2]
      _ = (P.p i)⁻¹ := mul_one _
  simpa using congrArg Units.val h3

theorem pVal_inv (P : PivotalStructure S) (hn : 0 < n) (i : Fin n) :
    P.pVal i * P.pVal (S.ring.dual i) = 1 := by
  rw [P.pVal_dual hn i, mul_inv_cancel₀ (P.pVal_ne_zero i)]

end PivotalStructure

/-- The categorical dimension of a simple in a pivotal structure,
`dim i = p i * kappa i` with `kappa i = coev i * ev i` the duality
normalisation.  By the snake equation this is `p i / F^{i i* i}_i(1,1)`. -/
noncomputable def dim {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}
    (P : PivotalStructure S) (i : Fin n) : k :=
  (P.p i : k) * S.kappa i

namespace PivotalStructure

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}

theorem dim_eq (P : PivotalStructure S) (i : Fin n) :
    dim P i = P.pVal i * S.kappa i := rfl

theorem dim_ne_zero (P : PivotalStructure S) (i : Fin n) : dim P i ≠ 0 :=
  mul_ne_zero (P.pVal_ne_zero i) (S.kappa_ne_zero i)

/-- **Sphericality** is the equality of the two trace functionals, i.e.
`dim (i*) = dim i` for every simple.  It is *not* the equation
`p i = p (i*)`: that is only the special case `kappa (i*) = kappa i`. -/
def IsSpherical (P : PivotalStructure S) : Prop :=
  ∀ i : Fin n, dim P (S.ring.dual i) = dim P i

/-- Sphericity in the form the pivotal scalars satisfy it:
`kappa (i*) = (p i)² * kappa i`. -/
theorem isSpherical_iff (P : PivotalStructure S) (hn : 0 < n) :
    P.IsSpherical ↔ ∀ i : Fin n,
      S.kappa (S.ring.dual i) = (P.pVal i) ^ 2 * S.kappa i := by
  constructor
  · intro h i
    have hi : dim P (S.ring.dual i) = dim P i := h i
    rw [dim_eq, dim_eq, P.pVal_dual hn i] at hi
    have hp : P.pVal i ≠ 0 := P.pVal_ne_zero i
    have h2 := congrArg (fun x => P.pVal i * x) hi
    rw [← mul_assoc] at h2
    rw [mul_inv_cancel₀ hp, one_mul] at h2
    rw [h2]
    ring
  · intro h i
    rw [dim_eq, dim_eq, P.pVal_dual hn i, h i]
    field_simp [P.pVal_ne_zero i]

/-- For a self-dual simple the sphericity equation is automatic. -/
theorem spherical_of_selfdual (P : PivotalStructure S)
    (h : ∀ i : Fin n, S.ring.dual i = i) : P.IsSpherical := by
  intro i
  rw [h i]

end PivotalStructure

/-! ## Pivotal and squared dimensions with respect to a `FPData` -/

/-- Pivotal dimension built from an external real dimension family `d`
(the FP-dimensions, typically). -/
noncomputable def pivotalDim {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) : k :=
  (P.p i : k) * algebraMap ℝ k (d i)

/-- The pivotal dimension of a simple object, `p i` itself. -/
def pivotalDimSimple {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (i : Fin n) : k :=
  (P.p i : k)

theorem pivotalDimSimple_unit {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n) :
    pivotalDimSimple P (⟨0, hn⟩ : Fin n) = 1 := by
  simp [pivotalDimSimple, P.p_unit hn]

theorem pivotalDimSimple_dual {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n) (i : Fin n) :
    pivotalDimSimple P (S.ring.dual i) = (pivotalDimSimple P i)⁻¹ := by
  simp only [pivotalDimSimple, P.pVal_dual hn i]

noncomputable def squaredNorm {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (d : Fin n → ℝ) (i : Fin n) : k :=
  pivotalDim P d i * pivotalDim P d (S.ring.dual i)

theorem squaredNorm_eq {n : ℕ} {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (P : PivotalStructure S) (hn : 0 < n)
    (d : Fin n → ℝ) (i : Fin n) :
    squaredNorm P d i = algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i)) := by
  unfold squaredNorm pivotalDim
  have h : (P.p (S.ring.dual i) : k) = ((P.p i)⁻¹ : k) := P.pVal_dual hn i
  rw [h]
  have h2 : (P.p i : k) * ((P.p i : k)⁻¹ : k) = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  calc (P.p i : k) * algebraMap ℝ k (d i) * (((P.p i : k)⁻¹ : k) * algebraMap ℝ k (d (S.ring.dual i)))
      = ((P.p i : k) * ((P.p i : k)⁻¹ : k)) * (algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i))) := by ring
    _ = 1 * (algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i))) := by rw [h2]
    _ = algebraMap ℝ k (d i) * algebraMap ℝ k (d (S.ring.dual i)) := by ring

end FusionCategory
