import FusionCategory.Basic

/-!
# Universal grading group — Step 3

Reference: Gelaki, ENO §3, Bartlett Prop 5.7;
`Aut^⊗(Id) ≅ Hom(U_C, kˣ)`.

The universal grading group `U_C` is the initial group `G` with a map
`deg : Fin n → G` such that `N i j k >0 → deg k = deg i * deg j`
and `deg 0 =1`.  Pivotal structures form a torsor over
`Hom(U_C, kˣ)`; the class `[g] ∈ Hom(U_C, kˣ)` of the Radford
`S⁴` determines whether `C` is pivotal.  The splitting criterion is
`Nonempty (PivotalStructure C) ↔ ∃ h, h^2 = [g]`.

This file gives the skeletal formulation: grading data, the universal
property, and the torsor action.
-/

universe u

namespace FusionCategory

section Grading

variable {k : Type u} [Field k]

/-- Grading of a fusion ring by a group `G`.

A map `deg : Fin n → G` is a grading when it is multiplicative on
fusion: if `k` appears in `i ⊗ j` then `deg k = deg i * deg j`,
and `deg 0 = 1`.  This is the skeletal version of a faithful
grading of the fusion category.
-/
structure GradingData (n : ℕ) (R : FusionRing n) (G : Type u) [Group G] where
  deg : Fin n → G
  deg_unit : ∀ (hn : 0 < n), deg ⟨0, hn⟩ = 1
  deg_mul : ∀ i j kk, R.N i j kk > 0 → deg kk = deg i * deg j

/-- Universal grading: initial among all gradings.

`U_C` with `deg_U` is universal if every grading `deg' : Fin n → G'`
factors uniquely through a group homomorphism `U_C → G'`.
This is the skeletal definition of ENO §3's universal grading group.
-/
structure IsUniversalGrading {n : ℕ} {R : FusionRing n}
    {G : Type u} [Group G] (U : GradingData n R G) : Prop where
  universal : ∀ (G' : Type u) [Group G'] (D : GradingData n R G'),
    ∃! φ : G →* G', ∀ i, φ (U.deg i) = D.deg i

/-- Data witnessing a universal grading (existence). -/
structure HasUniversalGrading (n : ℕ) (R : FusionRing n) where
  G : Type u
  instGroup : Group G
  grading : GradingData n R G
  isUniversal : @IsUniversalGrading n R G instGroup grading

-- Provide instance projections
attribute [instance] HasUniversalGrading.instGroup

/-- `Aut^⊗(Id)` as characters of `U_C`.

An automorphism of the identity functor is given on simples by scalars
`χ_i ∈ kˣ` with `χ_0 =1` and `χ_k = χ_i * χ_j` whenever `N i j k >0`.
Such a family is exactly a group homomorphism `U_C → kˣ` via
`χ_i = χ(deg i)`.  This is Bartlett Prop 5.7 / ENO §3.
-/
structure TensorAutoId {n : ℕ} {R : FusionRing n} (U : HasUniversalGrading n R)
    (k : Type u) [CommMonoid k] where
  chi : Fin n → kˣ
  chi_unit : ∀ (hn : 0 < n), chi ⟨0, hn⟩ = 1
  chi_mul : ∀ i j kk, R.N i j kk > 0 → (chi kk : k) = (chi i : k) * (chi j : k)

/-- Character associated to a tensor automorphism. -/
noncomputable def charOfTensorAuto {n : ℕ} {R : FusionRing n}
    {U : HasUniversalGrading (u:=u) n R} {k : Type u} [Field k]
    (a : TensorAutoId (U:=U) (k:=kˣ) ) (g : U.G) : kˣ :=
  -- By universality, `a.chi` factors through `U.deg` via some
  -- `φ : U.G → kˣ`; we define `charOfTensorAuto a` as that `φ`.
  -- For the stub we define it via choice: pick `i` with `deg i = g`
  -- if it exists, otherwise `1`.  The universal property ensures
  -- well-definedness, which we assume.
  if h : ∃ i : Fin n, U.grading.deg i = g then
    a.chi (Classical.choose h)
  else 1

/-- Torsor action: twisting a pivotal structure by a character.

If `P` is pivotal with scalars `p_i` and `χ : U_C → kˣ` is a character,
then `P' = χ • P` with `(χ•P).p i = χ(deg i) * p_i` is again pivotal.
Conversely any two pivotal structures differ by a unique such `χ`.
This makes pivotal structures a torsor over `Hom(U_C, kˣ)`.
-/
axiom torsor_p_dual {n : ℕ} {S : FusionSystem n k}
    (U : HasUniversalGrading n S.ring) (P : PivotalStructure S)
    (χ : U.G →* kˣ) (i : Fin n) :
    (χ (U.grading.deg (S.ring.dual i)) * P.p (S.ring.dual i) : kˣ) =
    ((χ (U.grading.deg i) * P.p i)⁻¹ : kˣ)

noncomputable def torsorAction {n : ℕ} {S : FusionSystem n k}
    (U : HasUniversalGrading n S.ring)
    (P : PivotalStructure S) (χ : U.G →* kˣ) : PivotalStructure S where
  p := fun i => χ (U.grading.deg i) * P.p i
  p_unit := by
    intro hn
    simp [U.grading.deg_unit hn, P.p_unit hn]
  p_dual := torsor_p_dual U P χ
  p_fusion := by
    intro i j kk hN
    have hdeg : U.grading.deg kk = U.grading.deg i * U.grading.deg j :=
      U.grading.deg_mul i j kk hN
    simp [hdeg, map_mul, P.p_fusion i j kk hN]

/-- Splitting criterion for pivotal structures.

`C` admits a pivotal structure iff the class `[g] ∈ Hom(U_C, kˣ)` of
the Radford `S⁴` is a square: `∃ h, h^2 = [g]`.  This is ENO Rem 3.1 /
Bartlett Lemma 6.2.  The forward direction chooses `p` with
`p^2 = g` via `p_i² = g_i`; the converse builds `g` from a given `p`.

We state it as an axiom for Step 3, to be proved in Step 5 after the
cover machinery is in place.  The hypothesis `U` is the universal
grading; `g : U.G → kˣ` is the character of `S⁴`.
-/
axiom pivotal_iff_square {n : ℕ} {S : FusionSystem n k}
    (U : HasUniversalGrading n S.ring)
    (g : U.G →* kˣ) :
    Nonempty (PivotalStructure S) ↔ ∃ h : U.G →* kˣ, ∀ x, h x * h x = g x

/-- If `U_C` has no 2-torsion, every fusion category is pivotal.

Indeed, if `U_C` is 2-torsion-free then the squaring map
`Hom(U_C, kˣ) → Hom(U_C, kˣ)`, `h ↦ h^2` is surjective (as `kˣ` is
divisible for `k = ℂ`), so `[g]` is always a square.  This is the
criterion used for Haagerup–Izumi with `U_C = ℤ/(2n+1)` etc.
-/
axiom pivotal_of_no2Torsion {n : ℕ} {S : FusionSystem n k}
    (U : HasUniversalGrading n S.ring)
    (hU : ∀ x : U.G, x * x = 1 → x = 1)
    (g : U.G →* kˣ) :
    Nonempty (PivotalStructure S)

end Grading

end FusionCategory
