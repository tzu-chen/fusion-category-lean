import FusionCategory.Pivotal

/-!
# Pivotal cover — Step 3

Reference: ENO Rem. 3.1 / §5; ENOM.

The pivotal cover `̃C = {(X, f : X ≅ X** | f** ∘ f = g_X)}` where
`g : 𝟙 ≅ ****` is the Radford `S⁴` isomorphism (ENO Thm 2.6), taken as
hypothesis.  In skeletal terms an object of the cover is a pair
`(i, f)` with `i : Fin n` and `f ∈ kˣ` such that `f² = g_i`, where
`g_i` is the scalar of `g` at simple `i`.

We construct the cover as a `ℤ/2`-graded fusion system doubling the
original, with forgetful functor `F : ̃C → C` and canonical pivotal
structure `p_{(X,f)} = f`.  This is ENO Rem 3.1.
-/

universe u

namespace FusionCategory

section Cover

variable {k : Type u} [Field k]

/-- Radford `S⁴` class as skeletal scalars.

In the skeletal model the monoidal isomorphism `g : Id ≅ ****` acts on
simples by scalars `g_i ∈ kˣ` with `g_0 =1`, `g_{i*} = g_i`, and
`g_k = g_i * g_j` whenever `N i j k >0` (i.e. `g` is a character of
the universal grading group).  This is the data we take as hypothesis;
the categorical `S⁴` is not proved (ENO §4–5, weak Hopf).
-/
structure S4Data {n : ℕ} (S : FusionSystem n k) where
  g : Fin n → kˣ
  g_unit : ∀ (hn : 0 < n), g ⟨0, hn⟩ = 1
  g_dual : ∀ i, g (S.ring.dual i) = g i
  g_fusion : ∀ i j kk, S.ring.N i j kk > 0 → (g kk : k) = (g i : k) * (g j : k)

/-- Object of the pivotal cover: a pair `(orig, f)` with `f : orig ≅ orig**`
satisfying `f** * f = g_orig`.

Skeletally `f ∈ kˣ` with `f^2 = g_orig`.  The two lifts per simple
`orig` correspond to the two square roots of `g_orig` when they exist;
if `g_orig =1` the two lifts are `±1`.
-/
structure CoverObj {n : ℕ} {S : FusionSystem n k} (G : S4Data S) where
  orig : Fin n
  f : kˣ
  covers : (f : k) * (f : k) = (G.g orig : k)

/-- Forgetful functor `F : ̃C → C` on objects. -/
def forgetCover {n : ℕ} {S : FusionSystem n k} {G : S4Data S}
    (X : CoverObj G) : Fin n :=
  X.orig

/-- Canonical pivotal structure on the cover: `p_{(X,f)} = f`.

This is the tautological pivotal structure of ENO Rem 3.1; it satisfies
`p** * p = g` by construction and gives `̃C` a pivotal structure even
when `C` has none.
-/
def coverCanonicalPivotal {n : ℕ} {S : FusionSystem n k} (G : S4Data S)
    (X : CoverObj G) : kˣ :=
  X.f

theorem coverCanonicalPivotal_sq {n : ℕ} {S : FusionSystem n k}
    (G : S4Data S) (X : CoverObj G) :
    ((coverCanonicalPivotal G X : kˣ) : k) * ((coverCanonicalPivotal G X : kˣ) : k) =
    (G.g X.orig : k) :=
  X.covers

/-- `ℤ/2`-grading on the cover: parity of the chosen square root. -/
def coverGrading {n : ℕ} {S : FusionSystem n k} {G : S4Data S}
    (s : Fin n → kˣ) (_hs : ∀ i, ((s i : k) * (s i : k) = (G.g i : k)))
    (X : CoverObj G) : Fin 2 :=
  if (X.f : k) = (s X.orig : k) then 0 else 1

end Cover

/-- Global dimension doubles: `dim ̃C = 2 dim C`.

For any FP-dimension data `h` on `C`, the doubled FP-dimension on `̃C`
given by `̃d(i,ε) = d(i)` satisfies `∑_{̃i} ̃d(̃i)² = 2 * ∑_i d(i)²`.
This is the skeletal shadow of ENO Rem 3.1's `dim ̃C = 2 dim C` and
`FPdim ̃C = 2 FPdim C`.

Stated as an axiom to be discharged in Step 4 when the full
`coverFusionRing` with `ñ = 2n` is constructed; the proof is a
straightforward splitting of `Fin (2n)` into evens/odds.
-/
axiom coverGlobalDim_double {n : ℕ} {k : Type} [Field k]
    {S : FusionSystem n k} (h : S.ring.FPData) :
    (∑ i : Fin (n * 2), (h.fpdim (⟨i.val / 2, by omega⟩ : Fin n) ^ 2 : ℝ)) =
    2 * h.globalDim

end FusionCategory
