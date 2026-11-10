/-
WP3 closure round, member m7, direction d11: the *structural* layer of the derived
twist on self-dual labels.

`DerivedJScalar.derivedJGen` is the ratio

  `derivedJGen S a b c = ψ_{a,b}|_c / ψ_{b*,a*}|_{c*}`,   `ψ = comparisonScalar`.

Nothing here recomputes a twist from an `F` table.  The point is that when the
labels are self-dual the two sides of that ratio are the *same term*, so the
whole content of the double-dual twist evaporates on those channels:

* `derivedJGen_selfDual_diag` — `derivedJGen S a a c = 1` for `dual a = a`,
  `dual c = c`, given only `comparisonScalar S a a c ≠ 0`.  No pentagon, no
  associator table, no symmetry of the comparison scalar: it is `div_self`.
* `derivedJGen_mul_swapDual` — off the diagonal the twist is the *reciprocal* of
  its swap-dual, `J_{a,b;c} · J_{b*,a*;c*} = 1` (again `div_self` after
  `dual_dual`), so on self-dual data `J_{a,b;c} · J_{b,a;c} = 1`.
* `not_j_match_of_selfDual_diag` / `not_j_match_of_selfDual_swap` — the
  consequences for `J_match`: on self-dual data the carried twist is *forced* to
  be `1` on every supported diagonal channel, and forced to be swap-antisymmetric
  off it.  A `J_match` failure on a diagonal channel is therefore impossible
  unless `comparisonScalar` vanishes there (the frozen `WP2.DerivedJ_ne_zero`
  degeneracy), never a property of the carried `J`.
* `settledJ_selfDual_diag` / `derivedJGen_eq_settledJ_selfDual_diag_iff` — why
  Yang–Lee separates the derived twist from the settled `(M)`-twist of
  `Prop821CNorm`: on the diagonal `derivedJGen` is `1` while
  `settledJ = f_c κ_a² / (κ_c f_a²)`, so the two agree there exactly when the
  `(M)`-twist is trivial on that channel.

Applications at the end: Yang–Lee (both supported channels of `τ ⊗ τ` are
diagonal), where the closed form reduces to two explicit nonvanishings.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJLaws
import FusionCategory.Prop821CNorm
import FusionCategory.DerivedJFunctor
import FusionCategory.DerivedJPivotalDichotomy
import FusionCategory.Examples.YangLee

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the field identity behind both statements -/

/-- In a field, a ratio times the reciprocal ratio is `1`.  Total division makes
this a statement about nonzero entries only: if either side vanishes the product
is `0`, which is why the twist statements below carry nonvanishing hypotheses. -/
theorem div_mul_div_swap (x y : k) (hx : x ≠ 0) (hy : y ≠ 0) : x / y * (y / x) = 1 := by
  rw [div_mul_div_comm, mul_comm y x, div_self (mul_ne_zero hx hy)]

/-! ## §2 — the twist is the reciprocal of its swap-dual -/

/-- **Swap law.**  The derived twist at `(a,b;c)` is the reciprocal of the derived
twist at `(b*,a*;c*)`.  This is the definition: the second factor of the first
ratio *is* the first factor of the second, and `dual_dual` closes the loop. -/
theorem derivedJGen_mul_swapDual (S : FusionSystem n k) (a b c : Fin n)
    (h1 : comparisonScalar S a b c ≠ 0)
    (h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0) :
    derivedJGen S a b c *
      derivedJGen S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) = 1 := by
  rw [derivedJGen_def, derivedJGen_def, FusionRing.dual_dual, FusionRing.dual_dual,
    FusionRing.dual_dual]
  exact div_mul_div_swap _ _ h1 h2

/-- **Diagonal triviality.**  On a label triple that is self-dual (`dual a = a`,
`dual c = c`) the two comparison scalars of the ratio are the same term, so the
derived twist is `1` on the channel — whatever the associator is. -/
theorem derivedJGen_selfDual_diag (S : FusionSystem n k) {a c : Fin n}
    (ha : S.ring.dual a = a) (hc : S.ring.dual c = c)
    (h : comparisonScalar S a a c ≠ 0) :
    derivedJGen S a a c = 1 := by
  rw [derivedJGen_def, ha, hc]
  exact div_self h

/-- The self-dual form of the swap law: `J_{a,b;c} · J_{b,a;c} = 1`. -/
theorem derivedJGen_selfDual_swap (S : FusionSystem n k) {a b c : Fin n}
    (ha : S.ring.dual a = a) (hb : S.ring.dual b = b) (hc : S.ring.dual c = c)
    (h1 : comparisonScalar S a b c ≠ 0)
    (h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0) :
    derivedJGen S a b c * derivedJGen S b a c = 1 := by
  have h := derivedJGen_mul_swapDual S a b c h1 h2
  rwa [ha, hb, hc] at h

/-! ## §3 — what this forces on the carried twist (`J_match`) -/

/-- On self-dual data the carried twist is forced to `1` on every supported
diagonal channel whose comparison scalar does not vanish. -/
theorem j_match_selfDual_diag (S : FusionSystem n k) {a c : Fin n}
    (ha : S.ring.dual a = a) (hc : S.ring.dual c = c)
    (hN : 0 < S.ring.N a a c) (h : comparisonScalar S a a c ≠ 0)
    (hJ : J_match S (derivedJGen S)) :
    S.J a a c = 1 := by
  rw [hJ a a c hN, derivedJGen_selfDual_diag S ha hc h]

/-- **Refutation criterion (diagonal).**  On self-dual data a carried twist that is
not `1` on a supported diagonal channel refutes `J_match`, independently of every
`F`/`Finv`/`ev` entry except the nonvanishing of that one comparison scalar. -/
theorem not_j_match_of_selfDual_diag (S : FusionSystem n k) {a c : Fin n}
    (ha : S.ring.dual a = a) (hc : S.ring.dual c = c)
    (hN : 0 < S.ring.N a a c) (h : comparisonScalar S a a c ≠ 0)
    (hJ : S.J a a c ≠ 1) :
    ¬ J_match S (derivedJGen S) :=
  fun hm => hJ (j_match_selfDual_diag S ha hc hN h hm)

/-- **Refutation criterion (off-diagonal).**  On self-dual data `J_match` forces the
carried twist to be swap-antisymmetric on every supported swapped pair — so a
carried twist with `J a b c · J b a c ≠ 1` cannot be the derived one. -/
theorem not_j_match_of_selfDual_swap (S : FusionSystem n k) {a b c : Fin n}
    (ha : S.ring.dual a = a) (hb : S.ring.dual b = b) (hc : S.ring.dual c = c)
    (hab : 0 < S.ring.N a b c) (hba : 0 < S.ring.N b a c)
    (h1 : comparisonScalar S a b c ≠ 0)
    (h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0)
    (hJ : S.J a b c * S.J b a c ≠ 1) :
    ¬ J_match S (derivedJGen S) := by
  intro hm
  apply hJ
  rw [hm a b c hab, hm b a c hba]
  exact derivedJGen_selfDual_swap S ha hb hc h1 h2

/-! ## §4 — the settled `(M)`-twist on the diagonal, and why Yang–Lee separates it

`Prop821CNorm.settledJ` is the twist the `(M)`/`(K)` chain computes.  On the
diagonal it reads `f_c κ_a² / (κ_c f_a²)`, against `1` for the derived twist, so
the two agree there exactly when the `(M)`-twist is trivial on that channel — the
general reason for the round-1 finding that Yang–Lee has the derived twist `1`
while `settledJ` is not `1`. -/

section Settled

variable [Algebra ℝ k]

/-- The settled twist on a diagonal channel, unfolded: no `b` appears. -/
theorem settledJ_selfDual_diag (S : FusionSystem n k) (hFP : S.ring.FPData)
    (a c : Fin n) :
    settledJ S hFP a a c =
      algebraMap ℝ k (hFP.fpdim c) * S.kappa a * S.kappa a /
        (S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim a)) :=
  rfl

/-- The settled twist is `1` on a diagonal channel exactly when the `(M)`-twist is
trivial there. -/
theorem settledJ_selfDual_diag_eq_one_iff (S : FusionSystem n k) (hFP : S.ring.FPData)
    {a c : Fin n}
    (hden : S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim a)
      ≠ 0) :
    settledJ S hFP a a c = 1 ↔
      algebraMap ℝ k (hFP.fpdim c) * S.kappa a * S.kappa a =
        S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim a) := by
  rw [settledJ_selfDual_diag, div_eq_one_iff_eq hden]

/-- **Derived versus settled on the diagonal.**  The derived twist is `1` there, so
the two twists agree on a supported diagonal channel exactly when the `(M)`-twist
is trivial on it. -/
theorem derivedJGen_eq_settledJ_selfDual_diag_iff (S : FusionSystem n k)
    (hFP : S.ring.FPData) {a c : Fin n}
    (ha : S.ring.dual a = a) (hc : S.ring.dual c = c)
    (h : comparisonScalar S a a c ≠ 0)
    (hden : S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim a)
      ≠ 0) :
    derivedJGen S a a c = settledJ S hFP a a c ↔
      algebraMap ℝ k (hFP.fpdim c) * S.kappa a * S.kappa a =
        S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim a) := by
  rw [derivedJGen_selfDual_diag S ha hc h, eq_comm,
    settledJ_selfDual_diag_eq_one_iff S hFP hden]

end Settled

/-! ## §4b — the unconditional pointed version

On pointed data the `OmegaNe` bundle is a theorem (`omegaNe_of_pointed`), and it is
exactly the nonvanishing of the comparison scalar (`comparisonScalar_ne_zero_of_omegaNe`),
so the two structural statements lose their hypotheses: on a pointed datum with
self-dual labels the derived twist is `1` on the diagonal and reciprocal on swapped
pairs, from the axioms alone. -/

/-- Pointed data: the diagonal comparison scalar never vanishes on a supported
channel. -/
theorem comparisonScalar_ne_zero_diag_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a c : Fin n} (hN : 0 < S.ring.N a a c) :
    comparisonScalar S a a c ≠ 0 :=
  comparisonScalar_ne_zero_of_omegaNe S hn (omegaNe_of_pointed S hn hP hN)

/-- **Unconditional pointed diagonal triviality.**  On pointed data,
`derivedJGen S a a c = 1` on every supported channel with `dual a = a`,
`dual c = c` — no nonvanishing hypothesis left. -/
theorem derivedJGen_selfDual_diag_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a c : Fin n} (ha : S.ring.dual a = a)
    (hc : S.ring.dual c = c) (hN : 0 < S.ring.N a a c) :
    derivedJGen S a a c = 1 :=
  derivedJGen_selfDual_diag S ha hc (comparisonScalar_ne_zero_diag_of_pointed S hn hP hN)

/-- **Unconditional pointed swap law.**  On pointed data with self-dual labels,
`J_{a,b;c} · J_{b,a;c} = 1` on every supported swapped pair. -/
theorem derivedJGen_selfDual_swap_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (ha : S.ring.dual a = a)
    (hb : S.ring.dual b = b) (hc : S.ring.dual c = c)
    (hab : 0 < S.ring.N a b c) (hba : 0 < S.ring.N b a c) :
    derivedJGen S a b c * derivedJGen S b a c = 1 := by
  have h1 : comparisonScalar S a b c ≠ 0 :=
    comparisonScalar_ne_zero_of_omegaNe S hn (omegaNe_of_pointed S hn hP hab)
  have h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0 := by
    rw [ha, hb, hc]
    exact comparisonScalar_ne_zero_of_omegaNe S hn (omegaNe_of_pointed S hn hP hba)
  exact derivedJGen_selfDual_swap S ha hb hc h1 h2

end FusionCategory

/-! ## §5 — application: Yang–Lee, where every supported channel is diagonal

The Yang–Lee fusion ring is `τ ⊗ τ = 1 ⊕ τ` with `dual = id`, so the supported
channels are `(1,1;0)`, `(1,1;1)` and the four unit channels — all of the form
`(a,a;c)` or with a unit.  `derivedJGen_selfDual_diag` therefore gives the closed
form as soon as the two comparison scalars are nonzero, and on `YangLee.system`
they are explicit products in `ℤ[√5]`. -/

namespace FusionCategory

namespace YangLeeSelfDual

open FusionCategory.YangLee

/-- Both diagonal comparison scalars of the Yang–Lee datum are nonzero: the
denominators are `1 · (-φ)` and `φ · (-φ)` in `ℤ[√5]`, i.e. `-φ` and `-1`
up to the factor `4` of the pair model, and `φ = (1+√5)/2` is not `0`. -/
theorem comparisonScalar_ne_zero_diag : ∀ c : Fin 2,
    comparisonScalar system 1 1 c ≠ 0 := by
  intro c
  rw [comparisonScalar_def, dif_pos (show 0 < 2 by norm_num)]
  fin_cases c <;>
    · simp only [system, F, Finv, evPair, Fpair, FinvPair, ZP.zval, YangLee.N,
        Examples.fibN, Examples.fibDual, Examples.FibonacciRing]
      norm_num
      intro h
      have h1 : s5 = -1 := by linarith
      have hs : s5 * s5 = (5 : ℝ) := s5_sq
      rw [h1] at hs
      norm_num at hs

/-- **The Yang–Lee closed form**, from the structural theorem: on both supported
channels of `τ ⊗ τ` the derived twist is `1`. -/
theorem derivedJGen_eq_one (c : Fin 2) (h : 0 < N 1 1 c) :
    derivedJGen system 1 1 c = 1 := by
  have hc : system.ring.dual c = c := by fin_cases c <;> rfl
  exact derivedJGen_selfDual_diag system rfl hc (comparisonScalar_ne_zero_diag c)

end YangLeeSelfDual

end FusionCategory

#print axioms FusionCategory.derivedJGen_mul_swapDual
#print axioms FusionCategory.derivedJGen_selfDual_diag
#print axioms FusionCategory.not_j_match_of_selfDual_diag
#print axioms FusionCategory.not_j_match_of_selfDual_swap
#print axioms FusionCategory.derivedJGen_eq_settledJ_selfDual_diag_iff
#print axioms FusionCategory.YangLeeSelfDual.derivedJGen_eq_one
