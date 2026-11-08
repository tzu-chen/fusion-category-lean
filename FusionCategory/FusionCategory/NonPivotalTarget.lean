import FusionCategory.DerivedJBlockMatrix
import FusionCategory.DerivedJMate

/-!
# The non-pivotal target: the refutation criterion, kernel-checked

The swarm's target asks for a legal `FusionSystem n k` with

  `¬ ∃ φ, (∀ i, φ i ≠ 0) ∧ ∀ a b c, 0 < N a b c → derivedJGen a b c = φ a * φ b / φ c`,

i.e. a datum whose computed double-dual twist is **not** a coboundary over `k`.

This file records how such a datum can arise, and proves that in the first two shapes it
arises exactly from a *vanishing* of the computed twist on a supported channel:

* `not_hasPivotalTwist_of_derivedJGen_eq_zero` — one supported channel with
  `derivedJGen a b c = 0` refutes the target outright (a coboundary of a nowhere-zero
  `φ` is nowhere zero, so this is the only "by zero" failure).
* `derivedJGen_eq_zero_of_pairScalar_eq_zero` / `not_hasPivotalTwist_of_pairScalar_eq_zero`
  — the third refutation shape of the task description: a degenerate mate pairing
  (`pairScalar = 0`) on a supported channel forces `derivedJGen = 0` there (total
  division), hence refutes the target.
* `not_hasPivotalTwist_of_not_omegaNe` — and `derivedJGen` vanishes on a supported
  channel **exactly** off `OmegaNe` (`derivedJGen_ne_zero_iff_omegaNe`), the repo's frozen
  obligation `WP2.DerivedJ_ne_zero`.
* `omegaNe_of_hasPivotalTwist` — conversely the target's *positive* side forces `OmegaNe`
  at every supported channel.  Hence the search for a refutation and the repo's
  nonvanishing obligation are complementary halves of one statement: a datum is
  pivotal-in-the-computed-sense iff `derivedJGen` vanishes nowhere and its class is
  trivial.
* `hasPivotalTwist_iff_exists_pivotalFactor` — on data whose mate pairing is
  nonvanishing, the target's shape and `PivotalFactor` agree, so "not pivotal" in the
  task's sense is the literature's "no pivotal structure".
* `pivotalFactor_ratio_character` — two pivotal factors differ by a *monoidal
  character* (`ψ a * ψ b * φ c = ψ c * (φ a * φ b)` on supported channels): the solution
  set is a torsor over `Hom(UC → kˣ)` (Penneys, *Higher linear algebra*, Prop. 3.6.10),
  so pivotality is one consistency condition per datum, not a system to be solved afresh.

Axiom budget `[propext, Classical.choice, Quot.sound]` — see the `#print axioms` lines.
-/

namespace FusionCategory

variable {n : ℕ} {k : Type*} [Field k]

/-- **The target's negation shape.**  `HasPivotalTwist S` is the statement the task asks
to refute: the computed twist is the coboundary `δ(φ)` of a nowhere-zero `φ` on every
supported channel. -/
def HasPivotalTwist (S : FusionSystem n k) : Prop :=
  ∃ φ : Fin n → k, (∀ i : Fin n, φ i ≠ 0) ∧
    ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c

/-- **A vanishing computed twist on a supported channel refutes the target.**  Nothing
else is needed: a coboundary of a nowhere-zero `φ` is nowhere zero. -/
theorem not_hasPivotalTwist_of_derivedJGen_eq_zero (S : FusionSystem n k) {a b c : Fin n}
    (hN : 0 < S.ring.N a b c) (h0 : derivedJGen S a b c = 0) :
    ¬ HasPivotalTwist S := by
  rintro ⟨φ, hφ, hbc⟩
  have h := hbc a b c hN
  rw [h0] at h
  have hne : φ a * φ b / φ c ≠ 0 :=
    div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c)
  exact hne h.symm

/-- **A degenerate mate pairing on a supported channel forces the computed twist to
vanish there** (total division: `x / 0 = 0`).  This is the third refutation shape of the
task description, in one step. -/
theorem derivedJGen_eq_zero_of_pairScalar_eq_zero (S : FusionSystem n k) {a b c : Fin n}
    (h : pairScalar S a b c = 0) : derivedJGen S a b c = 0 := by
  rw [derivedJGen_eq_pairDual_div, h, div_zero]

/-- The third refutation shape: `pairScalar` vanishing on a supported channel. -/
theorem not_hasPivotalTwist_of_pairScalar_eq_zero (S : FusionSystem n k) {a b c : Fin n}
    (hN : 0 < S.ring.N a b c) (h : pairScalar S a b c = 0) :
    ¬ HasPivotalTwist S :=
  not_hasPivotalTwist_of_derivedJGen_eq_zero S hN
    (derivedJGen_eq_zero_of_pairScalar_eq_zero S h)

/-- **The second refutation shape is exactly the repo's frozen obligation.**  Off
`OmegaNe` on a supported channel the computed twist vanishes, so a counterexample to
`WP2.DerivedJ_ne_zero` *is* a refutation of the target. -/
theorem not_hasPivotalTwist_of_not_omegaNe (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) (h : ¬ OmegaNe S hn a b c) :
    ¬ HasPivotalTwist S := by
  refine not_hasPivotalTwist_of_derivedJGen_eq_zero S hN ?_
  by_contra hne
  exact h ((derivedJGen_ne_zero_iff_omegaNe S hn hN).mp hne)

/-- **The target's positive side forces `OmegaNe` everywhere**: a datum whose twist is the
coboundary of a nowhere-zero `φ` has a nowhere-vanishing twist.  So the frozen
nonvanishing obligation is not an extra technicality — it is half of pivotality. -/
theorem omegaNe_of_hasPivotalTwist (S : FusionSystem n k) (hn : 0 < n)
    (h : HasPivotalTwist S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    OmegaNe S hn a b c := by
  obtain ⟨φ, hφ, hbc⟩ := h
  refine (derivedJGen_ne_zero_iff_omegaNe S hn hN).mp ?_
  rw [hbc a b c hN]
  exact div_ne_zero (mul_ne_zero (hφ a) (hφ b)) (hφ c)

/-- **The target's shape is the literature's pivotality** wherever the mate pairing is
nonvanishing: `HasPivotalTwist S ↔ ∃ φ, PivotalFactor S φ`.  `PivotalFactor S φ` is the
equation `γ_a γ_b = γ_c T^c_{ab}` of a pivotal structure, Thm. 5.4 of arXiv:1502.02882. -/
theorem hasPivotalTwist_iff_exists_pivotalFactor (S : FusionSystem n k)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0) :
    HasPivotalTwist S ↔ ∃ φ : Fin n → k, PivotalFactor S φ := by
  constructor
  · rintro ⟨φ, hφ, hbc⟩
    exact ⟨φ, pivotalFactor_of_coboundary S hφ hne hbc⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, hφ.1, derivedJGen_eq_coboundary_of_pivotalFactor S hφ hne⟩

/-- **Two pivotal factors differ by a monoidal character.**  On data whose mate pairing is
nonvanishing, the ratio of two pivotal factors is multiplicative on the supported
channels: `ψ a * ψ b * φ c = ψ c * (φ a * φ b)`.  Hence the pivotal factors of a datum
form a coset of `Hom(UC → kˣ)`. -/
theorem pivotalFactor_ratio_character (S : FusionSystem n k)
    (hne : ∀ a b c : Fin n, 0 < S.ring.N a b c → pairScalar S a b c ≠ 0)
    {φ ψ : Fin n → k} (hφ : PivotalFactor S φ) (hψ : PivotalFactor S ψ) :
    ∀ a b c : Fin n, 0 < S.ring.N a b c →
      ψ a * ψ b * φ c = ψ c * (φ a * φ b) := by
  intro a b c hN
  have hP := hne a b c hN
  have e1 := hφ.2 a b c hN
  have e2 := hψ.2 a b c hN
  have key : pairScalar S a b c * ((φ a * φ b) * ψ c)
      = pairScalar S a b c * ((ψ a * ψ b) * φ c) := by
    calc pairScalar S a b c * ((φ a * φ b) * ψ c)
        = (pairScalar S a b c * (φ a * φ b)) * ψ c := by ring
      _ = (pairDual S a b c * φ c) * ψ c := by rw [← e1]
      _ = (pairDual S a b c * ψ c) * φ c := by ring
      _ = (pairScalar S a b c * (ψ a * ψ b)) * φ c := by rw [← e2]
      _ = pairScalar S a b c * ((ψ a * ψ b) * φ c) := by ring
  have h3 : (φ a * φ b) * ψ c = (ψ a * ψ b) * φ c := mul_left_cancel₀ hP key
  calc ψ a * ψ b * φ c = (ψ a * ψ b) * φ c := by ring
    _ = (φ a * φ b) * ψ c := h3.symm
    _ = ψ c * (φ a * φ b) := by ring

/-- **The degenerate mate pairing is *one* inverse-associator entry.**  On a supported
channel the `F`-factor of `pairScalar` is a boundary entry, hence nonzero
(`boundary_F_ne_zero`), and `ev` is nowhere zero; so
`pairScalar a b c = 0 ↔ Finv a* a b b c 0 = 0`.  This is the exact scalar to compute
when searching for the degenerate-pairing refutation: no associator table is needed,
only the `(0,c)`-entry of the inverse block `F^{a* a b}_b`. -/
theorem pairScalar_ne_zero_iff_omegaQ_ne_zero (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    pairScalar S a b c ≠ 0 ↔ S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0 := by
  have hF : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b ≠ 0 := by
    have h := boundary_F_ne_zero S hn (x := S.ring.dual b) (y := S.ring.dual a)
      (z := S.ring.dual c) (N_dual_swap S hN)
    simpa only [FusionRing.dual_dual] using h
  have hev : S.ev a * S.ev b ≠ 0 := mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b)
  rw [pairScalar_self S hn a b c]
  constructor
  · intro h hQ
    exact h (by rw [hQ, mul_zero, zero_mul])
  · intro hQ
    exact mul_ne_zero (mul_ne_zero hF hQ) hev

/-- **The sharp form of the degenerate-pairing refutation**: a single vanishing
inverse-associator entry `Finv a* a b b c 0` on a supported channel refutes the target.
Together with `not_hasPivotalTwist_of_not_omegaNe` this shows that the task's "second"
and "third" refutation shapes are one and the same condition. -/
theorem not_hasPivotalTwist_of_omegaQ_eq_zero (S : FusionSystem n k) (hn : 0 < n)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c)
    (h : S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ = 0) :
    ¬ HasPivotalTwist S := by
  refine not_hasPivotalTwist_of_pairScalar_eq_zero S hN ?_
  by_contra hne
  exact ((pairScalar_ne_zero_iff_omegaQ_ne_zero S hn hN).mp hne) h

#print axioms FusionCategory.pairScalar_ne_zero_iff_omegaQ_ne_zero
#print axioms FusionCategory.not_hasPivotalTwist_of_omegaQ_eq_zero
#print axioms FusionCategory.not_hasPivotalTwist_of_derivedJGen_eq_zero
#print axioms FusionCategory.derivedJGen_eq_zero_of_pairScalar_eq_zero
#print axioms FusionCategory.not_hasPivotalTwist_of_pairScalar_eq_zero
#print axioms FusionCategory.not_hasPivotalTwist_of_not_omegaNe
#print axioms FusionCategory.omegaNe_of_hasPivotalTwist
#print axioms FusionCategory.hasPivotalTwist_iff_exists_pivotalFactor
#print axioms FusionCategory.pivotalFactor_ratio_character

end FusionCategory
