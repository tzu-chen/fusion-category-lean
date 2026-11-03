/-
WP2 round 2, member m8, direction D8: the pointed δ(κ) theorem for `derivedJ`.

Task 2.3 target 2 of the freeze (`WP2.DerivedJ_pointed_eq_delta_kappa`): on *pointed*
data — the fusion ring of a finite group — the derived twist is the coboundary of the
duality normalisation, `derivedJ a b c = κ_a κ_b / κ_c`.  Round 1 proved it on three
witnesses; this file proves it in general `n`, from the axioms alone.

The proof is the standard cocycle computation, in the reconstruction's own language:

* `N_shift`: on pointed data, `a ⊗ b ∋ c` implies `c ⊗ b* ∋ a` (the fusion ring's
  Frobenius reciprocity, from `associativity` + `unit`/`dual` normalisations);
* the three pentagon instances `pentagon_P1`–`P3`, each the pentagon at a four-factor
  tuple whose five terms are supported automatically, with the `k`-sum collapsed by
  multiplicity-freeness and the unit entries evaluated by `F_unit_left`,
  `F_unit_right` and `TriangleCheck.triangle`;
* `key_identity`: the resulting cocycle identity;
* `derivedJGen_eq_delta_kappa_of_pointed`: the theorem.

Nothing cancels an `F`-entry without the explicit nonvanishing `F_ne_zero_of_pointed`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.Statements2
import FusionCategory.Triangle
import FusionCategory.DerivedJScalar
import FusionCategory.DerivedJLaws

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — uniqueness of channels, and Frobenius reciprocity -/

/-- Pointedness makes the channel of `a ⊗ b` unique. -/
theorem pointed_unique (S : FusionSystem n k) (hP : WP2.Pointed S) {a b c c' : Fin n}
    (h : 0 < S.ring.N a b c) (h' : 0 < S.ring.N a b c') : c = c' := by
  obtain ⟨c₀, _, huniq⟩ := hP a b
  rw [huniq c h, huniq c' h']

/-- **Frobenius reciprocity on pointed data**: if `c` is a channel of `a ⊗ b`, then
`a` is a channel of `c ⊗ b*`.  From `associativity` with `(a, b, b*, a)` together with
`right_unit` and `dual_coeff`. -/
theorem N_shift (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    0 < S.ring.N c (S.ring.dual b) a := by
  have hsum := S.ring.associativity a b (S.ring.dual b) a
  -- ∑ p, N a b p * N p b* a = ∑ q, N b b* q * N a q a
  have hL : (∑ p : Fin n, (S.ring.N a b p : ℕ) * S.ring.N p (S.ring.dual b) a)
      = S.ring.N a b c * S.ring.N c (S.ring.dual b) a := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun p : Fin n => (S.ring.N a b p : ℕ) * S.ring.N p (S.ring.dual b) a) (a := c) ?_ ?_
    · intro p _ hp
      have hz : S.ring.N a b p = 0 := by
        have hle : S.ring.N a b p ≤ 1 := S.mult_free a b p
        rcases Nat.eq_zero_or_pos (S.ring.N a b p) with h0 | hpos
        · exact h0
        · exact absurd (pointed_unique S hP hpos hN) hp
      rw [hz]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : (∑ q : Fin n, (S.ring.N b (S.ring.dual b) q : ℕ) * S.ring.N a q a) = 1 := by
    have hstep : (∑ q : Fin n, (S.ring.N b (S.ring.dual b) q : ℕ) * S.ring.N a q a)
        = (S.ring.N b (S.ring.dual b) ⟨0, hn⟩ : ℕ) * S.ring.N a ⟨0, hn⟩ a := by
      refine Finset.sum_eq_single (s := Finset.univ)
        (f := fun q : Fin n => (S.ring.N b (S.ring.dual b) q : ℕ) * S.ring.N a q a)
        (a := (⟨0, hn⟩ : Fin n)) ?_ ?_
      · intro q _ hq
        have hq0 : S.ring.N b (S.ring.dual b) q = 0 := by
          rcases Nat.eq_zero_or_pos (S.ring.N b (S.ring.dual b) q) with h0 | hpos
          · exact h0
          · exact absurd (pointed_unique S hP hpos (pos_dual_coeff S hn b)) hq
        rw [hq0]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hstep]
    have h1 : S.ring.N b (S.ring.dual b) ⟨0, hn⟩ = 1 := by
      rw [S.ring.dual_coeff hn b]
      simp
    have h2 : S.ring.N a ⟨0, hn⟩ a = 1 := by
      rw [S.ring.right_unit hn a a]
      simp
    rw [h1, h2]
  rw [hL] at hsum
  rw [hR] at hsum
  have hc1 : S.ring.N a b c = 1 := by
    have := S.mult_free a b c
    omega
  rw [hc1, one_mul] at hsum
  omega

/-! ## §2 — nonvanishing and the reciprocity corollaries -/

/-- On pointed data, `F` is nonzero on every supported tuple.  (The collapse of
`F_comp_inv` computes it as the reciprocal of `Finv`.) -/
theorem F_ne_zero_of_pointed (S : FusionSystem n k) (hP : WP2.Pointed S) {a b c d e f : Fin n}
    (he : 0 < S.ring.N a b e) (hecd : 0 < S.ring.N e c d)
    (hbcf : 0 < S.ring.N b c f) (hafd : 0 < S.ring.N a f d) :
    S.F a b c d e f ≠ 0 := by
  have hu : ∀ f' : Fin n, 0 < S.ring.N b c f' → f' = f :=
    fun f' hf' => pointed_unique S hP hf' hbcf
  have h := finv_mul_F_of_unique' S hu he hecd hbcf hafd
  intro h0
  rw [h0, mul_zero] at h
  exact one_ne_zero h.symm

/-- `Finv` is the reciprocal of `F` on a supported block of a pointed datum. -/
theorem Finv_eq_inv_of_pointed (S : FusionSystem n k) (hP : WP2.Pointed S) {a b c d e f : Fin n}
    (he : 0 < S.ring.N a b e) (hecd : 0 < S.ring.N e c d)
    (hbcf : 0 < S.ring.N b c f) (hafd : 0 < S.ring.N a f d) :
    S.Finv a b c d f e = (S.F a b c d e f)⁻¹ := by
  have hu : ∀ f' : Fin n, 0 < S.ring.N b c f' → f' = f :=
    fun f' hf' => pointed_unique S hP hf' hbcf
  have h := finv_mul_F_of_unique' S hu he hecd hbcf hafd
  rw [mul_comm] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `a ⊗ b ∋ c` implies `b ⊗ c* ∋ a*` (duality transfer of `N_shift`). -/
theorem N_dual_shift (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := by
  have h := N_shift S hn hP hN
  have h2 : S.ring.N b (S.ring.dual c) (S.ring.dual a) = S.ring.N c (S.ring.dual b) a := by
    rw [S.ring.dual_symm c (S.ring.dual b) a]
    simp only [FusionRing.dual_dual]
  rw [h2]
  exact h

/-- `b ⊗ c* ∋ a*` implies `a* ⊗ c ∋ b` (the converse direction of `N_shift`). -/
theorem N_dual_shift' (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (h : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a)) :
    0 < S.ring.N (S.ring.dual a) c b := by
  have h' := N_shift S hn hP h
  rwa [FusionRing.dual_dual] at h'

/-- `a ⊗ b ∋ c` implies `b* ⊗ a* ∋ c*` (`dual_symm`). -/
theorem N_dual_symm (S : FusionSystem n k) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) := by
  rw [← S.ring.dual_symm a b c]
  exact hN

/-! ## §3 — the three pentagon instances

Each is the pentagon at a four-factor tuple `(a₁, b₁, c₁, d₁)`; with
`e = a₁b₁`, `k = b₁c₁`, `i = c₁d₁`, `j = b₁c₁d₁`, `x = a₁b₁c₁` and `r = a₁b₁c₁d₁`
all five of its terms are supported automatically, and the `k`-sum has a single
surviving term by multiplicity-freeness.  The unit entries are evaluated by
`F_unit_left`, `F_unit_right` and `TriangleCheck.triangle`. -/

/-- Pentagon at `(a, a*, a, b)`: `ω(a,a⁻¹,a)·ω(a⁻¹,a,b) = ω(a,a⁻¹,ab)`. -/
theorem pentagon_P1 (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F (S.ring.dual a) a b b ⟨0, hn⟩ c
      = S.F a (S.ring.dual a) c c ⟨0, hn⟩ b := by
  have hp := S.pentagon a (S.ring.dual a) a b ⟨0, hn⟩ c b c a
  have hcol : (∑ k : Fin n, S.F a (S.ring.dual a) a a ⟨0, hn⟩ k * S.F a k b c a b *
        S.F (S.ring.dual a) a b b k c)
      = S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ * S.F a ⟨0, hn⟩ b c a b *
        S.F (S.ring.dual a) a b b ⟨0, hn⟩ c := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun k : Fin n => S.F a (S.ring.dual a) a a ⟨0, hn⟩ k * S.F a k b c a b *
        S.F (S.ring.dual a) a b b k c) (a := (⟨0, hn⟩ : Fin n)) ?_ ?_
    · intro k _ hk
      have hz : S.F a (S.ring.dual a) a a ⟨0, hn⟩ k = 0 := by
        refine S.F_support a (S.ring.dual a) a a ⟨0, hn⟩ k ?_
        intro hcon
        exact hk (pointed_unique S hP hcon.2.2.1 (pos_dual_coeff' S hn a))
      rw [hz]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcol] at hp
  have hT : S.F a ⟨0, hn⟩ b c a b = 1 := TriangleCheck.triangle S hn a b c hN
  have hL : S.F ⟨0, hn⟩ a b c a c = 1 := by
    have h := S.F_unit_left hn a b c c hN
    simpa using h
  rw [hT, hL, mul_one, one_mul] at hp
  exact hp

/-- Pentagon at `(a, b, (ab)*, ab)`: `ω(a,b,(ab)⁻¹)·ω(a,a⁻¹,ab)·ω(b,(ab)⁻¹,ab) = ω(ab,(ab)⁻¹,ab)`. -/
theorem pentagon_P2 (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.F a (S.ring.dual a) c c ⟨0, hn⟩ b *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩
      = S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hbca : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := N_dual_shift S hn hP hN
  have hp := S.pentagon a b (S.ring.dual c) c c ⟨0, hn⟩ b c ⟨0, hn⟩
  have hcol : (∑ k : Fin n, S.F a b (S.ring.dual c) ⟨0, hn⟩ c k *
        S.F a k c c ⟨0, hn⟩ b * S.F b (S.ring.dual c) c b k ⟨0, hn⟩)
      = S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.F a (S.ring.dual a) c c ⟨0, hn⟩ b *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun k : Fin n => S.F a b (S.ring.dual c) ⟨0, hn⟩ c k * S.F a k c c ⟨0, hn⟩ b *
        S.F b (S.ring.dual c) c b k ⟨0, hn⟩) (a := S.ring.dual a) ?_ ?_
    · intro k _ hk
      have hz : S.F a b (S.ring.dual c) ⟨0, hn⟩ c k = 0 := by
        refine S.F_support a b (S.ring.dual c) ⟨0, hn⟩ c k ?_
        intro hcon
        exact hk (pointed_unique S hP hcon.2.2.1 hbca)
      rw [hz]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcol] at hp
  have hR : S.F a b ⟨0, hn⟩ c c b = 1 := by
    have h := S.F_unit_right hn a b c c hN
    simpa using h
  rw [hR, mul_one] at hp
  exact hp

/-- Pentagon at `(b, b*, a*, c)`: `ω(b,b⁻¹,a⁻¹)·ω(b,(ab)⁻¹,ab)·ω(b⁻¹,a⁻¹,ab) = ω(b,b⁻¹,b)`. -/
theorem pentagon_P3 (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ *
        S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b
      = S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hbac : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) := N_dual_symm S hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b :=
    N_dual_shift' S hn hP (N_dual_shift S hn hP hN)
  have hp := S.pentagon b (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ b ⟨0, hn⟩ b (S.ring.dual a)
  have hcol : (∑ k : Fin n, S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ k *
        S.F b k c b (S.ring.dual a) ⟨0, hn⟩ * S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ k b)
      = S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ *
        S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun k : Fin n => S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ k *
        S.F b k c b (S.ring.dual a) ⟨0, hn⟩ *
        S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ k b) (a := S.ring.dual c) ?_ ?_
    · intro k _ hk
      have hz : S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ k = 0 := by
        refine S.F_support b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ k ?_
        intro hcon
        exact hk (pointed_unique S hP hcon.2.2.1 hbac)
      rw [hz]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcol] at hp
  have hL : S.F ⟨0, hn⟩ (S.ring.dual a) c b (S.ring.dual a) b = 1 := by
    have h := S.F_unit_left hn (S.ring.dual a) c b b hacb
    simpa using h
  rw [hL, one_mul] at hp
  exact hp

/-! ## §4 — the resulting cocycle identity -/

/-- **The cocycle identity the three pentagon instances produce**, in the reconstruction's
own six-index language.  Written with `A₁ = F^{a a* a}_a(a,a)`, `A₂ = F^{a* a b}_b(1,ab)`,
`A₃ = F^{a a* ab}_{ab}(1,b)`, `B₁ = F^{a b (ab)*}_1(ab,a*)`, `B₂ = F^{b (ab)* ab}_{b}(a*,1)`,
`B₃ = F^{ab (ab)* ab}_{ab}(1,1)`, `C₁ = F^{b b* a*}_{a*}(1,(ab)*)`, `C₂ = F^{b* a* ab}_1((ab)*,b)`,
`C₃ = F^{b b* b}_b(1,1)` it reads `B₁ A₂ A₁ C₃ = C₂ C₁ B₃`. -/
theorem key_identity (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.F (S.ring.dual a) a b b ⟨0, hn⟩ c *
        S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩
      = S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
        S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hbca : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := N_dual_shift S hn hP hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b :=
    N_dual_shift' S hn hP (N_dual_shift S hn hP hN)
  -- hypothesis of the cancellation
  have hB2 : S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ ≠ 0 :=
    F_ne_zero_of_pointed S hP (a := b) (b := S.ring.dual c) (c := c) (d := b)
      (e := S.ring.dual a) (f := ⟨0, hn⟩) hbca hacb (pos_dual_coeff' S hn c)
      (pos_right_unit S hn b)
  have hP1' : S.F (S.ring.dual a) a b b ⟨0, hn⟩ c * S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩
      = S.F a (S.ring.dual a) c c ⟨0, hn⟩ b := by
    rw [mul_comm]
    exact pentagon_P1 S hn hP hN
  have hP2 := pentagon_P2 S hn hP (a := a) (b := b) (c := c) hN
  have hP3 := pentagon_P3 S hn hP (a := a) (b := b) (c := c) hN
  refine mul_right_cancel₀ hB2 ?_
  have e1 : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.F (S.ring.dual a) a b b ⟨0, hn⟩ c *
        S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩
      = S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by
    calc S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
          S.F (S.ring.dual a) a b b ⟨0, hn⟩ c *
          S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ *
          S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ *
          S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩
        = (S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
            (S.F (S.ring.dual a) a b b ⟨0, hn⟩ c *
              S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩)) *
            S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ *
            S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ := by ring
      _ = (S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
            S.F a (S.ring.dual a) c c ⟨0, hn⟩ b) *
            S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ *
            S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ := by rw [hP1']
      _ = ((S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
            S.F a (S.ring.dual a) c c ⟨0, hn⟩ b) *
            S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩) *
            S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by ring
      _ = S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
            S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by rw [hP2]
  have e2 : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
        S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩
      = S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by
    calc S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
          S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
          S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
          S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩
        = (S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩ (S.ring.dual c) *
            S.F b (S.ring.dual c) c b (S.ring.dual a) ⟨0, hn⟩ *
            S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b) *
          S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ := by ring
      _ = S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ *
            S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ := by
          rw [hP3]
          ring
  rw [e1, e2]

/-! ## §5 — the comparison-scalar form of the cocycle identity -/

/-- **The cocycle identity in the twist's own terms**: the product of the `c`-channel
comparison scalar's bracket with `κ_c` equals the product of the `(c*)`-channel
bracket with `κ_a κ_b`.  This is `key_identity` after replacing `Finv` by `F⁻¹`
(`Finv_eq_inv_of_pointed`) and `κ` by the snake values. -/
theorem key_bracket (S : FusionSystem n k) (hn : 0 < n) (hP : WP2.Pointed S)
    {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    (S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
        S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩) *
      S.kappa c
    = (S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
        S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩) * S.kappa a * S.kappa b := by
  have hbca : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := N_dual_shift S hn hP hN
  have hbasc : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    N_dual_symm S hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b := N_dual_shift' S hn hP hbca
  have hF1 : S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩
      = (S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩
          (S.ring.dual c))⁻¹ :=
    Finv_eq_inv_of_pointed S hP (pos_dual_coeff S hn b)
      (pos_left_unit S hn (S.ring.dual a)) hbasc hbca
  have hF2 : S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩
      = (S.F (S.ring.dual a) a b b ⟨0, hn⟩ c)⁻¹ :=
    Finv_eq_inv_of_pointed S hP (pos_dual_coeff' S hn a) (pos_left_unit S hn b) hN hacb
  have hka : S.kappa a = (S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩)⁻¹ := by
    have h : S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ * S.kappa a = 1 := by
      rw [mul_comm]
      exact S.snake_left hn a
    exact eq_inv_of_mul_eq_one_right h
  have hkb : S.kappa b = (S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩)⁻¹ := by
    have h : S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ * S.kappa b = 1 := by
      rw [mul_comm]
      exact S.snake_left hn b
    exact eq_inv_of_mul_eq_one_right h
  have hkc : S.kappa c = (S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩)⁻¹ := by
    have h : S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.kappa c = 1 := by
      rw [mul_comm]
      exact S.snake_left hn c
    exact eq_inv_of_mul_eq_one_right h
  have hne1 : S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩
      (S.ring.dual c) ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff S hn b) (pos_left_unit S hn (S.ring.dual a))
      hbasc hbca
  have hne2 : S.F (S.ring.dual a) a b b ⟨0, hn⟩ c ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff' S hn a) (pos_left_unit S hn b) hN hacb
  have hne3 : S.F a (S.ring.dual a) a a ⟨0, hn⟩ ⟨0, hn⟩ ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff S hn a) (pos_left_unit S hn a)
      (pos_dual_coeff' S hn a) (pos_right_unit S hn a)
  have hne4 : S.F b (S.ring.dual b) b b ⟨0, hn⟩ ⟨0, hn⟩ ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff S hn b) (pos_left_unit S hn b)
      (pos_dual_coeff' S hn b) (pos_right_unit S hn b)
  have hne5 : S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff S hn c) (pos_left_unit S hn c)
      (pos_dual_coeff' S hn c) (pos_right_unit S hn c)
  rw [hF1, hF2, hka, hkb, hkc]
  have hkey := key_identity S hn hP hN
  field_simp
  linear_combination hkey

/-! ## §6 — the pointed δ(κ) theorem -/

/-- The bookkeeping-free algebraic core of the last step. -/
theorem div_div_key {K : Type*} [Field K] (ev eva evb X Y ka kb kc : K)
    (hev : ev ≠ 0) (hD : eva * evb ≠ 0) (hY : Y ≠ 0) (hk : kc ≠ 0)
    (hkey : X * kc = Y * ka * kb) :
    ev / (Y * eva * evb) / (ev / (X * evb * eva)) = ka * kb / kc := by
  have ha : eva ≠ 0 := fun h => hD (by rw [h, zero_mul])
  have hb : evb ≠ 0 := fun h => hD (by rw [h, mul_zero])
  have h1 : ev / (Y * eva * evb) / (ev / (X * evb * eva))
      = (X * evb * eva) / (Y * eva * evb) := by
    field_simp
  rw [h1]
  have h2 : (X * evb * eva) / (Y * eva * evb) = X / Y := by
    field_simp
    try ring
  rw [h2]
  field_simp
  try linear_combination hkey

/-- **Task 2.3 target 2** (`WP2.DerivedJ_pointed_eq_delta_kappa`): on pointed data the
derived twist is the coboundary of the duality normalisation. -/
theorem derivedJGen_eq_delta_kappa_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    derivedJGen S a b c = S.kappa a * S.kappa b / S.kappa c := by
  have hkey := key_bracket S hn hP hN
  have hbca : 0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := N_dual_shift S hn hP hN
  have hbasc : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    N_dual_symm S hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b := N_dual_shift' S hn hP hbca
  have hFX : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) ≠ 0 :=
    F_ne_zero_of_pointed S hP hN (pos_dual_coeff S hn c) hbca (pos_dual_coeff S hn a)
  have hFB : S.F b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) ⟨0, hn⟩
      (S.ring.dual c) ≠ 0 :=
    F_ne_zero_of_pointed S hP (pos_dual_coeff S hn b) (pos_left_unit S hn (S.ring.dual a))
      hbasc hbca
  have hFiX : S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a)
      (S.ring.dual c) ⟨0, hn⟩ ≠ 0 := by
    rw [Finv_eq_inv_of_pointed S hP (pos_dual_coeff S hn b)
      (pos_left_unit S hn (S.ring.dual a)) hbasc hbca]
    exact inv_ne_zero hFB
  have hX : S.F a b (S.ring.dual c) ⟨0, hn⟩ c (S.ring.dual a) *
      S.Finv b (S.ring.dual b) (S.ring.dual a) (S.ring.dual a) (S.ring.dual c) ⟨0, hn⟩
      ≠ 0 := mul_ne_zero hFX hFiX
  have hFY : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b ≠ 0 :=
    F_ne_zero_of_pointed S hP hbasc (pos_dual_coeff' S hn c) hacb (pos_dual_coeff' S hn b)
  have hFiY : S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0 := by
    rw [Finv_eq_inv_of_pointed S hP (pos_dual_coeff' S hn a) (pos_left_unit S hn b) hN hacb]
    exact inv_ne_zero (F_ne_zero_of_pointed S hP (pos_dual_coeff' S hn a) (pos_left_unit S hn b)
      hN hacb)
  have hY : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b *
      S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0 := mul_ne_zero hFY hFiY
  unfold derivedJGen comparisonScalar
  rw [dif_pos hn, dif_pos hn]
  simp only [FusionRing.dual_dual, S.ev_dual]
  exact div_div_key (S.ev c) (S.ev a) (S.ev b) _ _ (S.kappa a) (S.kappa b) (S.kappa c)
    (S.ev_ne_zero c) (mul_ne_zero (S.ev_ne_zero a) (S.ev_ne_zero b)) hY (S.kappa_ne_zero c) hkey

/-- **The frozen statement of `Statements2`, discharged**: `WP2.DerivedJ_pointed_eq_delta_kappa`
holds of the derived twist. -/
theorem WP2_DerivedJ_pointed_eq_delta_kappa :
    WP2.DerivedJ_pointed_eq_delta_kappa
      (fun {n : ℕ} (S : FusionSystem n ℂ) => derivedJGen S) := by
  intro n S hP a b c hN
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact a.elim0
    · exact h0
  exact derivedJGen_eq_delta_kappa_of_pointed S hn hP hN

/-- On pointed data the comparison scalar is nonzero on every supported channel: its
bracket is a product of two nonzero `F`-entries and the evaluation. -/
theorem comparisonScalar_ne_zero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {x y z : Fin n} (hN : 0 < S.ring.N x y z) :
    comparisonScalar S x y z ≠ 0 := by
  have hyx : 0 < S.ring.N (S.ring.dual y) (S.ring.dual x) (S.ring.dual z) := N_dual_symm S hN
  have hxzy : 0 < S.ring.N (S.ring.dual x) z y :=
    N_dual_shift' S hn hP (N_dual_shift S hn hP hN)
  have hF : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y ≠ 0 :=
    F_ne_zero_of_pointed S hP hyx (pos_dual_coeff' S hn z) hxzy (pos_dual_coeff' S hn y)
  have hFi : S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ ≠ 0 := by
    rw [Finv_eq_inv_of_pointed S hP (pos_dual_coeff' S hn x) (pos_left_unit S hn y) hN hxzy]
    exact inv_ne_zero (F_ne_zero_of_pointed S hP (pos_dual_coeff' S hn x) (pos_left_unit S hn y)
      hN hxzy)
  unfold comparisonScalar
  rw [dif_pos hn]
  exact div_ne_zero (S.ev_ne_zero z) (mul_ne_zero (mul_ne_zero (mul_ne_zero hF hFi)
    (S.ev_ne_zero x)) (S.ev_ne_zero y))

/-- **Nonvanishing of the derived twist on pointed data** — the `Pointed` case of the frozen
`WP2.DerivedJ_ne_zero` (which is stated for arbitrary data, where `F` may vanish). -/
theorem derivedJGen_ne_zero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    derivedJGen S a b c ≠ 0 := by
  have h1 : comparisonScalar S a b c ≠ 0 := comparisonScalar_ne_zero_of_pointed S hn hP hN
  have h2 : comparisonScalar S (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) ≠ 0 :=
    comparisonScalar_ne_zero_of_pointed S hn hP (N_dual_symm S hN)
  exact div_ne_zero h1 h2

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.pointed_unique
#print axioms FusionCategory.N_shift
#print axioms FusionCategory.N_dual_shift
#print axioms FusionCategory.N_dual_shift'
#print axioms FusionCategory.N_dual_symm
#print axioms FusionCategory.F_ne_zero_of_pointed
#print axioms FusionCategory.Finv_eq_inv_of_pointed
#print axioms FusionCategory.pentagon_P1
#print axioms FusionCategory.pentagon_P2
#print axioms FusionCategory.pentagon_P3
#print axioms FusionCategory.key_identity
#print axioms FusionCategory.key_bracket
#print axioms FusionCategory.div_div_key
#print axioms FusionCategory.derivedJGen_eq_delta_kappa_of_pointed
#print axioms FusionCategory.WP2_DerivedJ_pointed_eq_delta_kappa
#print axioms FusionCategory.comparisonScalar_ne_zero_of_pointed
#print axioms FusionCategory.derivedJGen_ne_zero_of_pointed
