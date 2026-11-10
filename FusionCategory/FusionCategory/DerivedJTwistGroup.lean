/-
WP3 closure round, member m6, direction d14: **the twist group**.

`DerivedJLaws.withJ` replaces the carried twist `S.J` of a skeletal datum by any other
admissible table, and `derivedJGen_withJ` records that the computed (double-dual) twist is
blind to that replacement.  This file closes the structure of the set of admissible twists
itself: on a fixed datum — same ring, `F`, `Finv`, `ev`, `coev` — the admissible twists are
closed under **pointwise product** and **inversion**.  Hence they form a group, `derivedJGen`
is a canonical element of it, and `J_match S D` is exactly the statement that `D` agrees with
the canonical element; the failure of `J_match` on a tree witness is therefore a *torsor*
statement, not an accident of a particular table.

The two operations are cheap in the twist fields and not at all cheap in the associator: the
product field `J_coherent` is a polynomial identity that never divides, while the inverse
field needs the support split `F = 0` / `F ≠ 0` (cancellation is legal exactly on a supported
channel with a nonzero associator entry, and the `F = 0` case is vacuous on both sides).

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.DerivedJLaws
import FusionCategory.Statements

set_option autoImplicit false

namespace FusionCategory

universe u

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — the two operations on twist tables -/

/-- The pointwise product of two twist tables. -/
def twistMulTab (J J' : Fin n → Fin n → Fin n → k) : Fin n → Fin n → Fin n → k :=
  fun a b c => J a b c * J' a b c

/-- The pointwise inverse of a twist table. -/
def twistInvTab (J : Fin n → Fin n → Fin n → k) : Fin n → Fin n → Fin n → k :=
  fun a b c => (J a b c)⁻¹

@[simp] theorem twistMulTab_apply (J J' : Fin n → Fin n → Fin n → k) (a b c : Fin n) :
    twistMulTab J J' a b c = J a b c * J' a b c := rfl

@[simp] theorem twistInvTab_apply (J : Fin n → Fin n → Fin n → k) (a b c : Fin n) :
    twistInvTab J a b c = (J a b c)⁻¹ := rfl

/-- Double inversion returns the table. -/
theorem twistInvTab_involutive (J : Fin n → Fin n → Fin n → k) :
    twistInvTab (twistInvTab J) = J := by
  funext a b c
  simp

/-! ## §2 — closure of the twist axioms under the product -/

theorem twistMul_ne_zero (S : FusionSystem n k) (J J' : Fin n → Fin n → Fin n → k)
    (h : ∀ i j kk, 0 < S.ring.N i j kk → J i j kk ≠ 0)
    (h' : ∀ i j kk, 0 < S.ring.N i j kk → J' i j kk ≠ 0) :
    ∀ i j kk, 0 < S.ring.N i j kk → twistMulTab J J' i j kk ≠ 0 :=
  fun i j kk hN => mul_ne_zero (h i j kk hN) (h' i j kk hN)

theorem twistMul_unit_left (J J' : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1)
    (h' : ∀ (hn : 0 < n) (j : Fin n), J' ⟨0, hn⟩ j j = 1) :
    ∀ (hn : 0 < n) (j : Fin n), twistMulTab J J' ⟨0, hn⟩ j j = 1 :=
  fun hn j => by simp [twistMulTab, h hn j, h' hn j]

theorem twistMul_unit_right (J J' : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1)
    (h' : ∀ (hn : 0 < n) (i : Fin n), J' i ⟨0, hn⟩ i = 1) :
    ∀ (hn : 0 < n) (i : Fin n), twistMulTab J J' i ⟨0, hn⟩ i = 1 :=
  fun hn i => by simp [twistMulTab, h hn i, h' hn i]

theorem twistMul_dual (S : FusionSystem n k) (J J' : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (i : Fin n), J i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h' : ∀ (hn : 0 < n) (i : Fin n), J' i (S.ring.dual i) ⟨0, hn⟩ = 1) :
    ∀ (hn : 0 < n) (i : Fin n), twistMulTab J J' i (S.ring.dual i) ⟨0, hn⟩ = 1 :=
  fun hn i => by simp [twistMulTab, h hn i, h' hn i]

/-- The fourth law is closed under pointwise product: the `F`-factors need no
nonzero hypothesis, because the two hypotheses are multiplied against each other. -/
theorem twistMul_coherent (S : FusionSystem n k) (J J' : Fin n → Fin n → Fin n → k)
    (h : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f)
    (h' : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J' a b e * J' e c d * S.F a b c d e f = J' b c f * J' a f d * S.F a b c d e f) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      twistMulTab J J' a b e * twistMulTab J J' e c d * S.F a b c d e f =
        twistMulTab J J' b c f * twistMulTab J J' a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  have e1 := h a b c d e f h1 h2 h3 h4
  have e2 := h' a b c d e f h1 h2 h3 h4
  simp only [twistMulTab]
  calc J a b e * J' a b e * (J e c d * J' e c d) * S.F a b c d e f
      = (J a b e * J e c d * S.F a b c d e f) * (J' a b e * J' e c d) := by ring
    _ = (J b c f * J a f d * S.F a b c d e f) * (J' a b e * J' e c d) := by rw [e1]
    _ = (J b c f * J a f d) * (J' a b e * J' e c d * S.F a b c d e f) := by ring
    _ = (J b c f * J a f d) * (J' b c f * J' a f d * S.F a b c d e f) := by rw [e2]
    _ = J b c f * J' b c f * (J a f d * J' a f d) * S.F a b c d e f := by ring

/-! ## §3 — closure of the twist axioms under inversion -/

theorem twistInv_ne_zero (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k)
    (h : ∀ i j kk, 0 < S.ring.N i j kk → J i j kk ≠ 0) :
    ∀ i j kk, 0 < S.ring.N i j kk → twistInvTab J i j kk ≠ 0 :=
  fun i j kk hN => inv_ne_zero (h i j kk hN)

theorem twistInv_unit_left (J : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (j : Fin n), J ⟨0, hn⟩ j j = 1) :
    ∀ (hn : 0 < n) (j : Fin n), twistInvTab J ⟨0, hn⟩ j j = 1 :=
  fun hn j => by simp [twistInvTab, h hn j]

theorem twistInv_unit_right (J : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (i : Fin n), J i ⟨0, hn⟩ i = 1) :
    ∀ (hn : 0 < n) (i : Fin n), twistInvTab J i ⟨0, hn⟩ i = 1 :=
  fun hn i => by simp [twistInvTab, h hn i]

theorem twistInv_dual (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k)
    (h : ∀ (hn : 0 < n) (i : Fin n), J i (S.ring.dual i) ⟨0, hn⟩ = 1) :
    ∀ (hn : 0 < n) (i : Fin n), twistInvTab J i (S.ring.dual i) ⟨0, hn⟩ = 1 :=
  fun hn i => by simp [twistInvTab, h hn i]

/-- The fourth law is closed under inversion.  Cancellation is legal exactly on a
supported channel whose associator entry is nonzero; where the entry vanishes the
equation is vacuous on both sides. -/
theorem twistInv_coherent (S : FusionSystem n k) (J : Fin n → Fin n → Fin n → k)
    (h : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J a b e * J e c d * S.F a b c d e f = J b c f * J a f d * S.F a b c d e f) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      twistInvTab J a b e * twistInvTab J e c d * S.F a b c d e f =
        twistInvTab J b c f * twistInvTab J a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4
  have e1 := h a b c d e f h1 h2 h3 h4
  by_cases hF : S.F a b c d e f = 0
  · simp [twistInvTab, hF]
  · have key : J a b e * J e c d = J b c f * J a f d :=
      mul_right_cancel₀ hF e1
    have hinv : (J a b e)⁻¹ * (J e c d)⁻¹ = (J b c f)⁻¹ * (J a f d)⁻¹ := by
      rw [← mul_inv, ← mul_inv, key]
    simp only [twistInvTab]
    rw [hinv]

/-! ## §4 — the group structure on admissible twists -/

/-- **The datum with the pointwise product twist**: same ring, `F`, `Finv`, `ev`,
`coev`; carried twist `S.J * J'`. -/
noncomputable def twistMul (S : FusionSystem n k) (J' : Fin n → Fin n → Fin n → k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J' i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J' ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J' i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J' i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J' a b e * J' e c d * S.F a b c d e f = J' b c f * J' a f d * S.F a b c d e f) :
    FusionSystem n k :=
  withJ S (twistMulTab S.J J')
    (twistMul_ne_zero S S.J J' S.J_ne_zero hne)
    (twistMul_unit_left S.J J' S.J_unit_left h1)
    (twistMul_unit_right S.J J' S.J_unit_right h2)
    (twistMul_dual S S.J J' S.J_dual h3)
    (twistMul_coherent S S.J J' S.J_coherent h4)

/-- **The datum with the inverted carried twist.** -/
noncomputable def twistInv (S : FusionSystem n k) : FusionSystem n k :=
  withJ S (twistInvTab S.J)
    (twistInv_ne_zero S S.J S.J_ne_zero)
    (twistInv_unit_left S.J S.J_unit_left)
    (twistInv_unit_right S.J S.J_unit_right)
    (twistInv_dual S S.J S.J_dual)
    (twistInv_coherent S S.J S.J_coherent)

/-- The computed twist does not see the operation: it is a function of
`(ring, F, Finv, ev, coev)` only (`rfl`). -/
theorem derivedJGen_twistMul (S : FusionSystem n k) (J' : Fin n → Fin n → Fin n → k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J' i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J' ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J' i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J' i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J' a b e * J' e c d * S.F a b c d e f = J' b c f * J' a f d * S.F a b c d e f)
    (a b c : Fin n) :
    derivedJGen (twistMul S J' hne h1 h2 h3 h4) a b c = derivedJGen S a b c := rfl

/-- The same for the inverted datum. -/
theorem derivedJGen_twistInv (S : FusionSystem n k) (a b c : Fin n) :
    derivedJGen (twistInv S) a b c = derivedJGen S a b c := rfl

/-- The ring of the product datum is the ring: the operations move the twist only. -/
@[simp] theorem twistMul_ring (S : FusionSystem n k) (J' : Fin n → Fin n → Fin n → k)
    (hne h1 h2 h3 h4) : (twistMul S J' hne h1 h2 h3 h4).ring = S.ring := rfl

@[simp] theorem twistInv_ring (S : FusionSystem n k) : (twistInv S).ring = S.ring := rfl

/-- The carried twist of the product datum is the product of the carried twists. -/
@[simp] theorem twistMul_J (S : FusionSystem n k) (J' : Fin n → Fin n → Fin n → k)
    (hne h1 h2 h3 h4) (a b c : Fin n) :
    (twistMul S J' hne h1 h2 h3 h4).J a b c = S.J a b c * J' a b c := rfl

/-- The carried twist of the inverted datum is the inverse. -/
@[simp] theorem twistInv_J (S : FusionSystem n k) (a b c : Fin n) :
    (twistInv S).J a b c = (S.J a b c)⁻¹ := rfl

/-! ## §5 — `J_match` is a torsor statement

`J_match` compares a candidate table with the carried one.  Under the group
operations it becomes the statement that the *quotient* of the candidate by the
carried twist is trivial, i.e. that the carried twist is the canonical one — which
is what the tree's honest/false witness pair exhibits.  -/

/-- On the product datum, `J_match` at a candidate `D` is the pointwise equation
`D = S.J * J'`. -/
theorem j_match_twistMul_iff (S : FusionSystem n k) (J' : Fin n → Fin n → Fin n → k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → J' i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), J' ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), J' i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n), J' i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      J' a b e * J' e c d * S.F a b c d e f = J' b c f * J' a f d * S.F a b c d e f)
    (D : Fin n → Fin n → Fin n → k) :
    J_match (twistMul S J' hne h1 h2 h3 h4) D ↔
      ∀ a b c : Fin n, 0 < S.ring.N a b c → S.J a b c * J' a b c = D a b c :=
  Iff.rfl

/-- On the inverted datum, `J_match` at a candidate `D` is the pointwise equation
`D = S.J⁻¹`. -/
theorem j_match_twistInv_iff (S : FusionSystem n k) (D : Fin n → Fin n → Fin n → k) :
    J_match (twistInv S) D ↔
      ∀ a b c : Fin n, 0 < S.ring.N a b c → (S.J a b c)⁻¹ = D a b c :=
  Iff.rfl

/-- **The torsor form**: on `S`, a candidate `D` matches the carried twist iff its
quotient `D * S.J⁻¹` is the trivial table on every supported channel. -/
theorem j_match_iff_quotient_trivial (S : FusionSystem n k)
    (D : Fin n → Fin n → Fin n → k) :
    J_match S D ↔
      ∀ a b c : Fin n, 0 < S.ring.N a b c → S.J a b c * (D a b c)⁻¹ = 1 := by
  constructor
  · intro h a b c hN
    have hD : D a b c ≠ 0 := by
      rw [← h a b c hN]; exact S.J_ne_zero a b c hN
    rw [h a b c hN, mul_inv_cancel₀ hD]
  · intro h a b c hN
    have hD : D a b c ≠ 0 := by
      intro h0
      have hh := h a b c hN
      rw [h0, inv_zero, mul_zero] at hh
      exact one_ne_zero hh.symm
    have hh := congrArg (fun x => x * D a b c) (h a b c hN)
    simpa [mul_assoc, inv_mul_cancel₀ hD] using hh

/-- Inverting the twist twice returns the datum's own table (the operation is an
involution on the fibre over a fixed datum). -/
theorem twistInvTwistInv_J (S : FusionSystem n k) (a b c : Fin n) :
    (twistInv (twistInv S)).J a b c = S.J a b c := by
  simp [twistInv_J]

/-! ## §6 — the group laws, completed

The trivial table is the unit, and a twist times its own inverse is the unit on every
supported channel; with §2/§3 this is the group structure of admissible twists. -/

/-- **The unit**: multiplying by the trivial table returns the datum's own twist. -/
theorem twistMul_one_J (S : FusionSystem n k)
    (hne : ∀ i j kk, 0 < S.ring.N i j kk → (fun _ _ _ : Fin n => (1 : k)) i j kk ≠ 0)
    (h1 : ∀ (hn : 0 < n) (j : Fin n), (fun _ _ _ : Fin n => (1 : k)) ⟨0, hn⟩ j j = 1)
    (h2 : ∀ (hn : 0 < n) (i : Fin n), (fun _ _ _ : Fin n => (1 : k)) i ⟨0, hn⟩ i = 1)
    (h3 : ∀ (hn : 0 < n) (i : Fin n),
      (fun _ _ _ : Fin n => (1 : k)) i (S.ring.dual i) ⟨0, hn⟩ = 1)
    (h4 : ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      (fun _ _ _ : Fin n => (1 : k)) a b e * (fun _ _ _ : Fin n => (1 : k)) e c d
          * S.F a b c d e f =
        (fun _ _ _ : Fin n => (1 : k)) b c f * (fun _ _ _ : Fin n => (1 : k)) a f d
          * S.F a b c d e f)
    (a b c : Fin n) :
    (twistMul S (fun _ _ _ => 1) hne h1 h2 h3 h4).J a b c = S.J a b c := by
  simp [twistMul_J]

/-- **The inverse law**: a twist times its inverse is the trivial table on every
supported channel. -/
theorem twistMul_inv_J {S : FusionSystem n k} {J' : Fin n → Fin n → Fin n → k}
    (hne h1 h2 h3 h4) {a b c : Fin n} (hN : 0 < S.ring.N a b c)
    (hJJ' : J' a b c = (S.J a b c)⁻¹) :
    (twistMul S J' hne h1 h2 h3 h4).J a b c = 1 := by
  rw [twistMul_J, hJJ', mul_inv_cancel₀ (S.J_ne_zero a b c hN)]

/-- **The group acts on candidates**: `J_match` on the inverted datum at `D` is
`J_match` on the datum at `D⁻¹` (on supported channels). -/
theorem j_match_twistInv_iff_inv (S : FusionSystem n k)
    (D : Fin n → Fin n → Fin n → k) :
    J_match (twistInv S) D ↔
      J_match S (fun a b c => (D a b c)⁻¹) := by
  constructor
  · intro h a b c hN
    have hh : (S.J a b c)⁻¹ = D a b c := h a b c hN
    show S.J a b c = (D a b c)⁻¹
    rw [← hh]
    exact (inv_inv (S.J a b c)).symm
  · intro h a b c hN
    have hh : S.J a b c = (D a b c)⁻¹ := h a b c hN
    show (S.J a b c)⁻¹ = D a b c
    rw [hh]
    exact inv_inv (D a b c)

end FusionCategory
