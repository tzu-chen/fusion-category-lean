/-
WP2 round 3, the coordinator's proof: the three-factor (left-hand) side of the
pentagon, entrywise — the single remaining item of WP2 (see PLAN.md's Round 3
record).  With `U_entry` (the two-factor side, m3) and this file, the pentagon
`PentagonShapeHom` follows by `S.pentagon` at the labels, and with
`ReconClosureBridge` the reconstruction becomes a fusion category in the
library's own sense.

The statement is the one m3's `PentagonNSmul` header names: the composite
`(α_{A,B,C} ⊗ 𝟙_D) ≫ α_{A,B⊗C,D} ≫ (𝟙_A ⊗ α_{B,C,D})` collapses entrywise to
`if <four leaves match> then ∑ kk, F a b C e g kk * F a kk Dw d e h *
F b C Dw h kk f else 0`, the label-level `S.pentagon` sum.

Method (the engine, third application): destructure, case-split on the leaf
match, flatten both middle sums (`flatBlk`/`flatNest`), kill the binders one
at a time with `Finset.sum_eq_single` — the label pairs by
`tensorHom_apply_ne`, the element structures by `assocEntry_eq_zero_of_not`
plus component contradictions — and collapse the three free channel sums
(`sum_fin_const_nsmul` + the support facts) to the product.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.PentagonNSmul

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- The channel delta is `1`: channels are subsingletons by `mult_free`. -/
theorem chan_delta_one {a b c : Fin n} (ν ν' : Fin (S.ring.N a b c)) :
    (if ν = ν' then 1 else 0) = 1 := by
  have h : Subsingleton (Fin (S.ring.N a b c)) := channel_subsingleton S a b c
  simp [Subsingleton.elim ν ν']

/-- **A channel sum is its value at any witness.**  A present channel's index
type is a subsingleton, so the sum over it has a vacuous off-case: every
element equals the witness.  This disposes every channel binder without any
nsmul bookkeeping — the channel is simply *killed* to its witness. -/
theorem sum_subsingleton_witness {m : ℕ} (hm : m ≤ 1) (w : Fin m) (BODY : Fin m → k) :
    (∑ ν : Fin m, BODY ν) = BODY w := by
  have hsub : Subsingleton (Fin m) :=
    ⟨fun x y => Fin.ext (by have := x.isLt; have := y.isLt; omega)⟩
  exact Finset.sum_eq_single w (fun x _ hx => absurd (Subsingleton.elim x w) hx)
    (fun hw => absurd (Finset.mem_univ w) hw)

/-- **A channel sum, witness-free form**: over a `≤ 1` index type, the sum is
the value at `⟨0, _⟩` when the channel is present and `0` when it is not.
This is the disposal for channels with no fixed witness (t₂'s `σ`, the
s-block's `λ`, t₃'s channel): applied under binders via the hinner-technique. -/
theorem sum_channel {m : ℕ} (hm : m ≤ 1) (BODY : Fin m → k) :
    (∑ ν : Fin m, BODY ν) = (if hN : 0 < m then BODY ⟨0, hN⟩ else 0) := by
  by_cases hN : 0 < m
  · rw [dif_pos hN]
    have hsub : Subsingleton (Fin m) :=
      ⟨fun x y => Fin.ext (by have := x.isLt; have := y.isLt; omega)⟩
    refine Finset.sum_eq_single (⟨0, hN⟩ : Fin m)
      (fun x _ hx => absurd (Subsingleton.elim x (⟨0, hN⟩ : Fin m)) hx)
      (fun hw => absurd (Finset.mem_univ (⟨0, hN⟩ : Fin m)) hw)
  · have hm0 : m = 0 := by omega
    subst hm0
    exact Finset.sum_eq_zero fun x _ => x.elim0

/-- The identity block entry. -/
theorem idBlk_entry (X : FusionMat n k) (i : Fin n) (x y : X.blk i) :
    (CategoryStruct.id X) i x y = (if x = y then 1 else 0) := by
  show (1 : Matrix (X.blk i) (X.blk i) k) x y = _
  simp [Matrix.one_apply]

/-- **The channel normalisation of the three-factor side.**  The three free
channel sums contribute `(N a kk e) • ((N b C kk) • ((N kk Dw h) • prod))`;
in the nonzero case each factor is `1` by the support facts of the first and
third `F`-entries, and in the zero case the term vanishes.  The two outer
channels are `1` unconditionally (witnessed by the source and target
indices). -/
theorem pent_nsmul3 (d e f g h C Dw a b kk : Fin n)
    (hν : Fin (S.ring.N e Dw d)) (hν' : Fin (S.ring.N a h d))
    (hF1 : S.F a b C e g kk ≠ 0) (hF3 : S.F b C Dw h kk f ≠ 0)
    (x : k) :
    (S.ring.N e Dw d) • ((S.ring.N a h d) • ((S.ring.N a kk e) •
      ((S.ring.N b C kk) • ((S.ring.N kk Dw h) • x)))) = x := by
  have h1 : S.ring.N e Dw d = 1 := by
    have := hν.isLt
    have hle : S.ring.N e Dw d ≤ 1 := S.mult_free e Dw d
    omega
  have h2 : S.ring.N a h d = 1 := by
    have := hν'.isLt
    have hle : S.ring.N a h d ≤ 1 := S.mult_free a h d
    omega
  rw [h1, h2, one_smul, one_smul]
  by_cases hzero : x = 0
  · rw [hzero, nsmul_zero, nsmul_zero, nsmul_zero]
  · -- all three factors are 1: the support facts of the first and third F
    obtain ⟨-, -, hbCk, hake⟩ := F_ne_zero_supp S hF1
    obtain ⟨-, hkDh, -, -⟩ := F_ne_zero_supp S hF3
    rw [N_eq_one S hake, N_eq_one S hbCk, N_eq_one S hkDh,
      one_smul, one_smul, one_smul]

/-! ## The three-factor (left-hand) side of the pentagon, entrywise -/

section LHS

variable (S : FusionSystem n k)

/-- **The three-factor (left-hand) side of the pentagon, entrywise.**  The
composite `(α_{A,B,C} ⊗ 𝟙_D) ≫ α_{A,B⊗C,D} ≫ (𝟙_A ⊗ α_{B,C,D})` at a pair of
refined indices is the label-level pentagon sum on matched leaves and `0`
off them — the statement `PentagonNSmul`'s header names. -/
theorem LHS_entry (A B C D : FusionMat n k) (d : Fin n)
    (p : (tensorObj S (tensorObj S (tensorObj S A B) C) D).blk d)
    (q : (tensorObj S A (tensorObj S B (tensorObj S C D))).blk d) :
    (tensorHom S (associatorHom S A B C) (𝟙 D) ≫
        associatorHom S A (tensorObj S B C) D ≫
        tensorHom S (𝟙 A) (associatorHom S B C D)) d p q
      = if qlo A B C D S d p = qhi A B C D S d q then
          ∑ kk : Fin n,
            S.F p.2.2.1.2.2.1.1.1 p.2.2.1.2.2.1.1.2 p.2.2.1.1.2 p.1.1
                p.2.2.1.1.1 kk
              * S.F p.2.2.1.2.2.1.1.1 kk p.1.2 d p.1.1 q.1.2
              * S.F p.2.2.1.2.2.1.1.2 p.2.2.1.1.2 p.1.2 q.1.2 kk
                  q.2.2.2.1.2
        else 0 := by
  by_cases hleaf : qlo A B C D S d p = qhi A B C D S d q
  · rw [if_pos hleaf]
    obtain ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩ := p
    obtain ⟨⟨Aq, h⟩, ⟨ν', ⟨xq, ⟨⟨Bv, f⟩, ⟨μ', ⟨yq, ⟨⟨Cv, Dv⟩, ⟨lq, zq, zq₂⟩⟩⟩⟩⟩⟩⟩⟩ := q
    simp only [qlo, qhi] at hleaf
    have e1 : (⟨a, x⟩ : Σ a, A.blk a) = ⟨Aq, xq⟩ := congrArg Prod.fst hleaf
    have e2 : (⟨b, x₂⟩ : Σ b, B.blk b) = ⟨Bv, yq⟩ :=
      congrArg Prod.fst (congrArg Prod.snd hleaf)
    have e3 : (⟨Cc, y⟩ : Σ c, C.blk c) = ⟨Cv, zq⟩ :=
      congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd hleaf))
    have e4 : (⟨Dw, z⟩ : Σ w, D.blk w) = ⟨Dv, zq₂⟩ :=
      congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd hleaf))
    simp only [Sigma.mk.injEq] at e1 e2 e3 e4
    obtain ⟨ha, hx⟩ := e1
    obtain ⟨hb, hx₂⟩ := e2
    obtain ⟨hc, hy⟩ := e3
    obtain ⟨hd, hz⟩ := e4
    subst Aq
    subst Bv
    subst Cv
    subst Dv
    obtain rfl : x = xq := eq_of_heq hx
    obtain rfl : x₂ = yq := eq_of_heq hx₂
    obtain rfl : y = zq := eq_of_heq hy
    obtain rfl : z = zq₂ := eq_of_heq hz
    -- the composite as a triple matrix product: ≫ is right-assoc, so
    -- re-associate to (leg1 * α₂) * leg2, making the m2-index the OUTER sum
    simp only [CategoryStruct.comp]
    rw [← Matrix.mul_assoc]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    -- flatten the m2 middle (outer)
    rw [flatBlk S A (tensorObj S (tensorObj S B C) D) d]
    -- kill the m2 pair to (a, h): off it, leg2's entry vanishes
    refine (Finset.sum_eq_single (a, h) ?_ ?_).trans ?_
    · intro b_1 _ hb_1
      refine Finset.sum_eq_zero fun x_1 _ => Finset.sum_eq_zero fun x_2 _ =>
        Finset.sum_eq_zero fun x_3 _ => Finset.sum_eq_zero fun x_4 _ => ?_
      rw [tensorHom_apply_ne S (𝟙 A) (associatorHom S B C D) d hb_1, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    -- rewrite leg2's entry via the hinner-technique: state the entry
    -- transformation with OUR OWN binders, prove it (the hand-written shapes
    -- match), apply it through the sum via Finset.sum_congr chains
    have hleg2 : ∀ (ν₂ : Fin (S.ring.N (a, h).1 (a, h).2 d)) (w₂ : A.blk (a, h).1)
        (t₂ : (tensorObj S (tensorObj S B C) D).blk (a, h).2)
        (i : (tensorObj S (tensorObj S A (tensorObj S B C)) D).blk d),
        ((tensorHom S (associatorHom S A B C) (𝟙 D) d
            ⟨(e, Dw), (ν, ⟨(g, Cc), (μ, ⟨(a, b), ⟨l₀, x, x₂⟩⟩, y)⟩, z)⟩ i) *
          (associatorHom S A (tensorObj S B C) D d i ⟨(a, h), (ν₂, w₂, t₂)⟩)) *
          (tensorHom S (𝟙 A) (associatorHom S B C D) d ⟨(a, h), (ν₂, w₂, t₂)⟩
            ⟨(a, h), (ν', x, ⟨(b, f), (μ', x₂, ⟨(Cc, Dw), (lq, y, z)⟩)⟩)⟩)
        = ((tensorHom S (associatorHom S A B C) (𝟙 D) d
            ⟨(e, Dw), (ν, ⟨(g, Cc), (μ, ⟨(a, b), ⟨l₀, x, x₂⟩⟩, y)⟩, z)⟩ i) *
          (associatorHom S A (tensorObj S B C) D d i ⟨(a, h), (ν₂, w₂, t₂)⟩)) *
          ((if ν₂ = ν' then 1 else 0) *
            ((if w₂ = x then 1 else 0) *
              (associatorHom S B C D (a, h).2 t₂
                ⟨(b, f), (μ', x₂, ⟨(Cc, Dw), (lq, y, z)⟩)⟩))) := by
      intro ν₂ w₂ t₂ i
      have hsub : Subsingleton (Fin (S.ring.N (a, h).1 (a, h).2 d)) :=
        channel_subsingleton S (a, h).1 (a, h).2 d
      rw [tensorHom_apply, if_pos (Subsingleton.elim ν₂ ν'), idBlk_entry]
    simp only [hleg2]
    -- kill the ν₂ channel to its witness (q's channel ν'): vacuous off-case
    rw [sum_subsingleton_witness (S.mult_free (a, h).1 (a, h).2 d) ν']
    rw [if_pos rfl]
    simp only [one_mul]
    -- kill w₂ to x: off it, the A-delta vanishes
    refine (Finset.sum_eq_single x ?_ ?_).trans ?_
    · intro w₂ _ hw₂
      refine Finset.sum_eq_zero fun t₂ _ => Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg hw₂]
      ring
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    rw [if_pos rfl]
    simp only [one_mul]
    -- flatten t₂ at the concrete label h
    simp only [flatNest S (tensorObj S B C) D h]
    -- split the (E₂, Cw) pair and bring Cw outer
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    -- kill Cw → Dw: off it, the α_{B,C,D}-entry vanishes (its match's h3)
    refine (Finset.sum_eq_single Dw ?_ ?_).trans ?_
    · intro Cw _ hCw
      refine Finset.sum_eq_zero fun E₂ _ => Finset.sum_eq_zero fun σ _ =>
        Finset.sum_eq_zero fun t₃ _ => Finset.sum_eq_zero fun z₃ _ =>
          Finset.sum_eq_zero fun i _ => ?_
      by_cases hM : assocMatch S B C D h
        ⟨(E₂, Cw), (σ, (t₃, z₃))⟩
        ⟨(b, f), (μ', (x₂, ⟨(Cc, Dw), (lq, (y, z))⟩))⟩
      · obtain ⟨-, -, h3, -, -, -⟩ := hM
        exact (hCw h3).elim
      · rw [show associatorHom S B C D h ⟨(E₂, Cw), (σ, (t₃, z₃))⟩
            ⟨(b, f), (μ', (x₂, ⟨(Cc, Dw), (lq, (y, z))⟩))⟩ =
            assocEntry S B C D h ⟨(E₂, Cw), (σ, (t₃, z₃))⟩
              ⟨(b, f), (μ', (x₂, ⟨(Cc, Dw), (lq, (y, z))⟩))⟩ from rfl,
        assocEntry_eq_zero_of_not S B C D h _ _ hM]
        ring
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    -- the σ channel: witness-free disposal (present: kill to ⟨0, _⟩; absent: 0)
    simp only [sum_channel (S.mult_free _ Dw h)]
    rw [Matrix.mul_apply]
  · rw [if_neg hleaf]
    sorry

end LHS

end FusionCategory
