/-
WP2 round 3, member m3, direction D3: the pentagon of the reconstruction.

`U_entry`: the two-factor (right-hand) side of the pentagon
`α_{A⊗B,C,D} ≫ α_{A,B,C⊗D}` collapses entrywise to
`if <four leaves match> then F g C D d e f * F A B f d g h else 0`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.PentagonU

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- A transport along a *reflexive* label equality is the identity. -/
theorem cast_eq_of_eq_self {α : Type*} {β : α → Type*} {a : α} (h : a = a) (x : β a) :
    h ▸ x = x := by
  rw [Subsingleton.elim h rfl]

/-- A transport along any label equality is `HEq` to the identity. -/
theorem cast_self {α : Type*} {β : α → Type*} {a a' : α} (h : a = a') (x : β a') :
    HEq (h ▸ x) x := by
  cases h
  exact HEq.rfl

/-- The channel normalisation: the middle channel of the two-factor composite
is free, and its multiplicity is `0` or `1`. -/
theorem nsmul_mid (d e f g h C Dw a b : Fin n) :
    (S.ring.N g f d) • (S.F g C Dw d e f * S.F a b f d g h)
      = S.F g C Dw d e f * S.F a b f d g h := by
  by_cases hF : S.F g C Dw d e f * S.F a b f d g h = 0
  · simp [hF]
  · have hp1 : S.F g C Dw d e f ≠ 0 := fun hh => hF (by rw [hh, zero_mul])
    obtain ⟨-, -, -, hgfd⟩ := F_ne_zero_supp S hp1
    rw [N_eq_one S hgfd, one_smul]

/-- **The right-hand (two-factor) side of the pentagon, entrywise.** -/
theorem U_entry (A B C D : FusionMat n k) (d : Fin n)
    (p : (tensorObj S (tensorObj S (tensorObj S A B) C) D).blk d)
    (q : (tensorObj S A (tensorObj S B (tensorObj S C D))).blk d) :
    (associatorHom S (tensorObj S A B) C D ≫ associatorHom S A B (tensorObj S C D)) d p q
      = if qlo A B C D S d p = qhi A B C D S d q then
          S.F p.2.2.1.1.1 p.2.2.1.1.2 p.1.2 d p.1.1 q.2.2.2.1.2 *
            S.F p.2.2.1.2.2.1.1.1 p.2.2.1.2.2.1.1.2 q.2.2.2.1.2 d p.2.2.1.1.1 q.1.2
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
    rw [show (associatorHom S (tensorObj S A B) C D ≫ associatorHom S A B (tensorObj S C D)) d
        = (Matrix.of (assocEntry S (tensorObj S A B) C D d) *
            Matrix.of (assocEntry S A B (tensorObj S C D) d)) from rfl]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [flatBlk S (tensorObj S A B) (tensorObj S C D) d]
    -- kill the label pair of the middle index at `(g, f)`
    refine (Finset.sum_eq_single (g, f) ?_ ?_).trans ?_
    · intro p₁ _ hp₁
      refine Finset.sum_eq_zero fun ν₁ _ => Finset.sum_eq_zero fun w₁ _ =>
        Finset.sum_eq_zero fun t₁ _ => ?_
      by_cases hM1 : assocMatch S (tensorObj S A B) C D d
        ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩ ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩
      · by_cases hM2 : assocMatch S A B (tensorObj S C D) d ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩
          ⟨⟨a, h⟩, ⟨ν', ⟨x, ⟨⟨b, f⟩, ⟨μ', ⟨x₂, ⟨⟨Cc, Dw⟩, ⟨lq, y, z⟩⟩⟩⟩⟩⟩⟩⟩
        · obtain ⟨m1, -, m3, -, -, -⟩ := hM2
          obtain ⟨m1', -, -, -, -, -⟩ := hM1
          have hp : p₁ = (g, f) := Prod.ext m1'.symm m3
          exact absurd hp hp₁
        · rw [assocEntry_eq_zero_of_not S A B (tensorObj S C D) d ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩ _
            hM2, mul_zero]
      · rw [assocEntry_eq_zero_of_not S (tensorObj S A B) C D d _ ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩ hM1,
          zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    · -- the two remaining sums: kill the `A ⊗ B` and the `C ⊗ D` block
      have hinner : ∀ ν₁ : Fin (S.ring.N (g, f).1 (g, f).2 d),
          (∑ (w₁ : (tensorObj S A B).blk (g, f).1), ∑ (t₁ : (tensorObj S C D).blk (g, f).2),
            assocEntry S (tensorObj S A B) C D d
                ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩
                ⟨(g, f), ⟨ν₁, w₁, t₁⟩⟩ *
              assocEntry S A B (tensorObj S C D) d ⟨(g, f), ⟨ν₁, w₁, t₁⟩⟩
                ⟨⟨a, h⟩, ⟨ν', ⟨x, ⟨⟨b, f⟩, ⟨μ', ⟨x₂, ⟨⟨Cc, Dw⟩, ⟨lq, y, z⟩⟩⟩⟩⟩⟩⟩⟩)
          = S.F g Cc Dw d e f * S.F a b f d g h := by
        intro ν₁
        refine (Finset.sum_eq_single (⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g)
          ?_ ?_).trans ?_
        · intro w₁ _ hw₁
          refine Finset.sum_eq_zero fun t₁ _ => ?_
          by_cases hM1 : assocMatch S (tensorObj S A B) C D d
            ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩
            ⟨(g, f), ⟨ν₁, w₁, t₁⟩⟩
          · by_cases hM2 : assocMatch S A B (tensorObj S C D) d ⟨(g, f), ⟨ν₁, w₁, t₁⟩⟩
              ⟨⟨a, h⟩, ⟨ν', ⟨x, ⟨⟨b, f⟩, ⟨μ', ⟨x₂, ⟨⟨Cc, Dw⟩, ⟨lq, y, z⟩⟩⟩⟩⟩⟩⟩⟩
            · obtain ⟨m1, -, -, m4, -, -⟩ := hM1
              have hcast : (⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g) = w₁ :=
                m4.trans (eq_of_heq (cast_self m1 _))
              exact absurd hcast.symm hw₁
            · rw [assocEntry_eq_zero_of_not S A B (tensorObj S C D) d _ _ hM2, mul_zero]
          · rw [assocEntry_eq_zero_of_not S (tensorObj S A B) C D d _ _ hM1, zero_mul]
        · intro hh
          exact absurd (Finset.mem_univ _) hh
        · refine (Finset.sum_eq_single (⟨(Cc, Dw), ⟨lq, y, z⟩⟩ : (tensorObj S C D).blk f)
            ?_ ?_).trans ?_
          · intro t₁ _ ht₁
            by_cases hM1 : assocMatch S (tensorObj S A B) C D d
              ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩
              ⟨(g, f), ⟨ν₁, ⟨(a, b), ⟨l₀, x, x₂⟩⟩, t₁⟩⟩
            · by_cases hM2 : assocMatch S A B (tensorObj S C D) d
                ⟨(g, f), ⟨ν₁, ⟨(a, b), ⟨l₀, x, x₂⟩⟩, t₁⟩⟩
                ⟨⟨a, h⟩, ⟨ν', ⟨x, ⟨⟨b, f⟩, ⟨μ', ⟨x₂, ⟨⟨Cc, Dw⟩, ⟨lq, y, z⟩⟩⟩⟩⟩⟩⟩⟩
              · rcases hM2 with ⟨k1, k2, k3, kA, kB, kC⟩
                have hcast : t₁ = (⟨(Cc, Dw), ⟨lq, y, z⟩⟩ : (tensorObj S C D).blk f) :=
                  kC.trans (eq_of_heq (cast_self k3 _))
                exact absurd hcast ht₁
              · rw [assocEntry_eq_zero_of_not S A B (tensorObj S C D) d _ _ hM2, mul_zero]
            · rw [assocEntry_eq_zero_of_not S (tensorObj S A B) C D d _ _ hM1, zero_mul]
          · intro hh
            exact absurd (Finset.mem_univ _) hh
          · rw [assocEntry_eq_F_of S (tensorObj S A B) C D d _ _
              ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
              assocEntry_eq_F_of S A B (tensorObj S C D) d _ _
              ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩]
      rw [Finset.sum_congr rfl (fun ν₁ _ => hinner ν₁), sum_fin_const_nsmul]
      exact nsmul_mid S d e f g h Cc Dw a b
  · rw [if_neg hleaf]
    obtain ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩ := p
    obtain ⟨⟨Aq, h⟩, ⟨ν', ⟨xq, ⟨⟨Bv, f⟩, ⟨μ', ⟨yq, ⟨⟨Cv, Dv⟩, ⟨lq, zq, zq₂⟩⟩⟩⟩⟩⟩⟩⟩ := q
    rw [show (associatorHom S (tensorObj S A B) C D ≫ associatorHom S A B (tensorObj S C D)) d
        = (Matrix.of (assocEntry S (tensorObj S A B) C D d) *
            Matrix.of (assocEntry S A B (tensorObj S C D) d)) from rfl]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [flatBlk S (tensorObj S A B) (tensorObj S C D) d]
    refine Finset.sum_eq_zero fun p₁ _ => Finset.sum_eq_zero fun ν₁ _ =>
      Finset.sum_eq_zero fun w₁ _ => Finset.sum_eq_zero fun t₁ _ => ?_
    by_cases hM1 : assocMatch S (tensorObj S A B) C D d
      ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩ ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩
    · by_cases hM2 : assocMatch S A B (tensorObj S C D) d ⟨p₁, ⟨ν₁, w₁, t₁⟩⟩
        ⟨⟨Aq, h⟩, ⟨ν', ⟨xq, ⟨⟨Bv, f⟩, ⟨μ', ⟨yq, ⟨⟨Cv, Dv⟩, ⟨lq, zq, zq₂⟩⟩⟩⟩⟩⟩⟩⟩
      · exact absurd (U_match_imp S A B C D d _ _ _ hM1 hM2) hleaf
      · rw [assocEntry_eq_zero_of_not S A B (tensorObj S C D) d _ _ hM2, mul_zero]
    · rw [assocEntry_eq_zero_of_not S (tensorObj S A B) C D d _ _ hM1, zero_mul]

end FusionCategory
