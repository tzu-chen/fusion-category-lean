/-
WP2 round 3, member m3, direction D3: the pentagon of the reconstruction.

The two-factor (right-hand) side of the pentagon:
`(α_{A⊗B,C,D} ≫ α_{A,B,C⊗D})` collapses entrywise to
`if <four leaves match> then F g C D d e f * F A B f d g h else 0`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.PentagonAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- From `x = h ▸ y` (a transport along a label equality) to `HEq x y`. -/
theorem heq_of_eq_cast' {α : Type*} {β : α → Type*} {a a' : α} (h : a = a')
    {x : β a} {y : β a'} (h2 : x = h ▸ y) : HEq x y := by
  subst h
  exact heq_of_eq h2

/-- The `Sigma`-construction of an equality from a label equality and an `HEq`
of the fibres. -/
theorem sigma_eq_mk {α : Type*} {β : α → Type*} {a a' : α} {b : β a} {b' : β a'}
    (h : a = a') (h2 : HEq b b') : (⟨a, b⟩ : Sigma β) = ⟨a', b'⟩ := by
  subst h
  rw [eq_of_heq h2]

/-! ## The leaf match is forced by the two matches -/

theorem U_match_imp (A B C D : FusionMat n k) (d : Fin n)
    (p : (tensorObj S (tensorObj S (tensorObj S A B) C) D).blk d)
    (q : (tensorObj S A (tensorObj S B (tensorObj S C D))).blk d)
    (m : (tensorObj S (tensorObj S A B) (tensorObj S C D)).blk d)
    (hA : assocMatch S (tensorObj S A B) C D d p m)
    (hB : assocMatch S A B (tensorObj S C D) d m q) :
    qlo A B C D S d p = qhi A B C D S d q := by
  obtain ⟨⟨e, Dw⟩, ⟨ν, ⟨⟨g, Cc⟩, ⟨μ, ⟨⟨a, b⟩, ⟨l₀, x, x₂⟩⟩, y⟩⟩, z⟩⟩ := p
  obtain ⟨⟨Aq, h⟩, ⟨ν', ⟨xq, ⟨⟨Bv, f⟩, ⟨μ', ⟨yq, ⟨⟨Cv, Dv⟩, ⟨lq, zq, zq₂⟩⟩⟩⟩⟩⟩⟩⟩ := q
  obtain ⟨⟨g₁, k⟩, ⟨ν₁, w₁, t₁⟩⟩ := m
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩ := hA
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6⟩ := hB
  have hB3' : k = f := hB3
  -- the label pair of the `A ⊗ B` block is the same on both sides of `hA4`
  have hlab : ((⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g)).1 = w₁.1 := by
    have h1 : ((⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g)).1 = (hA1 ▸ w₁).1 :=
      congrArg Sigma.fst hA4
    rw [h1, cast_blk_fst S A B hA1 w₁]
  have ha : a = Aq := (congrArg Prod.fst hlab).trans hB1
  have hb : b = Bv := (congrArg Prod.snd hlab).trans hB2
  -- the `A`-block and the `B`-block
  have hX : HEq x xq := by
    have h1 : HEq ((⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g).2.2.1)
        (hA1 ▸ w₁).2.2.1 := congr_arg_heq (fun s => s.2.2.1) hA4
    exact HEq.trans (HEq.trans h1 (cast_blk_x S A B hA1 w₁)) (heq_of_eq_cast' hB1 hB4)
  have hX₂ : HEq x₂ yq := by
    have h1 : HEq ((⟨(a, b), ⟨l₀, x, x₂⟩⟩ : (tensorObj S A B).blk g).2.2.2)
        (hA1 ▸ w₁).2.2.2 := congr_arg_heq (fun s => s.2.2.2) hA4
    exact HEq.trans (HEq.trans h1 (cast_blk_y S A B hA1 w₁)) (heq_of_eq_cast' hB2 hB5)
  -- the `C` and `D` labels come from the fourth component of `q`, via `t₁ = hB3' ▸ t`
  have hCD : t₁.1 = ((Cv, Dv) : Fin n × Fin n) := by
    have h1 : t₁.1 = (hB3' ▸ (⟨(Cv, Dv), ⟨lq, zq, zq₂⟩⟩ : (tensorObj S C D).blk f)).1 :=
      congrArg Sigma.fst hB6
    rw [h1, cast_blk_fst S C D hB3]
  have hc : Cc = Cv := hA2.trans (congrArg Prod.fst hCD)
  have hd : Dw = Dv := hA3.trans (congrArg Prod.snd hCD)
  have hy : HEq y zq := by
    have h1 : HEq t₁.2.2.1
        (hB3' ▸ (⟨(Cv, Dv), ⟨lq, zq, zq₂⟩⟩ : (tensorObj S C D).blk f)).2.2.1 :=
      congr_arg_heq (fun s => s.2.2.1) hB6
    exact HEq.trans (heq_of_eq_cast' hA2 hA5) (HEq.trans h1 (cast_blk_x S C D hB3' ⟨(Cv, Dv), ⟨lq, zq, zq₂⟩⟩))
  have hz : HEq z zq₂ := by
    have h1 : HEq t₁.2.2.2
        (hB3' ▸ (⟨(Cv, Dv), ⟨lq, zq, zq₂⟩⟩ : (tensorObj S C D).blk f)).2.2.2 :=
      congr_arg_heq (fun s => s.2.2.2) hB6
    exact HEq.trans (heq_of_eq_cast' hA3 hA6) (HEq.trans h1 (cast_blk_y S C D hB3' ⟨(Cv, Dv), ⟨lq, zq, zq₂⟩⟩))
  simp only [qlo, qhi]
  exact Prod.ext (sigma_eq_mk ha hX)
    (Prod.ext (sigma_eq_mk hb hX₂)
      (Prod.ext (sigma_eq_mk hc hy) (sigma_eq_mk hd hz)))

end FusionCategory
