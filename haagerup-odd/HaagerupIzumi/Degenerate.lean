module

public import HaagerupIzumi.Balanced

@[expose] public section

/-!
# Degenerate cubics

Lemma 5.4 of the expanded proof: if some cross sum of the pair attached to
`(g, h, k, l)` vanishes, then `C g h k l = 0`.
-/

open Finset

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n] [CharZero K]

/-- The collision lemma in an arbitrary position: if `a (σ 0) + c (ρ 0) = 0` while
`a (σ 1) + c (ρ 1)` and `a (σ 2) + c (ρ 1)` are nonzero, then `δ^2 S - τ P = 0`. -/
theorem SP_collision_pos (hQ : ∀ g h, D.Q g h = 0) (a c : Fin 3 → ZMod n)
    (hbal : a 0 + a 1 + a 2 + c 0 + c 1 + c 2 = 0) (σ ρ : Equiv.Perm (Fin 3))
    (h0 : a (σ 0) + c (ρ 0) = 0) (hH : a (σ 1) + c (ρ 1) ≠ 0) (hV : a (σ 2) + c (ρ 1) ≠ 0) :
    D.δ ^ 2 * D.S a c - D.τ * D.P a c = 0 := by
  rw [← S_perm_left D a c σ, ← S_perm_right D (a ∘ σ) c ρ,
    ← P_perm_left D a c σ, ← P_perm_right D (a ∘ σ) c ρ]
  refine SP_collision D hQ (a ∘ σ) (c ∘ ρ) ?_ h0 hH hV
  have hs := Equiv.sum_comp σ a
  have hs' := Equiv.sum_comp ρ c
  simp only [Fin.sum_univ_three, Function.comp_apply] at hs hs' ⊢
  linear_combination hs + hs' + hbal

lemma trip_balanced (g h k l : ZMod n) :
    aTrip g h k l 0 + aTrip g h k l 1 + aTrip g h k l 2
      + cTrip g h k l 0 + cTrip g h k l 1 + cTrip g h k l 2 = 0 := by
  simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma sw01_0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
lemma sw01_1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
lemma sw01_2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
lemma sw02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
lemma sw02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
lemma sw02_2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide

/-- The first full match, `(k, l) = (0, -g)`. -/
theorem bracket_FM1 {g h : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0) :
    D.δ ^ 2 * D.S (aTrip g h 0 (-g)) (cTrip g h 0 (-g))
      - D.τ * D.P (aTrip g h 0 (-g)) (cTrip g h 0 (-g)) = D.τ ^ 3 * D.δ ^ 3 := by
  have hc : cTrip g h 0 (-g) = (fun j => -aTrip g h 0 (-g) j) ∘ ⇑(finRotate 3).symm := by
    funext j
    fin_cases j <;> simp [aTrip, cTrip] <;> ring
  rw [hc, S_perm_right, P_perm_right]
  apply SP_fullmatch <;>
    simp only [aTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  · intro e; apply hg; linear_combination e
  · intro e; apply hgh; linear_combination e
  · intro e; apply hh; linear_combination e

/-- The second full match, `(k, l) = (-h, 0)`. -/
theorem bracket_FM2 {g h : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0) :
    D.δ ^ 2 * D.S (aTrip g h (-h) 0) (cTrip g h (-h) 0)
      - D.τ * D.P (aTrip g h (-h) 0) (cTrip g h (-h) 0) = D.τ ^ 3 * D.δ ^ 3 := by
  have hc : cTrip g h (-h) 0 = (fun j => -aTrip g h (-h) 0 j) ∘ ⇑(finRotate 3) := by
    funext j
    fin_cases j <;> simp [aTrip, cTrip] <;> ring
  rw [hc, S_perm_right, P_perm_right]
  apply SP_fullmatch <;>
    simp only [aTrip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  · intro e; apply hgh; linear_combination e
  · intro e; apply hh; linear_combination e
  · intro e; apply hg; linear_combination -e

/-- The corrected bracket. -/
def bracket (g h k l : ZMod n) : K :=
  D.δ ^ 2 * D.S (aTrip g h k l) (cTrip g h k l)
    - D.τ * D.P (aTrip g h k l) (cTrip g h k l)
    - D.τ ^ 3 * D.δ ^ 3 * ((if g + l = 0 ∧ k = 0 then 1 else 0)
      + (if h + k = 0 ∧ l = 0 then 1 else 0))

lemma bracket_FM1' {g h : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0) :
    D.bracket g h 0 (-g) = 0 := by
  rw [bracket, bracket_FM1 D hg hh hgh, if_pos ⟨by ring, rfl⟩,
    if_neg (fun e => hh (by simpa using e.1))]
  ring

lemma bracket_FM2' {g h : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0) :
    D.bracket g h (-h) 0 = 0 := by
  rw [bracket, bracket_FM2 D hg hh hgh, if_neg (fun e => hg (by simpa using e.1)),
    if_pos ⟨by ring, rfl⟩]
  ring

lemma bracket_col (hQ : ∀ g h, D.Q g h = 0) (g h k l : ZMod n) (σ ρ : Equiv.Perm (Fin 3))
    (h0 : aTrip g h k l (σ 0) + cTrip g h k l (ρ 0) = 0)
    (hH : aTrip g h k l (σ 1) + cTrip g h k l (ρ 1) ≠ 0)
    (hV : aTrip g h k l (σ 2) + cTrip g h k l (ρ 1) ≠ 0)
    (c1 : ¬ (g + l = 0 ∧ k = 0)) (c2 : ¬ (h + k = 0 ∧ l = 0)) :
    D.bracket g h k l = 0 := by
  rw [bracket, SP_collision_pos D hQ _ _ (trip_balanced g h k l) σ ρ h0 hH hV, if_neg c1,
    if_neg c2]
  ring

/-- If the corrected bracket vanishes, so does the cubic residual. -/
lemma C_eq_zero_of_bracket {g h k l : ZMod n} (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g + h ≠ 0)
    (hb : D.bracket g h k l = 0) : D.C g h k l = 0 := by
  have h1 : D.Cs g h k l = 0 := by
    rw [Cs_factor' D hg hh hgh]
    rw [bracket] at hb
    rw [hb, mul_zero]
  rw [Cs] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ D.τ_ne_zero)

/-- Lemma 5.4: degenerate cubics vanish. -/
theorem C_degenerate (hQ : ∀ g h, D.Q g h = 0) (g h k l : ZMod n)
    (hdeg : ¬ Nondeg (aTrip g h k l) (cTrip g h k l)) : D.C g h k l = 0 := by
  by_cases hg : g = 0
  · subst hg
    by_cases hh : h = 0
    · subst hh; exact C_zero_zero D k l
    · exact C_g_zero D hQ hh k l
  by_cases hh : h = 0
  · subst hh; exact C_h_zero D hQ hg k l
  by_cases hgh : g + h = 0
  · have : h = -g := eq_neg_of_add_eq_zero_right hgh
    subst this; exact C_h_neg D hQ hg k l
  -- the main case
  unfold Nondeg at hdeg
  push_neg at hdeg
  obtain ⟨i, j, hij⟩ := hdeg
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := cross_sums g h k l
  apply C_eq_zero_of_bracket D hg hh hgh
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij
  · exact absurd (x00 ▸ hij) hgh
  · -- k = 0
    have hk : k = 0 := by rw [x01, neg_eq_zero] at hij; exact hij
    by_cases hgl : g + l = 0
    · have hl : l = -g := eq_neg_of_add_eq_zero_right hgl
      subst hk; subst hl; exact bracket_FM1' D hg hh hgh
    · refine bracket_col D hQ g h k l 1 (Equiv.swap 0 1) ?_ ?_ ?_ (fun e => hgl e.1)
        (fun e => hh (by rw [hk, add_zero] at e; exact e.1))
      · rw [Equiv.Perm.one_apply, sw01_0]; exact hij
      · rw [Equiv.Perm.one_apply, sw01_1, x10, hk, add_zero]; exact hh
      · rw [Equiv.Perm.one_apply, sw01_1, x20]; exact hgl
  · -- l = 0
    have hl : l = 0 := by rw [x02, neg_eq_zero] at hij; exact hij
    by_cases hhk : h + k = 0
    · have hk : k = -h := eq_neg_of_add_eq_zero_right hhk
      subst hk; subst hl; exact bracket_FM2' D hg hh hgh
    · refine bracket_col D hQ g h k l 1 (Equiv.swap 0 2) ?_ ?_ ?_
        (fun e => hg (by rw [hl, add_zero] at e; exact e.1)) (fun e => hhk e.1)
      · rw [Equiv.Perm.one_apply, sw02_0]; exact hij
      · rw [Equiv.Perm.one_apply, sw02_1, x11]; exact neg_ne_zero.mpr hg
      · rw [Equiv.Perm.one_apply, sw02_1, x21, hl]; intro e; exact hhk (by linear_combination -e)
  · -- h + k = 0
    have hk : k = -h := eq_neg_of_add_eq_zero_right (x10 ▸ hij)
    by_cases hl : l = 0
    · subst hk; subst hl; exact bracket_FM2' D hg hh hgh
    · refine bracket_col D hQ g h k l (Equiv.swap 0 1) 1 ?_ ?_ ?_
        (fun e => hh (by rw [hk] at e; simpa using e.2)) (fun e => hl e.2)
      · rw [Equiv.Perm.one_apply, sw01_0]; exact hij
      · rw [Equiv.Perm.one_apply, sw01_1, x01, hk, neg_neg]; exact hh
      · rw [Equiv.Perm.one_apply, sw01_2, x21, hk]; intro e; exact hl (by linear_combination e)
  · exact absurd (x11 ▸ hij) (neg_ne_zero.mpr hg)
  · -- k = g + l
    have hk : k = g + l := by rw [x12] at hij; linear_combination hij
    by_cases hgl : g + l = 0
    · have hl : l = -g := eq_neg_of_add_eq_zero_right hgl
      have hk0 : k = 0 := by rw [hk, hgl]
      subst hk0; subst hl; exact bracket_FM1' D hg hh hgh
    · refine bracket_col D hQ g h k l (Equiv.swap 0 1) (Equiv.swap 0 2) ?_ ?_ ?_
        (fun e => hgl e.1) (fun e => hgh (by
          have e1 := e.1; have e2 := e.2
          rw [e2, add_zero] at hk
          rw [hk] at e1; linear_combination e1))
      · rw [sw01_0, sw02_0]; exact hij
      · rw [sw01_1, sw02_1, x01, hk]; exact neg_ne_zero.mpr hgl
      · rw [sw01_2, sw02_1, x21, hk]; intro e; exact hgh (by linear_combination -e)
  · -- g + l = 0
    have hl : l = -g := eq_neg_of_add_eq_zero_right (x20 ▸ hij)
    by_cases hk : k = 0
    · subst hk; subst hl; exact bracket_FM1' D hg hh hgh
    · refine bracket_col D hQ g h k l (Equiv.swap 0 2) 1 ?_ ?_ ?_ (fun e => hk e.2)
        (fun e => hg (by rw [hl] at e; simpa using e.2))
      · rw [Equiv.Perm.one_apply, sw02_0]; exact hij
      · rw [Equiv.Perm.one_apply, sw02_1, x11]; exact neg_ne_zero.mpr hg
      · rw [Equiv.Perm.one_apply, sw02_2, x01]; exact neg_ne_zero.mpr hk
  · -- l = h + k
    have hl : l = h + k := by rw [x21] at hij; linear_combination hij
    by_cases hhk : h + k = 0
    · have hk : k = -h := eq_neg_of_add_eq_zero_right hhk
      have hl0 : l = 0 := by rw [hl, hhk]
      subst hk; subst hl0; exact bracket_FM2' D hg hh hgh
    · refine bracket_col D hQ g h k l (Equiv.swap 0 2) (Equiv.swap 0 1) ?_ ?_ ?_
        (fun e => hgh (by
          have e1 := e.1; have e2 := e.2
          rw [e2, add_zero] at hl; rw [hl] at e1; exact e1)) (fun e => hhk e.1)
      · rw [sw02_0, sw01_0]; exact hij
      · rw [sw02_1, sw01_1, x10]; exact hhk
      · rw [sw02_2, sw01_1, x00]; exact hgh
  · exact absurd (x22 ▸ hij) (neg_ne_zero.mpr hh)

end CoeffData
end HaagerupIzumi
