module

public import HaagerupIzumi.Residuals
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Reflection by matrix inversion

Lemma 9.3 of the expanded proof: for `g, h, g + h ≠ 0`, if all cubics with
first indices `(g, h)` vanish, then so do all cubics with first indices
`(-h, -g)`. The proof inverts the two sides of the cubic block.
-/

open Finset Matrix

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} {K : Type*} [Field K] (D : CoeffData n K) [NeZero n] [CharZero K]

/-! ### Column inverses -/

/-- The convolution identity `u p * u (-p) = τ^2 [· = 0]` for `p ≠ 0`. -/
theorem conv_column (hQ : ∀ g h, D.Q g h = 0) {p : ZMod n} (hp : p ≠ 0) (x : ZMod n) :
    ∑ a, D.u p a * D.u (-p) (x - a) = D.τ ^ 2 * (if x = 0 then 1 else 0) := by
  have := D.sum_B_quadratic x p
  rw [hQ, zero_add, if_neg hp, mul_zero, sub_zero] at this
  rw [← this]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ (fun a => ?_)
  rw [Equiv.subRight_apply, u_def, B_eq_u_neg D hp, sub_add_cancel]
  congr 2; ring

/-- The matrix `H p (k, m) = B p (k + m)`. -/
def Hm (p : ZMod n) : Matrix (ZMod n) (ZMod n) K := Matrix.of fun k m => D.B p (k + m)

/-- Its inverse `H' p (k, m) = τ⁻² u p (k + m)`. -/
def Hm' (p : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k m => D.τ⁻¹ ^ 2 * D.u p (k + m)

theorem Hm'_mul_Hm (hQ : ∀ g h, D.Q g h = 0) {p : ZMod n} (hp : p ≠ 0) :
    D.Hm' p * D.Hm p = 1 := by
  ext k l
  rw [mul_apply, one_apply]
  simp only [Hm, Hm', of_apply]
  have : ∑ m, D.τ⁻¹ ^ 2 * D.u p (k + m) * D.B p (m + l)
      = D.τ⁻¹ ^ 2 * ∑ a, D.u p a * D.u (-p) ((k - l) - a) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun m => ?_)
    rw [Equiv.coe_addLeft, B_eq_u_neg D hp, show -(m + l) = k - l - (k + m) by ring]
    ring
  rw [this, conv_column D hQ hp]
  have := D.τ_ne_zero
  by_cases hkl : k = l
  · subst hkl; simp; field_simp
  · rw [if_neg hkl, if_neg (fun e => hkl (sub_eq_zero.mp e))]; ring

theorem Hm_mul_Hm' (hQ : ∀ g h, D.Q g h = 0) {p : ZMod n} (hp : p ≠ 0) :
    D.Hm p * D.Hm' p = 1 := by
  ext k l
  rw [mul_apply, one_apply]
  simp only [Hm, Hm', of_apply]
  have : ∑ m, D.B p (k + m) * (D.τ⁻¹ ^ 2 * D.u p (m + l))
      = D.τ⁻¹ ^ 2 * ∑ a, D.u p a * D.u (-p) ((l - k) - a) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight l) _ _ (fun m => ?_)
    rw [Equiv.coe_addRight, B_eq_u_neg D hp, show l - k - (m + l) = -(k + m) by ring]
    ring
  rw [this, conv_column D hQ hp]
  have := D.τ_ne_zero
  by_cases hkl : k = l
  · subst hkl; simp; field_simp
  · rw [if_neg hkl, if_neg (fun e => hkl (sub_eq_zero.mp e).symm)]; ring

/-! ### The left side -/

section sides
variable {g h : ZMod n}

/-- The left side `L (k, l) = ∑ m, u t m * B g (m + k) * B h (m + l)`, `t = g + h`. -/
def Lmat (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => ∑ m, D.u (g + h) m * D.B g (m + k) * D.B h (m + l)

/-- The right side `R (k, l) = B (g + l) k * B (h + k) l`. -/
def Rmat (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => D.B (g + l) k * D.B (h + k) l

/-- The reflected left side `L^r (k, l) = L (-h, -g) (-k, -l)`. -/
def Lr (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => ∑ m, D.u (-(g + h)) m * D.B (-h) (m - k) * D.B (-g) (m - l)

/-- The reflected right side `R^r (k, l) = R (-h, -g) (-k, -l)`. -/
def Rr (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => D.B (-h - l) (-k) * D.B (-g - k) (-l)

/-- The correction matrix `E`. -/
def Emat (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => D.u h k * D.u g l + D.u h (k + (g + h)) * D.u g (l + (g + h))

lemma Lr_apply (k l : ZMod n) : D.Lr g h k l = D.Lmat (-h) (-g) (-k) (-l) := by
  simp only [Lr, Lmat, of_apply]
  apply sum_congr rfl; intro m _
  rw [show -h + -g = -(g + h) by ring, sub_eq_add_neg, sub_eq_add_neg]

lemma Rr_apply (k l : ZMod n) : D.Rr g h k l = D.Rmat (-h) (-g) (-k) (-l) := by
  simp only [Rr, Rmat, of_apply]
  rw [show -h + -l = -h - l by ring, show -g + -k = -g - k by ring]

/-- The cubic block in matrix form: `𝒞 g h k l = L (k, l) - τ R (k, l)`. -/
lemma Cs_eq_L_sub_R (hg : g ≠ 0) (hh : h ≠ 0) (k l : ZMod n) :
    D.Cs g h k l = D.Lmat g h k l - D.τ * D.Rmat g h k l := by
  rw [Cs_eq_B, if_neg (fun e => hg e.1), mul_zero, add_zero]
  simp only [Lmat, Rmat, of_apply, u_def]

/-- `L = H g * diag (u t) * H h`. -/
lemma Lmat_eq : D.Lmat g h = D.Hm g * diagonal (D.u (g + h)) * D.Hm h := by
  ext k l
  rw [Lmat, of_apply, mul_apply]
  apply sum_congr rfl; intro m _
  rw [mul_diagonal]
  simp only [Hm, of_apply]
  rw [add_comm k m]; ring

/-- The reciprocal of a diagonal entry (9.4). -/
lemma inv_u (ht : g + h ≠ 0) (m : ZMod n) :
    (D.u (g + h) m)⁻¹ = D.δ⁻¹ * D.u (-(g + h)) (-m)
      - D.τ * D.δ⁻¹ * ((if m = 0 then 1 else 0) + (if m = g + h then 1 else 0)) := by
  have hδ := D.δ_ne_zero
  apply inv_eq_of_mul_eq_one_right
  rw [u_eq D ht, u_eq D (neg_ne_zero.mpr ht), show -(g + h) - -m = -(g + h - m) by ring]
  have ht' := D.hrec (g + h) ht
  have hWt := D.hWne (g + h)
  have hWt' := D.hWne (-(g + h))
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, if_neg (Ne.symm ht)]
    simp only [D.hW0, sub_zero, neg_zero]
    field_simp
    rw [τ_def]; ring
  · by_cases hm' : m = g + h
    · subst hm'
      rw [if_neg hm, if_pos rfl]
      simp only [sub_self, D.hW0, neg_zero]
      field_simp
      rw [τ_def]; ring
    · rw [if_neg hm, if_neg hm']
      simp only [add_zero, mul_zero, sub_zero]
      have e1 := D.hrec m hm
      have e2 := D.hrec (g + h - m) (sub_ne_zero.mpr (Ne.symm hm'))
      have hWm := D.hWne m
      field_simp
      linear_combination (D.W (g + h - m) * D.W (-(g + h - m))) * e1 + D.δ * e2 - D.δ * ht'

/-- The inverse of the left side, written explicitly. -/
def Lmat' (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  D.Hm' h * diagonal (fun m => (D.u (g + h) m)⁻¹) * D.Hm' g

theorem Lmat'_mul_Lmat (hQ : ∀ g h, D.Q g h = 0) (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) :
    D.Lmat' g h * D.Lmat g h = 1 := by
  rw [Lmat', Lmat_eq]
  have hd : diagonal (fun m => (D.u (g + h) m)⁻¹) * diagonal (D.u (g + h)) = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    rw [diagonal_apply, one_apply]
    split_ifs with hij
    · subst hij; exact inv_mul_cancel₀ (D.u_ne_zero ht i)
    · rfl
  calc D.Hm' h * diagonal (fun m => (D.u (g + h) m)⁻¹) * D.Hm' g
        * (D.Hm g * diagonal (D.u (g + h)) * D.Hm h)
      = D.Hm' h * (diagonal (fun m => (D.u (g + h) m)⁻¹) * ((D.Hm' g * D.Hm g)
          * (diagonal (D.u (g + h)) * D.Hm h))) := by simp only [Matrix.mul_assoc]
    _ = D.Hm' h * D.Hm h := by
        rw [Hm'_mul_Hm D hQ hg, Matrix.one_mul,
          ← Matrix.mul_assoc (diagonal fun m => (D.u (g + h) m)⁻¹), hd, Matrix.one_mul]
    _ = 1 := Hm'_mul_Hm D hQ hh

/-- The entries of the inverse of the left side (9.5). -/
theorem Lmat'_apply (hh : h ≠ 0) (ht : g + h ≠ 0) (k l : ZMod n) :
    D.Lmat' g h k l = D.δ⁻¹ * D.τ⁻¹ ^ 4 * (D.Lr g h k l - D.τ * D.Emat g h k l) := by
  have hδ := D.δ_ne_zero
  have hτ := D.τ_ne_zero
  rw [Lmat', mul_apply]
  simp only [mul_diagonal, Hm', of_apply, inv_u D ht]
  have hB1 : ∀ m, D.B (-h) (m - k) = D.u h (k - m) := by
    intro m; rw [B_eq_u_sub, neg_neg, u_symm D hh]; congr 1; ring
  have hB2 : ∀ m, D.B (-g) (m - l) = D.u g (l - m) := by
    intro m
    rw [B_eq_u_sub, neg_neg]
    by_cases hg : g = 0
    · subst hg; simp only [neg_zero, sub_zero]; rw [u_def, u_def, B_axis_right, B_axis_right]
      by_cases hml : m = l
      · subst hml; simp
      · rw [if_neg (fun e => hml (sub_eq_zero.mp e)), if_neg (fun e => hml (sub_eq_zero.mp e).symm)]
    · rw [u_symm D hg]; congr 1; ring
  have hsum : ∑ m, D.τ⁻¹ ^ 2 * D.u h (k + m) * (D.δ⁻¹ * D.u (-(g + h)) (-m)
        - D.τ * D.δ⁻¹ * ((if m = 0 then 1 else 0) + (if m = g + h then 1 else 0)))
        * (D.τ⁻¹ ^ 2 * D.u g (m + l))
      = D.τ⁻¹ ^ 4 * D.δ⁻¹ * ∑ m, D.u h (k + m) * D.u (-(g + h)) (-m) * D.u g (m + l)
        - D.τ⁻¹ ^ 4 * D.τ * D.δ⁻¹ * ∑ m, D.u h (k + m) * D.u g (m + l)
          * ((if m = 0 then 1 else 0) + (if m = g + h then 1 else 0)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro m _; ring
  rw [hsum]
  have hE : ∑ m, D.u h (k + m) * D.u g (m + l)
      * ((if m = 0 then (1 : K) else 0) + (if m = g + h then 1 else 0)) = D.Emat g h k l := by
    simp only [mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      if_true, Emat, of_apply, add_zero, zero_add]
    rw [add_comm (g + h) l]
  have hL : ∑ m, D.u h (k + m) * D.u (-(g + h)) (-m) * D.u g (m + l) = D.Lr g h k l := by
    rw [Lr, of_apply]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun m => ?_)
    rw [Equiv.neg_apply, hB1, hB2, show k - -m = k + m by ring, show l - -m = m + l by ring]
    ring
  rw [hE, hL]; ring

/-- `(L^r - τ E) * L = δ τ^4 • 1`. -/
theorem Lr_mul_Lmat (hQ : ∀ g h, D.Q g h = 0) (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) :
    (D.Lr g h - D.τ • D.Emat g h) * D.Lmat g h = (D.δ * D.τ ^ 4) • (1 : Matrix (ZMod n) (ZMod n) K) := by
  have hδ := D.δ_ne_zero
  have hτ := D.τ_ne_zero
  have : D.Lr g h - D.τ • D.Emat g h = (D.δ * D.τ ^ 4) • D.Lmat' g h := by
    ext k l
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Lmat'_apply D hh ht,
      smul_eq_mul, smul_eq_mul]
    field_simp
  rw [this, Matrix.smul_mul, Lmat'_mul_Lmat D hQ hg hh ht]

/-! ### The right side -/

/-- `d₁ k = W (h + k) W (-k)`. -/
def d1 (h k : ZMod n) : K := D.W (h + k) * D.W (-k)
/-- `d₂ l = W (g + l) W (-l)`. -/
def d2 (g l : ZMod n) : K := D.W (g + l) * D.W (-l)

/-- The core matrix `M` of the right side, with its rank-two correction. -/
def Mm (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => D.u (-(g + h)) (k - l - g)
    + D.τ ^ 2 * ((if g + l = 0 ∧ k = 0 then 1 else 0) + (if h + k = 0 ∧ l = 0 then 1 else 0))

/-- The three terms of the inverse of `M`. -/
def U0 (g h k l : ZMod n) : K := D.u (g + h) (k - l + g)
def U1 (g h k l : ZMod n) : K := (D.u (g + h) g)⁻¹ * D.u (g + h) (k + g) * D.u (g + h) (g - l)
def U2 (g h k l : ZMod n) : K := (D.u (g + h) g)⁻¹ * D.u (g + h) (k + (g + h)) * D.u (g + h) (-l)

/-- The inverse of `M`. -/
def Mm' (g h : ZMod n) : Matrix (ZMod n) (ZMod n) K :=
  Matrix.of fun k l => D.τ⁻¹ ^ 2 * (D.U0 g h k l - D.U1 g h k l - D.U2 g h k l)

lemma u_t_h (ht : g + h ≠ 0) : D.u (g + h) h = D.u (g + h) g := by
  rw [u_symm D ht h]; congr 1; ring

lemma u_t_t (ht : g + h ≠ 0) : D.u (g + h) (g + h) = -1 := by
  rw [u_def, B_diag D ht]

lemma u_t_zero (ht : g + h ≠ 0) : D.u (g + h) 0 = -1 := by
  rw [u_def, B_zero_left D ht]

/-- `M' * M = 1`. -/
theorem Mm'_mul_Mm (hQ : ∀ g h, D.Q g h = 0) (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) :
    D.Mm' g h * D.Mm g h = 1 := by
  have hτ := D.τ_ne_zero
  have hb := D.u_ne_zero ht g
  ext k l
  rw [mul_apply, one_apply]
  simp only [Mm, Mm', of_apply]
  -- the three convolutions
  have c0 : ∑ m, D.U0 g h k m * D.u (-(g + h)) (m - l - g) = D.τ ^ 2 * (if k = l then 1 else 0) := by
    have := conv_column D hQ ht (k - l)
    simp only [sub_eq_zero] at this
    rw [← this]
    refine Fintype.sum_equiv (Equiv.subLeft (k + g)) _ _ (fun m => ?_)
    rw [Equiv.subLeft_apply, U0, show k - m + g = k + g - m by ring,
      show k - l - (k + g - m) = m - l - g by ring]
  have c1 : ∑ m, D.U1 g h k m * D.u (-(g + h)) (m - l - g)
      = (D.u (g + h) g)⁻¹ * D.u (g + h) (k + g) * (D.τ ^ 2 * (if l = 0 then 1 else 0)) := by
    have := conv_column D hQ ht (-l)
    simp only [neg_eq_zero] at this
    rw [← this, mul_sum]
    refine Fintype.sum_equiv (Equiv.subLeft g) _ _ (fun m => ?_)
    rw [Equiv.subLeft_apply, U1, show -l - (g - m) = m - l - g by ring]; ring
  have c2 : ∑ m, D.U2 g h k m * D.u (-(g + h)) (m - l - g)
      = (D.u (g + h) g)⁻¹ * D.u (g + h) (k + (g + h)) * (D.τ ^ 2 * (if g + l = 0 then 1 else 0)) := by
    have := conv_column D hQ ht (-(g + l))
    simp only [neg_eq_zero] at this
    rw [← this, mul_sum]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun m => ?_)
    rw [Equiv.neg_apply, U2, show -(g + l) - -m = m - l - g by ring]; ring
  -- the rank-two part
  have r0 : D.U0 g h k 0 - D.U1 g h k 0 - D.U2 g h k 0 = (D.u (g + h) g)⁻¹ * D.u (g + h) (k + (g + h)) := by
    simp only [U0, U1, U2, sub_zero, neg_zero, u_t_zero D ht]
    field_simp
    ring
  have rh : D.U0 g h k (-h) - D.U1 g h k (-h) - D.U2 g h k (-h) = (D.u (g + h) g)⁻¹ * D.u (g + h) (k + g) := by
    simp only [U0, U1, U2, sub_neg_eq_add, neg_neg, show k + h + g = k + (g + h) by ring,
      show g + h = g + h from rfl, u_t_h D ht]
    rw [u_t_t D ht]
    field_simp
    ring
  have hexp : ∀ m, D.τ⁻¹ ^ 2 * (D.U0 g h k m - D.U1 g h k m - D.U2 g h k m)
      * (D.u (-(g + h)) (m - l - g) + D.τ ^ 2 * ((if g + l = 0 ∧ m = 0 then 1 else 0)
        + (if h + m = 0 ∧ l = 0 then 1 else 0)))
      = D.τ⁻¹ ^ 2 * (D.U0 g h k m * D.u (-(g + h)) (m - l - g)
        - D.U1 g h k m * D.u (-(g + h)) (m - l - g) - D.U2 g h k m * D.u (-(g + h)) (m - l - g))
      + (if m = 0 then (if g + l = 0 then 1 else 0) * (D.U0 g h k 0 - D.U1 g h k 0 - D.U2 g h k 0) else 0)
      + (if m = -h then (if l = 0 then 1 else 0) * (D.U0 g h k (-h) - D.U1 g h k (-h) - D.U2 g h k (-h)) else 0) := by
    intro m
    by_cases hm0 : m = 0
    · subst hm0
      simp only [add_zero, and_true, true_and, eq_self_iff_true, if_true, zero_eq_neg, hh,
        if_false, false_and, and_false, mul_zero, add_zero]
      split_ifs <;> field_simp <;> ring
    · by_cases hmh : m = -h
      · subst hmh
        have e1 : h + -h = 0 := by ring
        simp only [e1, eq_self_iff_true, true_and, neg_eq_zero, hh, if_false, and_false, if_true,
          mul_zero, zero_add]
        split_ifs <;> field_simp <;> ring
      · have e2 : h + m ≠ 0 := fun e => hmh (eq_neg_of_add_eq_zero_right e)
        simp only [hm0, hmh, e2, and_false, false_and, if_false, mul_zero, add_zero]
        ring
  simp only [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_eq', mem_univ, if_true,
    c0, c1, c2, r0, rh]
  field_simp
  ring

/-- The factorization (9.7) of the right side. -/
theorem Rmat_eq (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) :
    D.Rmat g h = (D.δ⁻¹ ^ 2 * D.W (-(g + h))) • (diagonal (D.d1 h) * D.Mm g h * diagonal (D.d2 g)) := by
  ext k l
  rw [Matrix.smul_apply, mul_diagonal, diagonal_mul, smul_eq_mul]
  simp only [Rmat, Mm, of_apply, d1, d2]
  rw [B_uniform, B_uniform, u_eq D (neg_ne_zero.mpr ht),
    show -(g + h) - (k - l - g) = l - h - k by ring, show k - (g + l) = k - l - g by ring,
    show l - (h + k) = l - h - k by ring]
  have hWt := D.hWne (-(g + h))
  by_cases c1 : g + l = 0 ∧ k = 0
  · obtain ⟨e1, e2⟩ := c1
    have hl : l = -g := eq_neg_of_add_eq_zero_right e1
    subst e2; subst hl
    have c2 : ¬ (h + 0 = 0 ∧ -g = 0) := fun e => hh (by simpa using e.1)
    rw [if_pos ⟨e1, rfl⟩, if_neg c2]
    simp only [add_zero, neg_neg, neg_zero, sub_zero, e1, D.hW0, zero_sub]
    rw [show -g - h = -(g + h) by ring]
    field_simp
    ring
  · by_cases c2 : h + k = 0 ∧ l = 0
    · obtain ⟨e1, e2⟩ := c2
      have hk : k = -h := eq_neg_of_add_eq_zero_right e1
      subst e2; subst hk
      rw [if_neg c1, if_pos ⟨e1, rfl⟩]
      simp only [add_zero, neg_neg, neg_zero, sub_zero, zero_sub, e1, D.hW0]
      rw [show -h - g = -(g + h) by ring]
      field_simp
      ring
    · rw [if_neg c1, if_neg c2]
      field_simp
      ring

/-- The scalar `Z (k, l) = δ⁻³ W (-t) d₂ k d₁ l`. -/
def Zs (g h k l : ZMod n) : K := D.δ⁻¹ ^ 3 * D.W (-(g + h)) * D.d2 g k * D.d1 h l

/-- The entry identity (9.10) combined with the case analysis: `Z (R^r - E) = U0 - U1 - U2`. -/
theorem endpoints (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) (k l : ZMod n) :
    D.Zs g h k l * (D.Rr g h k l - D.Emat g h k l) = D.U0 g h k l - D.U1 g h k l - D.U2 g h k l := by
  have hδ := D.δ_ne_zero
  have hτ := D.τ_ne_zero
  have hne := D.hWne
  -- substitution lemmas `W (-a) = δ / W a`
  have sub : ∀ a : ZMod n, a ≠ 0 → D.W (-a) = D.δ / D.W a := by
    intro a ha; rw [eq_div_iff (hne a), mul_comm]; exact D.hrec a ha
  have e_t := sub (g + h) ht
  have e_g := sub g hg
  have e_h := sub h hh
  have e_t' : D.W (-g - h) = D.δ / D.W (g + h) := by
    rw [show -g - h = -(g + h) by ring]; exact e_t
  have hb : (D.u (g + h) g)⁻¹ = D.W (g + h) / (D.W g * D.W h) := by
    rw [u_eq D ht, show g + h - g = h by ring, inv_div]
  -- expand everything
  simp only [Rr, Emat, U0, U1, U2, Zs, of_apply, d1, d2, hb, B_uniform, u_eq D ht, u_eq D hg,
    u_eq D hh]
  rw [show -k - (-h - l) = h + l - k by ring, show -l - (-g - k) = g + k - l by ring,
    show g + h - (k - l + g) = h + l - k by ring, show g + h - (k + g) = h - k by ring,
    show g + h - (g - l) = h + l by ring, show g + h - (k + (g + h)) = -k by ring,
    show g + h - -l = g + h + l by ring, show h - (k + (g + h)) = -g - k by ring,
    show g - (l + (g + h)) = -h - l by ring, show l + (g + h) = g + h + l by ring, neg_neg, neg_neg]
  -- clean up the two correction indicators
  have i1 : ((-h - l = 0 ∧ -k = 0) ↔ (k = 0 ∧ l = -h)) := by
    constructor
    · rintro ⟨a, b⟩; exact ⟨neg_eq_zero.mp b, by linear_combination -a⟩
    · rintro ⟨a, b⟩; subst a; subst b; exact ⟨by ring, by ring⟩
  have i2 : ((-g - k = 0 ∧ -l = 0) ↔ (k = -g ∧ l = 0)) := by
    constructor
    · rintro ⟨a, b⟩; exact ⟨by linear_combination -a, neg_eq_zero.mp b⟩
    · rintro ⟨a, b⟩; subst a; subst b; exact ⟨by ring, by ring⟩
  simp only [i1, i2]
  -- case analysis
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rcases eq_or_ne l 0 with hl | hl
    · subst hl
      simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
        neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
        true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, if_false, false_and, and_false]
      simp only [e_t, e_g, e_h]
      ring_nf
      try simp only [e_t, e_g, e_h, e_t']
      field_simp [hne]; ring
    · rcases eq_or_ne l (-h) with hl' | hl'
      · subst hl'
        simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
          neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
          true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, if_false, false_and, and_false]
        simp only [e_t, e_g, e_h]
        ring_nf
        try simp only [e_t, e_g, e_h, e_t']
        field_simp [hne]; rw [τ_def]; ring
      · have hhl : h + l ≠ 0 := fun e => hl' (eq_neg_of_add_eq_zero_right e)
        have e_l := sub l hl
        have e_hl : D.W (-h - l) = D.δ / D.W (h + l) := by
          rw [show -h - l = -(h + l) by ring]; exact sub _ hhl
        simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
          neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
          true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, hl, hl', if_false, false_and,
          and_false]
        simp only [e_t, e_g, e_h, e_l, e_hl]
        ring_nf
        try simp only [e_t, e_g, e_h, e_l, e_hl, e_t']
        field_simp [hne]; ring
  · rcases eq_or_ne k (-g) with hk' | hk'
    · subst hk'
      rcases eq_or_ne l 0 with hl | hl
      · subst hl
        simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
          neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
          true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, if_false, false_and, and_false]
        simp only [e_t, e_g, e_h]
        ring_nf
        try simp only [e_t, e_g, e_h, e_t']
        field_simp [hne]; rw [τ_def]; ring
      · rcases eq_or_ne l (-h) with hl' | hl'
        · subst hl'
          simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
            neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
            true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, if_false, false_and, and_false]
          simp only [e_t, e_g, e_h]
          ring_nf
          try simp only [e_t, e_g, e_h, e_t']
          field_simp [hne]; ring
        · have hhl : h + l ≠ 0 := fun e => hl' (eq_neg_of_add_eq_zero_right e)
          have e_l := sub l hl
          have e_hl : D.W (-h - l) = D.δ / D.W (h + l) := by
            rw [show -h - l = -(h + l) by ring]; exact sub _ hhl
          simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
            neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
            true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, hl, hl', if_false, false_and,
            and_false]
          simp only [e_t, e_g, e_h, e_l, e_hl]
          ring_nf
          try simp only [e_t, e_g, e_h, e_l, e_hl, e_t']
          field_simp [hne]; ring
    · have hgk : g + k ≠ 0 := fun e => hk' (eq_neg_of_add_eq_zero_right e)
      have e_k := sub k hk
      have e_gk : D.W (-g - k) = D.δ / D.W (g + k) := by
        rw [show -g - k = -(g + k) by ring]; exact sub _ hgk
      rcases eq_or_ne l 0 with hl | hl
      · subst hl
        simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
          neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
          true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, hk, hk', if_false, false_and,
          and_false]
        simp only [e_t, e_g, e_h, e_k, e_gk]
        ring_nf
        try simp only [e_t, e_g, e_h, e_k, e_gk, e_t']
        field_simp [hne]; ring
      · rcases eq_or_ne l (-h) with hl' | hl'
        · subst hl'
          simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
            neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
            true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, hk, hk', if_false, false_and,
            and_false]
          simp only [e_t, e_g, e_h, e_k, e_gk]
          ring_nf
          try simp only [e_t, e_g, e_h, e_k, e_gk, e_t']
          field_simp [hne]; ring
        · have hhl : h + l ≠ 0 := fun e => hl' (eq_neg_of_add_eq_zero_right e)
          have e_l := sub l hl
          have e_hl : D.W (-h - l) = D.δ / D.W (h + l) := by
            rw [show -h - l = -(h + l) by ring]; exact sub _ hhl
          simp only [neg_zero, sub_zero, add_zero, zero_add, zero_sub, neg_neg, sub_neg_eq_add,
            neg_add_cancel, add_neg_cancel, sub_self, D.hW0, eq_self_iff_true, and_self, and_true,
            true_and, if_true, zero_eq_neg, neg_eq_zero, hg, hh, hk, hk', hl, hl', if_false,
            false_and, and_false]
          simp only [e_t, e_g, e_h, e_k, e_gk, e_l, e_hl]
          ring_nf
          try simp only [e_t, e_g, e_h, e_k, e_gk, e_l, e_hl, e_t']
          field_simp [hne]; ring

/-- `(R^r - E) * R = δ τ^2 • 1`. -/
theorem Rr_sub_E_mul_R (hQ : ∀ g h, D.Q g h = 0) (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0) :
    (D.Rr g h - D.Emat g h) * D.Rmat g h
      = (D.δ * D.τ ^ 2) • (1 : Matrix (ZMod n) (ZMod n) K) := by
  have hδ := D.δ_ne_zero
  have hτ := D.τ_ne_zero
  have hne := D.hWne
  have hM := D.Mm'_mul_Mm hQ hg hh ht
  ext k l
  rw [mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
  have hMkl : ∑ m, D.Mm' g h k m * D.Mm g h m l = if k = l then 1 else 0 := by
    have := congrFun (congrFun hM k) l
    rwa [mul_apply, one_apply] at this
  have hRE : ∀ m, (D.Rr g h - D.Emat g h) k m = D.τ ^ 2 * D.Mm' g h k m / D.Zs g h k m := by
    intro m
    have hZ : D.Zs g h k m ≠ 0 := by
      simp only [Zs, d1, d2]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hδ)) (hne _))
        (mul_ne_zero (hne _) (hne _))) (mul_ne_zero (hne _) (hne _))
    rw [eq_div_iff hZ, mul_comm, Matrix.sub_apply, endpoints D hg hh ht k m, Mm', of_apply]
    field_simp
  have hR : ∀ m, D.Rmat g h m l
      = D.δ⁻¹ ^ 2 * D.W (-(g + h)) * (D.d1 h m * D.Mm g h m l * D.d2 g l) := by
    intro m
    rw [Rmat_eq D hg hh ht, Matrix.smul_apply, mul_diagonal, diagonal_mul, smul_eq_mul]
    try ring
  simp only [hRE, hR]
  have hterm : ∀ m, D.τ ^ 2 * D.Mm' g h k m / D.Zs g h k m
      * (D.δ⁻¹ ^ 2 * D.W (-(g + h)) * (D.d1 h m * D.Mm g h m l * D.d2 g l))
      = (D.δ * D.τ ^ 2 * (D.d2 g l / D.d2 g k)) * (D.Mm' g h k m * D.Mm g h m l) := by
    intro m
    simp only [Zs, d1, d2]
    field_simp [hne]
    try ring
  simp only [hterm, ← mul_sum, hMkl]
  split_ifs with hkl
  · subst hkl
    have : D.d2 g k ≠ 0 := mul_ne_zero (hne _) (hne _)
    field_simp
  · ring

/-- Lemma 9.3 (reflection): if all cubics with first indices `(g, h)` vanish, then so do all
cubics with first indices `(-h, -g)`. -/
theorem C_reflect (hQ : ∀ g h, D.Q g h = 0) (hg : g ≠ 0) (hh : h ≠ 0) (ht : g + h ≠ 0)
    (hC : ∀ k l, D.C g h k l = 0) : ∀ k l, D.C (-h) (-g) k l = 0 := by
  have hδ := D.δ_ne_zero
  have hτ := D.τ_ne_zero
  -- the hypothesis in matrix form: `L = τ • R`
  have hL : D.Lmat g h = D.τ • D.Rmat g h := by
    ext k l
    rw [Matrix.smul_apply, smul_eq_mul]
    have h2 : D.Cs g h k l = 0 := by rw [Cs, hC, mul_zero]
    rw [Cs_eq_L_sub_R D hg hh] at h2
    linear_combination h2
  have h1 := D.Lr_mul_Lmat hQ hg hh ht
  have h2 := D.Rr_sub_E_mul_R hQ hg hh ht
  rw [hL, Matrix.mul_smul] at h1
  have h3 : (D.Lr g h - D.τ • D.Emat g h) * D.Rmat g h
      = (D.δ * D.τ ^ 3) • (1 : Matrix (ZMod n) (ZMod n) K) := by
    have := congrArg (fun M => D.τ⁻¹ • M) h1
    simp only [smul_smul, inv_mul_cancel₀ hτ, one_smul] at this
    rw [this]
    congr 1
    field_simp
    try ring
  have h4 : (D.Lr g h - D.τ • D.Rr g h) * D.Rmat g h = 0 := by
    have e : D.Lr g h - D.τ • D.Rr g h
        = (D.Lr g h - D.τ • D.Emat g h) - D.τ • (D.Rr g h - D.Emat g h) := by
      rw [smul_sub]; abel
    rw [e, Matrix.sub_mul, h3, Matrix.smul_mul, h2, smul_smul,
      show D.τ * (D.δ * D.τ ^ 2) = D.δ * D.τ ^ 3 by ring, sub_self]
  have hRinv : D.Rmat g h * ((D.δ * D.τ ^ 2)⁻¹ • (D.Rr g h - D.Emat g h)) = 1 := by
    have : ((D.δ * D.τ ^ 2)⁻¹ • (D.Rr g h - D.Emat g h)) * D.Rmat g h = 1 := by
      rw [Matrix.smul_mul, h2, smul_smul, inv_mul_cancel₀ (mul_ne_zero hδ (pow_ne_zero 2 hτ)),
        one_smul]
    exact mul_eq_one_comm.mp this
  have h5 : D.Lr g h - D.τ • D.Rr g h = 0 := by
    calc D.Lr g h - D.τ • D.Rr g h
        = (D.Lr g h - D.τ • D.Rr g h)
          * (D.Rmat g h * ((D.δ * D.τ ^ 2)⁻¹ • (D.Rr g h - D.Emat g h))) := by
          rw [hRinv, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  intro k l
  have := congrFun (congrFun h5 (-k)) (-l)
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Lr_apply, Rr_apply,
    neg_neg, neg_neg] at this
  have hCs : D.Cs (-h) (-g) k l = 0 := by
    rw [Cs_eq_L_sub_R D (neg_ne_zero.mpr hh) (neg_ne_zero.mpr hg)]
    exact this
  rw [Cs] at hCs
  exact (mul_eq_zero.mp hCs).resolve_left (pow_ne_zero _ hτ)

end sides



end CoeffData
end HaagerupIzumi
