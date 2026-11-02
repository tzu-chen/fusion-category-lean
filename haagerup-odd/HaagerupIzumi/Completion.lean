module

public import HaagerupIzumi.Degenerate
public import HaagerupIzumi.Reflection
public import HaagerupIzumi.Interpolation
public import HaagerupIzumi.Quartic

@[expose] public section

/-!
# Algebraic completion of the cubics

Section 9 of the expanded proof. The analytic input (Proposition 8.2 together
with the description of the restricted frequency set) is packaged as the
hypothesis `RestrictedFourier`: for every ordered triple `(g, h, l)` the discrete
Fourier transform of `k ↦ 𝒞 g h k l` vanishes outside a block of `g - 1`
consecutive frequencies. From this, the quadratic identities, and the algebraic
lemmas, all cubic residuals vanish.
-/

open Finset ZMod

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} [NeZero n] (D : CoeffData n ℂ)

/-- The analytic input: restricted Fourier vanishing in the ordered range. -/
def RestrictedFourier : Prop :=
  ∀ g h l : ℕ, 1 ≤ g → 1 ≤ h → g + h < n → 1 ≤ l → l ≤ h →
    ∃ k₀ : ZMod n, ∀ j : ZMod n, (∀ i : ℕ, i < g - 1 → j ≠ k₀ + i) →
      dft (fun k => D.Cs (g : ZMod n) (h : ZMod n) k (l : ZMod n)) j = 0

/-! ### Transfer along permutations and translations -/

/-- If the pair of `(g', h', k', l')` is obtained from the pair of `(g, h, k, l)` by
permutations and a translation, the vanishing of the cubic residual transfers. -/
theorem Cs_transfer {g h k l g' h' k' l' : ZMod n} (σ ρ : Equiv.Perm (Fin 3)) (t : ZMod n)
    (ha : aTrip g' h' k' l' = fun i => aTrip g h k l (σ i) - t)
    (hc : cTrip g' h' k' l' = fun j => cTrip g h k l (ρ j) + t)
    (hnd : Nondeg (aTrip g h k l) (cTrip g h k l))
    (h0 : D.Cs g' h' k' l' = 0) : D.Cs g h k l = 0 := by
  have hnd' : Nondeg (aTrip g' h' k' l') (cTrip g' h' k' l') := by
    intro i j
    rw [ha, hc]
    simp only
    rw [show aTrip g h k l (σ i) - t + (cTrip g h k l (ρ j) + t)
      = aTrip g h k l (σ i) + cTrip g h k l (ρ j) by ring]
    exact hnd _ _
  have hSP : D.δ ^ 2 * D.S (aTrip g' h' k' l') (cTrip g' h' k' l')
      - D.τ * D.P (aTrip g' h' k' l') (cTrip g' h' k' l')
      = D.δ ^ 2 * D.S (aTrip g h k l) (cTrip g h k l)
      - D.τ * D.P (aTrip g h k l) (cTrip g h k l) := by
    rw [ha, hc]
    have e1 : (fun i => aTrip g h k l (σ i) - t) = fun i => (aTrip g h k l ∘ σ) i - t := rfl
    have e2 : (fun j => cTrip g h k l (ρ j) + t) = fun j => (cTrip g h k l ∘ ρ) j + t := rfl
    rw [e1, e2, S_translate, P_translate, S_perm_left, S_perm_right, P_perm_left, P_perm_right]
  rw [Cs_factor D hnd'] at h0
  rw [Cs_factor D hnd, ← hSP]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exfalso
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (D.hWne _) (D.hWne _)) (D.hWne _))
      (pow_ne_zero _ D.δ_ne_zero) h1
  · rw [h1, mul_zero]

/-- The first descent map (9.2). -/
lemma descent1 (g h k l : ZMod n) :
    aTrip k h g (l + g - k) = (fun i => aTrip g h k l (Equiv.swap 0 1 i) - (k - g)) ∧
    cTrip k h g (l + g - k) = (fun j => cTrip g h k l j + (k - g)) := by
  constructor
  · funext i; fin_cases i <;> simp [aTrip, sw01_0, sw01_1, sw01_2] <;> ring
  · funext j; fin_cases j <;> simp [cTrip] <;> ring

/-- The second descent map (9.2). -/
lemma descent2 (g h k l : ZMod n) :
    aTrip k (-h - k) (k + h - l) (-g - l)
      = (fun i => aTrip g h k l ((finRotate 3).symm i) - (l - h)) ∧
    cTrip k (-h - k) (k + h - l) (-g - l)
      = (fun j => cTrip g h k l (Equiv.swap 0 2 j) + (l - h)) := by
  constructor
  · funext i; fin_cases i <;> simp [aTrip] <;> ring
  · funext j; fin_cases j <;> simp [cTrip, sw02_0, sw02_1, sw02_2] <;> ring

/-! ### Induction in the ordered range -/

/-- Proposition 9.1: the cubics vanish in the ordered range. -/
theorem Cs_ordered (hQ : ∀ g h, D.Q g h = 0) (hF : D.RestrictedFourier) :
    ∀ g h l : ℕ, 1 ≤ g → 1 ≤ h → g + h < n → 1 ≤ l → l ≤ h →
      ∀ k : ZMod n, D.Cs (g : ZMod n) (h : ZMod n) k (l : ZMod n) = 0 := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro h l hg hh hgh hl hlh
  obtain ⟨k₀, hk₀⟩ := hF g h l hg hh hgh hl hlh
  have hz : ∀ a : ℕ, 1 ≤ a → a ≤ g - 1 →
      D.Cs (g : ZMod n) (h : ZMod n) (a : ZMod n) (l : ZMod n) = 0 := by
    intro a ha1 ha2
    by_cases hnd : Nondeg (aTrip (g : ZMod n) h a l) (cTrip (g : ZMod n) h a l)
    · by_cases hcase : l + g - a ≤ h
      · -- first descent
        have h0 := ih a (by omega) h (l + g - a) ha1 hh (by omega) (by omega) hcase (g : ZMod n)
        have hcast : ((l + g - a : ℕ) : ZMod n) = (l : ZMod n) + g - a := by
          rw [Nat.cast_sub (by omega), Nat.cast_add]
        rw [hcast] at h0
        obtain ⟨e1, e2⟩ := descent1 (g : ZMod n) h a l
        exact Cs_transfer D (Equiv.swap 0 1) 1 (a - g) e1 (by simpa using e2) hnd h0
      · -- second descent
        push_neg at hcase
        have h0 := ih a (by omega) (n - h - a) (n - g - l) ha1 (by omega) (by omega) (by omega)
          (by omega) ((a + h - l : ℕ) : ZMod n)
        have c1 : ((n - h - a : ℕ) : ZMod n) = -(h : ZMod n) - a := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]; ring
        have c2 : ((n - g - l : ℕ) : ZMod n) = -(g : ZMod n) - l := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]; ring
        have c3 : ((a + h - l : ℕ) : ZMod n) = (a : ZMod n) + h - l := by
          rw [Nat.cast_sub (by omega), Nat.cast_add]
        rw [c1, c2, c3] at h0
        obtain ⟨e1, e2⟩ := descent2 (g : ZMod n) h a l
        exact Cs_transfer D (finRotate 3).symm (Equiv.swap 0 2) (l - h) e1 e2 hnd h0
    · -- degenerate
      have := D.C_degenerate hQ _ _ _ _ hnd
      rw [Cs, this, mul_zero]
  have hzero := eq_zero_of_dft_block (fun k => D.Cs (g : ZMod n) h k l) k₀ (g - 1) (by omega)
    hk₀ hz
  intro k
  exact congrFun hzero k

/-! ### The normal form -/

lemma sw12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
lemma sw12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
lemma sw12_2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
lemma rot_0 : (finRotate 3) (0 : Fin 3) = 1 := by decide
lemma rot_1 : (finRotate 3) (1 : Fin 3) = 2 := by decide
lemma rot_2 : (finRotate 3) (2 : Fin 3) = 0 := by decide
lemma rots_0 : (finRotate 3).symm (0 : Fin 3) = 2 := by decide
lemma rots_1 : (finRotate 3).symm (1 : Fin 3) = 0 := by decide
lemma rots_2 : (finRotate 3).symm (2 : Fin 3) = 1 := by decide

/-- The combinatorial core of Lemma 9.2: if all cross sums are nonzero and the diagonal
values sum to `2n`, some off-diagonal value dominates the diagonal value in its column. -/
theorem exists_offdiag_ge {a c : Fin 3 → ZMod n} (hnd : Nondeg a c)
    (hdiag : (a 0 + c 0).val + (a 1 + c 1).val + (a 2 + c 2).val = 2 * n) :
    ∃ i j : Fin 3, i ≠ j ∧ (a j + c j).val ≤ (a i + c j).val := by
  by_contra hcon
  push_neg at hcon
  have hn := NeZero.pos n
  -- basic bounds
  have hX : ∀ i j, 1 ≤ (a i + c j).val ∧ (a i + c j).val < n := fun i j =>
    ⟨Nat.one_le_iff_ne_zero.mpr (fun e => hnd i j ((ZMod.val_eq_zero _).mp e)), ZMod.val_lt _⟩
  -- the key relation `v i j + X j j = n + X i j` for `i ≠ j`
  have key : ∀ i j, i ≠ j → (a i - a j).val + (a j + c j).val = n + (a i + c j).val := by
    intro i j hij
    have h1 : a i + c j = (a j + c j) + (a i - a j) := by ring
    have h2 := ZMod.val_add (a j + c j) (a i - a j)
    rw [← h1] at h2
    have hlt := hcon i j hij
    have hv := ZMod.val_lt (a i - a j)
    have hX' := (hX j j).2
    by_cases hs : (a j + c j).val + (a i - a j).val < n
    · rw [Nat.mod_eq_of_lt hs] at h2; omega
    · push_neg at hs
      rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)] at h2
      omega
  -- `v i j + v j i = n`
  have pair : ∀ i j, i ≠ j → (a i - a j).val + (a j - a i).val = n := by
    intro i j hij
    have hne : a i - a j ≠ 0 := by
      intro e
      have := key i j hij
      rw [e, ZMod.val_zero] at this
      have := (hX j j).2
      omega
    rw [show a j - a i = -(a i - a j) by ring, ZMod.neg_val, if_neg hne]
    have := ZMod.val_lt (a i - a j); omega
  -- the two cyclic sums are multiples of `n`
  have cyc : ∀ x y z : ZMod n, x + y + z = 0 → n ∣ x.val + y.val + z.val := by
    intro x y z h
    rw [← CharP.cast_eq_zero_iff (ZMod n) n]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    exact h
  have c1 := cyc (a 0 - a 1) (a 1 - a 2) (a 2 - a 0) (by ring)
  have c2 := cyc (a 1 - a 0) (a 2 - a 1) (a 0 - a 2) (by ring)
  obtain ⟨q1, hq1⟩ := c1
  obtain ⟨q2, hq2⟩ := c2
  have k01 := key 0 1 (by decide)
  have k12 := key 1 2 (by decide)
  have k20 := key 2 0 (by decide)
  have k10 := key 1 0 (by decide)
  have k21 := key 2 1 (by decide)
  have k02 := key 0 2 (by decide)
  have p01 := pair 0 1 (by decide)
  have p12 := pair 1 2 (by decide)
  have p20 := pair 2 0 (by decide)
  have X00 := hX 0 0; have X11 := hX 1 1; have X22 := hX 2 2
  have X01 := hX 0 1; have X12 := hX 1 2; have X20 := hX 2 0
  have X10 := hX 1 0; have X21 := hX 2 1; have X02 := hX 0 2
  -- bound the multipliers
  have hq1' : q1 = 2 := by
    have lo : n * 1 < n * q1 := by rw [← hq1]; omega
    have hi : n * q1 < n * 3 := by rw [← hq1]; omega
    have := Nat.lt_of_mul_lt_mul_left lo
    have := Nat.lt_of_mul_lt_mul_left hi
    omega
  have hq2' : q2 = 2 := by
    have lo : n * 1 < n * q2 := by rw [← hq2]; omega
    have hi : n * q2 < n * 3 := by rw [← hq2]; omega
    have := Nat.lt_of_mul_lt_mul_left lo
    have := Nat.lt_of_mul_lt_mul_left hi
    omega
  subst hq1' hq2'
  omega

/-- Reading off the quadruple after reordering by `σ` and translating by `a (σ 0)`. -/
lemma normal_form_pair (g h k l : ZMod n) (σ : Equiv.Perm (Fin 3)) :
    aTrip (-(aTrip g h k l (σ 1) + cTrip g h k l (σ 1)))
        (-(aTrip g h k l (σ 2) + cTrip g h k l (σ 2)))
        (-(aTrip g h k l (σ 0) + cTrip g h k l (σ 1)))
        (-(aTrip g h k l (σ 0) + cTrip g h k l (σ 2)))
      = (fun i => aTrip g h k l (σ i) - aTrip g h k l (σ 0)) ∧
    cTrip (-(aTrip g h k l (σ 1) + cTrip g h k l (σ 1)))
        (-(aTrip g h k l (σ 2) + cTrip g h k l (σ 2)))
        (-(aTrip g h k l (σ 0) + cTrip g h k l (σ 1)))
        (-(aTrip g h k l (σ 0) + cTrip g h k l (σ 2)))
      = (fun j => cTrip g h k l (σ j) + aTrip g h k l (σ 0)) := by
  have hbal : aTrip g h k l (σ 0) + aTrip g h k l (σ 1) + aTrip g h k l (σ 2)
      + (cTrip g h k l (σ 0) + cTrip g h k l (σ 1) + cTrip g h k l (σ 2)) = 0 := by
    have hs := Equiv.sum_comp σ (aTrip g h k l)
    have hs' := Equiv.sum_comp σ (cTrip g h k l)
    have hb := trip_balanced g h k l
    simp only [Fin.sum_univ_three] at hs hs'
    linear_combination hs + hs' + hb
  simp only [aTrip, cTrip] at hbal
  constructor
  · funext i
    fin_cases i <;> simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;> ring
  · funext j
    fin_cases j <;> simp only [aTrip, cTrip, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · linear_combination -hbal
    · ring
    · ring

/-- Lemma 9.2 applied: a nondegenerate quadruple whose reordered pair has diagonal sum `2n` and
`X (σ 2) (σ 2) ≤ X (σ 0) (σ 2)` has vanishing cubic residual. -/
theorem Cs_of_perm (hQ : ∀ g h, D.Q g h = 0) (hF : D.RestrictedFourier) (g h k l : ZMod n)
    (hnd : Nondeg (aTrip g h k l) (cTrip g h k l)) (σ : Equiv.Perm (Fin 3))
    (hdiag : (aTrip g h k l (σ 0) + cTrip g h k l (σ 0)).val
      + (aTrip g h k l (σ 1) + cTrip g h k l (σ 1)).val
      + (aTrip g h k l (σ 2) + cTrip g h k l (σ 2)).val = 2 * n)
    (hle : (aTrip g h k l (σ 2) + cTrip g h k l (σ 2)).val
      ≤ (aTrip g h k l (σ 0) + cTrip g h k l (σ 2)).val) : D.Cs g h k l = 0 := by
  set a := aTrip g h k l with ha
  set c := cTrip g h k l with hc
  have hX : ∀ i j, 1 ≤ (a i + c j).val ∧ (a i + c j).val < n := fun i j =>
    ⟨Nat.one_le_iff_ne_zero.mpr (fun e => hnd i j ((ZMod.val_eq_zero _).mp e)), ZMod.val_lt _⟩
  have Xii := hX (σ 0) (σ 0); have Xrr := hX (σ 1) (σ 1); have Xjj := hX (σ 2) (σ 2)
  have Xij := hX (σ 0) (σ 2)
  have cast : ∀ i j, ((n - (a i + c j).val : ℕ) : ZMod n) = -(a i + c j) := by
    intro i j
    rw [Nat.cast_sub (ZMod.val_lt _).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  have h0 := D.Cs_ordered hQ hF (n - (a (σ 1) + c (σ 1)).val) (n - (a (σ 2) + c (σ 2)).val)
    (n - (a (σ 0) + c (σ 2)).val) (by omega) (by omega) (by omega) (by omega) (by omega)
    (-(a (σ 0) + c (σ 1)))
  rw [cast, cast, cast] at h0
  obtain ⟨e1, e2⟩ := normal_form_pair g h k l σ
  rw [← ha, ← hc] at e1 e2
  exact Cs_transfer D σ σ (a (σ 0)) e1 e2 hnd h0

/-- Proposition 9.4 for `g.val + h.val < n`. -/
theorem C_all_small (hQ : ∀ g h, D.Q g h = 0) (hF : D.RestrictedFourier) (g h : ZMod n)
    (hg : g ≠ 0) (hh : h ≠ 0) (hsum : g.val + h.val < n) (k l : ZMod n) : D.C g h k l = 0 := by
  by_cases hnd : Nondeg (aTrip g h k l) (cTrip g h k l)
  swap
  · exact D.C_degenerate hQ g h k l hnd
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := cross_sums g h k l
  have hdiag : (aTrip g h k l 0 + cTrip g h k l 0).val + (aTrip g h k l 1 + cTrip g h k l 1).val
      + (aTrip g h k l 2 + cTrip g h k l 2).val = 2 * n := by
    rw [x00, x11, x22, ZMod.val_add, Nat.mod_eq_of_lt hsum, ZMod.neg_val, ZMod.neg_val, if_neg hg,
      if_neg hh]
    have := ZMod.val_lt g; have := ZMod.val_lt h
    omega
  obtain ⟨i, j, hij, hle⟩ := exists_offdiag_ge hnd hdiag
  have hCs : D.Cs g h k l = 0 := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · -- (0,1): σ = swap 1 2
      refine Cs_of_perm D hQ hF g h k l hnd (Equiv.swap 1 2) ?_ ?_
      · rw [sw12_0, sw12_1, sw12_2]; omega
      · rw [sw12_0, sw12_2]; exact hle
    · -- (0,2): σ = 1
      refine Cs_of_perm D hQ hF g h k l hnd 1 ?_ ?_
      · simp only [Equiv.Perm.one_apply]; exact hdiag
      · simp only [Equiv.Perm.one_apply]; exact hle
    · -- (1,0): σ = finRotate 3
      refine Cs_of_perm D hQ hF g h k l hnd (finRotate 3) ?_ ?_
      · rw [rot_0, rot_1, rot_2]; omega
      · rw [rot_0, rot_2]; exact hle
    · exact absurd rfl hij
    · -- (1,2): σ = swap 0 1
      refine Cs_of_perm D hQ hF g h k l hnd (Equiv.swap 0 1) ?_ ?_
      · rw [sw01_0, sw01_1, sw01_2]; omega
      · rw [sw01_0, sw01_2]; exact hle
    · -- (2,0): σ = swap 0 2
      refine Cs_of_perm D hQ hF g h k l hnd (Equiv.swap 0 2) ?_ ?_
      · rw [sw02_0, sw02_1, sw02_2]; omega
      · rw [sw02_0, sw02_2]; exact hle
    · -- (2,1): σ = (finRotate 3).symm
      refine Cs_of_perm D hQ hF g h k l hnd (finRotate 3).symm ?_ ?_
      · rw [rots_0, rots_1, rots_2]; omega
      · rw [rots_0, rots_2]; exact hle
    · exact absurd rfl hij
  rw [Cs] at hCs
  exact (mul_eq_zero.mp hCs).resolve_left (pow_ne_zero _ D.τ_ne_zero)

/-- Proposition 9.4: all cubic residuals vanish. -/
theorem C_all (hQ : ∀ g h, D.Q g h = 0) (hF : D.RestrictedFourier) (g h k l : ZMod n) :
    D.C g h k l = 0 := by
  by_cases hnd : Nondeg (aTrip g h k l) (cTrip g h k l)
  swap
  · exact D.C_degenerate hQ g h k l hnd
  obtain ⟨x00, x01, x02, x10, x11, x12, x20, x21, x22⟩ := cross_sums g h k l
  have hgh : g + h ≠ 0 := x00 ▸ hnd 0 0
  have hg : g ≠ 0 := fun e => hnd 1 1 (by rw [x11, e, neg_zero])
  have hh : h ≠ 0 := fun e => hnd 2 2 (by rw [x22, e, neg_zero])
  have hvg := ZMod.val_lt g
  have hvh := ZMod.val_lt h
  rcases lt_trichotomy (g.val + h.val) n with hlt | heq | hgt
  · exact D.C_all_small hQ hF g h hg hh hlt k l
  · exfalso
    apply hgh
    rw [← ZMod.val_eq_zero, ZMod.val_add, heq, Nat.mod_self]
  · have h1 : (-h).val + (-g).val < n := by
      rw [ZMod.neg_val, ZMod.neg_val, if_neg hh, if_neg hg]; omega
    have h2 := D.C_all_small hQ hF (-h) (-g) (neg_ne_zero.mpr hh) (neg_ne_zero.mpr hg) h1
    have h3 := D.C_reflect hQ (neg_ne_zero.mpr hh) (neg_ne_zero.mpr hg)
      (by rw [show -h + -g = -(g + h) by ring]; exact neg_ne_zero.mpr hgh) h2 k l
    rwa [neg_neg, neg_neg] at h3

/-! ### The Evans–Gannon equations -/

/-- The four families of Evans–Gannon equations (with `ω = 1`), as in Theorem 1.2 of the
expanded proof. -/
structure EGEquations : Prop where
  linear : ∀ a b, D.A a b = D.A (-b) (a - b) ∧ D.A a b = D.A (b - a) (-a)
  sum_axis : ∑ a, D.A a 0 = -D.δ⁻¹
  quadratic : ∀ g h, D.Q g h = 0
  cubic : ∀ g h k l, D.C g h k l = 0
  quartic : ∀ g h i k, D.Kq g h i k = 0

/-- The algebraic main theorem: the quadratic identities together with the restricted Fourier
vanishing imply all Evans–Gannon equations. -/
theorem EGEquations_of (hQ : ∀ g h, D.Q g h = 0) (hF : D.RestrictedFourier) : D.EGEquations where
  linear a b := ⟨D.A_rot' a b, D.A_rot a b⟩
  sum_axis := D.sum_A_axis
  quadratic := hQ
  cubic := D.C_all hQ hF
  quartic := D.Kq_eq_zero hQ (D.C_all hQ hF)

end CoeffData
end HaagerupIzumi
