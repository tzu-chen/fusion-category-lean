module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Operations

@[expose] public section

/-!
# Vanishing Fourier block

Lemma 2.7 of the expanded proof: if the discrete Fourier transform of
`f : ZMod N → ℂ` vanishes outside a block of `m < N` consecutive frequencies,
and `f` vanishes at `1, …, m`, then `f = 0`.
-/

open Finset Polynomial ZMod

namespace HaagerupIzumi

variable {N : ℕ} [NeZero N]

lemma stdAddChar_ne_zero (x : ZMod N) : stdAddChar x ≠ (0 : ℂ) := by
  intro h
  have : stdAddChar x * stdAddChar (-x) = (1 : ℂ) := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma natCast_injOn_range (m : ℕ) (hm : m ≤ N) :
    Set.InjOn (fun j : ℕ => (j : ZMod N)) (Set.Iio m) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  have := (ZMod.natCast_eq_natCast_iff' i j N).mp hij
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- If `𝓕 f` vanishes outside `{k₀, k₀ + 1, …, k₀ + m - 1}` with `m < N`, and `f` vanishes
at `1, …, m`, then `f = 0`. -/
theorem eq_zero_of_dft_block (f : ZMod N → ℂ) (k₀ : ZMod N) (m : ℕ) (hm : m < N)
    (hF : ∀ k : ZMod N, (∀ j : ℕ, j < m → k ≠ k₀ + j) → 𝓕 f k = 0)
    (hz : ∀ a : ℕ, 1 ≤ a → a ≤ m → f (a : ZMod N) = 0) : f = 0 := by
  classical
  set c : ℕ → ℂ := fun j => 𝓕 f (k₀ + (j : ZMod N)) with hc
  set p : ℂ[X] := ∑ j ∈ range m, C (c j) * X ^ j with hp
  -- inversion restricted to the block
  have hinv : ∀ a : ZMod N,
      f a = (N : ℂ)⁻¹ * (stdAddChar (k₀ * a) * p.eval (stdAddChar a)) := by
    intro a
    have h1 : f a = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * a) • 𝓕 f j := by
      have := congrFun ((dft (N := N)).symm_apply_apply f) a
      rw [invDFT_apply] at this
      exact this.symm
    have himg : ∀ x ∈ (univ : Finset (ZMod N)),
        x ∉ (range m).image (fun j : ℕ => k₀ + (j : ZMod N)) →
        stdAddChar (x * a) • 𝓕 f x = 0 := by
      intro x _ hx
      rw [hF x (fun j hj e => hx (mem_image.mpr ⟨j, mem_range.mpr hj, e.symm⟩)), smul_zero]
    have hinj : Set.InjOn (fun j : ℕ => k₀ + (j : ZMod N)) ↑(range m) := by
      intro i hi j hj hij
      simp only [coe_range, Set.mem_Iio] at hi hj
      exact natCast_injOn_range m hm.le (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj)
        (add_left_cancel hij)
    rw [h1, ← sum_subset (subset_univ _) himg, sum_image hinj, smul_eq_mul]
    congr 1
    rw [hp, eval_finset_sum, mul_sum]
    apply sum_congr rfl; intro j _
    rw [smul_eq_mul, add_mul, AddChar.map_add_eq_mul, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow,
      eval_mul, eval_C, eval_pow, eval_X, hc]
    ring
  -- the block is empty: nothing to do
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have : 𝓕 f = 0 := funext (fun k => hF k (fun j hj => absurd hj (Nat.not_lt_zero j)))
    exact (LinearEquiv.map_eq_zero_iff _).mp this
  -- otherwise `p` has `m` distinct roots and degree `< m`
  have hp0 : p = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun i : Fin m => stdAddChar (((i : ℕ) + 1 : ℕ) : ZMod N)) ?_ ?_ ?_
    · intro i j hij
      have := injective_stdAddChar (N := N) hij
      have := natCast_injOn_range N le_rfl (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) this
      exact Fin.ext (by omega)
    · intro i
      have h0 := hz ((i : ℕ) + 1) (by omega) (by omega)
      rw [hinv] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)))
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h (stdAddChar_ne_zero _)
        · exact h
    · rw [Fintype.card_fin]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)) (Nat.sub_lt hm0 one_pos)
      exact (natDegree_C_mul_X_pow_le _ _).trans (by simp only [mem_range] at hj; omega)
  funext a
  rw [hinv, hp0, eval_zero, mul_zero, mul_zero, Pi.zero_apply]

end HaagerupIzumi
