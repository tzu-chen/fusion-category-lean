module

public import HaagerupIzumi.Analytic.ColumnFourier
public import HaagerupIzumi.Analytic.Restricted
public import HaagerupIzumi.FourierReduction
public import HaagerupIzumi.Completion

@[expose] public section

/-!
# The analytic input for the cubics and the main theorem

Sections 6–8 of the expanded proof produce the restricted Fourier vanishing
(Proposition 8.2). Here it is assembled from the Fourier reduction (Lemma 6.1),
the cancellation of the bracket (`bracket_zero`, Proposition 8.2) and the
description of the restricted frequency set (`exists_freq`), and combined with
the quadratic identities of Section 4 and the algebraic completion of Section 9
into the Evans–Gannon equations for the concrete coefficient matrix.
-/

open Complex Real ZMod Finset

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n)) (hodd : Odd n) [NeZero n]

omit G hodd in
/-- The restricted frequency set: if `j` is not in the block of `g - 1` consecutive frequencies
starting at `k₀ = n'g + 1` (where `n = 2n' + 1`), then the principal frequency
`v ≡ 2j - n(g+1) (mod 2n)` satisfies `|v| ≤ n - g`. -/
lemma exists_freq (g : ℕ) (hg : 1 ≤ g) (hgn : g < n) (n' : ℕ) (hn' : n = 2 * n' + 1) (j : ZMod n)
    (hj : ∀ i : ℕ, i < g - 1 → j ≠ ((n' * g + 1 : ℕ) : ZMod n) + i) :
    ∃ v : ℤ, (2 * n : ℤ) ∣ v - (2 * (j.val : ℤ) - n * (g + 1)) ∧ |v| ≤ n - g := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = j.val := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = 2 * k - n * (g + 1) + (n - g) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = X % (2 * n) := ⟨_, rfl⟩
  have h2n : (0 : ℤ) < 2 * n := by omega
  have hw0 : 0 ≤ w := by rw [hw]; exact Int.emod_nonneg _ h2n.ne'
  have hw1 : w < 2 * n := by rw [hw]; exact Int.emod_lt_of_pos _ h2n
  obtain ⟨q, hq⟩ : ∃ q : ℤ, X = w + 2 * n * q := by
    refine ⟨X / (2 * n), ?_⟩
    rw [hw, Int.emod_def]; ring
  refine ⟨w - (n - g), ⟨-q, by rw [← hk]; linear_combination hX - hq⟩, ?_⟩
  by_contra hcon
  have hwlarge : 2 * ((n : ℤ) - g) < w := by
    rw [abs_le, not_and_or] at hcon
    rcases hcon with h1 | h1 <;> push_neg at h1 <;> omega
  have hnZ : (n : ℤ) = 2 * n' + 1 := by exact_mod_cast hn'
  have hXeven : 2 ∣ X := ⟨k - n' * (g + 1) + n' - g, by rw [hX, hnZ]; ring⟩
  have hweven : 2 ∣ w := by
    obtain ⟨c, hc⟩ := hXeven
    exact ⟨c - n * q, by linear_combination hc - hq⟩
  obtain ⟨i', hi'⟩ := hweven
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = i' - (n - g) - 1 := ⟨(i' - (n - g) - 1).toNat, by omega⟩
  apply hj i (by omega)
  have h2 : 2 * k = 2 * ((n' * g + 1 : ℤ) + i + n * (1 + q)) := by
    linear_combination (-1 : ℤ) * hX + hq + (g : ℤ) * hnZ - 2 * hi + hi'
  have hkeq : k = (n' * g + 1 : ℤ) + i + n * (1 + q) := by linarith
  rw [← ZMod.natCast_zmod_val j, ← Int.cast_natCast (j.val), ← hk, hkeq]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- Proposition 8.2 together with the description of the restricted frequency set: for every
ordered triple, the Fourier transform of the cubic residual vanishes outside a block of `g - 1`
consecutive frequencies. -/
theorem restricted_fourier : (D n hn G hodd).RestrictedFourier := by
  intro g h l hg hh hgh hl hlh
  obtain ⟨n', hn'⟩ := hodd
  refine ⟨((n' * g + 1 : ℕ) : ZMod n), fun j hj => ?_⟩
  obtain ⟨v, hv, hvabs⟩ := exists_freq n g hg (by omega) n' hn' j hj
  have hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g) := by
    have h1 : |(v : ℝ)| ≤ n - g := by exact_mod_cast hvabs
    have hnω₁ := n_lt_ω₁ n
    have hω₂ := ω₂_pos n
    have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have habs : 0 ≤ |(v : ℝ)| := abs_nonneg _
    nlinarith
  have hb := bracket_zero n hn G ⟨n', hn'⟩ g h l hg hh hgh hl hlh (j.val : ℤ) v hv hvres
  have hg0 : (g : ZMod n) ≠ 0 := natCast_ne_zero' n g hg (by omega)
  rw [CoeffData.fourier_reduction (toCoeffData n hn G ⟨n', hn'⟩) (g : ZMod n) (h : ZMod n)
    (l : ZMod n) hg0 j]
  simp only [sL] at hb
  push_cast at hb
  simp only [ZMod.natCast_zmod_val] at hb
  rw [hb, mul_zero]

/-- The Evans–Gannon equations for the concrete coefficient matrix. -/
theorem EGEquations_concrete : (D n hn G hodd).EGEquations :=
  (D n hn G hodd).EGEquations_of (Q_eq_zero n hn G hodd) (restricted_fourier n hn G hodd)

end Concrete
end HaagerupIzumi
