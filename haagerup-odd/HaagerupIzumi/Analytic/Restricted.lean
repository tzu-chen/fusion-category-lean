module

public import HaagerupIzumi.Analytic.NegColumn

@[expose] public section

/-!
# Restricted Fourier vanishing (Proposition 8.2)

The bracket `û_{-g}(j) S_{p,q,s}(-j) - τ e^{-2πijl/n} S_{p',q',s'}(j)` is expressed through
the four centered kernels `K₄(R, X, Y + ω₂, Z)`, `K₄(R, X, Y - ω₁, Z)`, `K₄(R, X - ω₁, Y, Z)`,
`K₄(R, X + ω₂, Y, Z)` (Euler transformation, shift and evenness for the left product; the
right product is already centered), and the four-term identity makes it vanish.
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

section restricted
variable [NeZero n] (hodd : Odd n) (g h l : ℕ) (hg : 1 ≤ g) (hh : 1 ≤ h) (hgh : g + h < n)
  (hl : 1 ≤ l) (hlh : l ≤ h)

/-! ### No-pinch conditions -/

omit hn G in
/-- The no-pinch condition through the four opposite-parameter sums `Ω/2 + r ± s`, `Ω/2 + r ± x`. -/
lemma noPinch_of (r s x : ℂ)
    (h1 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + r + s ∉ poleSet (ω₁ n) (ω₂ n))
    (h2 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + r - s ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + r - x ∉ poleSet (ω₁ n) (ω₂ n))
    (h4 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + r + x ∉ poleSet (ω₁ n) (ω₂ n)) :
    K4NoPinch (ω₁ n) (ω₂ n) r s x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h1 using 2; unfold k4U; ring
  · convert h2 using 2; unfold k4V; ring
  · convert h3 using 2; unfold k4U k4V; ring
  · convert h4 using 2; unfold k4U k4V; ring

omit G in
include hn in
lemma ω₂_sub_nat_not_pole (m : ℕ) : (ω₂ n : ℂ) - m ∉ poleSet (ω₁ n) (ω₂ n) := by
  have := not_pole_of_pos_coeff n hn (-(m : ℚ)) 1 (-(m : ℝ) + (1 : ℚ) * ω₂ n)
    (by push_cast; ring) one_pos
  convert this using 2; push_cast; ring

omit G in
include hn in
lemma nat_not_pole (m : ℕ) (hm : 1 ≤ m) : (m : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  have := int_not_pole n hn m (by omega)
  exact_mod_cast this

omit G in
include hn in
lemma neg_nat_not_pole (m : ℕ) (hm : 1 ≤ m) : -(m : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) := by
  have := int_not_pole n hn (-(m : ℤ)) (by omega)
  push_cast at this; exact this

omit G in
include hn hg hh hgh hl hlh in
lemma np_rL_s1 : K4NoPinch (ω₁ n) (ω₂ n) (rL g) (s1L n g h) (XL n g l) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  apply noPinch_of
  · have := neg_nat_not_pole n hn (g + h) (by omega)
    convert this using 2; simp only [rL, s1L]; push_cast; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [rL, s1L]; linarith)
  · have := ω₂_sub_nat_not_pole n hn (g + l)
    convert this using 2; simp only [rL, XL]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [rL, XL]; linarith)

omit G in
include hn hg hh hgh hl hlh in
lemma np_RR_s1 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (s1L n g h) (XL n g l) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  apply noPinch_of
  · have := neg_nat_not_pole n hn h hh
    convert this using 2; simp only [RR, s1L]; push_cast; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, s1L]; linarith)
  · have := ω₂_sub_nat_not_pole n hn l
    convert this using 2; simp only [RR, XL]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)

omit G in
include hn hg hh hgh hl hlh in
lemma np_RR_X_s1 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l) (s1L n g h) := by
  obtain ⟨h1, h2, h3, h4⟩ := np_RR_s1 n hn g h l hg hh hgh hl hlh
  refine noPinch_of n _ _ _ ?_ ?_ ?_ ?_
  · convert h4 using 2; unfold k4U k4V; ring
  · convert h3 using 2; unfold k4U k4V; ring
  · convert h2 using 2; unfold k4V; ring
  · convert h1 using 2; unfold k4U; ring

omit G in
include hn hg hh hgh hl hlh in
lemma np_rL_s2 : K4NoPinch (ω₁ n) (ω₂ n) (rL g) (s2L n g h) (XL n g l) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h < n := by exact_mod_cast hgh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [rL, s2L]; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [rL, s2L]; linarith)
  · have := ω₂_sub_nat_not_pole n hn (g + l)
    convert this using 2; simp only [rL, XL]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [rL, XL]; linarith)

omit G in
include hn hg hh hgh hl hlh in
lemma np_RR_s2 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (s2L n g h) (XL n g l) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h < n := by exact_mod_cast hgh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, s2L]; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, s2L]; linarith)
  · have := ω₂_sub_nat_not_pole n hn l
    convert this using 2; simp only [RR, XL]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)

omit G in
include hn hg hh hgh hl hlh in
lemma np_RR_X_s2 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l) (s2L n g h) := by
  obtain ⟨h1, h2, h3, h4⟩ := np_RR_s2 n hn g h l hg hh hgh hl hlh
  refine noPinch_of n _ _ _ ?_ ?_ ?_ ?_
  · convert h4 using 2; unfold k4U k4V; ring
  · convert h3 using 2; unfold k4U k4V; ring
  · convert h2 using 2; unfold k4V; ring
  · convert h1 using 2; unfold k4U; ring

omit G in
include hn hg hh hgh hl hlh in
/-- No pinch for `K₄(R, X, Y + ω₂, ·)`. -/
lemma np_ft1 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l) (YR n g h + ω₂ n) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)
  · have := ω₂_sub_nat_not_pole n hn l
    convert this using 2; simp only [RR, XL]; push_cast; rw [hωC]; ring
  · have := neg_nat_not_pole n hn h hh
    convert this using 2; simp only [RR, YR]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, YR]; linarith)

omit G in
include hn hg hh hgh hl hlh in
/-- No pinch for `K₄(R, X, Y - ω₁, ·)`. -/
lemma np_ft2 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l) (YR n g h - ω₁ n) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h < n := by exact_mod_cast hgh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)
  · have := ω₂_sub_nat_not_pole n hn l
    convert this using 2; simp only [RR, XL]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, YR]; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, YR]; linarith)

omit G in
include hn hg hh hgh hl hlh in
/-- No pinch for `K₄(R, X - ω₁, Y, ·)`. -/
lemma np_ft3 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) (YR n g h) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h < n := by exact_mod_cast hgh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)
  · have := ω₂_sub_nat_not_pole n hn h
    convert this using 2; simp only [RR, YR]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, YR]; linarith)

omit G in
include hn hg hh hgh hl hlh in
/-- No pinch for `K₄(R, X + ω₂, Y, ·)`. -/
lemma np_ft4 : K4NoPinch (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) (YR n g h) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hnω₁ := n_lt_ω₁ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  apply noPinch_of
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, XL]; linarith)
  · have := neg_nat_not_pole n hn l hl
    convert this using 2; simp only [RR, XL]; push_cast; rw [hωC]; ring
  · have := ω₂_sub_nat_not_pole n hn h
    convert this using 2; simp only [RR, YR]; push_cast; rw [hωC]; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [RR, YR]; linarith)

/-! ### Convergence conditions and elementary identities -/

omit G in
include hn in
lemma yL_re_lt (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    |(yL n v).re| < (ω₁ n + ω₂ n - g) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hΩ' : 0 < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
  simp only [yL, ofReal_re]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hΩ', abs_of_pos (by linarith : (0 : ℝ) < 2 * n),
    div_lt_iff₀ (by linarith)]
  nlinarith

omit G in
include hn in
lemma conv_RR (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    K4Conv (ω₁ n) (ω₂ n) (RR g) (-(yL n v)) := by
  have := yL_re_lt n hn g v hvres
  unfold K4Conv
  simp only [neg_re, abs_neg, RR, div_ofNat_re, natCast_re]
  linarith

omit G in
include hn in
lemma conv_rL (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    K4Conv (ω₁ n) (ω₂ n) (rL g) (-(yL n v)) := by
  have := yL_re_lt n hn g v hvres
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  unfold K4Conv
  simp only [neg_re, abs_neg, rL, div_ofNat_re, natCast_re]
  linarith

omit hn G in
lemma yL_neg (v : ℤ) : yL n (-v) = -(yL n v) := by
  simp only [yL]; push_cast; ring

omit hn G in
lemma neg_rL : -(rL g) = RR g := by simp only [rL, RR]; ring

omit G in
include hn in
lemma neg_s1L : -(s1L n g h) = YR n g h + ω₂ n := by
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  simp only [s1L, YR]; push_cast; rw [hωC]; ring

omit G in
include hn in
lemma neg_s2L : -(s2L n g h) = YR n g h - ω₁ n := by
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  simp only [s2L, YR]; push_cast; rw [hωC]; ring

omit n hn G in
lemma Γr_neg (γ : ℂ → ℂ) (a b : ℝ) (r v : ℂ) : Γr γ a b r (-v) = Γr γ a b r v := by
  unfold Γr
  rw [mul_comm]
  congr 2 <;> ring

/-! ### The left kernels as centered kernels -/

include hn hg hh hgh hl hlh in
/-- Euler transformation, shift and evenness for the first left kernel. -/
theorem chain1 (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) * G.K4 (rL g) (s1L n g h) (XL n g l) (-(yL n v))
      = Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (XL n g l)
        * Complex.exp (π * I * (-(yL n v)) * (s1L n g h - XL n g l) / (ω₁ n * ω₂ n))
        * G.K4 (RR g) (XL n g l) (YR n g h + ω₂ n) (yL n v) := by
  have hc1 := conv_rL n hn g v hvres
  have hc2 := conv_RR n hn g v hvres
  rw [← neg_rL g] at hc2
  have e := G.K4_euler (rL g) (s1L n g h) (XL n g l) (-(yL n v)) hc1 hc2
    (np_rL_s1 n hn g h l hg hh hgh hl hlh)
    (by rw [neg_rL]; exact np_RR_s1 n hn g h l hg hh hgh hl hlh)
  have sw := G.K4_swap (-(rL g)) (s1L n g h) (XL n g l) (-(yL n v)) hc2
    (by rw [neg_rL]; exact np_RR_s1 n hn g h l hg hh hgh hl hlh)
  have ev := G.K4_even (-(rL g)) (XL n g l) (s1L n g h) (-(yL n v)) hc2
    (by rw [neg_rL]; exact np_RR_X_s1 n hn g h l hg hh hgh hl hlh)
  rw [Γr_neg] at e
  rw [e, sw, ev, neg_rL, neg_s1L n hn g h, neg_neg]
  ring

include hn hg hh hgh hl hlh in
/-- Euler transformation, shift and evenness for the second left kernel. -/
theorem chain2 (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) * G.K4 (rL g) (s2L n g h) (XL n g l) (-(yL n v))
      = Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (XL n g l)
        * Complex.exp (π * I * (-(yL n v)) * (s2L n g h - XL n g l) / (ω₁ n * ω₂ n))
        * G.K4 (RR g) (XL n g l) (YR n g h - ω₁ n) (yL n v) := by
  have hc1 := conv_rL n hn g v hvres
  have hc2 := conv_RR n hn g v hvres
  rw [← neg_rL g] at hc2
  have e := G.K4_euler (rL g) (s2L n g h) (XL n g l) (-(yL n v)) hc1 hc2
    (np_rL_s2 n hn g h l hg hh hgh hl hlh)
    (by rw [neg_rL]; exact np_RR_s2 n hn g h l hg hh hgh hl hlh)
  have sw := G.K4_swap (-(rL g)) (s2L n g h) (XL n g l) (-(yL n v)) hc2
    (by rw [neg_rL]; exact np_RR_s2 n hn g h l hg hh hgh hl hlh)
  have ev := G.K4_even (-(rL g)) (XL n g l) (s2L n g h) (-(yL n v)) hc2
    (by rw [neg_rL]; exact np_RR_X_s2 n hn g h l hg hh hgh hl hlh)
  rw [Γr_neg] at e
  rw [e, sw, ev, neg_rL, neg_s2L n hn g h, neg_neg]
  ring

/-! ### The gamma factors of Step 3 -/

include hn in
lemma Γr_s1 : Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h)
    = G.γ (-((g : ℂ) + h)) * G.γ ((ω₁ n : ℂ) + ω₂ n + h) := by
  unfold Γr
  congr 2 <;> (simp only [rL, s1L]; push_cast; ring)

include hn in
lemma Γr_s2 : Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h)
    = G.γ ((ω₁ n : ℂ) + ω₂ n - ((g : ℂ) + h)) * G.γ (h : ℂ) := by
  unfold Γr
  congr 2 <;> (simp only [rL, s2L]; push_cast; ring)

include hn in
lemma Γr_X : Γr G.γ (ω₁ n) (ω₂ n) (rL g) (XL n g l)
    = G.γ ((ω₁ n : ℂ) + l) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)) := by
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  unfold Γr
  congr 2 <;> (simp only [rL, XL]; push_cast; rw [hωC]; ring)

include hn in
lemma τ_toCoeffData : (toCoeffData n hn G hodd).τ = -(ω₂ n : ℂ) := by
  rw [CoeffData.τ_def]
  show (δ n : ℂ) - 1 = _
  exact_mod_cast τ_eq n

/-! ### Elementary facts about `F`, the sines and the gamma values -/

include hn in
lemma F_sum_ne (a b : ℕ) : F n G ((a : ℂ) + b) ≠ 0 := by
  have := F_nat_ne_zero n hn G (a + b); push_cast at this; exact this

include hn in
lemma F_neg_nat_ne (m : ℕ) : F n G (-(m : ℂ)) ≠ 0 := by
  have := F_int_ne_zero n hn G (-(m : ℤ)); push_cast at this; exact this

include hn in
lemma F_neg_sum_ne (a b : ℕ) : F n G (-((a : ℂ) + b)) ≠ 0 := by
  have := F_int_ne_zero n hn G (-((a + b : ℕ) : ℤ)); push_cast at this; exact this

omit G in
include hn in
lemma sin_nat_ne (m : ℕ) (hm : 1 ≤ m) : Complex.sin (π * (m : ℂ) / ω₁ n) ≠ 0 := by
  have := sin_int_div_ω₁_ne_zero n hn m (by omega); exact_mod_cast this

omit G in
include hn in
lemma sin_sum_ne (a b : ℕ) (h : 1 ≤ a + b) : Complex.sin (π * ((a : ℂ) + b) / ω₁ n) ≠ 0 := by
  have := sin_int_div_ω₁_ne_zero n hn (a + b) (by omega); push_cast at this; exact this

include hn in
lemma two_sin_nat (m : ℕ) (hm : 1 ≤ m) :
    2 * Complex.sin (π * (m : ℂ) / ω₁ n) * G.γ (-(m : ℂ)) = (-1) ^ (m : ℤ) * F n G (m : ℂ) := by
  have := two_sin_mul_γ_neg n hn G m (by omega); push_cast at this; exact this

include hn in
lemma two_sin_sum (a b : ℕ) (h : 1 ≤ a + b) :
    2 * Complex.sin (π * ((a : ℂ) + b) / ω₁ n) * G.γ (-((a : ℂ) + b))
      = (-1) ^ ((a : ℤ) + b) * F n G ((a : ℂ) + b) := by
  have := two_sin_mul_γ_neg n hn G (a + b) (by omega); push_cast at this; exact this

include hn in
lemma F_neg_mul_nat (m : ℕ) (hm : 1 ≤ m) :
    F n G (-(m : ℂ)) * F n G (m : ℂ) = (-1) ^ ((m : ℤ) + 1) := by
  have := F_neg_mul_F n hn G m (by omega); push_cast at this; exact this

include hn in
lemma F_neg_mul_sum (a b : ℕ) (h : 1 ≤ a + b) :
    F n G (-((a : ℂ) + b)) * F n G ((a : ℂ) + b) = (-1) ^ ((a : ℤ) + b + 1) := by
  have := F_neg_mul_F n hn G (a + b) (by omega); push_cast at this; exact this

include hn in
/-- `2 sin(πm/ω₁) γ(m) F(m) = 1` for `m ≥ 1`. -/
lemma γ_pos_nat (m : ℕ) (hm : 1 ≤ m) :
    2 * Complex.sin (π * (m : ℂ) / ω₁ n) * G.γ (m : ℂ) * F n G (m : ℂ) = 1 := by
  have A := two_sin_mul_γ_neg n hn G (-(m : ℤ)) (by omega)
  push_cast at A
  rw [neg_neg, show (π : ℂ) * -(m : ℂ) / ω₁ n = -(π * m / ω₁ n) by ring, Complex.sin_neg] at A
  have hF := F_neg_mul_nat n hn G m hm
  have hs : (-1 : ℂ) ^ (-(m : ℤ)) * (-1) ^ ((m : ℤ) + 1) = -1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show -(m : ℤ) + ((m : ℤ) + 1) = 1 by ring, zpow_one]
  linear_combination (-(F n G (m : ℂ))) * A - (-1 : ℂ) ^ (-(m : ℤ)) * hF - hs

include hn in
lemma γ_pos_sum (a b : ℕ) (h : 1 ≤ a + b) :
    2 * Complex.sin (π * ((a : ℂ) + b) / ω₁ n) * G.γ ((a : ℂ) + b) * F n G ((a : ℂ) + b) = 1 := by
  have := γ_pos_nat n hn G (a + b) h; push_cast at this; exact this

include hn in
lemma refl_nat (m : ℕ) (hm : 1 ≤ m) :
    G.γ (-(m : ℂ)) * G.γ ((ω₁ n : ℂ) + ω₂ n + m) = 1 := by
  have := G.reflect (-(m : ℂ)) (neg_nat_not_pole n hn m hm)
    (by have := intCast_not_mem_zeroSet n hn (-(m : ℤ)); push_cast at this; exact this)
  rw [show (ω₁ n : ℂ) + ω₂ n - -(m : ℂ) = ω₁ n + ω₂ n + m by ring] at this
  exact this

include hn in
lemma refl_sum (a b : ℕ) (h : 1 ≤ a + b) :
    G.γ ((a : ℂ) + b) * G.γ ((ω₁ n : ℂ) + ω₂ n - ((a : ℂ) + b)) = 1 := by
  have := G.reflect ((a : ℂ) + b) (by have := nat_not_pole n hn (a + b) h; push_cast at this; exact this)
    (by have := intCast_not_mem_zeroSet n hn ((a + b : ℕ) : ℤ); push_cast at this; exact this)
  exact this

include hn in
lemma γ_ω₁_add_nat (m : ℕ) : G.γ ((ω₁ n : ℂ) + m) = F n G (-(m : ℂ)) := by
  have := γ_ω₁_add_int n hn G m; push_cast at this; exact this

include hn in
lemma γ_ω₂_sub_sum (a b : ℕ) :
    G.γ ((ω₂ n : ℂ) - ((a : ℂ) + b)) * F n G (-((a : ℂ) + b)) = 1 := by
  have := γ_ω₂_sub_int n hn G ((a + b : ℕ) : ℤ)
  push_cast at this
  rw [this]
  exact inv_mul_cancel₀ (F_neg_sum_ne n hn G a b)

omit hn G in
lemma sin_neg_arg (x : ℂ) : Complex.sin (π * -x / ω₁ n) = -Complex.sin (π * x / ω₁ n) := by
  rw [← Complex.sin_neg]; congr 1; ring

/-! ### The constant `M` of (8.14) -/

/-- The sign of `M`. -/
noncomputable def MS : ℂ := (-1 : ℂ) ^ ((g : ℤ) + h * (l + 1))

/-- The phase of `M`. -/
noncomputable def Mexp (v : ℤ) : ℂ :=
  Complex.exp (π * I * yL n v * ((ω₁ n : ℂ) + l - g) / (ω₁ n * ω₂ n))

/-- `M = ω₂ (-1)^{g+h(l+1)} F(t₁) / (d F(l)) e^{πiZ(ω₁+l-g)/Ω}`. -/
noncomputable def Mc (v : ℤ) : ℂ :=
  (ω₂ n : ℂ) * MS g h l * F n G ((g : ℂ) + l) / (d n * F n G (l : ℂ)) * Mexp n g l v

omit G in
include hn hgh hlh in
/-- The phase relation (8.16) for the first right kernel. -/
lemma phase1 (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
        * Complex.exp (-π * I * yL n v * ((g : ℂ) + l) / (ω₁ n * ω₂ n))
      = (-1) ^ ((l : ℤ) * (g + 1)) * Mexp n g l v
        * Complex.exp (-π * I * yL n v * ω₁ n / (ω₁ n * ω₂ n)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hΩ' : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
    have : 0 < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := hv
  have hv' : (v : ℂ) = 2 * k - n * (g + 1) + 2 * n * m := by
    have : v = 2 * k - n * (g + 1) + 2 * n * m := by linarith
    rw [this]; push_cast; ring
  unfold Mexp
  rw [stdAddChar_eq n k (l : ZMod n), val_natCast' n l (by omega), ← Complex.exp_add]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  have key : -(2 * π * I * k * (l : ℂ) / n) + -π * I * yL n v * ((g : ℂ) + l) / (ω₁ n * ω₂ n)
      = π * I * yL n v * ((ω₁ n : ℂ) + l - g) / (ω₁ n * ω₂ n)
        + -π * I * yL n v * ω₁ n / (ω₁ n * ω₂ n)
        + ((-((l : ℤ) * (g + 1)) : ℤ) : ℂ) * (π * I) + ((l * m : ℤ) : ℂ) * (2 * π * I) := by
    simp only [yL]; push_cast
    rw [hΩC, hv']
    field_simp
    ring
  rw [key, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [show (-1 : ℂ) ^ (-((l : ℤ) * (g + 1))) = (-1) ^ ((l : ℤ) * (g + 1)) from
    neg_one_zpow_congr _ _ (by
      push_cast
      generalize (l : ZMod 2) = x
      generalize (g : ZMod 2) = y
      revert x y; decide)]
  ring

omit G in
include hn hgh hlh in
/-- The phase relation (8.16) for the second right kernel. -/
lemma phase2 (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
        * Complex.exp (-π * I * yL n v * ((g : ℂ) + l - n) / (ω₁ n * ω₂ n))
      = (-1) ^ ((l : ℤ) * (g + 1)) * Mexp n g l v
        * Complex.exp (-π * I * yL n v * ω₂ n / (ω₁ n * ω₂ n)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hω₂C : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hΩ' : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
    have : 0 < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := hv
  have hv' : (v : ℂ) = 2 * k - n * (g + 1) + 2 * n * m := by
    have : v = 2 * k - n * (g + 1) + 2 * n * m := by linarith
    rw [this]; push_cast; ring
  unfold Mexp
  rw [stdAddChar_eq n k (l : ZMod n), val_natCast' n l (by omega), ← Complex.exp_add]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  have key : -(2 * π * I * k * (l : ℂ) / n) + -π * I * yL n v * ((g : ℂ) + l - n) / (ω₁ n * ω₂ n)
      = π * I * yL n v * ((ω₁ n : ℂ) + l - g) / (ω₁ n * ω₂ n)
        + -π * I * yL n v * ω₂ n / (ω₁ n * ω₂ n)
        + ((-((l : ℤ) * (g + 1)) : ℤ) : ℂ) * (π * I) + ((l * m : ℤ) : ℂ) * (2 * π * I) := by
    simp only [yL]; push_cast
    rw [hΩC, hv']
    field_simp
    rw [hωC]
    ring
  rw [key, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [show (-1 : ℂ) ^ (-((l : ℤ) * (g + 1))) = (-1) ^ ((l : ℤ) * (g + 1)) from
    neg_one_zpow_congr _ _ (by
      push_cast
      generalize (l : ZMod 2) = x
      generalize (g : ZMod 2) = y
      revert x y; decide)]
  ring

/-! ### The four terms of the bracket (Step 5) -/

include hn hg hh hgh hl hlh in
/-- Term 1: `û c_L a₀ I₁ = M sin(πh/ω₁) K₄(R, X, Y + ω₂, Z)`, as an identity of coefficients. -/
theorem term1 (v : ℤ) :
    -(ω₂ n : ℂ) * Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n))
      * ((-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) / (d n * F n G (pL g h) * F n G (qL h)))
      * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n))
      * Complex.exp (π * I * (pL g h) * -(yL n v) / (ω₁ n * ω₂ n))
      * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (XL n g l)
      * Complex.exp (π * I * (-(yL n v)) * (s1L n g h - XL n g l) / (ω₁ n * ω₂ n))
    = Mc n G g h l v * Complex.sin (π * (h : ℂ) / ω₁ n) := by
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFp := F_sum_ne n hn G g h
  have hFh := F_nat_ne_zero n hn G h
  have hFl := F_nat_ne_zero n hn G l
  have hFt := F_sum_ne n hn G g l
  have hSp := sin_sum_ne n hn g h (by omega)
  have hSh := sin_nat_ne n hn h hh
  have hω₂C : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hnω₂ : (n : ℂ) + ω₂ n ≠ 0 := by
    have : 0 < (n : ℝ) + ω₂ n := by linarith [ω₂_pos n, (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
    exact_mod_cast this.ne'
  -- the gamma values
  have hγp : G.γ (-((g : ℂ) + h))
      = (-1) ^ ((g : ℤ) + h) * F n G ((g : ℂ) + h) / (2 * Complex.sin (π * ((g : ℂ) + h) / ω₁ n)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hSp)]
    linear_combination two_sin_sum n hn G g h (by omega)
  have hγΩh : G.γ ((ω₁ n : ℂ) + ω₂ n + h)
      = 2 * Complex.sin (π * (h : ℂ) / ω₁ n) * (-1) ^ (h : ℤ) / F n G (h : ℂ) := by
    rw [eq_div_iff hFh]
    have A := two_sin_nat n hn G h hh
    have R := refl_nat n hn G h hh
    have hs := neg_one_zpow_sq (h : ℤ)
    linear_combination (-((-1 : ℂ) ^ (h : ℤ) * G.γ ((ω₁ n : ℂ) + ω₂ n + h))) * A
      + (2 * Complex.sin (π * (h : ℂ) / ω₁ n) * (-1) ^ (h : ℤ)) * R
      - (F n G (h : ℂ) * G.γ ((ω₁ n : ℂ) + ω₂ n + h)) * hs
  have hγω₁l : G.γ ((ω₁ n : ℂ) + l) = (-1) ^ ((l : ℤ) + 1) / F n G (l : ℂ) := by
    rw [γ_ω₁_add_nat n hn G l, eq_div_iff hFl]
    exact F_neg_mul_nat n hn G l hl
  have hγω₂t : G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)) = F n G ((g : ℂ) + l) * (-1) ^ ((g : ℤ) + l + 1) := by
    have A := γ_ω₂_sub_sum n hn G g l
    have B := F_neg_mul_sum n hn G g l (by omega)
    have hs := neg_one_zpow_sq ((g : ℤ) + l + 1)
    linear_combination (-(G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)))) * hs
      + (-((-1 : ℂ) ^ ((g : ℤ) + l + 1) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)))) * B
      + ((-1 : ℂ) ^ ((g : ℤ) + l + 1) * F n G ((g : ℂ) + l)) * A
  have hcL : (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h))
        / (d n * F n G ((g : ℂ) + h) * F n G (-(h : ℂ)))
      = (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * (-1) ^ ((h : ℤ) + 1)
        * F n G (h : ℂ) / (d n * F n G ((g : ℂ) + h)) := by
    have B := F_neg_mul_nat n hn G h hh
    have hs := neg_one_zpow_sq ((h : ℤ) + 1)
    have hFnh := F_neg_nat_ne n hn G h
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hd hFp) hFnh) (mul_ne_zero hd hFp)]
    linear_combination (-((-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * d n
        * F n G ((g : ℂ) + h))) * hs
      + (-((-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * d n * F n G ((g : ℂ) + h)
        * (-1) ^ ((h : ℤ) + 1))) * B
  set Z := yL n v with hZ
  have hS1 : MS g h l = -((-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h))
      * (-1) ^ ((h : ℤ) + 1) * (-1) ^ (-(h : ℤ)) * (-1) ^ ((g : ℤ) + h) * (-1) ^ (h : ℤ)
      * (-1) ^ ((l : ℤ) + 1) * (-1) ^ ((g : ℤ) + l + 1)) := by
    have : (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h))
        * (-1) ^ ((h : ℤ) + 1) * (-1) ^ (-(h : ℤ)) * (-1) ^ ((g : ℤ) + h) * (-1) ^ (h : ℤ)
        * (-1) ^ ((l : ℤ) + 1) * (-1) ^ ((g : ℤ) + l + 1)
        = (-1) ^ (1 + ((g : ℤ) + h * (l + 1))) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      apply neg_one_zpow_congr
      push_cast
      generalize (g : ZMod 2) = x
      generalize (h : ZMod 2) = y
      generalize (l : ZMod 2) = z
      revert x y z; decide
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) 1 ((g : ℤ) + h * (l + 1)), zpow_one] at this
    unfold MS; linear_combination this
  have hE1 : Mexp n g l v = Complex.exp (-π * I * g * Z / (ω₁ n * ω₂ n))
      * Complex.exp (π * I * ((g : ℂ) + h) * -Z / (ω₁ n * ω₂ n))
      * Complex.exp (π * I * (-Z) * (s1L n g h - XL n g l) / (ω₁ n * ω₂ n)) := by
    unfold Mexp
    rw [← hZ, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [s1L, XL]; push_cast
    rw [hωC]
    field_simp
    ring
  rw [Γr_s1 n hn G g h, Γr_X n hn G g l]
  simp only [pL, qL, sL]
  push_cast
  rw [hγp, hγΩh, hγω₁l, hγω₂t, hcL]
  unfold Mc
  rw [hS1, hE1]
  field_simp
  try ring

include hn hg hh hgh hl hlh in
/-- Term 2. -/
theorem term2 (v : ℤ) :
    -(ω₂ n : ℂ) * Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n))
      * ((-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) / (d n * F n G (pL g h) * F n G (qL h)))
      * ((-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n))
      * Complex.exp (π * I * (n + (pL g h)) * -(yL n v) / (ω₁ n * ω₂ n))
      * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (XL n g l)
      * Complex.exp (π * I * (-(yL n v)) * (s2L n g h - XL n g l) / (ω₁ n * ω₂ n))
    = Mc n G g h l v * ((-1) ^ (g + l + 1) * Complex.sin (π * ((g + h : ℕ) : ℂ) / ω₁ n)
        * Complex.exp (-2 * π * I * yL n v * ω₁ n / (ω₁ n * ω₂ n))) := by
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFp := F_sum_ne n hn G g h
  have hFh := F_nat_ne_zero n hn G h
  have hFl := F_nat_ne_zero n hn G l
  have hFt := F_sum_ne n hn G g l
  have hSp := sin_sum_ne n hn g h (by omega)
  have hSh := sin_nat_ne n hn h hh
  have hω₂C : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hnω₂ : (n : ℂ) + ω₂ n ≠ 0 := by
    have : 0 < (n : ℝ) + ω₂ n := by linarith [ω₂_pos n, (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
    exact_mod_cast this.ne'
  have hγΩp : G.γ ((ω₁ n : ℂ) + ω₂ n - ((g : ℂ) + h))
      = 2 * Complex.sin (π * ((g : ℂ) + h) / ω₁ n) * F n G ((g : ℂ) + h) := by
    have C := γ_pos_sum n hn G g h (by omega)
    have R := refl_sum n hn G g h (by omega)
    linear_combination (-(G.γ ((ω₁ n : ℂ) + ω₂ n - ((g : ℂ) + h)))) * C
      + (2 * Complex.sin (π * ((g : ℂ) + h) / ω₁ n) * F n G ((g : ℂ) + h)) * R
  have hγh : G.γ (h : ℂ) = 1 / (2 * Complex.sin (π * (h : ℂ) / ω₁ n) * F n G (h : ℂ)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hSh) hFh)]
    linear_combination γ_pos_nat n hn G h hh
  have hγω₁l : G.γ ((ω₁ n : ℂ) + l) = (-1) ^ ((l : ℤ) + 1) / F n G (l : ℂ) := by
    rw [γ_ω₁_add_nat n hn G l, eq_div_iff hFl]
    exact F_neg_mul_nat n hn G l hl
  have hγω₂t : G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)) = F n G ((g : ℂ) + l) * (-1) ^ ((g : ℤ) + l + 1) := by
    have A := γ_ω₂_sub_sum n hn G g l
    have B := F_neg_mul_sum n hn G g l (by omega)
    have hs := neg_one_zpow_sq ((g : ℤ) + l + 1)
    linear_combination (-(G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)))) * hs
      + (-((-1 : ℂ) ^ ((g : ℤ) + l + 1) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l)))) * B
      + ((-1 : ℂ) ^ ((g : ℤ) + l + 1) * F n G ((g : ℂ) + l)) * A
  have hcL : (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h))
        / (d n * F n G ((g : ℂ) + h) * F n G (-(h : ℂ)))
      = (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * (-1) ^ ((h : ℤ) + 1)
        * F n G (h : ℂ) / (d n * F n G ((g : ℂ) + h)) := by
    have B := F_neg_mul_nat n hn G h hh
    have hs := neg_one_zpow_sq ((h : ℤ) + 1)
    have hFnh := F_neg_nat_ne n hn G h
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hd hFp) hFnh) (mul_ne_zero hd hFp)]
    linear_combination (-((-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * d n
        * F n G ((g : ℂ) + h))) * hs
      + (-((-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h)) * d n * F n G ((g : ℂ) + h)
        * (-1) ^ ((h : ℤ) + 1))) * B
  set Z := yL n v with hZ
  have hS2 : MS g h l = (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * (l - h))
      * (-1) ^ ((h : ℤ) + 1) * (-1) ^ ((l : ℤ) - h) * (-1) ^ ((l : ℤ) + 1) := by
    unfold MS
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply neg_one_zpow_congr
    push_cast
    generalize (g : ZMod 2) = x
    generalize (h : ZMod 2) = y
    generalize (l : ZMod 2) = z
    revert x y z; decide
  have hE2 : Mexp n g l v = Complex.exp (-π * I * g * Z / (ω₁ n * ω₂ n))
      * Complex.exp (π * I * ((n : ℂ) + ((g : ℂ) + h)) * -Z / (ω₁ n * ω₂ n))
      * Complex.exp (π * I * (-Z) * (s2L n g h - XL n g l) / (ω₁ n * ω₂ n))
      / Complex.exp (-2 * π * I * Z * ω₁ n / (ω₁ n * ω₂ n)) := by
    rw [eq_div_iff (Complex.exp_ne_zero _)]
    unfold Mexp
    rw [← hZ, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [s2L, XL]; push_cast
    rw [hωC]
    field_simp
    ring
  rw [Γr_s2 n hn G g h, Γr_X n hn G g l, ← zpow_natCast]
  simp only [pL, qL, sL]
  push_cast
  rw [sin_neg_arg, hγΩp, hγh, hγω₁l, hγω₂t, hcL]
  unfold Mc
  rw [hS2, hE2]
  field_simp
  try ring

include hn hodd hg hh hgh hl hlh in
/-- Term 3. -/
theorem term3 (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    -(toCoeffData n hn G hodd).τ * ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
      * ((-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) / (d n * F n G (pR g l) * F n G (qR l)))
      * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n))
      * Complex.exp (-π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n))
    = Mc n G g h l v * ((-1) ^ (g + h) * Complex.sin (π * ((g + l : ℕ) : ℂ) / ω₁ n)
        * Complex.exp (-π * I * yL n v * ω₁ n / (ω₁ n * ω₂ n))) := by
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFl := F_nat_ne_zero n hn G l
  have hFt := F_sum_ne n hn G g l
  have hFnt := F_neg_sum_ne n hn G g l
  have hSt := sin_sum_ne n hn g l (by omega)
  have hph := phase1 n hn g h l hgh hlh k v hv
  have hcR : (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
        / (d n * F n G (-((g : ℂ) + l)) * F n G (l : ℂ))
      = (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * (-1) ^ ((g : ℤ) + h)
        * (-1) ^ ((h : ℤ) + l + 1) * F n G ((g : ℂ) + l) / (d n * F n G (l : ℂ)) := by
    have B := F_neg_mul_sum n hn G g l (by omega)
    have hs : (-1 : ℂ) ^ ((g : ℤ) + h) * (-1) ^ ((h : ℤ) + l + 1) * (-1) ^ ((g : ℤ) + l + 1) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      rw [show (g : ℤ) + h + ((h : ℤ) + l + 1) + ((g : ℤ) + l + 1) = 2 * ((g : ℤ) + h + l + 1) by ring]
      exact Even.neg_one_zpow ⟨(g : ℤ) + h + l + 1, by ring⟩
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hd hFnt) hFl) (mul_ne_zero hd hFl)]
    linear_combination (-((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * d n
        * F n G (l : ℂ))) * hs
      - ((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * d n * F n G (l : ℂ)
        * (-1) ^ ((g : ℤ) + h) * (-1) ^ ((h : ℤ) + l + 1)) * B
  set Z := yL n v with hZ
  have hS3 : MS g h l = -((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
      * (-1) ^ ((h : ℤ) + l + 1) * (-1) ^ (l : ℤ) * (-1) ^ ((l : ℤ) * (g + 1))) := by
    have : (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
        * (-1) ^ ((h : ℤ) + l + 1) * (-1) ^ (l : ℤ) * (-1) ^ ((l : ℤ) * (g + 1))
        = (-1) ^ (1 + ((g : ℤ) + h * (l + 1))) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      apply neg_one_zpow_congr
      push_cast
      generalize (g : ZMod 2) = x
      generalize (h : ZMod 2) = y
      generalize (l : ZMod 2) = z
      revert x y z; decide
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) 1 ((g : ℤ) + h * (l + 1)), zpow_one] at this
    unfold MS; linear_combination this
  have hE3 : Mexp n g l v = ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
      * Complex.exp (-π * I * Z * ((g : ℂ) + l) / (ω₁ n * ω₂ n))
      / ((-1) ^ ((l : ℤ) * (g + 1)) * Complex.exp (-π * I * Z * ω₁ n / (ω₁ n * ω₂ n))) := by
    rw [eq_div_iff (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _))]
    linear_combination (-1 : ℂ) * hph
  rw [τ_toCoeffData, ← zpow_natCast]
  simp only [pR, qR, sR]
  push_cast
  rw [sin_neg_arg, hcR]
  unfold Mc
  rw [hS3, hE3]
  field_simp
  try ring

include hn hodd hg hh hgh hl hlh in
/-- Term 4. -/
theorem term4 (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    -(toCoeffData n hn G hodd).τ * ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
      * ((-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) / (d n * F n G (pR g l) * F n G (qR l)))
      * ((-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n))
      * Complex.exp (-π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n))
    = -(Mc n G g h l v * (Complex.sin (π * (l : ℂ) / ω₁ n)
        * Complex.exp (-π * I * yL n v * ω₂ n / (ω₁ n * ω₂ n)))) := by
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFl := F_nat_ne_zero n hn G l
  have hFt := F_sum_ne n hn G g l
  have hFnt := F_neg_sum_ne n hn G g l
  have hSl := sin_nat_ne n hn l hl
  have hph := phase2 n hn g h l hgh hlh k v hv
  have hcR : (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
        / (d n * F n G (-((g : ℂ) + l)) * F n G (l : ℂ))
      = (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * (-1) ^ ((g : ℤ) + l + 1)
        * F n G ((g : ℂ) + l) / (d n * F n G (l : ℂ)) := by
    have B := F_neg_mul_sum n hn G g l (by omega)
    have hs := neg_one_zpow_sq ((g : ℤ) + l + 1)
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hd hFnt) hFl) (mul_ne_zero hd hFl)]
    linear_combination (-((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * d n
        * F n G (l : ℂ))) * hs
      - ((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l)) * d n * F n G (l : ℂ)
        * (-1) ^ ((g : ℤ) + l + 1)) * B
  set Z := yL n v with hZ
  have hS4 : MS g h l = -((-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
      * (-1) ^ ((g : ℤ) + l + 1) * (-1) ^ ((g : ℤ) + h + l) * (-1) ^ ((l : ℤ) * (g + 1))) := by
    have : (-1 : ℂ) ^ (-((g : ℤ) + l) + l + l * ((g : ℤ) + h + l))
        * (-1) ^ ((g : ℤ) + l + 1) * (-1) ^ ((g : ℤ) + h + l) * (-1) ^ ((l : ℤ) * (g + 1))
        = (-1) ^ (1 + ((g : ℤ) + h * (l + 1))) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      apply neg_one_zpow_congr
      push_cast
      generalize (g : ZMod 2) = x
      generalize (h : ZMod 2) = y
      generalize (l : ZMod 2) = z
      revert x y z; decide
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) 1 ((g : ℤ) + h * (l + 1)), zpow_one] at this
    unfold MS; linear_combination this
  have hE4 : Mexp n g l v = ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
      * Complex.exp (-π * I * Z * ((g : ℂ) + l - n) / (ω₁ n * ω₂ n))
      / ((-1) ^ ((l : ℤ) * (g + 1)) * Complex.exp (-π * I * Z * ω₂ n / (ω₁ n * ω₂ n))) := by
    rw [eq_div_iff (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _))]
    linear_combination (-1 : ℂ) * hph
  rw [τ_toCoeffData]
  simp only [pR, qR, sR]
  push_cast
  rw [hcR]
  unfold Mc
  rw [hS4, hE4]
  field_simp
  try ring

/-! ### The main cancellation -/

include hn hodd hg hh hgh hl hlh in
/-- Proposition 8.2: the bracket (8.5) vanishes at the restricted frequencies. -/
theorem bracket_zero (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1)))
    (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    (∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
        * (toCoeffData n hn G hodd).B a (-(g : ZMod n)))
      * (∑ a : ZMod n, ZMod.stdAddChar (-(a * ((-k : ℤ) : ZMod n)))
          * (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
          * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n)))
      - (toCoeffData n hn G hodd).τ * ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n)))
        * (∑ b : ZMod n, ZMod.stdAddChar (-(b * (k : ZMod n)))
            * (toCoeffData n hn G hodd).B b (-((g + l : ℕ) : ZMod n))
            * (toCoeffData n hn G hodd).B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n)) = 0 := by
  -- the left frequency
  have hΩ' : 0 < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hvn : |(v : ℝ)| < n := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hvlt : v < (n : ℤ) := by exact_mod_cast (abs_lt.1 hvn).2
  have hvgt : -(n : ℤ) < v := by exact_mod_cast (abs_lt.1 hvn).1
  have hv1 : -(n : ℤ) ≤ -v := by omega
  have hv2 : -v ≤ n := by omega
  have hv' : (2 * n : ℤ) ∣ (-v) - (2 * (-k) + n * (g - 1)) := by
    obtain ⟨m, hm⟩ := hv
    exact ⟨1 - m, by linarith⟩
  -- the ingredients
  have hL := left_product n hn G hodd g h l hg hh hgh hl hlh (-k) (-v) hv' hv1 hv2
  have hR := right_product n hn G hodd g h l hg hh hgh hl hlh k v hv hvres
  have hU := neg_column n hn G hodd g hg (by omega) k v hv hvres
  have hK1 := chain1 n hn G g h l hg hh hgh hl hlh v hvres
  have hK2 := chain2 n hn G g h l hg hh hgh hl hlh v hvres
  have hFT := G.K4_four_term n g h l (yL n v) (by exact_mod_cast ω₁_sub_ω₂ n)
    (ω₁_mul_ω₂ n) hg hh hgh hl hlh
    (yL_re_lt n hn g v hvres) (np_ft1 n hn g h l hg hh hgh hl hlh) (np_ft2 n hn g h l hg hh hgh hl hlh)
    (np_ft3 n hn g h l hg hh hgh hl hlh) (np_ft4 n hn g h l hg hh hgh hl hlh)
  have hT1 := term1 n hn G g h l hg hh hgh hl hlh v
  have hT2 := term2 n hn G g h l hg hh hgh hl hlh v
  have hT3 := term3 n hn G hodd g h l hg hh hgh hl hlh k v hv
  have hT4 := term4 n hn G hodd g h l hg hh hgh hl hlh k v hv
  rw [yL_neg] at hL
  -- abbreviations
  set SL := ∑ a : ZMod n, ZMod.stdAddChar (-(a * ((-k : ℤ) : ZMod n)))
      * (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
      * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n)) with hSL
  set χ := ZMod.stdAddChar (-((l : ZMod n) * (k : ZMod n))) with hχ
  set eg := Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n)) with heg
  set ΓZ := Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) with hΓZ
  set cL := (-1 : ℂ) ^ ((pL g h) + (qL h) + (qL h) * (sL h l))
    / (d n * F n G (pL g h) * F n G (qL h)) with hcL
  set a₀ := (-1 : ℂ) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n) with ha₀
  set b₀ := (-1 : ℂ) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n) with hb₀
  set E₁ := Complex.exp (π * I * (pL g h) * -(yL n v) / (ω₁ n * ω₂ n)) with hE₁
  set E₂ := Complex.exp (π * I * (n + (pL g h)) * -(yL n v) / (ω₁ n * ω₂ n)) with hE₂
  set K₁ := G.K4 (RR g) (XL n g l) (YR n g h + ω₂ n) (yL n v) with hK₁
  set K₂ := G.K4 (RR g) (XL n g l) (YR n g h - ω₁ n) (yL n v) with hK₂
  set K₃ := G.K4 (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) with hK₃
  set K₄ := G.K4 (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) with hK₄
  set sΩ := (Real.sqrt (ω₁ n * ω₂ n) : ℂ) with hsΩ
  linear_combination SL * hU + (-(ω₂ n : ℂ) * eg * ΓZ) * hL
    + (-(toCoeffData n hn G hodd).τ * χ) * hR
    + ((-(ω₂ n : ℂ) * eg) * (-2 * sΩ * cL) * a₀ * E₁) * hK1
    + ((-(ω₂ n : ℂ) * eg) * (-2 * sΩ * cL) * b₀ * E₂) * hK2
    + (-2 * sΩ * K₁) * hT1 + (-2 * sΩ * K₂) * hT2 + (-2 * sΩ * K₃) * hT3 + (-2 * sΩ * K₄) * hT4
    + (2 * sΩ * Mc n G g h l v) * hFT

end restricted

end Concrete
end HaagerupIzumi
