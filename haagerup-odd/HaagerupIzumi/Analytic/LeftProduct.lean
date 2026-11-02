module

public import HaagerupIzumi.Analytic.Products

@[expose] public section

/-!
# The left product transform (Proposition 6.3 (1))

For the ordered labels `p = g + h`, `q = -h`, `s = l - h` of (6.8), the product
transform `S_{p,q,s}(k) = ∑_a u_p(a) u_q(a+s) e^{-2πika/n}` is expressed through
the two four-gamma kernels `K₄(r, s₁, X, y)`, `K₄(r, s₂, X, y)` of (8.4), with
`r = -g/2`, `X = (n+g)/2 + l`, `y = -Ω θ/(2π)`.
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

section left
variable [NeZero n] (hodd : Odd n) (g h l : ℕ) (hg : 1 ≤ g) (hh : 1 ≤ h) (hgh : g + h < n)
  (hl : 1 ≤ l) (hlh : l ≤ h)

/-- The label `p = g + h`. -/
abbrev pL : ℤ := ((g + h : ℕ) : ℤ)
/-- The label `q = -h`. -/
abbrev qL : ℤ := -(h : ℤ)
/-- The label `s = l - h`. -/
abbrev sL : ℤ := (l : ℤ) - h

omit hn G in
/-- The set of constants whose lattices the line `Re z = -ε` must avoid. -/
noncomputable def leftCs : Finset ℝ :=
  {-((g + h : ℕ) : ℝ), ω₂ n, ω₁ n, (l : ℝ), ω₂ n + ((l : ℝ) - h), ω₁ n + ((l : ℝ) - h),
    ω₁ n + l, ω₂ n - ((g + h : ℕ) : ℝ), 0, -ω₁ n, -ω₂ n, ((l : ℝ) - h),
    ω₂ n + ((l : ℝ) - h) - (ω₁ n + ω₂ n), ω₁ n + ((l : ℝ) - h) - (ω₁ n + ω₂ n),
    ((l : ℝ) - h) - ω₂ n}

/-- The avoidance property of `ε`. -/
def Avoid (ε : ℝ) : Prop :=
  (∀ c ∈ leftCs n g h l, ∀ r s : ℕ, ε ≠ c + (r * ω₁ n + s * ω₂ n)) ∧
  (∀ c ∈ leftCs n g h l, ∀ r s : ℕ, ε ≠ c - (r * ω₁ n + s * ω₂ n))

omit hn G in
/-- Existence of a good `ε` and the crossed-pole count `L`. -/
lemma left_eps_exists :
    ∃ (ε : ℝ) (L : ℕ), 0 < ε ∧ ε < 1 ∧
      (∀ ℓ : ℕ, ℓ ≤ L → -ε < ((g + h : ℕ) : ℝ) - ℓ * ω₂ n) ∧
      (∀ ℓ : ℕ, L + 1 ≤ ℓ → ((g + h : ℕ) : ℝ) - ℓ * ω₂ n < -ε) ∧ Avoid n g h l ε := by
  have hω := ω₂_pos n
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌊((g + h : ℕ) : ℝ) / ω₂ n⌋₊ := ⟨_, rfl⟩
  have hL1 : (L : ℝ) * ω₂ n ≤ ((g + h : ℕ) : ℝ) := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ ((g + h : ℕ) : ℝ) / ω₂ n)
    rw [← hL] at this; rwa [le_div_iff₀ hω] at this
  have hL2 : ((g + h : ℕ) : ℝ) < (L + 1) * ω₂ n := by
    have := Nat.lt_floor_add_one (((g + h : ℕ) : ℝ) / ω₂ n)
    rw [← hL] at this; rwa [div_lt_iff₀ hω] at this
  have hε₀ : 0 < min 1 ((L + 1) * ω₂ n - ((g + h : ℕ) : ℝ)) := lt_min one_pos (by linarith)
  obtain ⟨ε, hε0, hε1, hA, hB⟩ := exists_eps n _ hε₀ (leftCs n g h l)
  have hε1' : ε < 1 := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hε2 : ε < (L + 1) * ω₂ n - ((g + h : ℕ) : ℝ) := lt_of_lt_of_le hε1 (min_le_right _ _)
  refine ⟨ε, L, hε0, hε1', ?_, ?_, ⟨hA, hB⟩⟩
  · intro ℓ hℓ
    have hℓ' : (ℓ : ℝ) ≤ L := by exact_mod_cast hℓ
    have : (ℓ : ℝ) * ω₂ n ≤ L * ω₂ n := by gcongr
    linarith
  · intro ℓ hℓ
    have hℓ' : ((L + 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have : ((L + 1 : ℕ) : ℝ) * ω₂ n ≤ ℓ * ω₂ n := by gcongr
    push_cast at this
    linarith

include hn in
/-- The regularity conditions of the difference identity hold on the line `Re z = -ε`. -/
lemma left_line_cond (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) (hav : Avoid n g h l ε)
    (t : ℝ) : K2Cond n (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I) := by
  obtain ⟨hA, hB⟩ := hav
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hmem : ∀ c ∈ leftCs n g h l, True := fun _ _ => trivial
  simp only [leftCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := line_not_pole n (-((g + h : ℕ) : ℝ)) ε t (hA _ (by simp))
    convert this using 1; push_cast; ring
  · have := line_neg_not_pole n 0 ε t (hB _ (by simp))
    convert this using 1; push_cast; ring
  · exact line_not_pole n (ω₂ n) ε t (hA _ (by simp))
  · have := line_not_zero n (ω₂ n) ε t (fun r s => by
      have := hB (-ω₁ n) (by simp) r s; intro heq; apply this; rw [heq]; ring)
    exact this
  · exact line_not_pole n (ω₁ n) ε t (hA _ (by simp))
  · have := line_not_zero n (ω₁ n) ε t (fun r s => by
      have := hB (-ω₂ n) (by simp) r s; intro heq; apply this; rw [heq]; ring)
    exact this
  · have := line_not_pole n (l : ℝ) ε t (hA _ (by simp))
    convert this using 1; push_cast; ring
  · have := line_neg_not_pole n ((l : ℝ) - h) ε t (hB _ (by simp))
    convert this using 1; push_cast; ring
  · have := line_not_pole n (ω₂ n + ((l : ℝ) - h)) ε t (hA _ (by simp))
    convert this using 1; push_cast; ring
  · have := line_not_zero n (ω₂ n + ((l : ℝ) - h)) ε t (fun r s => by
      have := hB (ω₂ n + ((l : ℝ) - h) - (ω₁ n + ω₂ n)) (by simp) r s
      intro heq; apply this; rw [heq]; ring)
    convert this using 1; push_cast; ring
  · have := line_not_pole n (ω₁ n + ((l : ℝ) - h)) ε t (hA _ (by simp))
    convert this using 1; push_cast; ring
  · have := line_not_zero n (ω₁ n + ((l : ℝ) - h)) ε t (fun r s => by
      have := hB (ω₁ n + ((l : ℝ) - h) - (ω₁ n + ω₂ n)) (by simp) r s
      intro heq; apply this; rw [heq]; ring)
    convert this using 1; push_cast; ring
  · apply sin_pi_ne_zero_of_not_int
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      intCast_re, zero_add] at hre
    have h1' : (-1 : ℤ) < m := by exact_mod_cast (by linarith : (-1 : ℝ) < m)
    have h2' : m < (0 : ℤ) := by exact_mod_cast (by linarith : (m : ℝ) < 0)
    omega

/-- The crossed pole `z_j = p - j ω₂` in the notation of Proposition 6.3. -/
noncomputable abbrev zL (j : ℕ) : ℂ := pl n (g + h) j

include hn hodd hg hh hgh hl hlh in
/-- Step 5 (the residue rectangle) for the left product: the strip identity for the kernel. -/
theorem left_strip (θ : ℝ) (hθabs : |θ| ≤ π)
    (hθn : Complex.exp (-I * θ * n) = -((-1) ^ (pL g h + qL h)))
    (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < ((g + h : ℕ) : ℝ) - ℓ * ω₂ n)
    (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → ((g + h : ℕ) : ℝ) - ℓ * ω₂ n < -ε) :
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pL g h) (qL h) (sL h l) θ (((-ε : ℝ) : ℂ) + t * I)) ∧
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pL g h) (qL h) (sL h l) θ (((n - ε : ℝ) : ℂ) + t * I)) ∧
    lineIntegral (K2' n G (pL g h) (qL h) (sL h l) θ) (n - ε)
      - lineIntegral (K2' n G (pL g h) (qL h) (sL h l) θ) (-ε)
      = 2 * π * I * (∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * θ * ((a.val : ℤ) : ℂ))
            * (Rz n G (pL g h) ((a.val : ℤ) : ℂ) * Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l)))
          + ∑ j ∈ Finset.range L, 4 * π * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n)
              * ρJ1 n G (pL g h) (qL h) (sL h l) θ (zL n g h (j + 1))
            + (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n)
              * ρJ2 n G (pL g h) (qL h) (sL h l) θ (zL n g h (j + 1)))) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΩ := ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hpn : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  -- the finite sets of poles
  set Sint : Finset ℂ := Finset.univ.image (fun a : ZMod n => ((a.val : ℕ) : ℂ)) with hSint
  set Scross : Finset ℂ := (Finset.range L).image (fun j => zL n g h (j + 1)) with hScross
  have hval_inj : Function.Injective (fun a : ZMod n => ((a.val : ℕ) : ℂ)) :=
    fun a b hab => ZMod.val_injective n (Nat.cast_injective (R := ℂ) (by simpa using hab))
  have hcross_inj : Function.Injective (fun j : ℕ => zL n g h (j + 1)) :=
    fun x y hxy => by have := pl_injective n (g + h) hxy; omega
  have hdisj : Disjoint Sint Scross := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hq'
    exact pl_ne_nat n hn (g + h) j a.val hj
  -- the residue function
  set ρK : ℂ → ℂ := fun w => if w ∈ Sint then Complex.cos (π * w) * Complex.exp (-I * θ * w)
    * (Rz n G (pL g h) w * Rz n G (qL h) (w + (sL h l)))
    else 4 * π * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n)
        * ρJ1 n G (pL g h) (qL h) (sL h l) θ w
      + (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n) * ρJ2 n G (pL g h) (qL h) (sL h l) θ w)
    with hρK
  -- residues
  have hres : ∀ q ∈ Sint ∪ Scross, HasResidueGen (K2' n G (pL g h) (qL h) (sL h l) θ) q (ρK q) := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      have : ρK ((a.val : ℕ) : ℂ) = (-1) ^ (a.val : ℤ) * Complex.exp (-I * θ * ((a.val : ℤ) : ℂ))
          * (Rz n G (pL g h) ((a.val : ℤ) : ℂ) * Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l))) := by
        simp only [hρK, if_pos hq]
        rw [show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi', zpow_natCast]
        push_cast; ring
      rw [this]
      have := K2'_residue_int n hn G (pL g h) (qL h) (sL h l) θ (a.val : ℤ)
      push_cast at this ⊢
      exact this.hasResidueGen
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
      have hnot : zL n g h (j + 1) ∉ Sint := fun hmem => Finset.disjoint_left.1 hdisj hmem hq
      have : ρK (zL n g h (j + 1)) = 4 * π * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n)
          * ρJ1 n G (pL g h) (qL h) (sL h l) θ (zL n g h (j + 1))
          + (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n)
            * ρJ2 n G (pL g h) (qL h) (sL h l) θ (zL n g h (j + 1))) := by
        simp only [hρK, if_neg hnot]
      rw [this]
      have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      apply K2'_residue_of_shift n G _ _ _ θ _ _ _
        (K2'_shift_eventually n G hodd _ _ _ θ hθn _)
      · -- continuity of the shifted kernel at `z_{j+1}`
        apply K2'_shift_continuousAt
        · have := not_pole_of_pos_const n hn n (-j) ((n : ℝ) + (-j : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n by omega))
          convert this using 2; simp only [zL, pl, pL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_coeff n hn (-(g + h : ℚ)) (j + 2)
            (-((g + h : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zL, pl, pL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_const n hn (n + (g + h) + l) (-j)
            ((n + (g + h) + l : ℝ) + (-j : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n + (g + h) + l by omega))
          convert this using 2; simp only [zL, pl, pL, qL, sL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) (j + 2)
            (-((g + l : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zL, pl, pL, sL]; push_cast; (try rw [hωC]); ring
        · apply sin_pi_ne_zero_of_not_int
          intro m hm
          have := ne_int_of_coeff_ne_zero n hn ((g + h : ℕ) + n) (-(j + 1 : ℚ))
            (((g + h : ℕ) : ℝ) + n - (j + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
          apply this
          have h2 : (((((g + h : ℕ) : ℝ) + n - (j + 1) * ω₂ n) : ℝ) : ℂ) = ((m : ℤ) : ℂ) := by
            rw [← hm]; simp only [zL, pl]; push_cast; ring
          exact_mod_cast h2
      · -- residue of `e^{-iθz} J₁` at `z_{j+1}`
        apply HasResidue.hasResidueGen
        apply J1_residue
        · exact ⟨0, j + 1, by simp only [zL, pl, pL]; push_cast; ring⟩
        · have := not_pole_of_pos_coeff n hn (-(g + h : ℚ)) (j + 1)
            (-((g + h : ℕ) : ℝ) + (j + 1 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zL, pl, pL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) (j + 2)
            (-((g + l : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zL, pl, pL, sL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_const n hn (n + (g + h) + l) (-j)
            ((n + (g + h) + l : ℝ) + (-j : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n + (g + h) + l by omega))
          convert this using 2; simp only [zL, pl, pL, qL, sL]; push_cast; (try rw [hωC]); ring
      · -- residue of `e^{-iθz} J₂` at `z_{j+1}`
        apply HasResidue.hasResidueGen
        apply J2_residue
        · exact ⟨0, j, by simp only [zL, pl, pL]; push_cast; ring⟩
        · have := not_pole_of_pos_const n hn (n - (g + h : ℚ)) (j + 2)
            ((n : ℝ) - ((g + h : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring)
            (by have : ((g + h : ℕ) : ℚ) < n := by exact_mod_cast hgh
                push_cast at this ⊢; linarith)
          convert this using 2; simp only [zL, pl, pL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) (j + 1)
            (-((g + l : ℕ) : ℝ) + (j + 1 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zL, pl, pL, sL]; push_cast; (try rw [hωC]); ring
        · have := not_pole_of_pos_const n hn ((g + h : ℚ) + l) (-(j + 1 : ℚ))
            (((g + h : ℕ) : ℝ) + l + (-(j + 1 : ℚ)) * ω₂ n) (by push_cast; ring)
            (by have : (0 : ℚ) < (g + h : ℚ) + l := by exact_mod_cast (show 0 < g + h + l by omega)
                exact this)
          convert this using 2; simp only [zL, pl, pL, qL, sL]; push_cast; (try rw [hωC]); ring
  -- the poles are interior
  obtain ⟨M, T, hT, hM⟩ := K2'_bound n G (pL g h) (qL h) (sL h l) θ (-ε) (n - ε)
  have hSpos : ∀ q ∈ Sint ∪ Scross, -ε < q.re ∧ q.re < n - ε ∧ |q.im| < T := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      have h1 : (a.val : ℝ) ≤ n - 1 := by
        have : (a.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show a.val ≤ n - 1 by
          have := ZMod.val_lt a; omega)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
      have h2 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
      simp only [natCast_re, natCast_im, abs_zero]
      exact ⟨by linarith, by linarith, hT⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
      have hjL : j + 1 ≤ L := by have := Finset.mem_range.1 hj; omega
      have := hP1 (j + 1) hjL
      have hre : (zL n g h (j + 1)).re = (g : ℝ) + h - (j + 1) * ω₂ n := by
        simp [zL, pl]
      have him : (zL n g h (j + 1)).im = 0 := by simp [zL, pl]
      rw [hre, him, abs_zero]
      push_cast at this
      have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      refine ⟨this, ?_, hT⟩
      nlinarith
  -- differentiability off the poles
  have hd : ∀ ζ : ℂ, -ε ≤ ζ.re → ζ.re ≤ n - ε → ζ ∉ Sint ∪ Scross →
      DifferentiableAt ℂ (K2' n G (pL g h) (qL h) (sL h l) θ) ζ := by
    intro ζ hζ1 hζ2 hζS
    have hζint : ζ ∉ Sint := fun hmem => hζS (Finset.mem_union.2 (Or.inl hmem))
    have hζcross : ζ ∉ Scross := fun hmem => hζS (Finset.mem_union.2 (Or.inr hmem))
    apply K2'_differentiableAt
    · rintro ⟨r, s', hrs⟩
      have hζ : ζ = (g : ℂ) + h - r * ω₁ n - (s' + 1) * ω₂ n := by
        simp only [pL] at hrs; push_cast at hrs ⊢; linear_combination hrs
      have hre : ζ.re = (g : ℝ) + h - r * ω₁ n - (s' + 1) * ω₂ n := by rw [hζ]; simp
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rcases le_or_gt (s' + 1) L with hs | hs
        · apply hζcross
          refine Finset.mem_image.2 ⟨s', Finset.mem_range.2 (by omega), ?_⟩
          rw [hζ]; simp only [zL, pl]; push_cast; ring
        · have := hP2 (s' + 1) (by omega)
          simp only [Nat.cast_zero, zero_mul, sub_zero] at hre
          push_cast at this hre
          linarith
      · have := left_pole_lt n hn (g + h) (by omega) ε hε1 r (s' + 1) hr
        push_cast at this hre
        linarith
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · refine HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ ?_
      simp only [sL, qL, sub_re, add_re, ofReal_re, intCast_re, natCast_re, neg_re, sub_neg_eq_add]
      push_cast; linarith
    · refine HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ ?_
      simp only [sL, sub_re, add_re, ofReal_re, intCast_re, natCast_re]
      push_cast; linarith
    · apply sin_pi_ne_zero_of_not_int
      intro m hm
      apply hζint
      have hre : ζ.re = m := by rw [hm]; simp
      have h1 : (0 : ℤ) ≤ m := by
        have : (-1 : ℝ) < m := by linarith
        have : (-1 : ℤ) < m := by exact_mod_cast this
        omega
      have h2 : m ≤ (n : ℤ) - 1 := by
        have : (m : ℝ) < n := by linarith
        have : m < (n : ℤ) := by exact_mod_cast this
        omega
      refine Finset.mem_image.2 ⟨((m.toNat : ℕ) : ZMod n), Finset.mem_univ _, ?_⟩
      rw [val_natCast' n _ (by omega), hm]
      have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h1
      exact_mod_cast this
  -- decay rate
  have hc0 : 0 < π - |θ| + π * ((pL g h) + (qL h)) / (ω₁ n * ω₂ n) := by
    have e : ((pL g h : ℤ) : ℝ) + ((qL h : ℤ) : ℝ) = g := by push_cast [pL, qL]; ring
    rw [e]
    have : 0 < π * g / (ω₁ n * ω₂ n) := by positivity
    linarith
  obtain ⟨hint0, hint1, hEq⟩ := strip_residues_gen (K2' n G (pL g h) (qL h) (sL h l) θ) (-ε) (n - ε)
    (by linarith) (Sint ∪ Scross) T hT hSpos ρK hres hd M _ hc0 (by
      intro z hza hzb hzT
      have := hM z hza hzb hzT
      push_cast at this ⊢
      exact this)
  refine ⟨hint0, hint1, ?_⟩
  rw [hEq]
  congr 1
  rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => hval_inj hxy),
    Finset.sum_image (fun x _ y _ hxy => hcross_inj hxy)]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    have hmem : ((a.val : ℕ) : ℂ) ∈ Sint := Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    simp only [hρK, if_pos hmem]
    rw [show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi', zpow_natCast]
    push_cast; ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hmem : zL n g h (j + 1) ∈ Scross := Finset.mem_image.2 ⟨j, hj, rfl⟩
    have hnot : zL n g h (j + 1) ∉ Sint := fun h' => Finset.disjoint_left.1 hdisj h' hmem
    simp only [hρK, if_neg hnot]

/-! ### The centered kernels of (8.4) -/

/-- The frequency `θ = π v / n`. -/
noncomputable abbrev θL (v : ℤ) : ℝ := π * v / n
/-- `r = -g/2`. -/
noncomputable abbrev rL : ℂ := -(g : ℂ) / 2
/-- `s₁ = -Ω/2 - g/2 - h`. -/
noncomputable abbrev s1L : ℂ := -((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 - (g : ℂ) / 2 - h
/-- `s₂ = Ω/2 - g/2 - h`. -/
noncomputable abbrev s2L : ℂ := ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 - (g : ℂ) / 2 - h
/-- `X = (n + g)/2 + l`. -/
noncomputable abbrev XL : ℂ := ((n : ℂ) + g) / 2 + l
/-- `y = -Ω θ/(2π) = -Ω v/(2n)`. -/
noncomputable abbrev yL (v : ℤ) : ℂ := ((-(ω₁ n + ω₂ n) * v / (2 * n) : ℝ) : ℂ)

include hn in
/-- The integrand of `K₄(r, s₁, X, y)` at `z` is `e^{-πipy/Ω} e^{-iθw} J₁(w)`, `w = z + p/2`. -/
lemma k4_J1_eq (v : ℤ) (z : ℂ) :
    k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) (XL n g l) (yL n v) z
      = Complex.exp (-π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n))
        * (Complex.exp (-I * (θL n v) * (z + (pL g h) / 2))
          * J1 n G (pL g h) (qL h) (sL h l) (z + (pL g h) / 2)) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hexp : Complex.exp (2 * π * I * yL n v * z / (ω₁ n * ω₂ n))
      = Complex.exp (-π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n))
        * Complex.exp (-I * (θL n v) * (z + (pL g h) / 2)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [yL, θL, pL]; push_cast
    rw [hΩC]
    have hΩ0 : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
      have : (0 : ℝ) < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
      exact_mod_cast this.ne'
    field_simp
    ring
  unfold k4Integrand k4U k4V J1
  rw [hexp]
  have e1 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g + s1L n g h) / 2 + z = z + (pL g h) / 2 - (pL g h) := by
    simp only [rL, s1L, pL]; push_cast; ring
  have e2 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g + s1L n g h) / 2 - z = -(z + (pL g h) / 2) := by
    simp only [rL, s1L, pL]; push_cast; ring
  have e3 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g - s1L n g h) / 2 + z + XL n g l
      = ω₁ n + (z + (pL g h) / 2) + (sL h l) - (qL h) := by
    simp only [rL, s1L, pL, XL, sL, qL]; push_cast; rw [hωC]; ring
  have e4 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g - s1L n g h) / 2 - z - XL n g l
      = ω₂ n - (z + (pL g h) / 2) - (sL h l) := by
    simp only [rL, s1L, pL, XL, sL]; push_cast; rw [hωC]; ring
  rw [e1, e2, e3, e4]; ring

include hn in
/-- The integrand of `K₄(r, s₂, X, y)` at `z` is `e^{-πi(n+p)y/Ω} e^{-iθw} J₂(w)`,
`w = z + (n+p)/2`. -/
lemma k4_J2_eq (v : ℤ) (z : ℂ) :
    k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) (XL n g l) (yL n v) z
      = Complex.exp (-π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n))
        * (Complex.exp (-I * (θL n v) * (z + (n + (pL g h)) / 2))
          * J2 n G (pL g h) (qL h) (sL h l) (z + (n + (pL g h)) / 2)) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hexp : Complex.exp (2 * π * I * yL n v * z / (ω₁ n * ω₂ n))
      = Complex.exp (-π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n))
        * Complex.exp (-I * (θL n v) * (z + (n + (pL g h)) / 2)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [yL, θL, pL]; push_cast
    rw [hΩC]
    have hΩ0 : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
      have : (0 : ℝ) < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
      exact_mod_cast this.ne'
    field_simp
    ring
  unfold k4Integrand k4U k4V J2
  rw [hexp]
  have e1 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g + s2L n g h) / 2 + z
      = ω₂ n + (z + (n + (pL g h)) / 2) - (pL g h) := by
    simp only [rL, s2L, pL]; push_cast; rw [hωC]; ring
  have e2 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g + s2L n g h) / 2 - z
      = ω₁ n - (z + (n + (pL g h)) / 2) := by
    simp only [rL, s2L, pL]; push_cast; rw [hωC]; ring
  have e3 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g - s2L n g h) / 2 + z + XL n g l
      = (z + (n + (pL g h)) / 2) + (sL h l) - (qL h) := by
    simp only [rL, s2L, pL, XL, sL, qL]; push_cast; ring
  have e4 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (rL g - s2L n g h) / 2 - z - XL n g l
      = -(z + (n + (pL g h)) / 2) - (sL h l) := by
    simp only [rL, s2L, pL, XL, sL]; push_cast; ring
  rw [e1, e2, e3, e4]; ring

include hn hodd hg hh hgh hl hlh in
/-- Step 3: the line identity `∫(K(z+n) - K(z)) = -4π (a₀ ∫ e^{-iθz}J₁ + b₀ ∫ e^{-iθz}J₂)`. -/
theorem left_line (θ : ℝ)
    (hθn : Complex.exp (-I * θ * n) = -((-1) ^ (pL g h + qL h)))
    (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) (hav : Avoid n g h l ε)
    (hint0 : MeasureTheory.Integrable
      (fun t : ℝ => K2' n G (pL g h) (qL h) (sL h l) θ (((-ε : ℝ) : ℂ) + t * I)))
    (hint1 : MeasureTheory.Integrable
      (fun t : ℝ => K2' n G (pL g h) (qL h) (sL h l) θ (((n - ε : ℝ) : ℂ) + t * I)))
    (hJ1 : MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * θ * (((-ε : ℝ) : ℂ) + t * I))
      * J1 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I)))
    (hJ2 : MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * θ * (((-ε : ℝ) : ℂ) + t * I))
      * J2 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I))) :
    lineIntegral (K2' n G (pL g h) (qL h) (sL h l) θ) (n - ε)
      - lineIntegral (K2' n G (pL g h) (qL h) (sL h l) θ) (-ε)
      = -4 * π * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n)
          * lineIntegral (fun z => Complex.exp (-I * θ * z) * J1 n G (pL g h) (qL h) (sL h l) z) (-ε)
        + (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n)
          * lineIntegral (fun z => Complex.exp (-I * θ * z) * J2 n G (pL g h) (qL h) (sL h l) z) (-ε)) := by
  have hline : ∀ t : ℝ, K2' n G (pL g h) (qL h) (sL h l) θ (((n - ε : ℝ) : ℂ) + t * I)
      - K2' n G (pL g h) (qL h) (sL h l) θ (((-ε : ℝ) : ℂ) + t * I)
      = -4 * π * Complex.exp (-I * θ * (((-ε : ℝ) : ℂ) + t * I))
        * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n)
            * J1 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I)
          + (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n)
            * J2 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I)) := by
    intro t
    have := K2'_shift n G hodd (pL g h) (qL h) (sL h l) θ hθn _
      (left_line_cond n hn g h l ε L hε0 hε1 hav t)
    rw [show ((n - ε : ℝ) : ℂ) + t * I = (((-ε : ℝ) : ℂ) + t * I) + n by push_cast; ring]
    exact this
  unfold lineIntegral
  rw [← MeasureTheory.integral_sub (hint1.mul_const I) (hint0.mul_const I),
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add ((hJ1.mul_const I).const_mul _) ((hJ2.mul_const I).const_mul _),
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext t
  rw [← sub_mul, hline t]; ring

/-! ### Step 6 for the left product: the crossed poles and the centered kernels -/

include hn hodd hg hh hgh hl hlh in
/-- The first four-gamma integral along `Re z = -ε`, with the crossed poles `z_0, …, z_L`
added back, is the centered kernel `K₄(r, s₁, X, y)` up to the phase of (8.4). -/
theorem left_K4_1 (v : ℤ) (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n)
    (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < ((g + h : ℕ) : ℝ) - ℓ * ω₂ n)
    (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → ((g + h : ℕ) : ℝ) - ℓ * ω₂ n < -ε) (hav : Avoid n g h l ε) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * (θL n v) * (((-ε : ℝ) : ℂ) + t * I))
      * J1 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I)) ∧
    Complex.exp (-π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n))
      * (lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pL g h) (qL h) (sL h l) z) (-ε)
        + 2 * π * I * ∑ j ∈ Finset.range (L + 1), ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h j))
      = I * Real.sqrt (ω₁ n * ω₂ n) * G.K4 (rL g) (s1L n g h) (XL n g l) (yL n v) := by
  classical
  obtain ⟨hA, hB⟩ := hav
  simp only [leftCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hpn : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hvr : (v : ℝ) ≤ n := by exact_mod_cast hv2
  have hvl : -(n : ℝ) ≤ v := by exact_mod_cast hv1
  -- the parameters
  have hU : k4U (ω₁ n) (ω₂ n) (rL g) (s1L n g h) = -(((g + h : ℕ) : ℂ)) / 2 := by
    unfold k4U; simp only [rL, s1L]; push_cast; ring
  have hV : k4V (ω₁ n) (ω₂ n) (rL g) (s1L n g h) = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + (h : ℂ) / 2 := by
    unfold k4V; simp only [rL, s1L]; push_cast; ring
  set Φ : ℂ → ℂ := fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pL g h) (qL h) (sL h l) z
    with hΦ
  set E : ℂ := Complex.exp (-π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n)) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  set c : ℝ := ((g : ℝ) + h) / 2 with hc
  have hk4 : ∀ z, k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) (XL n g l) (yL n v) z
      = E * Φ (z - ((-c : ℝ) : ℂ)) := by
    intro z
    rw [k4_J1_eq n hn G g h l v z, hΦ, hE]
    simp only [c]
    congr 2 <;> (congr 1; push_cast; ring)
  -- the crossed poles
  set SL : Finset ℂ := (Finset.range (L + 1)).image (fun j => zL n g h j - ((g + h : ℕ) : ℂ) / 2)
    with hSL
  have hSL_inj : Function.Injective (fun j : ℕ => zL n g h j - ((g + h : ℕ) : ℂ) / 2) :=
    fun x y hxy => pl_injective n (g + h) (by simpa using hxy)
  set ρL : ℂ → ℂ := fun w => E * ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (w + ((g + h : ℕ) : ℂ) / 2)
    with hρL
  -- residues of `Φ` at `z_j`
  have hresΦ : ∀ j : ℕ, j ≤ L →
      HasResidue Φ (zL n g h j) (ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h j)) := by
    intro j hj
    apply J1_residue
    · exact ⟨0, j, by simp only [zL, pl, pL]; push_cast; ring⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have := int_not_pole n hn (-((g + h : ℕ) : ℤ)) (by omega)
        convert this using 2; simp only [zL, pl]; push_cast; ring
      · have := not_pole_of_pos_coeff n hn (-(g + h : ℚ)) j
          (-((g + h : ℕ) : ℝ) + (j : ℚ) * ω₂ n) (by push_cast; ring) (by exact_mod_cast hj0)
        convert this using 2; simp only [zL, pl]; push_cast; ring
    · have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) (j + 1)
        (-((g + l : ℕ) : ℝ) + (j + 1 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
      convert this using 2; simp only [zL, pl, sL]; push_cast; ring
    · have := not_pole_of_pos_const n hn (n + (g + h) + l) (1 - j)
        ((n + (g + h) + l : ℝ) + (1 - j : ℚ) * ω₂ n) (by push_cast; ring)
        (by exact_mod_cast (show 0 < n + (g + h) + l by omega))
      convert this using 2; simp only [zL, pl, pL, qL, sL]; push_cast; rw [hωC]; ring
  -- apply the line characterization of `K₄`
  obtain ⟨hint, heq⟩ := G.K4_line (rL g) (s1L n g h) (XL n g l) (yL n v) (-ε - c) SL ∅ ρL 0
    (by
      -- convergence
      unfold K4Conv
      simp only [yL, rL, ofReal_re, neg_re, ofReal_im, natCast_re]
      push_cast
      have : |-(ω₁ n + ω₂ n) * v / (2 * n)| ≤ (ω₁ n + ω₂ n) / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < ω₁ n + ω₂ n),
          abs_of_pos (by linarith : (0 : ℝ) < 2 * n), div_le_div_iff₀ (by linarith) (by norm_num)]
        have : |(v : ℝ)| ≤ n := abs_le.2 ⟨hvl, hvr⟩
        nlinarith
      simp only [neg_re, natCast_re, re_ofNat, natCast_im, im_ofNat, mul_zero, sub_zero,
        div_ofNat_re] at *
      linarith)
    (by
      -- no pinch
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hU]
        have := int_not_pole n hn (-((g + h : ℕ) : ℤ)) (by omega)
        convert this using 2; push_cast; ring
      · rw [hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
      · rw [hU, hV]
        have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) 1 (-((g + l : ℕ) : ℝ) + (1 : ℚ) * ω₂ n)
          (by push_cast; ring) one_pos
        convert this using 2; simp only [XL]; push_cast; rw [hωC]; ring
      · rw [hU, hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [XL, add_re, sub_re, neg_re, ofReal_re, natCast_re, natCast_im,
            ofReal_im, re_ofNat, im_ofNat, mul_zero, sub_zero, div_ofNat_re]
          push_cast; linarith))
    (by
      intro a b
      rw [hU]
      simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div]
      intro heq
      apply hA (-((g + h : ℕ) : ℝ)) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [XL, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, add_re]
      intro heq
      apply hA (ω₁ n + l) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hU]
      simp only [add_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      intro heq
      apply hB 0 (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [XL, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
        mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      intro heq
      apply hB (((l : ℝ) - h) - ω₂ n) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      -- the crossed left poles
      intro w
      rw [hU, hV]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        have hjL : j ≤ L := by have := Finset.mem_range.1 hj; omega
        refine ⟨Or.inl ⟨0, j, by simp only [zL, pl]; push_cast; ring⟩, ?_⟩
        have := hP1 j hjL
        simp only [zL, pl, sub_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
          sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        push_cast at this ⊢; linarith
      · rintro ⟨hfam, hre⟩
        rcases hfam with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
        · simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
            mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div] at hre
          rcases Nat.eq_zero_or_pos a with rfl | ha
          · rcases le_or_gt b L with hb | hb
            · refine Finset.mem_image.2 ⟨b, Finset.mem_range.2 (by omega), ?_⟩
              simp only [zL, pl]; push_cast; ring
            · exfalso; have := hP2 b hb; push_cast at this hre; linarith
          · exfalso
            have := left_pole_lt n hn (g + h) (by omega) ε hε1 a b ha
            push_cast at this hre; linarith
        · exfalso
          simp only [XL, sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re,
            ofReal_im, mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re] at hre
          have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
          have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
          push_cast at hre; linarith)
    (by
      -- no crossed right poles
      intro w
      rw [hU, hV]
      simp only [Finset.notMem_empty, false_iff, not_and, not_lt]
      rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · simp only [add_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
          mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith
      · simp only [XL, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re,
          ofReal_im, mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith)
    (by
      -- residues at the crossed poles
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      have hjL : j ≤ L := by have := Finset.mem_range.1 hj; omega
      have h1 := hasResidueGen_const_mul
        (hasResidueGen_comp_sub (hresΦ j hjL).hasResidueGen ((-c : ℝ) : ℂ)) E
      have h3 := hasResidueGen_congr_fun h1 (fun z => (hk4 z).symm)
      have hpt : zL n g h j - ((g + h : ℕ) : ℂ) / 2 = zL n g h j + ((-c : ℝ) : ℂ) := by
        simp only [c]; push_cast; ring
      rw [hpt]
      convert h3 using 2
      simp only [hρL, c]; congr 2; push_cast; ring)
    (by intro w hw; exact absurd hw (Finset.notMem_empty w))
  -- translate the conclusion
  refine ⟨?_, ?_⟩
  · refine (hint.const_mul E⁻¹).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [hk4, ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
    congr 1; push_cast; ring
  · rw [Finset.sum_empty, mul_zero, sub_zero] at heq
    have hli : lineIntegral (k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) (XL n g l) (yL n v))
        (-ε - c) = E * lineIntegral Φ (-ε) := by
      rw [show k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s1L n g h) (XL n g l) (yL n v)
          = fun z => E * Φ (z - ((-c : ℝ) : ℂ)) from funext hk4, lineIntegral_const_mul,
        lineIntegral_comp_sub, show -ε - c - (-c) = -ε by ring]
    rw [hli, Finset.sum_image (fun x _ y _ hxy => hSL_inj hxy)] at heq
    have hsum : ∑ j ∈ Finset.range (L + 1), ρL (zL n g h j - ((g + h : ℕ) : ℂ) / 2)
        = E * ∑ j ∈ Finset.range (L + 1), ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hρL]
      congr 2; ring
    rw [hsum] at heq
    rw [← heq]; ring

include hn hodd hg hh hgh hl hlh in
/-- The second four-gamma integral along `Re z = -ε`, with the crossed poles `z_1, …, z_L`
added back, is the centered kernel `K₄(r, s₂, X, y)` up to the phase of (8.4). -/
theorem left_K4_2 (v : ℤ) (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n)
    (ε : ℝ) (L : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hP1 : ∀ ℓ : ℕ, ℓ ≤ L → -ε < ((g + h : ℕ) : ℝ) - ℓ * ω₂ n)
    (hP2 : ∀ ℓ : ℕ, L + 1 ≤ ℓ → ((g + h : ℕ) : ℝ) - ℓ * ω₂ n < -ε) (hav : Avoid n g h l ε) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * (θL n v) * (((-ε : ℝ) : ℂ) + t * I))
      * J2 n G (pL g h) (qL h) (sL h l) (((-ε : ℝ) : ℂ) + t * I)) ∧
    Complex.exp (-π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n))
      * (lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pL g h) (qL h) (sL h l) z) (-ε)
        + 2 * π * I * ∑ j ∈ Finset.range L, ρJ2 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h (j + 1)))
      = I * Real.sqrt (ω₁ n * ω₂ n) * G.K4 (rL g) (s2L n g h) (XL n g l) (yL n v) := by
  classical
  obtain ⟨hA, hB⟩ := hav
  simp only [leftCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hpn : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hvr : (v : ℝ) ≤ n := by exact_mod_cast hv2
  have hvl : -(n : ℝ) ≤ v := by exact_mod_cast hv1
  -- the parameters
  have hU : k4U (ω₁ n) (ω₂ n) (rL g) (s2L n g h)
      = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 - (((g + h : ℕ) : ℂ)) / 2 := by
    unfold k4U; simp only [rL, s2L]; push_cast; ring
  have hV : k4V (ω₁ n) (ω₂ n) (rL g) (s2L n g h) = (h : ℂ) / 2 := by
    unfold k4V; simp only [rL, s2L]; push_cast; ring
  set Φ : ℂ → ℂ := fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pL g h) (qL h) (sL h l) z
    with hΦ
  set E : ℂ := Complex.exp (-π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n)) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  set c : ℝ := ((n : ℝ) + (g + h)) / 2 with hc
  have hk4 : ∀ z, k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) (XL n g l) (yL n v) z
      = E * Φ (z - ((-c : ℝ) : ℂ)) := by
    intro z
    rw [k4_J2_eq n hn G g h l v z, hΦ, hE]
    simp only [c, pL]
    congr 2 <;> (congr 1; push_cast; ring)
  -- the crossed poles
  set SL : Finset ℂ := (Finset.range L).image
    (fun j => zL n g h (j + 1) - ((n : ℂ) + ((g + h : ℕ) : ℂ)) / 2) with hSL
  have hSL_inj : Function.Injective
      (fun j : ℕ => zL n g h (j + 1) - ((n : ℂ) + ((g + h : ℕ) : ℂ)) / 2) :=
    fun x y hxy => by have := pl_injective n (g + h) (by simpa using hxy); omega
  set ρL : ℂ → ℂ := fun w => E * ρJ2 n G (pL g h) (qL h) (sL h l) (θL n v)
    (w + ((n : ℂ) + ((g + h : ℕ) : ℂ)) / 2) with hρL
  -- residues of `Φ` at `z_{j+1}`
  have hresΦ : ∀ j : ℕ, HasResidue Φ (zL n g h (j + 1))
      (ρJ2 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h (j + 1))) := by
    intro j
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    apply J2_residue
    · exact ⟨0, j, by simp only [zL, pl, pL]; push_cast; ring⟩
    · have := not_pole_of_pos_const n hn (n - (g + h : ℚ)) (j + 2)
        ((n : ℝ) - ((g + h : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring)
        (by have : ((g + h : ℕ) : ℚ) < n := by exact_mod_cast hgh
            push_cast at this ⊢; linarith)
      convert this using 2; simp only [zL, pl, pL]; push_cast; rw [hωC]; ring
    · have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) (j + 1)
        (-((g + l : ℕ) : ℝ) + (j + 1 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
      convert this using 2; simp only [zL, pl, pL, sL]; push_cast; ring
    · have := not_pole_of_pos_const n hn ((g + h : ℚ) + l) (-(j + 1 : ℚ))
        (((g + h : ℕ) : ℝ) + l + (-(j + 1 : ℚ)) * ω₂ n) (by push_cast; ring)
        (by have : (0 : ℚ) < (g + h : ℚ) + l := by exact_mod_cast (show 0 < g + h + l by omega)
            exact this)
      convert this using 2; simp only [zL, pl, pL, qL, sL]; push_cast; ring
  -- apply the line characterization of `K₄`
  obtain ⟨hint, heq⟩ := G.K4_line (rL g) (s2L n g h) (XL n g l) (yL n v) (-ε - c) SL ∅ ρL 0
    (by
      unfold K4Conv
      simp only [yL, rL, ofReal_re, neg_re, ofReal_im, natCast_re, div_ofNat_re]
      push_cast
      have : |-(ω₁ n + ω₂ n) * v / (2 * n)| ≤ (ω₁ n + ω₂ n) / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < ω₁ n + ω₂ n),
          abs_of_pos (by linarith : (0 : ℝ) < 2 * n), div_le_div_iff₀ (by linarith) (by norm_num)]
        have : |(v : ℝ)| ≤ n := abs_le.2 ⟨hvl, hvr⟩
        nlinarith
      (try simp only [neg_re, natCast_re, natCast_im, mul_zero, sub_zero, div_ofNat_re] at *)
      linarith)
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hU]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [sub_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, natCast_re,
            natCast_im, mul_zero, sub_zero, div_ofNat_re, zero_mul]
          push_cast; linarith)
      · rw [hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im, mul_zero, sub_zero,
            div_ofNat_re, zero_mul]
          linarith)
      · rw [hU, hV]
        have := not_pole_of_pos_coeff n hn (-(g + l : ℚ)) 1 (-((g + l : ℕ) : ℝ) + (1 : ℚ) * ω₂ n)
          (by push_cast; ring) one_pos
        convert this using 2; simp only [XL]; push_cast; rw [hωC]; ring
      · rw [hU, hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [XL, add_re, sub_re, neg_re, ofReal_re, natCast_re, natCast_im,
            ofReal_im, re_ofNat, im_ofNat, mul_zero, sub_zero, div_ofNat_re]
          push_cast; linarith))
    (by
      intro a b
      rw [hU]
      simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div]
      intro heq
      apply hA (ω₂ n - ((g + h : ℕ) : ℝ)) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [XL, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, add_re]
      intro heq
      apply hA (l : ℝ) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hU]
      simp only [add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      intro heq
      apply hB (-ω₁ n) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [XL, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
        mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      intro heq
      apply hB ((l : ℝ) - h) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro w
      rw [hU, hV]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        have hjL : j + 1 ≤ L := by have := Finset.mem_range.1 hj; omega
        refine ⟨Or.inl ⟨0, j, by simp only [zL, pl]; push_cast; rw [hωC]; ring⟩, ?_⟩
        have := hP1 (j + 1) hjL
        simp only [zL, pl, sub_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
          sub_zero, add_re, re_ofNat, im_ofNat, div_ofNat_re]
        push_cast at this ⊢; linarith
      · rintro ⟨hfam, hre⟩
        rcases hfam with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
        · simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
            mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div] at hre
          rcases Nat.eq_zero_or_pos a with rfl | ha
          · rcases le_or_gt (b + 1) L with hb | hb
            · refine Finset.mem_image.2 ⟨b, Finset.mem_range.2 (by omega), ?_⟩
              simp only [zL, pl]; push_cast; rw [hωC]; ring
            · exfalso; have := hP2 (b + 1) hb; push_cast at this hre; linarith
          · exfalso
            have := left_pole_lt n hn (g + h) (by omega) ε hε1 a (b + 1) ha
            push_cast at this hre; linarith
        · exfalso
          simp only [XL, sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re,
            ofReal_im, mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re] at hre
          have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
          have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
          push_cast at hre; linarith)
    (by
      intro w
      rw [hU, hV]
      simp only [Finset.notMem_empty, false_iff, not_and, not_lt]
      rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · simp only [add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
          mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith
      · simp only [XL, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re,
          ofReal_im, mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith)
    (by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      have h1 := hasResidueGen_const_mul
        (hasResidueGen_comp_sub (hresΦ j).hasResidueGen ((-c : ℝ) : ℂ)) E
      have h3 := hasResidueGen_congr_fun h1 (fun z => (hk4 z).symm)
      have hpt : zL n g h (j + 1) - ((n : ℂ) + ((g + h : ℕ) : ℂ)) / 2
          = zL n g h (j + 1) + ((-c : ℝ) : ℂ) := by
        simp only [c]; push_cast; ring
      rw [hpt]
      convert h3 using 2
      simp only [hρL, c]; congr 2; push_cast; ring)
    (by intro w hw; exact absurd hw (Finset.notMem_empty w))
  refine ⟨?_, ?_⟩
  · refine (hint.const_mul E⁻¹).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [hk4, ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
    congr 1; push_cast; ring
  · rw [Finset.sum_empty, mul_zero, sub_zero] at heq
    have hli : lineIntegral (k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) (XL n g l) (yL n v))
        (-ε - c) = E * lineIntegral Φ (-ε) := by
      rw [show k4Integrand G.γ (ω₁ n) (ω₂ n) (rL g) (s2L n g h) (XL n g l) (yL n v)
          = fun z => E * Φ (z - ((-c : ℝ) : ℂ)) from funext hk4, lineIntegral_const_mul,
        lineIntegral_comp_sub, show -ε - c - (-c) = -ε by ring]
    rw [hli, Finset.sum_image (fun x _ y _ hxy => hSL_inj hxy)] at heq
    have hsum : ∑ j ∈ Finset.range L, ρL (zL n g h (j + 1) - ((n : ℂ) + ((g + h : ℕ) : ℂ)) / 2)
        = E * ∑ j ∈ Finset.range L,
          ρJ2 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h (j + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hρL]
      congr 2; ring
    rw [hsum] at heq
    rw [← heq]; ring

/-! ### Step 1 and Step 6 for the left product -/

omit hn G in
include hg in
lemma left_sign_collapse (a : ℕ) :
    (-1 : ℂ) ^ (a : ℤ) * (-1) ^ ((a * (g - 1) : ℕ) : ℤ) * (-1) ^ ((pL g h) * ((a : ℤ) + 1))
      * (-1) ^ ((qL h) * (((a : ℤ) + (sL h l)) + 1))
      = (-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [pL, qL, sL, Nat.add_sub_cancel]
  push_cast
  generalize (a : ZMod 2) = x
  generalize (g' : ZMod 2) = y
  generalize (h : ZMod 2) = z
  generalize (l : ZMod 2) = w
  revert x y z w; decide

include hn hodd hg hh hgh hl hlh in
/-- Step 1 for the left product: the residues at the integers give the product transform plus
the sample correction `ω₂ e^{-2πikp/n} u_q(p+s)`. -/
theorem left_residue_sum (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (g - 1))) :
    ∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * (θL n v) * ((a.val : ℤ) : ℂ))
        * (Rz n G (pL g h) ((a.val : ℤ) : ℂ) * Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l)))
      = (-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) * (d n * F n G (pL g h) * F n G (qL h))
        * (∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
            * (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
            * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n))
          + ω₂ n * Complex.exp (-(2 * π * I * k * ((g + h : ℕ) : ℂ) / n))
            * (toCoeffData n hn G hodd).B (((g + l : ℕ) : ZMod n)) (-(h : ZMod n))) := by
  classical
  have hd0 := sqrt_d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pL g h)
  have hFq := F_int_ne_zero n hn G (qL h)
  have hsq := sqrt_d_sq n
  -- the summand
  have hterm : ∀ a : ZMod n,
      (-1) ^ (a.val : ℤ) * Complex.exp (-I * (θL n v) * ((a.val : ℤ) : ℂ))
        * (Rz n G (pL g h) ((a.val : ℤ) : ℂ) * Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l)))
      = (-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) * (d n * F n G (pL g h) * F n G (qL h))
        * (ZMod.stdAddChar (-(a * (k : ZMod n)))
          * (((toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
              + ω₂ n * (if a.val = g + h then 1 else 0))
            * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n)))) := by
    intro a
    have hav : a.val ≤ n - 1 := by have := ZMod.val_lt a; omega
    -- `R_p(a) = t_p(a) √d F(p) (-1)^{p(a+1)}`
    have hRp : Rz n G (pL g h) ((a.val : ℤ) : ℂ)
        = tz n G (pL g h) (a.val : ℤ) * (Real.sqrt (d n) * F n G (pL g h))
          * (-1) ^ ((pL g h) * ((a.val : ℤ) + 1)) := by
      unfold tz
      have := neg_one_zpow_sq ((pL g h) * ((a.val : ℤ) + 1))
      field_simp
      linear_combination (-(Rz n G (pL g h) ((a.val : ℤ) : ℂ))) * this
    have hRq : Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l))
        = tz n G (qL h) ((a.val : ℤ) + (sL h l)) * (Real.sqrt (d n) * F n G (qL h))
          * (-1) ^ ((qL h) * (((a.val : ℤ) + (sL h l)) + 1)) := by
      unfold tz
      have := neg_one_zpow_sq ((qL h) * (((a.val : ℤ) + (sL h l)) + 1))
      have hFq' : F n G ((qL h : ℤ) : ℂ) ≠ 0 := hFq
      simp only [sL, qL] at this hFq' ⊢
      push_cast at this hFq' ⊢
      field_simp
      linear_combination (-(Rz n G (-(h : ℤ)) ((a.val : ℂ) + ((l : ℂ) - h)))) * this
    -- the sample rules
    have htp : tz n G (pL g h) (a.val : ℤ) = (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
        + ω₂ n * (if a.val = g + h then 1 else 0) := by
      have := tz_pos n hn G hodd (g + h) (by omega) (by omega) a.val hav
      rw [ZMod.natCast_zmod_val] at this
      exact this
    have htq : tz n G (qL h) ((a.val : ℤ) + (sL h l))
        = (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n)) := by
      rcases le_or_gt h (a.val + l) with hcase | hcase
      · -- nonnegative sample point
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m = a.val + l - h := ⟨_, rfl⟩
        have hm' : (a.val : ℤ) + (sL h l) = m := by simp only [sL]; omega
        rw [hm', tz_neg_nonneg n hn G hodd h hh (by omega) m (by omega)]
        congr 2
        rw [← ZMod.natCast_zmod_val a]
        have : ((m : ℤ) : ZMod n) = ((a.val : ℤ) + (sL h l) : ℤ) := by rw [hm']
        simp only [sL] at this ⊢
        push_cast at this ⊢
        linear_combination this
      · -- negative sample point
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m = h - l - a.val := ⟨_, rfl⟩
        have hm' : (a.val : ℤ) + (sL h l) = -(m : ℤ) := by simp only [sL]; omega
        rw [hm', tz_neg_neg n hn G hodd h hh (by omega) m (by omega) (by omega),
          if_neg (by omega), mul_zero, add_zero]
        congr 2
        rw [← ZMod.natCast_zmod_val a]
        have : ((-(m : ℤ) : ℤ) : ZMod n) = ((a.val : ℤ) + (sL h l) : ℤ) := by rw [hm']
        simp only [sL] at this ⊢
        push_cast at this ⊢
        linear_combination this
    rw [hRp, hRq, htp, htq]
    have hθa := theta_sample n hn g hg k v hv a.val
    have hχ := stdAddChar_eq n k a
    have hsgn := left_sign_collapse g h l hg a.val
    have hd : ((Real.sqrt (d n) : ℂ)) * Real.sqrt (d n) = d n := by rw [← sq]; exact hsq
    rw [← zpow_natCast (-1 : ℂ) (a.val * (g - 1))] at hθa
    simp only [θL, pL, qL, sL] at hθa hχ hsgn ⊢
    push_cast [Nat.cast_sub hg] at hθa hχ hsgn ⊢
    rw [hθa, hχ]
    calc (-1 : ℂ) ^ (a.val : ℤ) * (Complex.exp (-(2 * π * I * k * a.val / n))
          * (-1) ^ ((a.val : ℤ) * ((g : ℤ) - 1)))
        * (((toCoeffData n hn G hodd).B a ((g : ZMod n) + h) + ω₂ n * (if a.val = g + h then 1 else 0))
            * (Real.sqrt (d n) * F n G ((g : ℂ) + h)) * (-1) ^ (((g : ℤ) + h) * ((a.val : ℤ) + 1))
          * ((toCoeffData n hn G hodd).B (a + ((l : ZMod n) - h)) (-(h : ZMod n))
            * (Real.sqrt (d n) * F n G (-(h : ℂ))) * (-1) ^ (-(h : ℤ) * ((a.val : ℤ) + ((l : ℤ) - h) + 1))))
        = ((-1 : ℂ) ^ (a.val : ℤ) * (-1) ^ ((a.val : ℤ) * ((g : ℤ) - 1))
            * (-1) ^ (((g : ℤ) + h) * ((a.val : ℤ) + 1))
            * (-1) ^ (-(h : ℤ) * ((a.val : ℤ) + ((l : ℤ) - h) + 1)))
          * ((Real.sqrt (d n) : ℂ) * Real.sqrt (d n))
          * (Complex.exp (-(2 * π * I * k * a.val / n))
            * (((toCoeffData n hn G hodd).B a ((g : ZMod n) + h) + ω₂ n * (if a.val = g + h then 1 else 0))
              * (toCoeffData n hn G hodd).B (a + ((l : ZMod n) - h)) (-(h : ZMod n)))
            * (F n G ((g : ℂ) + h) * F n G (-(h : ℂ)))) := by ring
      _ = (-1 : ℂ) ^ ((g : ℤ) + h + -(h : ℤ) + -(h : ℤ) * ((l : ℤ) - h)) * (d n : ℂ)
          * (Complex.exp (-(2 * π * I * k * a.val / n))
            * (((toCoeffData n hn G hodd).B a ((g : ZMod n) + h) + ω₂ n * (if a.val = g + h then 1 else 0))
              * (toCoeffData n hn G hodd).B (a + ((l : ZMod n) - h)) (-(h : ZMod n)))
            * (F n G ((g : ℂ) + h) * F n G (-(h : ℂ)))) := by rw [hsgn, hd]
      _ = _ := by ring
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
  congr 1
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro a _; ring
  · rw [Finset.sum_eq_single ((g + h : ℕ) : ZMod n)]
    · rw [val_natCast' n (g + h) (by omega), if_pos rfl, mul_one, stdAddChar_eq n k,
        val_natCast' n (g + h) (by omega)]
      have : ((g + h : ℕ) : ZMod n) + ((sL h l : ℤ) : ZMod n) = ((g + l : ℕ) : ZMod n) := by
        simp only [sL]; push_cast; ring
      rw [this]; push_cast; ring
    · intro a _ ha
      have : a.val ≠ g + h := by
        intro e; apply ha; rw [← ZMod.natCast_zmod_val a, e]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs

omit hn G in
include hg in
lemma left_sign_zero :
    (-1 : ℂ) ^ (qL h) * (-1) ^ ((((g + h) * (g - 1) : ℕ) : ℤ)) * (-1) ^ (pL g h) * (-1) ^ (qL h)
      * (-1) ^ ((qL h) * (((g + l : ℕ) : ℤ) + 1))
      = (-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [pL, qL, sL, Nat.add_sub_cancel]
  push_cast
  generalize (g' : ZMod 2) = y
  generalize (h : ZMod 2) = z
  generalize (l : ZMod 2) = w
  revert y z w; decide

include hn hodd hg hh hgh hl hlh in
/-- Step 6 for the left product: the surviving residue at `z_0 = p` reproduces the sample
correction. -/
theorem left_residue_zero (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (g - 1))) :
    4 * π * ((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n))
        * ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h 0)
      = (-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) * (d n * F n G (pL g h) * F n G (qL h))
        * (ω₂ n * Complex.exp (-(2 * π * I * k * ((g + h : ℕ) : ℂ) / n))
          * (toCoeffData n hn G hodd).B (((g + l : ℕ) : ZMod n)) (-(h : ZMod n))) := by
  have hd0 := sqrt_d_ne_zero n
  have hsq := sqrt_d_sq n
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hFp : F n G ((g : ℂ) + h) ≠ 0 := by
    have := F_int_ne_zero n hn G ((g + h : ℕ) : ℤ); push_cast at this; exact this
  have hFq : F n G (-(h : ℂ)) ≠ 0 := by
    have := F_int_ne_zero n hn G (-(h : ℤ)); push_cast at this; exact this
  have hx0 : ((g + l : ℕ) : ℤ) ≠ 0 := by omega
  have hxq : ((g + l : ℕ) : ℤ) + h ≠ 0 := by omega
  -- the residue at the origin
  have hres0 := G.residue_zero_eq
  -- `γ(ω₁ + x + h) γ(ω₂ - x) = R_{-h}(x + n)` with `x = g + l`
  have hRz : G.γ ((ω₁ n : ℂ) + ((g : ℂ) + l) + h) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l))
      = Rz n G (-(h : ℤ)) (((g : ℂ) + l) + n) := by
    rw [Rz_add_n n G (-(h : ℤ)) ((g : ℂ) + l)
      (by have := ω₁_add_int_not_pole n hn ((g + l : ℕ) : ℤ); push_cast at this; exact this)
      (by have := ω₁_add_int_not_zero n hn ((g + l : ℕ) : ℤ); push_cast at this; exact this)]
    push_cast
    congr 2; ring
  -- `R_{-h}(x + n) = (-1)^{-h} R_{-h}(x)`
  have hshift : Rz n G (-(h : ℤ)) (((g : ℂ) + l) + n)
      = (-1) ^ (-(h : ℤ)) * Rz n G (-(h : ℤ)) ((g : ℂ) + l) := by
    rw [Rz_eq_F, Rz_eq_F]
    have h1 := F_int_add_n n hn G ((g + l : ℕ) : ℤ) hx0
    have h2 := F_int_add_n n hn G (((g + l : ℕ) : ℤ) + h) hxq
    have hF1 := F_int_ne_zero n hn G ((g + l : ℕ) : ℤ)
    have hF2 := F_int_ne_zero n hn G (((g + l : ℕ) : ℤ) + h)
    push_cast at h1 h2 hF1 hF2 ⊢
    rw [show (g : ℂ) + l + n - -(h : ℂ) = (g : ℂ) + l + h + n by ring,
      show (g : ℂ) + l - -(h : ℂ) = (g : ℂ) + l + h by ring, h1, h2]
    have hz1 : (-1 : ℂ) ^ ((g : ℤ) + l + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hz2 : (-1 : ℂ) ^ ((g : ℤ) + l + h + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hsgn : (-1 : ℂ) ^ ((g : ℤ) + l + 1) = (-1) ^ (-(h : ℤ)) * (-1) ^ ((g : ℤ) + l + h + 1) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]; congr 1; ring
    rw [hsgn]
    field_simp
    try ring
  -- `R_{-h}(x) = t_{-h}(x) √d F(-h) (-1)^{-h(x+1)}` and the sample rule
  have hRq : Rz n G (-(h : ℤ)) ((g : ℂ) + l)
      = tz n G (-(h : ℤ)) ((g : ℤ) + l) * (Real.sqrt (d n) * F n G (-(h : ℂ)))
        * (-1) ^ (-(h : ℤ) * (((g : ℤ) + l) + 1)) := by
    unfold tz
    have := neg_one_zpow_sq (-(h : ℤ) * (((g : ℤ) + l) + 1))
    push_cast
    field_simp
    linear_combination (-(Rz n G (-(h : ℤ)) ((g : ℂ) + l))) * this
  have htq : tz n G (-(h : ℤ)) ((g : ℤ) + l)
      = (toCoeffData n hn G hodd).B ((g : ZMod n) + l) (-(h : ZMod n)) := by
    have := tz_neg_nonneg n hn G hodd h hh (by omega) (g + l) (by omega)
    push_cast at this; exact this
  -- `2 sin(πp/ω₁) γ(-p) = (-1)^p F(p)`
  have hsin := two_sin_mul_γ_neg n hn G ((g + h : ℕ) : ℤ) (by omega)
  push_cast at hsin
  -- the frequency
  have hθp := theta_sample n hn g hg k v hv (g + h)
  rw [← zpow_natCast (-1 : ℂ) ((g + h) * (g - 1))] at hθp
  have hsqrt : (Real.sqrt (ω₁ n * ω₂ n) : ℂ) = ω₂ n * Real.sqrt (d n) := by
    rw [sqrt_Ω]; push_cast; ring
  have hsgn := left_sign_zero g h l hg
  -- assemble
  unfold ρJ1
  simp only [zL, pl, pL, qL, sL, θL] at hsgn hθp ⊢
  push_cast [Nat.cast_sub hg] at hsgn hθp ⊢
  rw [show (g : ℂ) + h - 0 * (ω₂ n : ℂ) = (g : ℂ) + h by ring, sub_self, hres0, hsqrt]
  rw [show ((ω₂ n : ℂ) - ((g : ℂ) + h) - ((l : ℂ) - h)) = (ω₂ n : ℂ) - ((g : ℂ) + l) by ring,
    show ((ω₁ n : ℂ) + ((g : ℂ) + h) + ((l : ℂ) - h) - -(h : ℂ)) = (ω₁ n : ℂ) + ((g : ℂ) + l) + h by ring]
  have hsin' : Complex.sin (π * ((g : ℂ) + h) / ω₁ n) * G.γ (-((g : ℂ) + h))
      = (-1) ^ ((g : ℤ) + h) * F n G ((g : ℂ) + h) / 2 := by
    linear_combination hsin / 2
  calc 4 * π * ((-1 : ℂ) ^ (-(h : ℤ)) * Complex.sin (π * ((g : ℂ) + h) / ω₁ n))
        * (Complex.exp (-I * (π * v / n) * ((g : ℂ) + h)) * G.γ (-((g : ℂ) + h))
          * ((ω₂ n : ℂ) * Real.sqrt (d n) / (2 * π)) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l))
          * G.γ ((ω₁ n : ℂ) + ((g : ℂ) + l) + h))
      = 2 * (ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (-(h : ℤ))
          * (Complex.sin (π * ((g : ℂ) + h) / ω₁ n) * G.γ (-((g : ℂ) + h)))
          * Complex.exp (-I * (π * v / n) * ((g : ℂ) + h))
          * (G.γ ((ω₁ n : ℂ) + ((g : ℂ) + l) + h) * G.γ ((ω₂ n : ℂ) - ((g : ℂ) + l))) := by
        field_simp; ring
    _ = 2 * (ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (-(h : ℤ))
          * ((-1) ^ ((g : ℤ) + h) * F n G ((g : ℂ) + h) / 2)
          * (Complex.exp (-(2 * π * I * k * ((g : ℂ) + h) / n)) * (-1) ^ (((g : ℤ) + h) * ((g : ℤ) - 1)))
          * ((-1) ^ (-(h : ℤ)) * ((toCoeffData n hn G hodd).B ((g : ZMod n) + l) (-(h : ZMod n))
              * (Real.sqrt (d n) * F n G (-(h : ℂ))) * (-1) ^ (-(h : ℤ) * (((g : ℤ) + l) + 1)))) := by
        rw [hsin', hθp, hRz, hshift, hRq, htq]
    _ = ((-1 : ℂ) ^ (-(h : ℤ)) * (-1) ^ (((g : ℤ) + h) * ((g : ℤ) - 1)) * (-1) ^ ((g : ℤ) + h)
          * (-1) ^ (-(h : ℤ)) * (-1) ^ (-(h : ℤ) * (((g : ℤ) + l) + 1)))
          * ((Real.sqrt (d n) : ℂ) * Real.sqrt (d n))
          * (F n G ((g : ℂ) + h) * F n G (-(h : ℂ)) * (ω₂ n * Complex.exp (-(2 * π * I * k * ((g : ℂ) + h) / n))
            * (toCoeffData n hn G hodd).B ((g : ZMod n) + l) (-(h : ZMod n)))) := by ring
    _ = _ := by rw [hsgn, ← sq, hsq]; push_cast; ring

/-! ### The left product formula -/

include hn hodd hg hh hgh hl hlh in
/-- Proposition 6.3 (1) together with (8.4): the product transform
`S_{p,q,s}(k) = ∑_a u_p(a) u_q(a+s) e^{-2πika/n}` for the ordered labels equals
`-2√Ω c₀ (a₀ e^{πipy/Ω} K₄(r, s₁, X, y) + b₀ e^{πi(n+p)y/Ω} K₄(r, s₂, X, y))`. -/
theorem left_product (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k + n * (g - 1)))
    (hv1 : -(n : ℤ) ≤ v) (hv2 : v ≤ n) :
    ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
        * (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
        * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n))
      = -2 * Real.sqrt (ω₁ n * ω₂ n)
        * ((-1) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) / (d n * F n G (pL g h) * F n G (qL h)))
        * (((-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n))
            * Complex.exp (π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n))
            * G.K4 (rL g) (s1L n g h) (XL n g l) (yL n v)
          + ((-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n))
            * Complex.exp (π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n))
            * G.K4 (rL g) (s2L n g h) (XL n g l) (yL n v)) := by
  classical
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pL g h)
  have hFq := F_int_ne_zero n hn G (qL h)
  -- the frequency facts
  have hθabs : |θL n v| ≤ π := theta_abs_le n hn v hv1 hv2
  have hθn : Complex.exp (-I * (θL n v) * n) = -((-1) ^ (pL g h + qL h)) := by
    have := theta_period n hn hodd g hg k v hv
    rw [show pL g h + qL h = ((g : ℕ) : ℤ) by simp only [pL, qL]; push_cast; ring, zpow_natCast]
    simp only [θL]; push_cast at this ⊢; exact this
  -- the strip
  obtain ⟨ε, L, hε0, hε1, hP1, hP2, hav⟩ := left_eps_exists n g h l
  obtain ⟨hint0, hint1, hE1⟩ := left_strip n hn G hodd g h l hg hh hgh hl hlh (θL n v) hθabs hθn
    ε L hε0 hε1 hP1 hP2
  obtain ⟨hJ1, hE3⟩ := left_K4_1 n hn G hodd g h l hg hh hgh hl hlh v hv1 hv2 ε L hε0 hε1 hP1 hP2 hav
  obtain ⟨hJ2, hE4⟩ := left_K4_2 n hn G hodd g h l hg hh hgh hl hlh v hv1 hv2 ε L hε0 hε1 hP1 hP2 hav
  have hE2 := left_line n hn G hodd g h l hg hh hgh hl hlh (θL n v) hθn ε L hε0 hε1 hav hint0 hint1
    hJ1 hJ2
  have hE5 := left_residue_sum n hn G hodd g h l hg hh hgh hl hlh k v hv
  have hE6 := left_residue_zero n hn G hodd g h l hg hh hgh hl hlh k v hv
  -- abbreviations
  set S := ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
      * (toCoeffData n hn G hodd).B a ((g + h : ℕ) : ZMod n)
      * (toCoeffData n hn G hodd).B (a + ((sL h l : ℤ) : ZMod n)) (-(h : ZMod n)) with hS
  set Sres := ∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * (θL n v) * ((a.val : ℤ) : ℂ))
      * (Rz n G (pL g h) ((a.val : ℤ) : ℂ) * Rz n G (qL h) (((a.val : ℤ) : ℂ) + (sL h l))) with hSres
  set a₀ : ℂ := (-1) ^ (qL h) * Complex.sin (π * (pL g h) / ω₁ n) with ha₀
  set b₀ : ℂ := (-1) ^ (sL h l) * Complex.sin (π * (qL h) / ω₁ n) with hb₀
  set LJ₁ := lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pL g h) (qL h) (sL h l) z)
    (-ε) with hLJ₁
  set LJ₂ := lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pL g h) (qL h) (sL h l) z)
    (-ε) with hLJ₂
  set Sig1 := ∑ j ∈ Finset.range L, ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h (j + 1)) with hSig1
  set Sig2 := ∑ j ∈ Finset.range L, ρJ2 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h (j + 1)) with hSig2
  set ρ₀ := ρJ1 n G (pL g h) (qL h) (sL h l) (θL n v) (zL n g h 0) with hρ₀
  set E₁ := Complex.exp (-π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n)) with hE₁
  set E₂ := Complex.exp (-π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n)) with hE₂
  set K₁ := G.K4 (rL g) (s1L n g h) (XL n g l) (yL n v) with hK₁
  set K₂ := G.K4 (rL g) (s2L n g h) (XL n g l) (yL n v) with hK₂
  set C := (-1 : ℂ) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) * (d n * F n G (pL g h) * F n G (qL h))
    with hC
  set u := ω₂ n * Complex.exp (-(2 * π * I * k * ((g + h : ℕ) : ℂ) / n))
    * (toCoeffData n hn G hodd).B (((g + l : ℕ) : ZMod n)) (-(h : ZMod n)) with hu
  set Ω := (Real.sqrt (ω₁ n * ω₂ n) : ℂ) with hΩ
  rw [Finset.sum_range_succ'] at hE3
  have hE₁0 : E₁ ≠ 0 := Complex.exp_ne_zero _
  have hE₂0 : E₂ ≠ 0 := Complex.exp_ne_zero _
  have hE3' : LJ₁ + 2 * π * I * (Sig1 + ρ₀) = E₁⁻¹ * (I * Ω * K₁) := by
    rw [eq_inv_mul_iff_mul_eq₀ hE₁0]; exact hE3
  have hE4' : LJ₂ + 2 * π * I * Sig2 = E₂⁻¹ * (I * Ω * K₂) := by
    rw [eq_inv_mul_iff_mul_eq₀ hE₂0]; exact hE4
  -- the sums in `hE1` combine
  have hE1' : lineIntegral (K2' n G (pL g h) (qL h) (sL h l) (θL n v)) (n - ε)
      - lineIntegral (K2' n G (pL g h) (qL h) (sL h l) (θL n v)) (-ε)
      = 2 * π * I * (Sres + 4 * π * (a₀ * Sig1 + b₀ * Sig2)) := by
    rw [hE1]; congr 1; congr 1
    simp only [hSig1, hSig2, ha₀, hb₀, Finset.mul_sum, ← Finset.sum_add_distrib]
    try (apply Finset.sum_congr rfl; intro j _; ring)
  -- Step 7
  have key : 2 * π * I * Sres = -4 * π * I * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂)
      + 8 * π ^ 2 * I * a₀ * ρ₀ := by
    linear_combination -hE1' + hE2 - (4 * π * a₀) * hE3' - (4 * π * b₀) * hE4'
  have hSres : Sres = -2 * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂) + 4 * π * a₀ * ρ₀ := by
    have hI : I ≠ 0 := I_ne_zero
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hI)
    linear_combination key
  rw [hE5] at hSres
  rw [hE6] at hSres
  have hC0 : C ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num))
    (mul_ne_zero (mul_ne_zero hd hFp) hFq)
  have hinvE₁ : Complex.exp (π * I * (pL g h) * yL n v / (ω₁ n * ω₂ n)) = E₁⁻¹ := by
    rw [hE₁, ← Complex.exp_neg]; congr 1; ring
  have hinvE₂ : Complex.exp (π * I * (n + (pL g h)) * yL n v / (ω₁ n * ω₂ n)) = E₂⁻¹ := by
    rw [hE₂, ← Complex.exp_neg]; congr 1; ring
  rw [hinvE₁, hinvE₂]
  have hsq := neg_one_zpow_sq ((pL g h) + (qL h) + (qL h) * (sL h l))
  have hcancel : C * S = -2 * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂) := by
    linear_combination hSres
  rw [show (-1 : ℂ) ^ ((pL g h) + (qL h) + (qL h) * (sL h l)) / (d n * F n G (pL g h) * F n G (qL h))
      = C⁻¹ by
    rw [hC, mul_inv, div_eq_mul_inv]
    congr 1
    exact (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)).symm]
  apply mul_left_cancel₀ hC0
  rw [hcancel]
  field_simp
  try ring

end left

end Concrete
end HaagerupIzumi
