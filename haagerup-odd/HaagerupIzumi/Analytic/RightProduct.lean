module

public import HaagerupIzumi.Analytic.LeftProduct

@[expose] public section

/-!
# The right product transform (Proposition 6.3 (2))

For the labels `p' = -t₁`, `q' = l`, `s' = t` with `t₁ = g + l`, `t₂ = g + h`,
`t = g + h + l`, the product transform is evaluated on the window
`{-t, …, n - t - 1}` with the line `Re z = -t - ε`. The crossed poles form the
two families `-t₁ - jω₂`, `-t₂ - jω₂`, which coincide when `h = l` (double
poles); the residue theorem is applied with generalized residues, whose values
at the crossed families are only needed to exist.
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

section right
variable [NeZero n] (hodd : Odd n) (g h l : ℕ) (hg : 1 ≤ g) (hh : 1 ≤ h) (hgh : g + h < n)
  (hl : 1 ≤ l) (hlh : l ≤ h)

/-- The label `p' = -(g + l)`. -/
abbrev pR : ℤ := -((g + l : ℕ) : ℤ)
/-- The label `q' = l`. -/
abbrev qR : ℤ := (l : ℤ)
/-- The label `s' = g + h + l`. -/
abbrev sR : ℤ := ((g + h + l : ℕ) : ℤ)

omit hn G in
/-- The constants whose lattices the line `Re z = -t - ε` must avoid. -/
noncomputable def rightCs : Finset ℝ :=
  {-(h : ℝ), ω₂ n - ((g + h + l : ℕ) : ℝ), ω₁ n - ((g + h + l : ℕ) : ℝ), -(l : ℝ), ω₂ n, ω₁ n,
    ω₂ n - h, -((g + h + l : ℕ) : ℝ), -ω₁ n - ((g + h + l : ℕ) : ℝ), -ω₂ n - ((g + h + l : ℕ) : ℝ),
    0, -ω₁ n, -ω₂ n, -(((g + l : ℕ) : ℝ) + ((g + h + l : ℕ) : ℝ)),
    (l : ℝ) - ω₂ n - ((g + h + l : ℕ) : ℝ)}

/-- The avoidance property of `ε` for the right product. -/
def AvoidR (ε : ℝ) : Prop :=
  (∀ c ∈ rightCs n g h l, ∀ r s : ℕ, ε ≠ c + (r * ω₁ n + s * ω₂ n)) ∧
  (∀ c ∈ rightCs n g h l, ∀ r s : ℕ, ε ≠ c - (r * ω₁ n + s * ω₂ n))

omit hn G in
/-- Existence of a good `ε` and the two crossed-pole counts `L_h`, `L_l`. -/
lemma right_eps_exists :
    ∃ (ε : ℝ) (Lh Ll : ℕ), 0 < ε ∧ ε < 1 ∧
      (∀ j : ℕ, j ≤ Lh → -ε < (h : ℝ) - j * ω₂ n) ∧
      (∀ j : ℕ, Lh + 1 ≤ j → (h : ℝ) - j * ω₂ n < -ε) ∧
      (∀ j : ℕ, j ≤ Ll → -ε < (l : ℝ) - j * ω₂ n) ∧
      (∀ j : ℕ, Ll + 1 ≤ j → (l : ℝ) - j * ω₂ n < -ε) ∧ AvoidR n g h l ε ∧ (h = l → Lh = Ll) := by
  have hω := ω₂_pos n
  obtain ⟨Lh, hLh⟩ : ∃ L : ℕ, L = ⌊(h : ℝ) / ω₂ n⌋₊ := ⟨_, rfl⟩
  obtain ⟨Ll, hLl⟩ : ∃ L : ℕ, L = ⌊(l : ℝ) / ω₂ n⌋₊ := ⟨_, rfl⟩
  have hLh1 : (Lh : ℝ) * ω₂ n ≤ h := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (h : ℝ) / ω₂ n)
    rw [← hLh] at this; rwa [le_div_iff₀ hω] at this
  have hLh2 : (h : ℝ) < (Lh + 1) * ω₂ n := by
    have := Nat.lt_floor_add_one ((h : ℝ) / ω₂ n)
    rw [← hLh] at this; rwa [div_lt_iff₀ hω] at this
  have hLl1 : (Ll : ℝ) * ω₂ n ≤ l := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (l : ℝ) / ω₂ n)
    rw [← hLl] at this; rwa [le_div_iff₀ hω] at this
  have hLl2 : (l : ℝ) < (Ll + 1) * ω₂ n := by
    have := Nat.lt_floor_add_one ((l : ℝ) / ω₂ n)
    rw [← hLl] at this; rwa [div_lt_iff₀ hω] at this
  have hε₀ : 0 < min 1 (min ((Lh + 1) * ω₂ n - h) ((Ll + 1) * ω₂ n - l)) :=
    lt_min one_pos (lt_min (by linarith) (by linarith))
  obtain ⟨ε, hε0, hε1, hA, hB⟩ := exists_eps n _ hε₀ (rightCs n g h l)
  have hε1' : ε < 1 := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hε2 : ε < (Lh + 1) * ω₂ n - h :=
    lt_of_lt_of_le hε1 ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε < (Ll + 1) * ω₂ n - l :=
    lt_of_lt_of_le hε1 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, Lh, Ll, hε0, hε1', ?_, ?_, ?_, ?_, ⟨hA, hB⟩, fun hhl => by subst hhl; rw [hLh, hLl]⟩
  · intro j hj
    have hj' : (j : ℝ) ≤ Lh := by exact_mod_cast hj
    have : (j : ℝ) * ω₂ n ≤ Lh * ω₂ n := by gcongr
    linarith
  · intro j hj
    have hj' : ((Lh + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    have : ((Lh + 1 : ℕ) : ℝ) * ω₂ n ≤ j * ω₂ n := by gcongr
    push_cast at this; linarith
  · intro j hj
    have hj' : (j : ℝ) ≤ Ll := by exact_mod_cast hj
    have : (j : ℝ) * ω₂ n ≤ Ll * ω₂ n := by gcongr
    linarith
  · intro j hj
    have hj' : ((Ll + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    have : ((Ll + 1 : ℕ) : ℝ) * ω₂ n ≤ j * ω₂ n := by gcongr
    push_cast at this; linarith

/-- The point on the line `Re z = -t - ε`. -/
noncomputable abbrev lineR (ε t : ℝ) : ℂ := ((-((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I

omit hn G in
lemma lineR_eq (ε t : ℝ) :
    lineR g h l ε t = ((-((g + h + l : ℕ) : ℝ) : ℝ) : ℂ) + (((-ε : ℝ) : ℂ) + t * I) := by
  simp only [lineR]; push_cast; ring

include hn in
/-- The regularity conditions of the difference identity hold on the line `Re z = -t - ε`. -/
lemma right_line_cond (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hav : AvoidR n g h l ε) (t : ℝ) :
    K2Cond n (pR g l) (qR l) (sR g h l) (lineR g h l ε t) := by
  obtain ⟨hA, hB⟩ := hav
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  simp only [rightCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  rw [lineR_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := line_not_pole n (-(h : ℝ)) ε t (hA _ (by simp))
    convert this using 1 <;> (try simp only [pR]) <;> (try push_cast) <;> (try ring)
  · have := line_neg_not_pole n (-((g + h + l : ℕ) : ℝ)) ε t (hB _ (by simp))
    convert this using 1 <;> (try push_cast) <;> (try ring)
  · have := line_not_pole n (ω₂ n - ((g + h + l : ℕ) : ℝ)) ε t (hA _ (by simp))
    convert this using 1 <;> (try push_cast) <;> (try ring)
  · have := line_not_zero n (ω₂ n - ((g + h + l : ℕ) : ℝ)) ε t (fun r s => by
      have := hB (-ω₁ n - ((g + h + l : ℕ) : ℝ)) (by simp) r s
      intro heq; apply this; rw [heq]; ring)
    convert this using 1 <;> (try push_cast) <;> (try ring)
  · have := line_not_pole n (ω₁ n - ((g + h + l : ℕ) : ℝ)) ε t (hA _ (by simp))
    convert this using 1 <;> (try push_cast) <;> (try ring)
  · have := line_not_zero n (ω₁ n - ((g + h + l : ℕ) : ℝ)) ε t (fun r s => by
      have := hB (-ω₂ n - ((g + h + l : ℕ) : ℝ)) (by simp) r s
      intro heq; apply this; rw [heq]; ring)
    convert this using 1 <;> (try push_cast) <;> (try ring)
  · have := line_not_pole n (-(l : ℝ)) ε t (hA _ (by simp))
    convert this using 1 <;> (try simp only [qR, sR]) <;> (try push_cast) <;> (try ring)
  · have := line_neg_not_pole n 0 ε t (hB _ (by simp))
    convert this using 1 <;> (try simp only [sR]) <;> (try push_cast) <;> (try ring)
  · have := line_not_pole n (ω₂ n) ε t (hA _ (by simp))
    convert this using 1 <;> (try simp only [sR]) <;> (try push_cast) <;> (try ring)
  · have := line_not_zero n (ω₂ n) ε t (fun r s => by
      have := hB (-ω₁ n) (by simp) r s; intro heq; apply this; rw [heq]; ring)
    convert this using 1 <;> (try simp only [sR]) <;> (try push_cast) <;> (try ring)
  · have := line_not_pole n (ω₁ n) ε t (hA _ (by simp))
    convert this using 1 <;> (try simp only [sR]) <;> (try push_cast) <;> (try ring)
  · have := line_not_zero n (ω₁ n) ε t (fun r s => by
      have := hB (-ω₂ n) (by simp) r s; intro heq; apply this; rw [heq]; ring)
    convert this using 1 <;> (try simp only [sR]) <;> (try push_cast) <;> (try ring)
  · apply sin_pi_ne_zero_of_not_int
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      intCast_re, zero_add] at hre
    have h1' : (-((g + h + l : ℕ) : ℤ) - 1 : ℤ) < m := by
      have : (-((g + h + l : ℕ) : ℝ) - 1 : ℝ) < m := by linarith
      exact_mod_cast this
    have h2' : m < -((g + h + l : ℕ) : ℤ) := by
      have : (m : ℝ) < -((g + h + l : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    omega

/-- The crossed poles of the first family `-t₁ - j ω₂`. -/
noncomputable abbrev zA (j : ℕ) : ℂ := -((g + l : ℕ) : ℂ) - j * ω₂ n
/-- The crossed poles of the second family `-t₂ - j ω₂`. -/
noncomputable abbrev zB (j : ℕ) : ℂ := -((g + h : ℕ) : ℂ) - j * ω₂ n

omit hn G in
lemma zA_injective : Function.Injective (zA n g l) := by
  intro x y hxy
  have hω : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have : (x : ℂ) * ω₂ n = y * ω₂ n := by simp only [zA] at hxy; linear_combination -hxy
  exact_mod_cast mul_right_cancel₀ hω this

omit hn G in
lemma zB_injective : Function.Injective (zB n g h) := by
  intro x y hxy
  have hω : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have : (x : ℂ) * ω₂ n = y * ω₂ n := by simp only [zB] at hxy; linear_combination -hxy
  exact_mod_cast mul_right_cancel₀ hω this

include hn in
/-- No crossed pole is an integer. -/
lemma zA_ne_int (j : ℕ) (m : ℤ) : zA n g l (j + 1) ≠ (m : ℂ) := by
  have := ne_int_of_coeff_ne_zero n hn (-(g + l : ℚ)) (-(j + 1 : ℚ))
    (-((g + l : ℕ) : ℝ) - (j + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
  intro heq
  apply this
  have h2 : (((-((g + l : ℕ) : ℝ) - (j + 1) * ω₂ n) : ℝ) : ℂ) = (m : ℂ) := by
    rw [← heq]; simp only [zA]; push_cast; ring
  exact_mod_cast h2

include hn in
lemma zB_ne_int (j : ℕ) (m : ℤ) : zB n g h (j + 1) ≠ (m : ℂ) := by
  have := ne_int_of_coeff_ne_zero n hn (-(g + h : ℚ)) (-(j + 1 : ℚ))
    (-((g + h : ℕ) : ℝ) - (j + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
  intro heq
  apply this
  have h2 : (((-((g + h : ℕ) : ℝ) - (j + 1) * ω₂ n) : ℝ) : ℂ) = (m : ℂ) := by
    rw [← heq]; simp only [zB]; push_cast; ring
  exact_mod_cast h2

/-- The crossed families `z_A`, `z_B` with `j ≥ 1`, as a finite set. -/
noncomputable def SAB (Lh Ll : ℕ) : Finset ℂ :=
  (Finset.range Lh).image (fun j => zA n g l (j + 1)) ∪ (Finset.range Ll).image (fun j => zB n g h (j + 1))

include hn hg hh hgh hl hlh in
/-- At the crossed families, `e^{-iθz} J₁'` and `e^{-iθz} J₂'` have generalized residues. -/
lemma right_residues_exist (θ : ℝ) (Lh Ll : ℕ) (hLhl : h = l → Lh = Ll) :
    ∃ ρ₁ ρ₂ : ℂ → ℂ,
      (∀ w ∈ SAB n g h l Lh Ll,
        HasResidueGen (fun z => Complex.exp (-I * θ * z) * J1 n G (pR g l) (qR l) (sR g h l) z) w (ρ₁ w)) ∧
      (∀ w ∈ SAB n g h l Lh Ll,
        HasResidueGen (fun z => Complex.exp (-I * θ * z) * J2 n G (pR g l) (qR l) (sR g h l) z) w (ρ₂ w)) ∧
      (∀ w ∈ SAB n g h l Lh Ll, w ∉ (Finset.range Lh).image (fun j => zA n g l (j + 1)) → ρ₁ w = 0) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  -- each crossed point is `-t_i - (j+1) ω₂` for `i = 1, 2`
  have hpts : ∀ w ∈ SAB n g h l Lh Ll, ∃ (c : ℕ) (j : ℕ), (c = g + l ∨ c = g + h) ∧
      w = -((c : ℕ) : ℂ) - (j + 1) * ω₂ n := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨g + l, j, Or.inl rfl, by simp only [zA]; push_cast; ring⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨g + h, j, Or.inr rfl, by simp only [zB]; push_cast; ring⟩
  -- regularity of the regular factors at such a point
  have hreg : ∀ (c j : ℕ), (c = g + l ∨ c = g + h) → ∀ w : ℂ, w = -((c : ℕ) : ℂ) - (j + 1) * ω₂ n →
      -w ∉ poleSet (ω₁ n) (ω₂ n) ∧
      (ω₂ n : ℂ) - w - (sR g h l) ∉ poleSet (ω₁ n) (ω₂ n) ∧
      (ω₁ n : ℂ) + w + (sR g h l) - (qR l) ∉ poleSet (ω₁ n) (ω₂ n) ∧
      (ω₁ n : ℂ) - w ∉ poleSet (ω₁ n) (ω₂ n) ∧
      -w - (sR g h l) ∉ poleSet (ω₁ n) (ω₂ n) := by
    intro c j hc w hw
    have hc1 : 1 ≤ c := by omega
    have hcn : c ≤ n - 1 := by omega
    have hcR : (1 : ℚ) ≤ c := by exact_mod_cast hc1
    have hct : (c : ℚ) ≤ g + h + l := by
      rcases hc with rfl | rfl <;> push_cast <;> linarith [(Nat.cast_nonneg h : (0:ℚ) ≤ h),
        (Nat.cast_nonneg l : (0:ℚ) ≤ l)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := not_pole_of_pos_coeff n hn c (j + 1) ((c : ℝ) + (j + 1 : ℚ) * ω₂ n)
        (by push_cast; ring) (by linarith)
      convert this using 2; rw [hw]; push_cast; ring
    · have := not_pole_of_pos_coeff n hn ((c : ℚ) - (g + h + l)) (j + 2)
        ((c : ℝ) - ((g + h + l : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
      convert this using 2; rw [hw]; simp only [sR]; push_cast; ring
    · have := not_pole_of_pos_const n hn (n - (c : ℚ) + (g + h + l) - l) (-j)
        ((n : ℝ) - c + ((g + h + l : ℕ) : ℝ) - l + (-j : ℚ) * ω₂ n) (by push_cast; ring)
        (by have h1 : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
            have h2 : (l : ℚ) ≤ h := by exact_mod_cast hlh
            have h3 : (c : ℚ) ≤ n - 1 := by
              have : (c : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hcn
              rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
            push_cast at hct ⊢; linarith)
      convert this using 2; rw [hw]; simp only [sR, qR]; push_cast; rw [hωC]; ring
    · have := not_pole_of_pos_const n hn ((n : ℚ) + c) (j + 2) ((n : ℝ) + c + (j + 2 : ℚ) * ω₂ n)
        (by push_cast; ring) (by have : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
                                 push_cast; linarith)
      convert this using 2; rw [hw]; push_cast; rw [hωC]; ring
    · have := not_pole_of_pos_coeff n hn ((c : ℚ) - (g + h + l)) (j + 1)
        ((c : ℝ) - ((g + h + l : ℕ) : ℝ) + (j + 1 : ℚ) * ω₂ n) (by push_cast; ring) (by linarith)
      convert this using 2; rw [hw]; simp only [sR]; push_cast; ring
  -- existence of residues of `e^{-iθz} J₁'`
  have hJ1 : ∀ w ∈ SAB n g h l Lh Ll, ∃ ρ,
      HasResidueGen (fun z => Complex.exp (-I * θ * z) * J1 n G (pR g l) (qR l) (sR g h l) z) w ρ := by
    intro w hw
    obtain ⟨c, j, hc, hwc⟩ := hpts w hw
    obtain ⟨h1, h2, h3, -, -⟩ := hreg c j hc w hwc
    have hfun : (fun z => Complex.exp (-I * θ * z) * J1 n G (pR g l) (qR l) (sR g h l) z)
        = fun z => (Complex.exp (-I * θ * z) * G.γ (-z) * G.γ (ω₂ n - z - (sR g h l))
            * G.γ (ω₁ n + z + (sR g h l) - (qR l))) * G.γ (-(pR g l : ℂ) + z) := by
      funext z; simp only [J1]; rw [show z - (pR g l : ℂ) = -(pR g l : ℂ) + z by ring]; ring
    rw [hfun]
    refine exists_hasResidueGen_mul (Or.inl ?_) (atMostSimple_γ_add n G _ w)
    refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_) ?_
    · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (-I * θ * z)).differentiableAt
    · exact (G.differentiableAt _ h1).comp w (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z) w)
    · exact (G.differentiableAt _ h2).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) - z - (sR g h l)) w)
    · exact (G.differentiableAt _ h3).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₁ n : ℂ) + z + (sR g h l) - (qR l)) w)
  -- existence of residues of `e^{-iθz} J₂'`
  have hJ2 : ∀ w ∈ SAB n g h l Lh Ll, ∃ ρ,
      HasResidueGen (fun z => Complex.exp (-I * θ * z) * J2 n G (pR g l) (qR l) (sR g h l) z) w ρ := by
    intro w hw
    obtain ⟨c, j, hc, hwc⟩ := hpts w hw
    obtain ⟨-, -, -, h4, h5⟩ := hreg c j hc w hwc
    have hfun : (fun z => Complex.exp (-I * θ * z) * J2 n G (pR g l) (qR l) (sR g h l) z)
        = fun z => ((Complex.exp (-I * θ * z) * G.γ (ω₁ n - z) * G.γ (-z - (sR g h l)))
            * G.γ ((ω₂ n : ℂ) - (pR g l) + z)) * G.γ (((sR g h l : ℂ) - (qR l)) + z) := by
      funext z; simp only [J2]
      rw [show (ω₂ n : ℂ) + z - (pR g l) = (ω₂ n : ℂ) - (pR g l) + z by ring,
        show z + (sR g h l : ℂ) - (qR l) = ((sR g h l : ℂ) - (qR l)) + z by ring]; ring
    rw [hfun]
    refine exists_hasResidueGen_mul ?_ (atMostSimple_γ_add n G _ w)
    refine AtMostSimple.differentiableAt_mul ?_ ?_ (atMostSimple_γ_add n G _ w)
    · refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
      · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (-I * θ * z)).differentiableAt
      · exact differentiableAt_γ_sub n G _ w h4
      · exact (G.differentiableAt _ h5).comp w
          (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z - (sR g h l)) w)
    · have e1 := eventually_differentiableAt_γ_sub n G (ω₁ n : ℂ) w
      have e2 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => -z - (sR g h l))
        (fun x y hxy => by simpa using hxy) w).eventually
        (eventually_not_mem_poleSet hω₁ hω₂ (-w - (sR g h l)))
      filter_upwards [e1, e2] with z hz1 hz2
      refine DifferentiableAt.mul (DifferentiableAt.mul ?_ hz1) ?_
      · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (-I * θ * z)).differentiableAt
      · exact (G.differentiableAt _ hz2).comp z
          (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z - (sR g h l)) z)
  choose! ρ₁₀ hρ₁₀ using hJ1
  choose! ρ₂ hρ₂ using hJ2
  -- off the first family `e^{-iθz} J₁'` is regular, and the residue is taken to be `0`
  set SA' : Finset ℂ := (Finset.range Lh).image (fun j => zA n g l (j + 1)) with hSA'
  refine ⟨fun w => if w ∈ SA' then ρ₁₀ w else 0, ρ₂, ?_, hρ₂, ?_⟩
  · intro w hw
    by_cases hwA : w ∈ SA'
    · simp only [if_pos hwA]; exact hρ₁₀ w hw
    · simp only [if_neg hwA]
      -- `w` is in the second family and `h ≠ l`
      have hwB : w ∈ (Finset.range Ll).image (fun j => zB n g h (j + 1)) := by
        rcases Finset.mem_union.1 hw with hw' | hw'
        · exact absurd hw' hwA
        · exact hw'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hwB
      have hne : h ≠ l := by
        intro heq
        apply hwA
        have hL := hLhl heq
        subst heq
        rw [hSA', hL]
        exact Finset.mem_image.2 ⟨j, hj, rfl⟩
      have hlt : l < h := lt_of_le_of_ne hlh (Ne.symm hne)
      -- `e^{-iθz} J₁'` is regular at `-t₂ - (j+1) ω₂`
      obtain ⟨h1, h2, h3, -, -⟩ := hreg (g + h) j (Or.inr rfl) (zB n g h (j + 1))
        (by simp only [zB]; push_cast; ring)
      have h4 : zB n g h (j + 1) - (pR g l) ∉ poleSet (ω₁ n) (ω₂ n) := by
        have := not_pole_of_const_mem_Ioo n hn ((l : ℚ) - h) (-(j + 1 : ℚ))
          ((l : ℝ) - h - (j + 1) * ω₂ n) (by push_cast; ring)
          (by have : (h : ℚ) < n := by exact_mod_cast (by omega : h < n)
              have : (0 : ℚ) ≤ l := Nat.cast_nonneg l
              linarith)
          (by have hlt' : (l : ℚ) < h := by exact_mod_cast hlt
              linarith)
        convert this using 2; simp only [zB, pR]; push_cast; ring
      apply HasResidue.hasResidueGen
      apply HasResidue.of_continuousAt
      refine ContinuousAt.mul ?_ ?_
      · exact (Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z)).continuousAt
      · unfold J1
        refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_
        · exact ContinuousAt.comp (f := fun z : ℂ => -z) (G.continuousAt _ h1) (by fun_prop)
        · exact ContinuousAt.comp (f := fun z : ℂ => z - (pR g l : ℂ)) (G.continuousAt _ h4)
            (by fun_prop)
        · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) - z - (sR g h l)) (G.continuousAt _ h2)
            (by fun_prop)
        · exact ContinuousAt.comp (f := fun z : ℂ => (ω₁ n : ℂ) + z + (sR g h l) - (qR l))
            (G.continuousAt _ h3) (by fun_prop)
  · intro w hw hwA
    simp only [if_neg hwA]

/-- The window integer `a.val - t` as a complex number. -/
noncomputable abbrev wR (a : ZMod n) : ℂ := (((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) : ℂ)

include hn hodd hg hh hgh hl hlh in
/-- Step 3 of the proof of Proposition 6.3 (2): the residue rectangle on the shifted strip. -/
theorem right_strip (θ : ℝ) (hθ : |θ| < π * (1 - g / (ω₁ n * ω₂ n)))
    (hθn : Complex.exp (-I * θ * n) = -((-1) ^ (pR g l + qR l)))
    (ε : ℝ) (Lh Ll : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hA1 : ∀ j : ℕ, j ≤ Lh → -ε < (h : ℝ) - j * ω₂ n)
    (hA2 : ∀ j : ℕ, Lh + 1 ≤ j → (h : ℝ) - j * ω₂ n < -ε)
    (hB1 : ∀ j : ℕ, j ≤ Ll → -ε < (l : ℝ) - j * ω₂ n)
    (hB2 : ∀ j : ℕ, Ll + 1 ≤ j → (l : ℝ) - j * ω₂ n < -ε)
    (ρ₁ ρ₂ : ℂ → ℂ)
    (hρ₁ : ∀ w ∈ SAB n g h l Lh Ll,
      HasResidueGen (fun z => Complex.exp (-I * θ * z) * J1 n G (pR g l) (qR l) (sR g h l) z) w (ρ₁ w))
    (hρ₂ : ∀ w ∈ SAB n g h l Lh Ll,
      HasResidueGen (fun z => Complex.exp (-I * θ * z) * J2 n G (pR g l) (qR l) (sR g h l) z) w (ρ₂ w)) :
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pR g l) (qR l) (sR g h l) θ
      (((-((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I)) ∧
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pR g l) (qR l) (sR g h l) θ
      (((n - ((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I)) ∧
    lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) θ) (n - ((g + h + l : ℕ) : ℝ) - ε)
      - lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) θ) (-((g + h + l : ℕ) : ℝ) - ε)
      = 2 * π * I * (∑ a : ZMod n, (-1) ^ ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))
            * Complex.exp (-I * θ * wR n g h l a)
            * (Rz n G (pR g l) (wR n g h l a) * Rz n G (qR l) (wR n g h l a + (sR g h l)))
          + ∑ w ∈ SAB n g h l Lh Ll, 4 * π * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n) * ρ₁ w
            + (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n) * ρ₂ w)) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  set t : ℝ := ((g + h + l : ℕ) : ℝ) with ht
  push_cast at ht
  -- the finite sets of poles
  set Sint : Finset ℂ := Finset.univ.image (fun a : ZMod n => wR n g h l a) with hSint
  have hval_inj : Function.Injective (fun a : ZMod n => wR n g h l a) := by
    intro a b hab
    simp only [wR] at hab
    have : ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) = ((b.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) :=
      Int.cast_injective hab
    exact ZMod.val_injective n (by omega)
  have hnotint : ∀ w ∈ SAB n g h l Lh Ll, w ∉ Sint := by
    intro w hw hmem
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hmem
    rcases Finset.mem_union.1 hw with hw | hw
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hw
      exact zA_ne_int n hn g l j _ hj
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hw
      exact zB_ne_int n hn g h j _ hj
  have hdisj : Disjoint Sint (SAB n g h l Lh Ll) := by
    rw [Finset.disjoint_right]
    exact hnotint
  -- the residue function
  set ρK : ℂ → ℂ := fun w => if w ∈ Sint then Complex.cos (π * w) * Complex.exp (-I * θ * w)
    * (Rz n G (pR g l) w * Rz n G (qR l) (w + (sR g h l)))
    else 4 * π * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n) * ρ₁ w
      + (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n) * ρ₂ w) with hρK
  -- residues
  have hres : ∀ q ∈ Sint ∪ SAB n g h l Lh Ll, HasResidueGen (K2' n G (pR g l) (qR l) (sR g h l) θ) q (ρK q) := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      have : ρK (wR n g h l a) = (-1) ^ ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))
          * Complex.exp (-I * θ * wR n g h l a)
          * (Rz n G (pR g l) (wR n g h l a) * Rz n G (qR l) (wR n g h l a + (sR g h l))) := by
        simp only [hρK, if_pos hq]
        rw [show (π : ℂ) * wR n g h l a = ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) * π by
          simp only [wR]; ring, cos_int_mul_pi']
      rw [this]
      exact (K2'_residue_int n hn G (pR g l) (qR l) (sR g h l) θ _).hasResidueGen
    · have hnot : q ∉ Sint := hnotint q hq
      have : ρK q = 4 * π * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n) * ρ₁ q
          + (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n) * ρ₂ q) := by
        simp only [hρK, if_neg hnot]
      rw [this]
      apply K2'_residue_of_shift n G _ _ _ θ _ _ _
        (K2'_shift_eventually n G hodd _ _ _ θ hθn _) _ (hρ₁ q hq) (hρ₂ q hq)
      -- continuity of the shifted kernel at the crossed point
      rcases Finset.mem_union.1 hq with hq | hq
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
        apply K2'_shift_continuousAt
        · have := not_pole_of_pos_const n hn n (-j) ((n : ℝ) + (-j : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n by omega))
          convert this using 2; simp only [zA, pR]; push_cast; ring
        · have := not_pole_of_pos_const n hn (g + l) (j + 2) (((g + l : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n)
            (by push_cast; ring) (by exact_mod_cast (show 0 < g + l by omega))
          convert this using 2; simp only [zA]; push_cast; rw [hωC]; ring
        · have := not_pole_of_pos_const n hn (n + h - l) (-j) ((n : ℝ) + h - l + (-j : ℚ) * ω₂ n)
            (by push_cast; ring)
            (by have : (l : ℚ) ≤ h := by exact_mod_cast hlh
                have : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
                linarith)
          convert this using 2; simp only [zA, sR, qR]; push_cast; ring
        · have := not_pole_of_pos_coeff n hn (-h) (j + 2) (-(h : ℝ) + (j + 2 : ℚ) * ω₂ n)
            (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zA, sR]; push_cast; rw [hωC]; ring
        · apply sin_pi_ne_zero_of_not_int
          intro m hm
          have := ne_int_of_coeff_ne_zero n hn ((n : ℚ) - (g + l)) (-(j + 1 : ℚ))
            ((n : ℝ) - ((g + l : ℕ) : ℝ) - (j + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
          apply this
          have h2 : ((((n : ℝ) - ((g + l : ℕ) : ℝ) - (j + 1) * ω₂ n) : ℝ) : ℂ) = ((m : ℤ) : ℂ) := by
            rw [← hm]; simp only [zA]; push_cast; ring
          exact_mod_cast h2
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
        apply K2'_shift_continuousAt
        · have := not_pole_of_pos_const n hn (n + l - h) (-j) ((n : ℝ) + l - h + (-j : ℚ) * ω₂ n)
            (by push_cast; ring)
            (by have : (h : ℚ) ≤ n - 1 := by
                  have : ((g + h : ℕ) : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
                  rw [Nat.cast_sub (by omega)] at this; push_cast at this
                  linarith [(Nat.cast_nonneg g : (0:ℚ) ≤ g)]
                have : (1 : ℚ) ≤ l := by exact_mod_cast hl
                linarith)
          convert this using 2; simp only [zB, pR]; push_cast; ring
        · have := not_pole_of_pos_const n hn (g + h) (j + 2) (((g + h : ℕ) : ℝ) + (j + 2 : ℚ) * ω₂ n)
            (by push_cast; ring) (by exact_mod_cast (show 0 < g + h by omega))
          convert this using 2; simp only [zB]; push_cast; rw [hωC]; ring
        · have := not_pole_of_pos_const n hn n (-j) ((n : ℝ) + (-j : ℚ) * ω₂ n) (by push_cast; ring)
            (by exact_mod_cast (show 0 < n by omega))
          convert this using 2; simp only [zB, sR, qR]; push_cast; ring
        · have := not_pole_of_pos_coeff n hn (-l) (j + 2) (-(l : ℝ) + (j + 2 : ℚ) * ω₂ n)
            (by push_cast; ring) (by linarith)
          convert this using 2; simp only [zB, sR]; push_cast; rw [hωC]; ring
        · apply sin_pi_ne_zero_of_not_int
          intro m hm
          have := ne_int_of_coeff_ne_zero n hn ((n : ℚ) - (g + h)) (-(j + 1 : ℚ))
            ((n : ℝ) - ((g + h : ℕ) : ℝ) - (j + 1) * ω₂ n) (by push_cast; ring) (by push_cast; linarith) m
          apply this
          have h2 : ((((n : ℝ) - ((g + h : ℕ) : ℝ) - (j + 1) * ω₂ n) : ℝ) : ℂ) = ((m : ℤ) : ℂ) := by
            rw [← hm]; simp only [zB]; push_cast; ring
          exact_mod_cast h2
  -- the poles are interior
  obtain ⟨M, T, hT, hM⟩ := K2'_bound n G (pR g l) (qR l) (sR g h l) θ (-t - ε) (n - t - ε)
  have hSpos : ∀ q ∈ Sint ∪ SAB n g h l Lh Ll, -t - ε < q.re ∧ q.re < n - t - ε ∧ |q.im| < T := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      have h1 : (a.val : ℝ) ≤ n - 1 := by
        have : (a.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show a.val ≤ n - 1 by
          have := ZMod.val_lt a; omega)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
      have h2 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
      simp only [wR, intCast_re, intCast_im, abs_zero]
      push_cast
      exact ⟨by linarith, by linarith, hT⟩
    · rcases Finset.mem_union.1 hq with hq | hq
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
        have hjL : j + 1 ≤ Lh := by have := Finset.mem_range.1 hj; omega
        have := hA1 (j + 1) hjL
        have hre : (zA n g l (j + 1)).re = -((g + l : ℕ) : ℝ) - (j + 1) * ω₂ n := by simp [zA]
        have him : (zA n g l (j + 1)).im = 0 := by simp [zA]
        rw [hre, him, abs_zero]
        push_cast at this ⊢
        have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        refine ⟨by linarith, ?_, hT⟩
        nlinarith
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
        have hjL : j + 1 ≤ Ll := by have := Finset.mem_range.1 hj; omega
        have := hB1 (j + 1) hjL
        have hre : (zB n g h (j + 1)).re = -((g + h : ℕ) : ℝ) - (j + 1) * ω₂ n := by simp [zB]
        have him : (zB n g h (j + 1)).im = 0 := by simp [zB]
        rw [hre, him, abs_zero]
        push_cast at this ⊢
        have h3 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        refine ⟨by linarith, ?_, hT⟩
        nlinarith
  -- differentiability off the poles
  have hd : ∀ ζ : ℂ, -t - ε ≤ ζ.re → ζ.re ≤ n - t - ε → ζ ∉ Sint ∪ SAB n g h l Lh Ll →
      DifferentiableAt ℂ (K2' n G (pR g l) (qR l) (sR g h l) θ) ζ := by
    intro ζ hζ1 hζ2 hζS
    have hζint : ζ ∉ Sint := fun hmem => hζS (Finset.mem_union.2 (Or.inl hmem))
    have hζAB : ζ ∉ SAB n g h l Lh Ll := fun hmem => hζS (Finset.mem_union.2 (Or.inr hmem))
    apply K2'_differentiableAt
    · rintro ⟨r, s', hrs⟩
      have hζ : ζ = -((g : ℂ) + l) - r * ω₁ n - (s' + 1) * ω₂ n := by
        simp only [pR] at hrs; push_cast at hrs ⊢; linear_combination hrs
      have hre : ζ.re = -((g : ℝ) + l) - r * ω₁ n - (s' + 1) * ω₂ n := by rw [hζ]; simp
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rcases le_or_gt (s' + 1) Lh with hs | hs
        · apply hζAB
          refine Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨s', Finset.mem_range.2 (by omega), ?_⟩))
          rw [hζ]; simp only [zA]; push_cast; ring
        · have := hA2 (s' + 1) (by omega)
          simp only [Nat.cast_zero, zero_mul, sub_zero] at hre
          push_cast at this hre ht
          linarith
      · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
        have h5 : ω₁ n ≤ r * ω₁ n := by nlinarith
        have h6 : (0 : ℝ) ≤ s' * ω₂ n := by positivity
        push_cast at hre ht
        linarith
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · rintro ⟨r, s', hrs⟩
      have hζ : ζ = -((g : ℂ) + h) - r * ω₁ n - (s' + 1) * ω₂ n := by
        simp only [sR, qR] at hrs; push_cast at hrs ⊢; linear_combination hrs
      have hre : ζ.re = -((g : ℝ) + h) - r * ω₁ n - (s' + 1) * ω₂ n := by rw [hζ]; simp
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rcases le_or_gt (s' + 1) Ll with hs | hs
        · apply hζAB
          refine Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨s', Finset.mem_range.2 (by omega), ?_⟩))
          rw [hζ]; simp only [zB]; push_cast; ring
        · have := hB2 (s' + 1) (by omega)
          simp only [Nat.cast_zero, zero_mul, sub_zero] at hre
          push_cast at this hre ht
          linarith
      · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
        have h5 : ω₁ n ≤ r * ω₁ n := by nlinarith
        have h6 : (0 : ℝ) ≤ s' * ω₂ n := by positivity
        push_cast at hre ht
        linarith
    · refine HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ ?_
      simp only [sR, sub_re, add_re, ofReal_re, intCast_re, natCast_re]
      push_cast at ht ⊢; linarith
    · apply sin_pi_ne_zero_of_not_int
      intro m hm
      apply hζint
      have hre : ζ.re = m := by rw [hm]; simp
      have h1 : -((g + h + l : ℕ) : ℤ) ≤ m := by
        have : (-t - 1 : ℝ) < m := by linarith
        rw [ht] at this
        have : (-((g + h + l : ℕ) : ℤ) - 1 : ℤ) < m := by exact_mod_cast this
        omega
      have h2 : m ≤ (n : ℤ) - ((g + h + l : ℕ) : ℤ) - 1 := by
        have : (m : ℝ) < n - t := by linarith
        rw [ht] at this
        have : m < (n : ℤ) - ((g + h + l : ℕ) : ℤ) := by exact_mod_cast this
        omega
      refine Finset.mem_image.2 ⟨(((m + ((g + h + l : ℕ) : ℤ)).toNat : ℕ) : ZMod n), Finset.mem_univ _, ?_⟩
      simp only [wR]
      rw [val_natCast' n _ (by omega), hm]
      have : (((m + ((g + h + l : ℕ) : ℤ)).toNat : ℕ) : ℤ) = m + ((g + h + l : ℕ) : ℤ) :=
        Int.toNat_of_nonneg (by omega)
      rw [this]; push_cast; ring
  -- decay rate
  have hc0 : 0 < π - |θ| + π * ((pR g l) + (qR l)) / (ω₁ n * ω₂ n) := by
    have e : ((pR g l : ℤ) : ℝ) + ((qR l : ℤ) : ℝ) = -g := by push_cast [pR, qR]; ring
    rw [e]
    have hΩ0 : 0 < ω₁ n * ω₂ n := by positivity
    have : π * (1 - g / (ω₁ n * ω₂ n)) = π - π * g / (ω₁ n * ω₂ n) := by field_simp
    rw [this] at hθ
    have : π * (-(g : ℝ)) / (ω₁ n * ω₂ n) = -(π * g / (ω₁ n * ω₂ n)) := by ring
    rw [this]
    linarith
  obtain ⟨hint0, hint1, hEq⟩ := strip_residues_gen (K2' n G (pR g l) (qR l) (sR g h l) θ) (-t - ε)
    (n - t - ε) (by linarith) (Sint ∪ SAB n g h l Lh Ll) T hT hSpos ρK hres hd M _ hc0 (by
      intro z hza hzb hzT
      have := hM z hza hzb hzT
      push_cast at this ⊢
      exact this)
  refine ⟨hint0, hint1, ?_⟩
  rw [hEq]
  congr 1
  rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ hxy => hval_inj hxy)]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    have hmem : wR n g h l a ∈ Sint := Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    simp only [hρK, if_pos hmem]
    rw [show (π : ℂ) * wR n g h l a = ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) * π by
      simp only [wR]; ring, cos_int_mul_pi']
  · apply Finset.sum_congr rfl
    intro w hw
    simp only [hρK, if_neg (hnotint w hw)]

include hn hodd hg hh hgh hl hlh in
/-- The line identity for the right product. -/
theorem right_line (θ : ℝ)
    (hθn : Complex.exp (-I * θ * n) = -((-1) ^ (pR g l + qR l)))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hav : AvoidR n g h l ε)
    (hint0 : MeasureTheory.Integrable (fun t : ℝ => K2' n G (pR g l) (qR l) (sR g h l) θ
      (((-((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I)))
    (hint1 : MeasureTheory.Integrable (fun t : ℝ => K2' n G (pR g l) (qR l) (sR g h l) θ
      (((n - ((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I)))
    (hJ1 : MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * θ * lineR g h l ε t)
      * J1 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t)))
    (hJ2 : MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * θ * lineR g h l ε t)
      * J2 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t))) :
    lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) θ) (n - ((g + h + l : ℕ) : ℝ) - ε)
      - lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) θ) (-((g + h + l : ℕ) : ℝ) - ε)
      = -4 * π * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n)
          * lineIntegral (fun z => Complex.exp (-I * θ * z) * J1 n G (pR g l) (qR l) (sR g h l) z)
            (-((g + h + l : ℕ) : ℝ) - ε)
        + (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n)
          * lineIntegral (fun z => Complex.exp (-I * θ * z) * J2 n G (pR g l) (qR l) (sR g h l) z)
            (-((g + h + l : ℕ) : ℝ) - ε)) := by
  have hline : ∀ t : ℝ, K2' n G (pR g l) (qR l) (sR g h l) θ
      (((n - ((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I)
      - K2' n G (pR g l) (qR l) (sR g h l) θ (lineR g h l ε t)
      = -4 * π * Complex.exp (-I * θ * lineR g h l ε t)
        * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n)
            * J1 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t)
          + (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n)
            * J2 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t)) := by
    intro t
    have := K2'_shift n G hodd (pR g l) (qR l) (sR g h l) θ hθn _
      (right_line_cond n hn g h l ε hε0 hε1 hav t)
    rw [show ((n - ((g + h + l : ℕ) : ℝ) - ε : ℝ) : ℂ) + t * I = lineR g h l ε t + n by
      simp only [lineR]; push_cast; ring]
    exact this
  unfold lineIntegral
  simp only [lineR] at hline hJ1 hJ2 ⊢
  rw [← MeasureTheory.integral_sub (hint1.mul_const I) (hint0.mul_const I),
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add ((hJ1.mul_const I).const_mul _) ((hJ2.mul_const I).const_mul _),
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext t
  rw [← sub_mul, hline t]; ring

/-! ### The centered kernels of (8.10) -/

/-- `R = g/2`. -/
noncomputable abbrev RR : ℂ := (g : ℂ) / 2
/-- `Y = (n + g)/2 + h`. -/
noncomputable abbrev YR : ℂ := ((n : ℂ) + g) / 2 + h

include hn in
/-- The integrand of `K₄(R, X - ω₁, Y, Z)` at `z` is `e^{πiZt₁/Ω} e^{-iθw} J₁'(w)`, `w = z - t₁/2`. -/
lemma k4_J1R_eq (v : ℤ) (z : ℂ) :
    k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) z
      = Complex.exp (π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n))
        * (Complex.exp (-I * (θL n v) * (z - ((g + l : ℕ) : ℂ) / 2))
          * J1 n G (pR g l) (qR l) (sR g h l) (z - ((g + l : ℕ) : ℂ) / 2)) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hexp : Complex.exp (2 * π * I * yL n v * z / (ω₁ n * ω₂ n))
      = Complex.exp (π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n))
        * Complex.exp (-I * (θL n v) * (z - ((g + l : ℕ) : ℂ) / 2)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [yL, θL]; push_cast
    rw [hΩC]
    have hΩ0 : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
      have : (0 : ℝ) < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
      exact_mod_cast this.ne'
    field_simp
    ring
  unfold k4Integrand k4U k4V J1
  rw [hexp]
  have e1 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g + (XL n g l - ω₁ n)) / 2 + z
      = z - ((g + l : ℕ) : ℂ) / 2 - (pR g l) := by
    simp only [RR, XL, pR]; push_cast; rw [hωC]; ring
  have e2 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g + (XL n g l - ω₁ n)) / 2 - z
      = -(z - ((g + l : ℕ) : ℂ) / 2) := by
    simp only [RR, XL]; push_cast; rw [hωC]; ring
  have e3 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g - (XL n g l - ω₁ n)) / 2 + z + YR n g h
      = ω₁ n + (z - ((g + l : ℕ) : ℂ) / 2) + (sR g h l) - (qR l) := by
    simp only [RR, XL, YR, sR, qR]; push_cast; rw [hωC]; ring
  have e4 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g - (XL n g l - ω₁ n)) / 2 - z - YR n g h
      = ω₂ n - (z - ((g + l : ℕ) : ℂ) / 2) - (sR g h l) := by
    simp only [RR, XL, YR, sR]; push_cast; rw [hωC]; ring
  rw [e1, e2, e3, e4]; ring

include hn in
/-- The integrand of `K₄(R, X + ω₂, Y, Z)` at `z` is `e^{πiZ(t₁-n)/Ω} e^{-iθw} J₂'(w)`,
`w = z - (t₁ - n)/2`. -/
lemma k4_J2R_eq (v : ℤ) (z : ℂ) :
    k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) z
      = Complex.exp (π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n))
        * (Complex.exp (-I * (θL n v) * (z - (((g + l : ℕ) : ℂ) - n) / 2))
          * J2 n G (pR g l) (qR l) (sR g h l) (z - (((g + l : ℕ) : ℂ) - n) / 2)) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hexp : Complex.exp (2 * π * I * yL n v * z / (ω₁ n * ω₂ n))
      = Complex.exp (π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n))
        * Complex.exp (-I * (θL n v) * (z - (((g + l : ℕ) : ℂ) - n) / 2)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [yL, θL]; push_cast
    rw [hΩC]
    have hΩ0 : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by
      have : (0 : ℝ) < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
      exact_mod_cast this.ne'
    field_simp
    ring
  unfold k4Integrand k4U k4V J2
  rw [hexp]
  have e1 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g + (XL n g l + ω₂ n)) / 2 + z
      = ω₂ n + (z - (((g + l : ℕ) : ℂ) - n) / 2) - (pR g l) := by
    simp only [RR, XL, pR]; push_cast; rw [hωC]; ring
  have e2 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g + (XL n g l + ω₂ n)) / 2 - z
      = ω₁ n - (z - (((g + l : ℕ) : ℂ) - n) / 2) := by
    simp only [RR, XL]; push_cast; rw [hωC]; ring
  have e3 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g - (XL n g l + ω₂ n)) / 2 + z + YR n g h
      = (z - (((g + l : ℕ) : ℂ) - n) / 2) + (sR g h l) - (qR l) := by
    simp only [RR, XL, YR, sR, qR]; push_cast; rw [hωC]; ring
  have e4 : ((ω₁ n + ω₂ n : ℝ) : ℂ) / 4 + (RR g - (XL n g l + ω₂ n)) / 2 - z - YR n g h
      = -(z - (((g + l : ℕ) : ℂ) - n) / 2) - (sR g h l) := by
    simp only [RR, XL, YR, sR]; push_cast; rw [hωC]; ring
  rw [e1, e2, e3, e4]; ring

/-! ### Step 6 for the right product: the crossed poles and the centered kernels -/

include hn hodd hg hh hgh hl hlh in
/-- The first four-gamma integral of the right product, with the crossed poles `-t₁ - jω₂`
(`0 ≤ j ≤ L_h`) added back, is the centered kernel `K₄(R, X - ω₁, Y, Z)` up to the phase of (8.10). -/
theorem right_K4_1 (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g))
    (ε : ℝ) (Lh Ll : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hA1 : ∀ j : ℕ, j ≤ Lh → -ε < (h : ℝ) - j * ω₂ n)
    (hA2 : ∀ j : ℕ, Lh + 1 ≤ j → (h : ℝ) - j * ω₂ n < -ε) (hav : AvoidR n g h l ε)
    (ρ₁ : ℂ → ℂ)
    (hρ₁ : ∀ w ∈ SAB n g h l Lh Ll,
      HasResidueGen (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pR g l) (qR l) (sR g h l) z) w (ρ₁ w))
    (hρ₁0 : ∀ w ∈ SAB n g h l Lh Ll, w ∉ (Finset.range Lh).image (fun j => zA n g l (j + 1)) → ρ₁ w = 0) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * (θL n v) * lineR g h l ε t)
      * J1 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t)) ∧
    Complex.exp (π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n))
      * (lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pR g l) (qR l) (sR g h l) z)
          (-((g + h + l : ℕ) : ℝ) - ε)
        + 2 * π * I * (ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0)
          + ∑ w ∈ SAB n g h l Lh Ll, ρ₁ w))
      = I * Real.sqrt (ω₁ n * ω₂ n) * G.K4 (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) := by
  classical
  obtain ⟨hA, hB⟩ := hav
  simp only [rightCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  -- the parameters
  have hU : k4U (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) = ((g + l : ℕ) : ℂ) / 2 := by
    unfold k4U; simp only [RR, XL]; push_cast; rw [hωC]; ring
  have hV : k4V (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n)
      = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 - (l : ℂ) / 2 := by
    unfold k4V; simp only [RR, XL]; push_cast; rw [hωC]; ring
  set Φ : ℂ → ℂ := fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pR g l) (qR l) (sR g h l) z
    with hΦ
  set E : ℂ := Complex.exp (π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n)) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  set c : ℝ := ((g : ℝ) + l) / 2 with hc
  set t : ℝ := ((g + h + l : ℕ) : ℝ) with ht
  push_cast at ht
  have hk4 : ∀ z, k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) z
      = E * Φ (z - (c : ℂ)) := by
    intro z
    rw [k4_J1R_eq n hn G g h l v z, hΦ, hE]
    simp only [c]
    congr 2 <;> (congr 1; push_cast; ring)
  -- the crossed poles in the coordinates of the kernel
  set SL : Finset ℂ := (insert (zA n g l 0) ((Finset.range Lh).image (fun j => zA n g l (j + 1)))).image
    (fun w => w + (c : ℂ)) with hSL
  have hshift_inj : Function.Injective (fun w : ℂ => w + (c : ℂ)) := add_left_injective _
  have hnot0 : zA n g l 0 ∉ (Finset.range Lh).image (fun j => zA n g l (j + 1)) := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    have := zA_injective n g l hj
    omega
  -- the residue function on `SL`
  set ρ₁' : ℂ → ℂ := fun w => if w = zA n g l 0
    then ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0) else ρ₁ w with hρ₁'
  set ρL : ℂ → ℂ := fun w => E * ρ₁' (w - (c : ℂ)) with hρL
  -- the residue at `-t₁`
  have hres0 : HasResidue Φ (zA n g l 0) (ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0)) := by
    apply J1_residue
    · exact ⟨0, 0, by simp only [zA, pR]; push_cast; ring⟩
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [zA]; push_cast; linarith)
    · have := not_pole_of_pos_coeff n hn (-h) 1 (-(h : ℝ) + (1 : ℚ) * ω₂ n) (by push_cast; ring) one_pos
      convert this using 2; simp only [zA, sR]; push_cast; ring
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
        simp only [zA, sR, qR, add_re, sub_re, ofReal_re, natCast_re, intCast_re, neg_re, mul_re,
          natCast_im, ofReal_im, mul_zero, sub_zero, Nat.cast_zero, zero_mul]
        push_cast; linarith)
  -- apply the line characterization of `K₄`
  obtain ⟨hint, heq⟩ := G.K4_line (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) (-t - ε + c) SL ∅ ρL 0
    (by
      unfold K4Conv
      simp only [yL, RR, ofReal_re, div_ofNat_re, natCast_re]
      push_cast
      have hvn : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g) := hvres
      have : |-(ω₁ n + ω₂ n) * v / (2 * n)| < (ω₁ n + ω₂ n) / 2 - g / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < ω₁ n + ω₂ n),
          abs_of_pos (by linarith : (0 : ℝ) < 2 * n), div_lt_iff₀ (by linarith)]
        nlinarith
      (try simp only [neg_re, natCast_re, natCast_im, mul_zero, sub_zero, div_ofNat_re] at *)
      linarith)
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hU]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im, mul_zero, sub_zero,
            div_ofNat_re, zero_mul]
          push_cast; linarith)
      · rw [hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [sub_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, natCast_re,
            natCast_im, mul_zero, sub_zero, div_ofNat_re, zero_mul]
          push_cast; linarith)
      · rw [hU, hV]
        have := not_pole_of_pos_coeff n hn (-h) 1 (-(h : ℝ) + (1 : ℚ) * ω₂ n) (by push_cast; ring) one_pos
        convert this using 2; simp only [YR]; push_cast; rw [hωC]; ring
      · rw [hU, hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [YR, add_re, sub_re, ofReal_re, natCast_re, natCast_im, ofReal_im, re_ofNat,
            im_ofNat, mul_zero, sub_zero, div_ofNat_re]
          push_cast; linarith))
    (by
      intro a b
      rw [hU]
      simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im,
        mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div]
      intro heq
      apply hA (-(h : ℝ)) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [YR, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im,
        mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, add_re]
      have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
      push_cast; intro heq; linarith)
    (by
      intro a b
      rw [hU]
      simp only [add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im, mul_zero,
        sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
      push_cast; intro heq; linarith)
    (by
      intro a b
      rw [hV]
      simp only [YR, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
      push_cast; intro heq; linarith)
    (by
      -- the crossed left poles
      intro w
      rw [hU, hV]
      constructor
      · intro hw
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
        have : ∃ j : ℕ, j ≤ Lh ∧ w' = zA n g l j := by
          rcases Finset.mem_insert.1 hw' with h0 | hmem
          · exact ⟨0, by omega, h0⟩
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hmem
            exact ⟨j + 1, by have := Finset.mem_range.1 hj; omega, rfl⟩
        obtain ⟨j, hj, rfl⟩ := this
        refine ⟨Or.inl ⟨0, j, by simp only [zA, c]; push_cast; ring⟩, ?_⟩
        have := hA1 j hj
        simp only [zA, add_re, sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im,
          mul_zero, sub_zero]
        push_cast; linarith
      · rintro ⟨hfam, hre⟩
        rcases hfam with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
        · simp only [sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im,
            mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div] at hre
          rcases Nat.eq_zero_or_pos a with rfl | ha
          · rcases le_or_gt b Lh with hb | hb
            · refine Finset.mem_image.2 ⟨zA n g l b, ?_, by simp only [zA, c]; push_cast; ring⟩
              rcases Nat.eq_zero_or_pos b with rfl | hb0
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨b - 1, Finset.mem_range.2 (by omega),
                  by congr 1; omega⟩)
            · exfalso; have := hA2 b hb; push_cast at this hre; linarith
          · exfalso
            have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
            have h5 : ω₁ n ≤ a * ω₁ n := by nlinarith
            have h6 : (0 : ℝ) ≤ b * ω₂ n := by positivity
            push_cast at hre; linarith
        · exfalso
          simp only [YR, sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
            mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re] at hre
          have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
          have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
          push_cast at hre; linarith)
    (by
      intro w
      rw [hU, hV]
      simp only [Finset.notMem_empty, false_iff, not_and, not_lt]
      rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · simp only [add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im, mul_zero,
          sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith
      · simp only [YR, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
          mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith)
    (by
      -- residues at the crossed poles
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
      have hres' : HasResidueGen Φ w' (ρ₁' w') := by
        rcases Finset.mem_insert.1 hw' with rfl | hmem
        · simp only [hρ₁', if_pos rfl]; exact hres0.hasResidueGen
        · have hne : w' ≠ zA n g l 0 := fun h0 => hnot0 (h0 ▸ hmem)
          simp only [hρ₁', if_neg hne]
          exact hρ₁ w' (Finset.mem_union.2 (Or.inl hmem))
      have h1 := hasResidueGen_const_mul (hasResidueGen_comp_sub hres' (c : ℂ)) E
      have h3 := hasResidueGen_congr_fun h1 (fun z => (hk4 z).symm)
      have h4 : ρL (w' + (c : ℂ)) = E * ρ₁' w' := by
        simp only [hρL]; congr 2; ring
      rw [h4]; exact h3)
    (by intro w hw; exact absurd hw (Finset.notMem_empty w))
  refine ⟨?_, ?_⟩
  · refine (hint.const_mul E⁻¹).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [hk4, ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
    congr 1; simp only [lineR]; rw [ht]; push_cast; ring
  · rw [Finset.sum_empty, mul_zero, sub_zero] at heq
    have hli : lineIntegral (k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v))
        (-t - ε + c) = E * lineIntegral Φ (-((g + h + l : ℕ) : ℝ) - ε) := by
      rw [show k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v)
          = fun z => E * Φ (z - (c : ℂ)) from funext hk4, lineIntegral_const_mul,
        lineIntegral_comp_sub, show -t - ε + c - c = -((g + h + l : ℕ) : ℝ) - ε by rw [ht]; push_cast; ring]
    rw [hli, Finset.sum_image (fun x _ y _ hxy => hshift_inj hxy), Finset.sum_insert hnot0] at heq
    have hsum : ρL (zA n g l 0 + (c : ℂ)) + ∑ x ∈ (Finset.range Lh).image (fun j => zA n g l (j + 1)),
        ρL (x + (c : ℂ)) = E * (ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0)
          + ∑ w ∈ SAB n g h l Lh Ll, ρ₁ w) := by
      have e1 : ρL (zA n g l 0 + (c : ℂ)) = E * ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0) := by
        simp only [hρL, hρ₁', add_sub_cancel_right, if_pos]
      have e2 : ∑ x ∈ (Finset.range Lh).image (fun j => zA n g l (j + 1)), ρL (x + (c : ℂ))
          = E * ∑ w ∈ SAB n g h l Lh Ll, ρ₁ w := by
        rw [Finset.mul_sum]
        have hsub : (Finset.range Lh).image (fun j => zA n g l (j + 1)) ⊆ SAB n g h l Lh Ll :=
          Finset.subset_union_left
        rw [← Finset.sum_subset hsub (fun w hw hw' => by rw [hρ₁0 w hw hw', mul_zero])]
        apply Finset.sum_congr rfl
        intro w hw
        have hne : w ≠ zA n g l 0 := fun h0 => hnot0 (h0 ▸ hw)
        simp only [hρL, hρ₁', add_sub_cancel_right, if_neg hne]
      rw [e1, e2]; ring
    rw [hsum] at heq
    rw [← heq]; ring

include hn in
/-- `-t₂` is not one of the crossed family points. -/
lemma zB_zero_not_mem (Lh Ll : ℕ) : zB n g h 0 ∉ SAB n g h l Lh Ll := by
  intro hmem
  rcases Finset.mem_union.1 hmem with hw | hw
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hw
    exact zA_ne_int n hn g l j (-((g + h : ℕ) : ℤ)) (by rw [hj]; simp [zB])
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hw
    have := zB_injective n g h hj
    omega

include hn hodd hg hh hgh hl hlh in
/-- The second four-gamma integral of the right product, with the crossed poles (both families
and `-t₂`) added back, is the centered kernel `K₄(R, X + ω₂, Y, Z)` up to the phase of (8.10). -/
theorem right_K4_2 (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g))
    (ε : ℝ) (Lh Ll : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hA1 : ∀ j : ℕ, j ≤ Lh → -ε < (h : ℝ) - j * ω₂ n)
    (hA2 : ∀ j : ℕ, Lh + 1 ≤ j → (h : ℝ) - j * ω₂ n < -ε)
    (hB1 : ∀ j : ℕ, j ≤ Ll → -ε < (l : ℝ) - j * ω₂ n)
    (hB2 : ∀ j : ℕ, Ll + 1 ≤ j → (l : ℝ) - j * ω₂ n < -ε) (hav : AvoidR n g h l ε)
    (ρ₂ : ℂ → ℂ)
    (hρ₂ : ∀ w ∈ SAB n g h l Lh Ll,
      HasResidueGen (fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pR g l) (qR l) (sR g h l) z) w (ρ₂ w)) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * (θL n v) * lineR g h l ε t)
      * J2 n G (pR g l) (qR l) (sR g h l) (lineR g h l ε t)) ∧
    Complex.exp (π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n))
      * (lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pR g l) (qR l) (sR g h l) z)
          (-((g + h + l : ℕ) : ℝ) - ε)
        + 2 * π * I * (ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0)
          + ∑ w ∈ SAB n g h l Lh Ll, ρ₂ w))
      = I * Real.sqrt (ω₁ n * ω₂ n) * G.K4 (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) := by
  classical
  obtain ⟨hA, hB⟩ := hav
  simp only [rightCs, Finset.mem_insert, Finset.mem_singleton] at hA hB
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hωC : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have hωR : ω₁ n = n + ω₂ n := ω₁_eq n
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlh' : (l : ℝ) ≤ h := by exact_mod_cast hlh
  have hghR : (g : ℝ) + h ≤ n - 1 := by
    have : ((g + h : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : g + h ≤ n - 1)
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  -- the parameters
  have hU : k4U (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n)
      = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + ((g + l : ℕ) : ℂ) / 2 := by
    unfold k4U; simp only [RR, XL]; push_cast; rw [hωC]; ring
  have hV : k4V (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) = -(l : ℂ) / 2 := by
    unfold k4V; simp only [RR, XL]; push_cast; rw [hωC]; ring
  set Φ : ℂ → ℂ := fun z => Complex.exp (-I * (θL n v) * z) * J2 n G (pR g l) (qR l) (sR g h l) z
    with hΦ
  set E : ℂ := Complex.exp (π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n)) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  set c : ℝ := (((g : ℝ) + l) - n) / 2 with hc
  set t : ℝ := ((g + h + l : ℕ) : ℝ) with ht
  push_cast at ht
  have hk4 : ∀ z, k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) z
      = E * Φ (z - (c : ℂ)) := by
    intro z
    rw [k4_J2R_eq n hn G g h l v z, hΦ, hE]
    simp only [c]
    congr 2 <;> (congr 1; push_cast; ring)
  -- the crossed poles in the coordinates of the kernel
  have hnot0 := zB_zero_not_mem n hn g h l Lh Ll
  set SL : Finset ℂ := (insert (zB n g h 0) (SAB n g h l Lh Ll)).image (fun w => w + (c : ℂ)) with hSL
  have hshift_inj : Function.Injective (fun w : ℂ => w + (c : ℂ)) := add_left_injective _
  set ρ₂' : ℂ → ℂ := fun w => if w = zB n g h 0
    then ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0) else ρ₂ w with hρ₂'
  set ρL : ℂ → ℂ := fun w => E * ρ₂' (w - (c : ℂ)) with hρL
  -- the residue at `-t₂`
  have hres0 : HasResidue Φ (zB n g h 0) (ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0)) := by
    apply J2_residue'
    · exact ⟨0, 0, by simp only [zB, sR, qR]; push_cast; ring⟩
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [zB]; push_cast; linarith)
    · have := not_pole_of_pos_coeff n hn ((l : ℚ) - h) 1 ((l : ℝ) - h + (1 : ℚ) * ω₂ n)
        (by push_cast; ring) one_pos
      convert this using 2; simp only [zB, pR]; push_cast; ring
    · have := int_not_pole n hn (-(l : ℤ)) (by omega)
      convert this using 2; simp only [zB, sR]; push_cast; ring
  -- apply the line characterization of `K₄`
  obtain ⟨hint, heq⟩ := G.K4_line (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) (-t - ε + c) SL ∅ ρL 0
    (by
      unfold K4Conv
      simp only [yL, RR, ofReal_re, div_ofNat_re, natCast_re]
      push_cast
      have hvn : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g) := hvres
      have : |-(ω₁ n + ω₂ n) * v / (2 * n)| < (ω₁ n + ω₂ n) / 2 - g / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < ω₁ n + ω₂ n),
          abs_of_pos (by linarith : (0 : ℝ) < 2 * n), div_lt_iff₀ (by linarith)]
        nlinarith
      (try simp only [neg_re, natCast_re, natCast_im, mul_zero, sub_zero, div_ofNat_re] at *)
      linarith)
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hU]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, natCast_re,
            natCast_im, mul_zero, sub_zero, div_ofNat_re, zero_mul]
          push_cast; linarith)
      · rw [hV]
        have := int_not_pole n hn (-(l : ℤ)) (by omega)
        convert this using 2; push_cast; ring
      · rw [hU, hV]
        have := not_pole_of_pos_coeff n hn (-h) 1 (-(h : ℝ) + (1 : ℚ) * ω₂ n) (by push_cast; ring) one_pos
        convert this using 2; simp only [YR]; push_cast; rw [hωC]; ring
      · rw [hU, hV]
        exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by
          simp only [YR, add_re, sub_re, neg_re, ofReal_re, natCast_re, natCast_im, ofReal_im,
            re_ofNat, im_ofNat, mul_zero, sub_zero, div_ofNat_re, neg_div]
          push_cast; linarith))
    (by
      intro a b
      rw [hU]
      simp only [sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      intro heq
      apply hA (ω₂ n - h) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hV]
      simp only [YR, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im,
        mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, add_re, neg_div]
      intro heq
      apply hA (-(l : ℝ)) (by simp) a b
      push_cast at heq ⊢; linarith)
    (by
      intro a b
      rw [hU]
      simp only [add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im, mul_zero,
        sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
      have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
      push_cast; intro heq; linarith)
    (by
      intro a b
      rw [hV]
      simp only [YR, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
        mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div]
      have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
      push_cast; intro heq; linarith)
    (by
      -- the crossed left poles
      intro w
      rw [hU, hV]
      constructor
      · intro hw
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
        rcases Finset.mem_insert.1 hw' with rfl | hmem
        · refine ⟨Or.inr ⟨0, 0, by simp only [zB, YR, c]; push_cast; ring⟩, ?_⟩
          simp only [zB, add_re, sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im,
            ofReal_im, mul_zero, sub_zero, Nat.cast_zero, zero_mul]
          push_cast; linarith
        · rcases Finset.mem_union.1 hmem with hmem | hmem
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hmem
            have hjL : j + 1 ≤ Lh := by have := Finset.mem_range.1 hj; omega
            refine ⟨Or.inl ⟨0, j, by simp only [zA, c]; push_cast; rw [hωC]; ring⟩, ?_⟩
            have := hA1 (j + 1) hjL
            simp only [zA, add_re, sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im,
              ofReal_im, mul_zero, sub_zero]
            push_cast at this ⊢; linarith
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hmem
            have hjL : j + 1 ≤ Ll := by have := Finset.mem_range.1 hj; omega
            refine ⟨Or.inr ⟨0, j + 1, by simp only [zB, YR, c]; push_cast; ring⟩, ?_⟩
            have := hB1 (j + 1) hjL
            simp only [zB, add_re, sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im,
              ofReal_im, mul_zero, sub_zero]
            push_cast at this ⊢; linarith
      · rintro ⟨hfam, hre⟩
        rcases hfam with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
        · simp only [sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re,
            mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re] at hre
          rcases Nat.eq_zero_or_pos a with rfl | ha
          · rcases le_or_gt (b + 1) Lh with hb | hb
            · refine Finset.mem_image.2 ⟨zA n g l (b + 1), ?_, by simp only [zA, c]; push_cast; rw [hωC]; ring⟩
              exact Finset.mem_insert_of_mem (Finset.mem_union.2 (Or.inl
                (Finset.mem_image.2 ⟨b, Finset.mem_range.2 (by omega), rfl⟩)))
            · exfalso; have := hA2 (b + 1) hb; push_cast at this hre; linarith
          · exfalso
            have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
            have h5 : ω₁ n ≤ a * ω₁ n := by nlinarith
            have h6 : (0 : ℝ) ≤ b * ω₂ n := by positivity
            push_cast at hre; linarith
        · simp only [YR, sub_re, neg_re, add_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
            mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div] at hre
          rcases Nat.eq_zero_or_pos a with rfl | ha
          · rcases le_or_gt b Ll with hb | hb
            · refine Finset.mem_image.2 ⟨zB n g h b, ?_, by simp only [zB, YR, c]; push_cast; ring⟩
              rcases Nat.eq_zero_or_pos b with rfl | hb0
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_union.2 (Or.inr
                  (Finset.mem_image.2 ⟨b - 1, Finset.mem_range.2 (by omega), by congr 1; omega⟩)))
            · exfalso; have := hB2 b hb; push_cast at this hre; linarith
          · exfalso
            have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
            have h5 : ω₁ n ≤ a * ω₁ n := by nlinarith
            have h6 : (0 : ℝ) ≤ b * ω₂ n := by positivity
            push_cast at hre; linarith)
    (by
      intro w
      rw [hU, hV]
      simp only [Finset.notMem_empty, false_iff, not_and, not_lt]
      rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · simp only [add_re, natCast_re, natCast_im, ofReal_re, ofReal_im, mul_re, mul_im, mul_zero,
          sub_zero, re_ofNat, im_ofNat, div_ofNat_re]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith
      · simp only [YR, add_re, sub_re, neg_re, natCast_re, natCast_im, ofReal_re, ofReal_im,
          mul_re, mul_im, mul_zero, sub_zero, re_ofNat, im_ofNat, div_ofNat_re, neg_div]
        have h1 : (0 : ℝ) ≤ a * ω₁ n := by positivity
        have h2 : (0 : ℝ) ≤ b * ω₂ n := by positivity
        push_cast; linarith)
    (by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
      have hres' : HasResidueGen Φ w' (ρ₂' w') := by
        rcases Finset.mem_insert.1 hw' with rfl | hmem
        · simp only [hρ₂', if_pos rfl]; exact hres0.hasResidueGen
        · have hne : w' ≠ zB n g h 0 := fun h0 => hnot0 (h0 ▸ hmem)
          simp only [hρ₂', if_neg hne]
          exact hρ₂ w' hmem
      have h1 := hasResidueGen_const_mul (hasResidueGen_comp_sub hres' (c : ℂ)) E
      have h3 := hasResidueGen_congr_fun h1 (fun z => (hk4 z).symm)
      have h4 : ρL (w' + (c : ℂ)) = E * ρ₂' w' := by
        simp only [hρL]; congr 2; ring
      rw [h4]; exact h3)
    (by intro w hw; exact absurd hw (Finset.notMem_empty w))
  refine ⟨?_, ?_⟩
  · refine (hint.const_mul E⁻¹).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [hk4, ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
    congr 1; simp only [lineR]; rw [ht]; push_cast; ring
  · rw [Finset.sum_empty, mul_zero, sub_zero] at heq
    have hli : lineIntegral (k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v))
        (-t - ε + c) = E * lineIntegral Φ (-((g + h + l : ℕ) : ℝ) - ε) := by
      rw [show k4Integrand G.γ (ω₁ n) (ω₂ n) (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v)
          = fun z => E * Φ (z - (c : ℂ)) from funext hk4, lineIntegral_const_mul,
        lineIntegral_comp_sub, show -t - ε + c - c = -((g + h + l : ℕ) : ℝ) - ε by rw [ht]; push_cast; ring]
    rw [hli, Finset.sum_image (fun x _ y _ hxy => hshift_inj hxy), Finset.sum_insert hnot0] at heq
    have hsum : ρL (zB n g h 0 + (c : ℂ)) + ∑ x ∈ SAB n g h l Lh Ll, ρL (x + (c : ℂ))
        = E * (ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0)
          + ∑ w ∈ SAB n g h l Lh Ll, ρ₂ w) := by
      have e1 : ρL (zB n g h 0 + (c : ℂ)) = E * ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0) := by
        simp only [hρL, hρ₂', add_sub_cancel_right, if_pos]
      have e2 : ∑ x ∈ SAB n g h l Lh Ll, ρL (x + (c : ℂ)) = E * ∑ w ∈ SAB n g h l Lh Ll, ρ₂ w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        have hne : w ≠ zB n g h 0 := fun h0 => hnot0 (h0 ▸ hw)
        simp only [hρL, hρ₂', add_sub_cancel_right, if_neg hne]
      rw [e1, e2]; ring
    rw [hsum] at heq
    rw [← heq]; ring

/-! ### Step 5 for the right product: the residues at the window integers -/

omit G in
include hn hodd in
/-- The frequency of the right product: `v ≡ 2k - n(g+1) (mod 2n)` gives `e^{-iθn} = -(-1)^{p+q}`. -/
lemma theta_period_right (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    Complex.exp (-I * (θL n v) * n) = -((-1) ^ (pR g l + qR l)) := by
  have hv' : (2 * n : ℤ) ∣ v - (2 * k + n * ((g + 2 : ℕ) - 1)) := by
    obtain ⟨m, hm⟩ := hv
    exact ⟨m - (g + 1), by push_cast; linarith⟩
  have hθ := theta_period n hn hodd (g + 2) (by omega) k v hv'
  have hsgn : (-1 : ℂ) ^ (pR g l + qR l) = (-1) ^ (g + 2) := by
    rw [← zpow_natCast]
    apply neg_one_zpow_congr
    simp only [pR, qR]; push_cast
    generalize (g : ZMod 2) = x; generalize (l : ZMod 2) = y; revert x y; decide
  rw [hsgn]; simp only [θL]; push_cast at hθ ⊢; exact hθ

omit G in
include hn in
/-- `e^{-iθa} = e^{-2πika/n} (-1)^{a(g+1)}` for the frequency of the right product and an
integer `a`. -/
lemma theta_sample_int (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) (a : ℤ) :
    Complex.exp (-I * ((π * v / n : ℝ) : ℂ) * a)
      = Complex.exp (-(2 * π * I * k * a / n)) * (-1) ^ (a * (g + 1)) := by
  obtain ⟨m, hm⟩ := hv
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hv' : (v : ℂ) = 2 * k - n * (g + 1) + 2 * n * m := by
    have : v = 2 * k - n * (g + 1) + 2 * n * m := by linarith
    rw [this]; push_cast; ring
  push_cast
  have e1 : -I * (π * v / n) * (a : ℂ) = -(2 * π * I * k * a / n)
      + (((a * (g + 1) : ℤ) : ℂ) * (π * I) + ((-(a * m) : ℤ) : ℂ) * (2 * π * I)) := by
    rw [hv']; push_cast; field_simp; ring
  rw [e1, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

include hn hodd in
/-- Lemma 3.9 for a negative label `-t₁` and a sample point in the window `(-n - t₁, n - 1]`:
the only correction is at `a = -t₁`. -/
lemma tz_neg_window (t₁ : ℕ) (ht1 : 1 ≤ t₁) (ht2 : t₁ ≤ n - 1) (a : ℤ)
    (ha1 : -(n : ℤ) - t₁ < a) (ha2 : a ≤ n - 1) :
    tz n G (-(t₁ : ℤ)) a = (toCoeffData n hn G hodd).B (a : ZMod n) (-(t₁ : ZMod n))
      + (ω₂ n : ℂ) * (if a = -(t₁ : ℤ) then 1 else 0) := by
  rcases le_or_gt 0 a with ha | ha
  · -- `0 ≤ a ≤ n - 1`
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = m := ⟨a.toNat, by omega⟩
    rw [tz_neg_nonneg n hn G hodd t₁ ht1 ht2 m (by omega), if_neg (by omega), mul_zero, add_zero,
      Int.cast_natCast]
  rcases le_or_gt (-(n : ℤ) + 1) a with ha' | ha'
  · -- `-(n-1) ≤ a ≤ -1`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a = -(m : ℤ) := ⟨(-a).toNat, by omega⟩
    subst hm
    rw [tz_neg_neg n hn G hodd t₁ ht1 ht2 m (by omega) (by omega)]
    have e1 : ((-(m : ℤ) : ℤ) : ZMod n) = -(m : ZMod n) := by push_cast; ring
    have e2 : (-(m : ℤ) = -(t₁ : ℤ)) ↔ (m = t₁) := by omega
    rw [e1]; simp only [e2]
  · -- `a ≤ -n`: shift the sample point by `n`
    have hshift := tz_add_n n hn G hodd (-(t₁ : ℤ)) a (by omega) (by omega)
    rw [← hshift]
    rcases le_or_gt 0 (a + n) with hb | hb
    · have hb0 : a + n = 0 := by omega
      have h0 := tz_neg_nonneg n hn G hodd t₁ ht1 ht2 0 (by omega)
      simp only [Nat.cast_zero] at h0
      rw [hb0, h0, if_neg (by omega), mul_zero, add_zero]
      congr 2
      rw [show a = -(n : ℤ) by omega]; push_cast; simp
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, a + n = -(m : ℤ) := ⟨(-(a + n)).toNat, by omega⟩
      rw [hm, tz_neg_neg n hn G hodd t₁ ht1 ht2 m (by omega) (by omega), if_neg (by omega),
        mul_zero, add_zero, if_neg (by omega), mul_zero, add_zero]
      congr 2
      have : (a : ZMod n) = ((a + n : ℤ) : ZMod n) := by push_cast; simp
      rw [this, hm]; push_cast; ring

include hn hodd in
/-- `t_p(a + n) = u_p(a)` for `1 ≤ a ≤ n - 1`, including the diagonal point `a = p`. -/
lemma tz_pos_add_n (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ n - 1) (a : ℕ) (ha1 : 1 ≤ a)
    (ha2 : a ≤ n - 1) :
    tz n G p ((a : ℤ) + n) = (toCoeffData n hn G hodd).B (a : ZMod n) (p : ZMod n) := by
  by_cases hap : a = p
  · subst hap
    have hne : (a : ZMod n) ≠ 0 := natCast_ne_zero' n a ha1 ha2
    have hn2 := natCast_zmod2_of_odd n hodd
    rw [(toCoeffData n hn G hodd).B_diag hne, tz, Rz_eq_F]
    have h1 := F_int_add_n n hn G a (by omega)
    have hFa := F_int_ne_zero n hn G a
    have hd0 := sqrt_d_ne_zero n
    have hFn := F_n n hn G
    push_cast at h1 hFa hFn ⊢
    rw [show (a : ℂ) + n - a = n by ring, h1, hFn]
    have hsgn : (-1 : ℂ) ^ ((a : ℤ) * ((a : ℤ) + n + 1)) * (-1) ^ ((a : ℤ) + 1) = -1 := by
      have e := neg_one_zpow_congr ((a : ℤ) * ((a : ℤ) + n + 1) + ((a : ℤ) + 1)) 1 (by
        push_cast; rw [hn2]
        generalize (a : ZMod 2) = x; revert x; decide)
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), e, zpow_one]
    field_simp
    linear_combination hsgn
  · rw [tz_add_n n hn G hodd p a (by omega) (by omega), tz_pos n hn G hodd p hp1 hp2 a ha2,
      if_neg hap, mul_zero, add_zero]

omit hn G in
/-- The signs of Step 5 collapse to the constant `(-1)^{p+q+qs}`. -/
lemma right_sign_collapse (a : ℤ) :
    (-1 : ℂ) ^ (a - ((g + h + l : ℕ) : ℤ)) * (-1) ^ ((a - ((g + h + l : ℕ) : ℤ)) * (g + 1))
      * (-1) ^ ((pR g l) * ((a - ((g + h + l : ℕ) : ℤ)) + 1)) * (-1) ^ ((qR l) * (a + 1))
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  simp only [pR, qR, sR]
  push_cast
  generalize (a : ZMod 2) = x
  generalize (g : ZMod 2) = y
  generalize (h : ZMod 2) = z
  generalize (l : ZMod 2) = w
  revert x y z w; decide

include hn hodd hg hh hgh hl hlh in
/-- Step 5 for the right product: the residues at the window integers give the product
transform plus the three sample corrections. -/
theorem right_residue_sum (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    ∑ a : ZMod n, (-1) ^ ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))
        * Complex.exp (-I * (θL n v) * wR n g h l a)
        * (Rz n G (pR g l) (wR n g h l a) * Rz n G (qR l) (wR n g h l a + (sR g h l)))
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * (d n * F n G (pR g l) * F n G (qR l))
        * (∑ b : ZMod n, ZMod.stdAddChar (-(b * (k : ZMod n)))
            * (toCoeffData n hn G hodd).B b (-((g + l : ℕ) : ZMod n))
            * (toCoeffData n hn G hodd).B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n)
          + ω₂ n * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n)
            * (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n)
          + ω₂ n * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
            * (toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n))
          + ω₂ n ^ 2 * (if h = l then 1 else 0)
            * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n)) := by
  classical
  have hd0 := sqrt_d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pR g l)
  have hFq := F_int_ne_zero n hn G (qR l)
  have hsq := sqrt_d_sq n
  set B := (toCoeffData n hn G hodd).B with hB
  set E : ZMod n → ℂ := (fun a =>
    Complex.exp (-(2 * π * I * k * (((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) : ℂ) / n))) with hE
  set X : ZMod n → ℂ := (fun a =>
    B ((((a.val : ℤ) - ((g + h + l : ℕ) : ℤ) : ℤ) : ZMod n)) (-((g + l : ℕ) : ZMod n))) with hX
  set Y : ZMod n → ℂ := (fun a => B a (l : ZMod n)) with hY
  -- the summand
  have hterm : ∀ a : ZMod n,
      (-1) ^ ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ)) * Complex.exp (-I * (θL n v) * wR n g h l a)
        * (Rz n G (pR g l) (wR n g h l a) * Rz n G (qR l) (wR n g h l a + (sR g h l)))
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * (d n * F n G (pR g l) * F n G (qR l))
        * (E a * ((X a + ω₂ n * (if a.val = h then 1 else 0))
            * (Y a + ω₂ n * (if a.val = l then 1 else 0)))) := by
    intro a
    have hav : a.val ≤ n - 1 := by have := ZMod.val_lt a; omega
    have hθa := theta_sample_int n hn g k v hv ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))
    have hsgn := right_sign_collapse g h l (a.val : ℤ)
    simp only [hE, hX, hY]
    set w : ℤ := (a.val : ℤ) - ((g + h + l : ℕ) : ℤ) with hw
    have hwR : wR n g h l a = (w : ℂ) := rfl
    have hws : wR n g h l a + (sR g h l : ℂ) = ((a.val : ℤ) : ℂ) := by
      simp only [wR, sR]; push_cast; ring
    rw [hwR, hws]
    -- `R_p(w) = t_p(w) √d F(p) (-1)^{p(w+1)}`
    have hRp : Rz n G (pR g l) (w : ℂ)
        = tz n G (pR g l) w * (Real.sqrt (d n) * F n G (pR g l)) * (-1) ^ ((pR g l) * (w + 1)) := by
      unfold tz
      have := neg_one_zpow_sq ((pR g l) * (w + 1))
      field_simp
      linear_combination (-(Rz n G (pR g l) (w : ℂ))) * this
    have hRq : Rz n G (qR l) ((a.val : ℤ) : ℂ)
        = tz n G (qR l) (a.val : ℤ) * (Real.sqrt (d n) * F n G (qR l))
          * (-1) ^ ((qR l) * ((a.val : ℤ) + 1)) := by
      unfold tz
      have := neg_one_zpow_sq ((qR l) * ((a.val : ℤ) + 1))
      field_simp
      linear_combination (-(Rz n G (qR l) ((a.val : ℤ) : ℂ))) * this
    -- the sample rules
    have htp : tz n G (pR g l) w = B (w : ZMod n) (-((g + l : ℕ) : ZMod n))
        + ω₂ n * (if a.val = h then 1 else 0) := by
      show tz n G (-((g + l : ℕ) : ℤ)) w = _
      rw [tz_neg_window n hn G hodd (g + l) (by omega) (by omega) w (by omega) (by omega)]
      simp only [show (w = -((g + l : ℕ) : ℤ)) ↔ (a.val = h) from by omega]
      rfl
    have htq : tz n G (qR l) (a.val : ℤ) = B a (l : ZMod n) + ω₂ n * (if a.val = l then 1 else 0) := by
      have := tz_pos n hn G hodd l hl (by omega) a.val hav
      rw [ZMod.natCast_zmod_val] at this
      exact this
    rw [hRp, hRq, htp, htq, hθa, ← hsq]
    linear_combination ((Real.sqrt (d n) : ℂ) ^ 2 * Complex.exp (-(2 * π * I * k * (w : ℂ) / n))
      * (B (w : ZMod n) (-((g + l : ℕ) : ZMod n)) + ω₂ n * (if a.val = h then 1 else 0))
      * (B a (l : ZMod n) + ω₂ n * (if a.val = l then 1 else 0))
      * (F n G (pR g l) * F n G (qR l))) * hsgn
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
  congr 1
  -- the phases and the casts
  have hχ : ∀ a : ZMod n, E a
      = ZMod.stdAddChar (-((a - ((g + h + l : ℕ) : ZMod n)) * (k : ZMod n))) := by
    intro a
    have := ZMod.stdAddChar_coe (N := n) (-(k * ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))))
    rw [show ((-(k * ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))) : ℤ) : ZMod n)
        = -((a - ((g + h + l : ℕ) : ZMod n)) * (k : ZMod n)) by
      push_cast; rw [ZMod.natCast_zmod_val]; ring] at this
    rw [this]; simp only [hE]; congr 1; push_cast; ring
  have hcast : ∀ a : ZMod n, X a = B (a - ((g + h + l : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n)) := by
    intro a
    simp only [hX]
    congr 2
    push_cast; rw [ZMod.natCast_zmod_val]
  have e_h : E (h : ZMod n) = Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) := by
    simp only [hE]; rw [val_natCast' n h (by omega)]; congr 1; push_cast; ring
  have e_l : E (l : ZMod n) = Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n) := by
    simp only [hE]; rw [val_natCast' n l (by omega)]; congr 1; push_cast; ring
  have x_l : X (l : ZMod n) = B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n)) := by
    simp only [hX]; rw [val_natCast' n l (by omega)]; congr 2; push_cast; ring
  -- expand the product
  have hsplit : ∀ a : ZMod n, E a * ((X a + ω₂ n * (if a.val = h then 1 else 0))
        * (Y a + ω₂ n * (if a.val = l then 1 else 0)))
      = E a * X a * Y a + ω₂ n * (if a.val = h then 1 else 0) * (E a * Y a)
        + ω₂ n * (if a.val = l then 1 else 0) * (E a * X a)
        + ω₂ n ^ 2 * (if a.val = h then 1 else 0) * (if a.val = l then 1 else 0) * E a := by
    intro a; split_ifs <;> ring
  have hmain : ∑ a : ZMod n, E a * X a * Y a
      = ∑ b : ZMod n, ZMod.stdAddChar (-(b * (k : ZMod n))) * B b (-((g + l : ℕ) : ZMod n))
          * B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n) := by
    have e : ∀ a : ZMod n, E a * X a * Y a
        = (fun b : ZMod n => ZMod.stdAddChar (-(b * (k : ZMod n))) * B b (-((g + l : ℕ) : ZMod n))
            * B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n)) (a - ((g + h + l : ℕ) : ZMod n)) := by
      intro a
      simp only [sub_add_cancel]
      rw [hχ a, hcast a, hY]
    rw [Finset.sum_congr rfl (fun a _ => e a)]
    exact Fintype.sum_equiv (Equiv.subRight ((g + h + l : ℕ) : ZMod n)) _ _
      (fun a => by simp only [Equiv.subRight_apply])
  have hc1 : ∑ a : ZMod n, ω₂ n * (if a.val = h then 1 else 0) * (E a * Y a)
      = ω₂ n * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * B (h : ZMod n) (l : ZMod n) := by
    rw [Finset.sum_eq_single (h : ZMod n)]
    · rw [val_natCast' n h (by omega), if_pos rfl, mul_one, e_h, hY]; ring
    · intro a _ ha
      have : a.val ≠ h := by intro e; apply ha; rw [← ZMod.natCast_zmod_val a, e]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hc2 : ∑ a : ZMod n, ω₂ n * (if a.val = l then 1 else 0) * (E a * X a)
      = ω₂ n * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
        * B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n)) := by
    rw [Finset.sum_eq_single (l : ZMod n)]
    · rw [val_natCast' n l (by omega), if_pos rfl, mul_one, e_l, x_l]; ring
    · intro a _ ha
      have : a.val ≠ l := by intro e; apply ha; rw [← ZMod.natCast_zmod_val a, e]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hc3 : ∑ a : ZMod n, ω₂ n ^ 2 * (if a.val = h then 1 else 0) * (if a.val = l then 1 else 0) * E a
      = ω₂ n ^ 2 * (if h = l then 1 else 0) * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) := by
    rw [Finset.sum_eq_single (h : ZMod n)]
    · rw [val_natCast' n h (by omega), if_pos rfl, mul_one, e_h]
    · intro a _ ha
      have : a.val ≠ h := by intro e; apply ha; rw [← ZMod.natCast_zmod_val a, e]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
  simp only [Finset.sum_add_distrib]
  rw [hmain, hc1, hc2, hc3]

/-! ### Step 6 for the right product: the two surviving residues -/

omit hn G in
include hodd in
lemma right_sign_one :
    (-1 : ℂ) ^ (qR l) * (-1) ^ (pR g l) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * (-1) ^ ((qR l) * ((h : ℤ) + n + 1))
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) := by
  have hn2 := natCast_zmod2_of_odd n hodd
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  simp only [pR, qR, sR]
  push_cast
  rw [hn2]
  generalize (g : ZMod 2) = y
  generalize (h : ZMod 2) = z
  generalize (l : ZMod 2) = w
  revert y z w; decide

omit hn G in
lemma right_sign_two :
    (-1 : ℂ) ^ (sR g h l) * (-1) ^ (qR l) * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1))
      * (-1) ^ ((pR g l) * ((-((g + h : ℕ) : ℤ)) + 1))
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  simp only [pR, qR, sR]
  push_cast
  generalize (g : ZMod 2) = y
  generalize (h : ZMod 2) = z
  generalize (l : ZMod 2) = w
  revert y z w; decide

include hn hodd hg hh hgh hl hlh in
/-- (6.13): the residue of `e^{-iθz} J₁'` at `z = p' = -t₁` reproduces the first sample
correction. -/
theorem right_residue_one (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    4 * π * ((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n))
        * ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0)
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * (d n * F n G (pR g l) * F n G (qR l))
        * (ω₂ n * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n)
          * (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n)) := by
  have hd0 := sqrt_d_ne_zero n
  have hsq := sqrt_d_sq n
  have hd : ((Real.sqrt (d n) : ℂ)) * Real.sqrt (d n) = d n := by rw [← sq]; exact hsq
  have hFp := F_int_ne_zero n hn G (pR g l)
  have hFq := F_int_ne_zero n hn G (qR l)
  -- the residue at the origin
  have hres2 : 2 * π * G.residue 0 = (ω₂ n : ℂ) * Real.sqrt (d n) := by
    rw [G.residue_zero_eq, sqrt_Ω]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  -- `γ(ω₁ + h - q) γ(ω₂ - h) = R_q(h + n)`
  have hRz : G.γ ((ω₁ n : ℂ) + ((h : ℂ) - ((qR l : ℤ) : ℂ))) * G.γ ((ω₂ n : ℂ) - h)
      = Rz n G (qR l) ((h : ℂ) + n) := by
    rw [Rz_add_n n G (qR l) (h : ℂ)
      (by have := ω₁_add_int_not_pole n hn (h : ℤ); push_cast at this; exact this)
      (by have := ω₁_add_int_not_zero n hn (h : ℤ); push_cast at this; exact this)]
  -- `R_q(h + n) = t_q(h + n) √d F(q) (-1)^{q(h+n+1)}`
  have hRq : Rz n G (qR l) ((h : ℂ) + n)
      = tz n G (qR l) ((h : ℤ) + n) * (Real.sqrt (d n) * F n G (qR l))
        * (-1) ^ ((qR l) * ((h : ℤ) + n + 1)) := by
    unfold tz
    have := neg_one_zpow_sq ((qR l) * ((h : ℤ) + n + 1))
    rw [show ((((h : ℤ) + n) : ℤ) : ℂ) = (h : ℂ) + n by push_cast; ring]
    field_simp
    linear_combination (-(Rz n G (qR l) ((h : ℂ) + n))) * this
  have htq : tz n G (qR l) ((h : ℤ) + n) = (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n) :=
    tz_pos_add_n n hn G hodd l hl (by omega) h hh (by omega)
  -- `2 sin(πp/ω₁) γ(-p) = (-1)^p F(p)`
  have hsin := two_sin_mul_γ_neg n hn G (pR g l) (by simp only [pR]; omega)
  -- the frequency
  have hθ := theta_sample_int n hn g k v hv (pR g l)
  have hexp : Complex.exp (-(2 * π * I * k * ((pR g l : ℤ) : ℂ) / n))
      = Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) := by
    congr 1; simp only [pR]; push_cast; ring
  have hsgn := right_sign_one n hodd g h l
  -- assemble
  unfold ρJ1
  simp only [zA, Nat.cast_zero, zero_mul, sub_zero, θL]
  rw [show -((g + l : ℕ) : ℂ) = ((pR g l : ℤ) : ℂ) by simp only [pR]; push_cast; ring, sub_self,
    show (ω₂ n : ℂ) - ((pR g l : ℤ) : ℂ) - ((sR g h l : ℤ) : ℂ) = (ω₂ n : ℂ) - h by
      simp only [pR, sR]; push_cast; ring,
    show (ω₁ n : ℂ) + ((pR g l : ℤ) : ℂ) + ((sR g h l : ℤ) : ℂ) - ((qR l : ℤ) : ℂ)
      = (ω₁ n : ℂ) + ((h : ℂ) - ((qR l : ℤ) : ℂ)) by simp only [pR, sR, qR]; push_cast; ring,
    hθ, hexp]
  linear_combination
    (2 * (-1 : ℂ) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n)
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * G.γ (-((pR g l : ℤ) : ℂ)) * G.γ ((ω₂ n : ℂ) - h)
      * G.γ ((ω₁ n : ℂ) + ((h : ℂ) - ((qR l : ℤ) : ℂ)))) * hres2
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (qR l)
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * G.γ ((ω₂ n : ℂ) - h) * G.γ ((ω₁ n : ℂ) + ((h : ℂ) - ((qR l : ℤ) : ℂ)))) * hsin
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (qR l)
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * (-1) ^ (pR g l) * F n G (pR g l)) * hRz
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (qR l)
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * (-1) ^ (pR g l) * F n G (pR g l)) * hRq
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (qR l)
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * (-1) ^ ((pR g l) * ((g : ℤ) + 1))
      * (-1) ^ (pR g l) * F n G (pR g l) * (Real.sqrt (d n) * F n G (qR l))
      * (-1) ^ ((qR l) * ((h : ℤ) + n + 1))) * htq
    + ((Real.sqrt (d n) : ℂ) * Real.sqrt (d n) * ω₂ n
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * F n G (pR g l) * F n G (qR l)
      * (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n)) * hsgn
    + ((-1 : ℂ) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * ω₂ n
      * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) * F n G (pR g l) * F n G (qR l)
      * (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n)) * hd

include hn hodd hg hh hgh hl hlh in
/-- (6.14): the residue of `e^{-iθz} J₂'` at `z = q' - s' = -t₂` reproduces the second and
third sample corrections. -/
theorem right_residue_two (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    4 * π * ((-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n))
        * ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0)
      = (-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * (d n * F n G (pR g l) * F n G (qR l))
        * (ω₂ n * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
          * ((toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n))
            + ω₂ n * (if h = l then 1 else 0))) := by
  have hd0 := sqrt_d_ne_zero n
  have hsq := sqrt_d_sq n
  have hd : ((Real.sqrt (d n) : ℂ)) * Real.sqrt (d n) = d n := by rw [← sq]; exact hsq
  have hFp := F_int_ne_zero n hn G (pR g l)
  have hFq := F_int_ne_zero n hn G (qR l)
  have hres2 : 2 * π * G.residue 0 = (ω₂ n : ℂ) * Real.sqrt (d n) := by
    rw [G.residue_zero_eq, sqrt_Ω]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  -- `γ(ω₂ + w - p) γ(ω₁ - w) = R_p(w)` at `w = -t₂`
  have hRz : G.γ ((ω₂ n : ℂ) + (((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((pR g l : ℤ) : ℂ)))
      * G.γ ((ω₁ n : ℂ) - ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ))
      = Rz n G (pR g l) ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Rz_refl n G (pR g l) _ (ω₂_add_int_not_pole n hn _) (ω₂_add_int_not_zero n hn _)]
  have hRp : Rz n G (pR g l) ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ)
      = tz n G (pR g l) (-((g + h : ℕ) : ℤ)) * (Real.sqrt (d n) * F n G (pR g l))
        * (-1) ^ ((pR g l) * ((-((g + h : ℕ) : ℤ)) + 1)) := by
    unfold tz
    have := neg_one_zpow_sq ((pR g l) * ((-((g + h : ℕ) : ℤ)) + 1))
    field_simp
    linear_combination (-(Rz n G (pR g l) ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ))) * this
  have htp : tz n G (pR g l) (-((g + h : ℕ) : ℤ))
      = (toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n))
        + ω₂ n * (if h = l then 1 else 0) := by
    show tz n G (-((g + l : ℕ) : ℤ)) _ = _
    rw [tz_neg_window n hn G hodd (g + l) (by omega) (by omega) _ (by omega) (by omega)]
    simp only [show (-((g + h : ℕ) : ℤ) = -((g + l : ℕ) : ℤ)) ↔ (h = l) from by omega]
    congr 3
    push_cast; ring
  have hsin := two_sin_mul_γ_neg n hn G (qR l) (by simp only [qR]; omega)
  have hθ := theta_sample_int n hn g k v hv (-((g + h : ℕ) : ℤ))
  have hexp : Complex.exp (-(2 * π * I * k * ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) / n))
      = Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n) := by
    congr 1; push_cast; ring
  have hsgn := right_sign_two g h l
  -- assemble
  unfold ρJ2'
  simp only [zB, Nat.cast_zero, zero_mul, sub_zero, θL]
  rw [show -((g + h : ℕ) : ℂ) = ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) by push_cast; ring,
    show ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) + ((sR g h l : ℤ) : ℂ) - ((qR l : ℤ) : ℂ) = 0 by
      simp only [sR, qR]; push_cast; ring,
    show -((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((sR g h l : ℤ) : ℂ) = -((qR l : ℤ) : ℂ) by
      simp only [sR, qR]; push_cast; ring,
    show (ω₂ n : ℂ) + ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((pR g l : ℤ) : ℂ)
      = (ω₂ n : ℂ) + (((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((pR g l : ℤ) : ℂ)) by ring,
    hθ, hexp]
  linear_combination
    (2 * (-1 : ℂ) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n)
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
      * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1))
      * G.γ ((ω₁ n : ℂ) - ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ))
      * G.γ ((ω₂ n : ℂ) + (((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((pR g l : ℤ) : ℂ)))
      * G.γ (-((qR l : ℤ) : ℂ))) * hres2
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (sR g h l)
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
      * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1))
      * G.γ ((ω₁ n : ℂ) - ((-((g + h : ℕ) : ℤ) : ℤ) : ℂ))
      * G.γ ((ω₂ n : ℂ) + (((-((g + h : ℕ) : ℤ) : ℤ) : ℂ) - ((pR g l : ℤ) : ℂ)))) * hsin
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (sR g h l)
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
      * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1)) * (-1) ^ (qR l) * F n G (qR l)) * hRz
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (sR g h l)
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
      * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1)) * (-1) ^ (qR l) * F n G (qR l)) * hRp
    + ((ω₂ n : ℂ) * Real.sqrt (d n) * (-1) ^ (sR g h l)
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
      * (-1) ^ ((-((g + h : ℕ) : ℤ)) * ((g : ℤ) + 1)) * (-1) ^ (qR l) * F n G (qR l)
      * (Real.sqrt (d n) * F n G (pR g l)) * (-1) ^ ((pR g l) * ((-((g + h : ℕ) : ℤ)) + 1))) * htp
    + ((Real.sqrt (d n) : ℂ) * Real.sqrt (d n) * ω₂ n
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n) * F n G (pR g l) * F n G (qR l)
      * ((toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n))
        + ω₂ n * (if h = l then 1 else 0))) * hsgn
    + ((-1 : ℂ) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) * ω₂ n
      * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n) * F n G (pR g l) * F n G (qR l)
      * ((toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n))
        + ω₂ n * (if h = l then 1 else 0))) * hd

/-! ### The right product formula -/

include hn hodd hg hh hgh hl hlh in
/-- Proposition 6.3 (2) together with (8.10): the product transform
`S_{p',q',s'}(k) = ∑_b u_{p'}(b) u_{q'}(b+s') e^{-2πikb/n}` for the labels
`(p', q', s') = (-t₁, l, t)` equals
`-2√Ω c₀ (a₀ e^{-πiZt₁/Ω} K₄(R, X - ω₁, Y, Z) + b₀ e^{-πiZ(t₁-n)/Ω} K₄(R, X + ω₂, Y, Z))`. -/
theorem right_product (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1)))
    (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    ∑ b : ZMod n, ZMod.stdAddChar (-(b * (k : ZMod n)))
        * (toCoeffData n hn G hodd).B b (-((g + l : ℕ) : ZMod n))
        * (toCoeffData n hn G hodd).B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n)
      = -2 * Real.sqrt (ω₁ n * ω₂ n)
        * ((-1) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) / (d n * F n G (pR g l) * F n G (qR l)))
        * (((-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n))
            * Complex.exp (-π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n))
            * G.K4 (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v)
          + ((-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n))
            * Complex.exp (-π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n))
            * G.K4 (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v)) := by
  classical
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : (d n : ℂ) ≠ 0 := by exact_mod_cast d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pR g l)
  have hFq := F_int_ne_zero n hn G (qR l)
  -- the frequency facts
  have hθ : |θL n v| < π * (1 - g / (ω₁ n * ω₂ n)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hΩ := ω₁_mul_ω₂ n
    have hΩ' : 0 < ω₁ n + ω₂ n := by linarith [ω₁_pos n, ω₂_pos n]
    have hΩne : ω₁ n + ω₂ n ≠ 0 := hΩ'.ne'
    have h1 : |(v : ℝ)| < n * (1 - g / (ω₁ n * ω₂ n)) := by
      rw [hΩ, show (n : ℝ) * (1 - g / (ω₁ n + ω₂ n)) = n * (ω₁ n + ω₂ n - g) / (ω₁ n + ω₂ n) by
        field_simp, lt_div_iff₀ hΩ']
      exact hvres
    simp only [θL]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn0, div_lt_iff₀ hn0]
    calc π * |(v : ℝ)| < π * (n * (1 - g / (ω₁ n * ω₂ n))) := by gcongr
      _ = π * (1 - g / (ω₁ n * ω₂ n)) * n := by ring
  have hθn : Complex.exp (-I * (θL n v) * n) = -((-1) ^ (pR g l + qR l)) :=
    theta_period_right n hn hodd g l k v hv
  -- the strip
  obtain ⟨ε, Lh, Ll, hε0, hε1, hA1, hA2, hB1, hB2, hav, hLhl⟩ := right_eps_exists n g h l
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hρ₁0⟩ :=
    right_residues_exist n hn G g h l hg hh hgh hl hlh (θL n v) Lh Ll hLhl
  obtain ⟨hint0, hint1, hE1⟩ := right_strip n hn G hodd g h l hg hh hgh hl hlh (θL n v) hθ hθn
    ε Lh Ll hε0 hε1 hA1 hA2 hB1 hB2 ρ₁ ρ₂ hρ₁ hρ₂
  obtain ⟨hJ1, hE3⟩ := right_K4_1 n hn G hodd g h l hg hh hgh hl hlh v hvres ε Lh Ll hε0 hε1
    hA1 hA2 hav ρ₁ hρ₁ hρ₁0
  obtain ⟨hJ2, hE4⟩ := right_K4_2 n hn G hodd g h l hg hh hgh hl hlh v hvres ε Lh Ll hε0 hε1
    hA1 hA2 hB1 hB2 hav ρ₂ hρ₂
  have hE2 := right_line n hn G hodd g h l hg hh hgh hl hlh (θL n v) hθn ε hε0 hε1 hav hint0 hint1
    hJ1 hJ2
  have hE5 := right_residue_sum n hn G hodd g h l hg hh hgh hl hlh k v hv
  have hE6 := right_residue_one n hn G hodd g h l hg hh hgh hl hlh k v hv
  have hE7 := right_residue_two n hn G hodd g h l hg hh hgh hl hlh k v hv
  -- abbreviations
  set S := ∑ b : ZMod n, ZMod.stdAddChar (-(b * (k : ZMod n)))
      * (toCoeffData n hn G hodd).B b (-((g + l : ℕ) : ZMod n))
      * (toCoeffData n hn G hodd).B (b + ((g + h + l : ℕ) : ZMod n)) (l : ZMod n) with hS
  set Sres := ∑ a : ZMod n, (-1) ^ ((a.val : ℤ) - ((g + h + l : ℕ) : ℤ))
      * Complex.exp (-I * (θL n v) * wR n g h l a)
      * (Rz n G (pR g l) (wR n g h l a) * Rz n G (qR l) (wR n g h l a + (sR g h l))) with hSres
  set a₀ : ℂ := (-1) ^ (qR l) * Complex.sin (π * (pR g l) / ω₁ n) with ha₀
  set b₀ : ℂ := (-1) ^ (sR g h l) * Complex.sin (π * (qR l) / ω₁ n) with hb₀
  set LJ₁ := lineIntegral (fun z => Complex.exp (-I * (θL n v) * z)
    * J1 n G (pR g l) (qR l) (sR g h l) z) (-((g + h + l : ℕ) : ℝ) - ε) with hLJ₁
  set LJ₂ := lineIntegral (fun z => Complex.exp (-I * (θL n v) * z)
    * J2 n G (pR g l) (qR l) (sR g h l) z) (-((g + h + l : ℕ) : ℝ) - ε) with hLJ₂
  set Sig1 := ∑ w ∈ SAB n g h l Lh Ll, ρ₁ w with hSig1
  set Sig2 := ∑ w ∈ SAB n g h l Lh Ll, ρ₂ w with hSig2
  set ρ₀₁ := ρJ1 n G (pR g l) (qR l) (sR g h l) (θL n v) (zA n g l 0) with hρ₀₁
  set ρ₀₂ := ρJ2' n G (pR g l) (qR l) (sR g h l) (θL n v) (zB n g h 0) with hρ₀₂
  set E₁ := Complex.exp (π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n)) with hE₁
  set E₂ := Complex.exp (π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n)) with hE₂
  set K₁ := G.K4 (RR g) (XL n g l - ω₁ n) (YR n g h) (yL n v) with hK₁
  set K₂ := G.K4 (RR g) (XL n g l + ω₂ n) (YR n g h) (yL n v) with hK₂
  set C := (-1 : ℂ) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l))
    * (d n * F n G (pR g l) * F n G (qR l)) with hC
  set u₁ := ω₂ n * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n)
    * (toCoeffData n hn G hodd).B (h : ZMod n) (l : ZMod n) with hu₁
  set u₂ := ω₂ n * Complex.exp (2 * π * I * k * ((g + h : ℕ) : ℂ) / n)
    * (toCoeffData n hn G hodd).B (-((g + h : ℕ) : ZMod n)) (-((g + l : ℕ) : ZMod n)) with hu₂
  set u₃ := ω₂ n ^ 2 * (if h = l then 1 else 0)
    * Complex.exp (2 * π * I * k * ((g + l : ℕ) : ℂ) / n) with hu₃
  set Ω := (Real.sqrt (ω₁ n * ω₂ n) : ℂ) with hΩ
  have hE₁0 : E₁ ≠ 0 := Complex.exp_ne_zero _
  have hE₂0 : E₂ ≠ 0 := Complex.exp_ne_zero _
  have hE3' : LJ₁ + 2 * π * I * (ρ₀₁ + Sig1) = E₁⁻¹ * (I * Ω * K₁) := by
    rw [eq_inv_mul_iff_mul_eq₀ hE₁0]; exact hE3
  have hE4' : LJ₂ + 2 * π * I * (ρ₀₂ + Sig2) = E₂⁻¹ * (I * Ω * K₂) := by
    rw [eq_inv_mul_iff_mul_eq₀ hE₂0]; exact hE4
  -- the sums in `hE1` combine
  have hE1' : lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) (θL n v)) (n - ((g + h + l : ℕ) : ℝ) - ε)
      - lineIntegral (K2' n G (pR g l) (qR l) (sR g h l) (θL n v)) (-((g + h + l : ℕ) : ℝ) - ε)
      = 2 * π * I * (Sres + 4 * π * (a₀ * Sig1 + b₀ * Sig2)) := by
    rw [hE1]; congr 1; congr 1
    simp only [hSig1, hSig2, ha₀, hb₀, Finset.mul_sum, ← Finset.sum_add_distrib]
    try (apply Finset.sum_congr rfl; intro j _; ring)
  -- the second surviving residue gives `u₂ + u₃`
  have hE7' : 4 * π * b₀ * ρ₀₂ = C * (u₂ + u₃) := by
    rw [hE7]
    simp only [hu₂, hu₃]
    by_cases hhl : h = l
    · subst hhl; ring
    · simp only [if_neg hhl]; ring
  -- Step 7
  have key : 2 * π * I * Sres = -4 * π * I * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂)
      + 8 * π ^ 2 * I * (a₀ * ρ₀₁ + b₀ * ρ₀₂) := by
    linear_combination -hE1' + hE2 - (4 * π * a₀) * hE3' - (4 * π * b₀) * hE4'
  have hSres : Sres = -2 * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂)
      + 4 * π * (a₀ * ρ₀₁ + b₀ * ρ₀₂) := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero)
    linear_combination key
  rw [hE5] at hSres
  have hCS : C * S = -2 * Ω * (a₀ * E₁⁻¹ * K₁ + b₀ * E₂⁻¹ * K₂) := by
    linear_combination hSres + hE6 + hE7'
  have hC0 : C ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num))
    (mul_ne_zero (mul_ne_zero hd hFp) hFq)
  have hinvE₁ : Complex.exp (-π * I * yL n v * ((g + l : ℕ) : ℂ) / (ω₁ n * ω₂ n)) = E₁⁻¹ := by
    rw [hE₁, ← Complex.exp_neg]; congr 1; ring
  have hinvE₂ : Complex.exp (-π * I * yL n v * (((g + l : ℕ) : ℂ) - n) / (ω₁ n * ω₂ n)) = E₂⁻¹ := by
    rw [hE₂, ← Complex.exp_neg]; congr 1; ring
  rw [hinvE₁, hinvE₂]
  have hsq := neg_one_zpow_sq ((pR g l) + (qR l) + (qR l) * (sR g h l))
  rw [show (-1 : ℂ) ^ ((pR g l) + (qR l) + (qR l) * (sR g h l)) / (d n * F n G (pR g l) * F n G (qR l))
      = C⁻¹ by
    rw [hC, mul_inv, div_eq_mul_inv]
    congr 1
    exact (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)).symm]
  apply mul_left_cancel₀ hC0
  rw [hCS]
  field_simp
  try ring

end right

end Concrete
end HaagerupIzumi
