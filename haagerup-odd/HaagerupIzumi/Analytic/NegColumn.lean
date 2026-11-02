module

public import HaagerupIzumi.Analytic.RightProduct

@[expose] public section

/-!
# The negative-column transform (Lemma 8.1)

The column Fourier formula for the label `-g`: the kernel is the two-ratio kernel
`K2'` with labels `(p, q, s) = (-g, 0, 0)`, whose only poles in the strip
`-ε < Re z < n - ε` are the integers, and whose difference identity has a single
term, integrated by the two-gamma formula without crossed poles.
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

section neg
variable [NeZero n] (hodd : Odd n) (g : ℕ) (hg : 1 ≤ g) (hgn : g < n)

/-- The label `-g`. -/
abbrev pN : ℤ := -(g : ℤ)

omit G in
include hn hodd in
/-- The frequency `v ≡ 2k - n(g+1) (mod 2n)` in the form needed by the difference identity. -/
lemma theta_period_neg (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    Complex.exp (-I * (θL n v) * n) = -((-1) ^ (pN g + (0 : ℤ))) := by
  have := theta_period_right n hn hodd g 0 k v hv
  rw [this]
  congr 2 <;> simp [pR, qR, pN]

omit hodd in
include hn hg in
/-- The kernel conditions on the line `Re z = -ε`: no pole avoidance is needed. -/
lemma neg_line_cond (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℝ) :
    K2Cond n (pN g) 0 0 (((-ε : ℝ) : ℂ) + t * I) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h7 : ∀ r s : ℕ, ε ≠ 0 + (r * ω₁ n + s * ω₂ n) := by
    intro r s heq
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp at heq; linarith
      · have : (1 : ℝ) ≤ s := by exact_mod_cast hs
        have : (0 : ℝ) ≤ (0 : ℕ) * ω₁ n := by positivity
        nlinarith
    · have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ s * ω₂ n := by positivity
      nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [pN]; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · have := line_not_pole n 0 ε t h7
    convert this using 1; push_cast; ring
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
  · exact HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
  · apply sin_pi_ne_zero_of_not_int
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      intCast_re, zero_add] at hre
    have h1' : (-1 : ℤ) < m := by
      have : (-1 : ℝ) < m := by linarith
      exact_mod_cast this
    have h2' : m < 0 := by
      have : (m : ℝ) < 0 := by linarith
      exact_mod_cast this
    omega

include hn hodd hg hgn in
/-- The strip identity for the negative-column kernel: only the integer poles contribute. -/
theorem neg_strip (θ : ℝ) (hθ : |θ| < π * (1 - g / (ω₁ n * ω₂ n)))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pN g) 0 0 θ (((-ε : ℝ) : ℂ) + t * I)) ∧
    MeasureTheory.Integrable (fun t : ℝ => K2' n G (pN g) 0 0 θ (((n - ε : ℝ) : ℂ) + t * I)) ∧
    lineIntegral (K2' n G (pN g) 0 0 θ) (n - ε) - lineIntegral (K2' n G (pN g) 0 0 θ) (-ε)
      = 2 * π * I * ∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * θ * ((a.val : ℤ) : ℂ))
          * Rz n G (pN g) ((a.val : ℤ) : ℂ) := by
  classical
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  set Sint : Finset ℂ := Finset.univ.image (fun a : ZMod n => ((a.val : ℕ) : ℂ)) with hSint
  have hval_inj : Function.Injective (fun a : ZMod n => ((a.val : ℕ) : ℂ)) :=
    fun a b hab => ZMod.val_injective n (Nat.cast_injective (R := ℂ) (by simpa using hab))
  -- `R_0 = 1` at the integers
  have hRz0 : ∀ a : ℤ, Rz n G 0 ((a : ℂ) + ((0 : ℤ) : ℂ)) = 1 := by
    intro a
    rw [Rz_eq_F]; simp only [Int.cast_zero, add_zero, sub_zero]
    exact div_self (F_int_ne_zero n hn G a)
  -- the residue function
  set ρK : ℂ → ℂ := fun w => Complex.cos (π * w) * Complex.exp (-I * θ * w) * Rz n G (pN g) w
    with hρK
  have hres : ∀ q ∈ Sint, HasResidueGen (K2' n G (pN g) 0 0 θ) q (ρK q) := by
    intro q hq
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    have : ρK ((a.val : ℕ) : ℂ) = (-1) ^ (a.val : ℤ) * Complex.exp (-I * θ * ((a.val : ℤ) : ℂ))
        * (Rz n G (pN g) ((a.val : ℤ) : ℂ) * Rz n G 0 (((a.val : ℤ) : ℂ) + ((0 : ℤ) : ℂ))) := by
      simp only [hρK]
      rw [hRz0, mul_one, show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi',
        zpow_natCast]
      push_cast; ring
    rw [this]
    have := K2'_residue_int n hn G (pN g) 0 0 θ (a.val : ℤ)
    push_cast at this ⊢
    exact this.hasResidueGen
  -- the poles are interior
  obtain ⟨M, T, hT, hM⟩ := K2'_bound n G (pN g) 0 0 θ (-ε) (n - ε)
  have hSpos : ∀ q ∈ Sint, -ε < q.re ∧ q.re < n - ε ∧ |q.im| < T := by
    intro q hq
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    have h1 : (a.val : ℝ) ≤ n - 1 := by
      have : (a.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show a.val ≤ n - 1 by
        have := ZMod.val_lt a; omega)
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
    have h2 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
    simp only [natCast_re, natCast_im, abs_zero]
    exact ⟨by linarith, by linarith, hT⟩
  -- differentiability off the integers
  have hd : ∀ ζ : ℂ, -ε ≤ ζ.re → ζ.re ≤ n - ε → ζ ∉ Sint →
      DifferentiableAt ℂ (K2' n G (pN g) 0 0 θ) ζ := by
    intro ζ hζ1 hζ2 hζS
    apply K2'_differentiableAt
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp [pN]; linarith)
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · exact HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    · apply sin_pi_ne_zero_of_not_int
      intro m hm
      apply hζS
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
  have hc0 : 0 < π - |θ| + π * ((pN g) + (0 : ℤ)) / (ω₁ n * ω₂ n) := by
    have e : ((pN g : ℤ) : ℝ) + ((0 : ℤ) : ℝ) = -g := by simp [pN]
    rw [e]
    have : π * (-(g : ℝ)) / (ω₁ n * ω₂ n) = -(π * (g / (ω₁ n * ω₂ n))) := by ring
    rw [this]
    have : π * (1 - g / (ω₁ n * ω₂ n)) = π - π * (g / (ω₁ n * ω₂ n)) := by ring
    linarith
  obtain ⟨hint0, hint1, hEq⟩ := strip_residues_gen (K2' n G (pN g) 0 0 θ) (-ε) (n - ε)
    (by linarith) Sint T hT hSpos ρK hres hd M _ hc0 (by
      intro z hza hzb hzT
      have := hM z hza hzb hzT
      push_cast at this ⊢
      exact this)
  refine ⟨hint0, hint1, ?_⟩
  rw [hEq]
  congr 1
  rw [Finset.sum_image (fun x _ y _ hxy => hval_inj hxy)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [hρK]
  rw [show (π : ℂ) * (a.val : ℂ) = a.val * π by ring, cos_nat_mul_pi', zpow_natCast]
  push_cast; ring

include hn hodd hg in
/-- The line identity for the negative column: a single term survives. -/
theorem neg_line (θ : ℝ) (hθn : Complex.exp (-I * θ * n) = -((-1) ^ (pN g + (0 : ℤ))))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hint0 : MeasureTheory.Integrable (fun t : ℝ => K2' n G (pN g) 0 0 θ (((-ε : ℝ) : ℂ) + t * I)))
    (hint1 : MeasureTheory.Integrable (fun t : ℝ => K2' n G (pN g) 0 0 θ (((n - ε : ℝ) : ℂ) + t * I)))
    (hJ1 : MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * θ * (((-ε : ℝ) : ℂ) + t * I))
      * J1 n G (pN g) 0 0 (((-ε : ℝ) : ℂ) + t * I))) :
    lineIntegral (K2' n G (pN g) 0 0 θ) (n - ε) - lineIntegral (K2' n G (pN g) 0 0 θ) (-ε)
      = -4 * π * Complex.sin (π * (pN g) / ω₁ n)
        * lineIntegral (fun z => Complex.exp (-I * θ * z) * J1 n G (pN g) 0 0 z) (-ε) := by
  have hline : ∀ t : ℝ, K2' n G (pN g) 0 0 θ (((n - ε : ℝ) : ℂ) + t * I)
      - K2' n G (pN g) 0 0 θ (((-ε : ℝ) : ℂ) + t * I)
      = -4 * π * Complex.sin (π * (pN g) / ω₁ n)
        * (Complex.exp (-I * θ * (((-ε : ℝ) : ℂ) + t * I))
          * J1 n G (pN g) 0 0 (((-ε : ℝ) : ℂ) + t * I)) := by
    intro t
    have := K2'_shift n G hodd (pN g) 0 0 θ hθn _ (neg_line_cond n hn g hg ε hε0 hε1 t)
    rw [show ((n - ε : ℝ) : ℂ) + t * I = (((-ε : ℝ) : ℂ) + t * I) + n by push_cast; ring, this]
    simp only [Int.cast_zero, zero_mul, mul_zero, zero_div, Complex.sin_zero, add_zero, zpow_zero,
      one_mul]
    ring
  unfold lineIntegral
  rw [← MeasureTheory.integral_sub (hint1.mul_const I) (hint0.mul_const I),
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext t
  rw [← sub_mul, hline t]; ring

include hn hg hgn in
/-- The two-gamma formula for the negative column: no crossed poles. -/
theorem neg_two_gamma (v : ℤ) (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-I * (θL n v) * (((-ε : ℝ) : ℂ) + t * I))
      * J1 n G (pN g) 0 0 (((-ε : ℝ) : ℂ) + t * I)) ∧
    lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pN g) 0 0 z) (-ε)
      = I * Real.sqrt (ω₁ n * ω₂ n) * Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n))
        * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) * G.γ g := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hω₂1 := one_lt_ω₂ n
  have hnω₁ := n_lt_ω₁ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hΩ : ω₁ n * ω₂ n = ω₁ n + ω₂ n := ω₁_mul_ω₂ n
  have hΩC : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast hΩ
  have hΩ' : 0 < ω₁ n + ω₂ n := by linarith
  have hΩ'C : (ω₁ n : ℂ) + ω₂ n ≠ 0 := by exact_mod_cast hΩ'.ne'
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  set α : ℂ := (((ω₁ n + ω₂ n - g) / 2 + (-(ω₁ n + ω₂ n) * v / (2 * n)) : ℝ) : ℂ) with hα
  have hαre : 0 < α.re ∧ α.re < ω₁ n + ω₂ n - g := by
    simp only [hα, ofReal_re]
    have h1 : |(v : ℝ)| * (ω₁ n + ω₂ n) / n < ω₁ n + ω₂ n - g := by
      rw [div_lt_iff₀ hn0]; linarith
    have h2 : |(-(ω₁ n + ω₂ n) * v / (2 * n))| = |(v : ℝ)| * (ω₁ n + ω₂ n) / n / 2 := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos hΩ', abs_of_pos (by linarith : (0 : ℝ) < 2 * n)]
      ring
    have h3 := abs_lt.1 (show |(-(ω₁ n + ω₂ n) * v / (2 * n))| < (ω₁ n + ω₂ n - g) / 2 by
      rw [h2]; linarith)
    constructor <;> linarith [h3.1, h3.2]
  have hexp_eq : ∀ z : ℂ, Complex.exp (π * I * z * (2 * α + 0 + (g : ℂ) - ω₁ n - ω₂ n)
      / (ω₁ n * ω₂ n)) = Complex.exp (-I * (θL n v) * z) := by
    intro z; congr 1
    simp only [hα, θL]; push_cast
    rw [hΩC]
    field_simp
    ring
  obtain ⟨hint, heq⟩ := G.two_gamma (g : ℂ) 0 α (-ε) ∅ 0 hαre.1
    (by simp only [sub_re, add_re, ofReal_re, natCast_re, zero_re, sub_zero]; exact hαre.2)
    (by simp; linarith)
    (by
      intro r s r' s' heq
      have := congrArg Complex.re heq
      simp only [sub_re, add_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im,
        mul_zero, sub_zero, zero_re, zero_add] at this
      have h1 : (0 : ℝ) ≤ r * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ s * ω₂ n := by positivity
      have h3 : (0 : ℝ) ≤ r' * ω₁ n := by positivity
      have h4 : (0 : ℝ) ≤ s' * ω₂ n := by positivity
      linarith)
    (by
      intro r s
      simp only [sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
        sub_zero]
      have h1 : (0 : ℝ) ≤ r * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ s * ω₂ n := by positivity
      intro heq; linarith)
    (by
      intro w
      simp only [Finset.notMem_empty, false_iff, not_and, not_lt]
      rintro ⟨r, s, rfl⟩
      simp only [sub_re, neg_re, natCast_re, mul_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
        sub_zero]
      have h1 : (0 : ℝ) ≤ r * ω₁ n := by positivity
      have h2 : (0 : ℝ) ≤ s * ω₂ n := by positivity
      linarith)
    (by simp)
  -- the two-gamma integrand is `e^{-iθz} J₁'` on the line
  have hpt : ∀ t : ℝ, Complex.exp (π * I * (((-ε : ℝ) : ℂ) + t * I)
        * (2 * α + 0 + (g : ℂ) - ω₁ n - ω₂ n) / (ω₁ n * ω₂ n))
        * G.γ ((g : ℂ) + (((-ε : ℝ) : ℂ) + t * I)) * G.γ (0 - (((-ε : ℝ) : ℂ) + t * I))
      = Complex.exp (-I * (θL n v) * (((-ε : ℝ) : ℂ) + t * I))
        * J1 n G (pN g) 0 0 (((-ε : ℝ) : ℂ) + t * I) := by
    intro t
    rw [hexp_eq]
    have hp1 : (ω₁ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ poleSet (ω₁ n) (ω₂ n) :=
      HypGamma.not_mem_poleSet_of_re_pos hω₁ hω₂ (by simp; linarith)
    have hz1 : (ω₁ n : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ zeroSet (ω₁ n) (ω₂ n) :=
      HypGamma.not_mem_zeroSet_of_re_lt hω₁ hω₂ (by simp; linarith)
    set z : ℂ := ((-ε : ℝ) : ℂ) + t * I with hz
    have hrefl := G.reflect ((ω₁ n : ℂ) + z) hp1 hz1
    rw [show (ω₁ n : ℂ) + ω₂ n - (ω₁ n + z) = ω₂ n - z by ring] at hrefl
    simp only [J1, pN, Int.cast_neg, Int.cast_natCast, Int.cast_zero]
    rw [show z - -(g : ℂ) = g + z by ring, show (0 : ℂ) - z = -z by ring, sub_zero, add_zero,
      sub_zero]
    linear_combination (-(Complex.exp (-I * (θL n v) * z) * G.γ ((g : ℂ) + z) * G.γ (-z))) * hrefl
  refine ⟨hint.congr (Filter.Eventually.of_forall fun t => hpt t), ?_⟩
  rw [Finset.sum_empty, mul_zero, add_zero] at heq
  have hli : lineIntegral (fun z => Complex.exp (π * I * z * (2 * α + 0 + (g : ℂ) - ω₁ n - ω₂ n)
      / (ω₁ n * ω₂ n)) * G.γ ((g : ℂ) + z) * G.γ (0 - z)) (-ε)
      = lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pN g) 0 0 z) (-ε) := by
    unfold lineIntegral; congr 1; funext t; beta_reduce; rw [hpt t]
  rw [hli] at heq
  rw [heq]
  unfold Γr
  have e1 : Complex.exp (π * I / (2 * (ω₁ n : ℂ) * (ω₂ n : ℂ)) * ((0 : ℂ) - g)
      * (2 * α + 0 + g - ω₁ n - ω₂ n))
      = Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n)) := by
    congr 1; simp only [hα, yL]; push_cast; ring
  have e3 : (ω₁ n : ℂ) + ω₂ n - 0 - g - α = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + rL g - yL n v := by
    simp only [hα, yL, rL]; push_cast; ring
  have e2 : α = ((ω₁ n + ω₂ n : ℝ) : ℂ) / 2 + rL g + yL n v := by
    simp only [hα, yL, rL]; push_cast; ring
  rw [e1, e3, e2, add_zero]; ring

include hn hodd hg hgn in
/-- The residues at the integers give `(-1)^g √d F(-g) û_{-g}(k)`: no sample correction for a
negative label on the window `{0, …, n-1}`. -/
theorem neg_residue_sum (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1))) :
    ∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * (θL n v) * ((a.val : ℤ) : ℂ))
        * Rz n G (pN g) ((a.val : ℤ) : ℂ)
      = (-1) ^ g * Real.sqrt (d n) * F n G (pN g)
        * ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
          * (toCoeffData n hn G hodd).B a (-(g : ZMod n)) := by
  have hd0 := sqrt_d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pN g)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hav : a.val ≤ n - 1 := by have := ZMod.val_lt a; omega
  have hRp : Rz n G (pN g) ((a.val : ℤ) : ℂ)
      = tz n G (pN g) (a.val : ℤ) * (Real.sqrt (d n) * F n G (pN g))
        * (-1) ^ ((pN g) * ((a.val : ℤ) + 1)) := by
    unfold tz
    have := neg_one_zpow_sq ((pN g) * ((a.val : ℤ) + 1))
    field_simp
    linear_combination (-(Rz n G (pN g) ((a.val : ℤ) : ℂ))) * this
  have htp : tz n G (pN g) (a.val : ℤ) = (toCoeffData n hn G hodd).B a (-(g : ZMod n)) := by
    have := tz_neg_nonneg n hn G hodd g hg (by omega) a.val hav
    rw [ZMod.natCast_zmod_val] at this
    exact this
  have hθa := theta_sample_int n hn g k v hv (a.val : ℤ)
  have hχ := stdAddChar_eq n k a
  have hsgn : (-1 : ℂ) ^ (a.val : ℤ) * (-1) ^ ((a.val : ℤ) * (g + 1))
      * (-1) ^ ((pN g) * ((a.val : ℤ) + 1)) = (-1) ^ g := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      ← zpow_natCast]
    apply neg_one_zpow_congr
    simp only [pN]; push_cast
    generalize (a.val : ZMod 2) = x
    generalize (g : ZMod 2) = y
    revert x y; decide
  rw [hRp, htp]
  simp only [Int.cast_natCast] at hθa ⊢
  rw [hθa, hχ]
  linear_combination (Complex.exp (-(2 * π * I * k * (a.val : ℂ) / n))
    * (toCoeffData n hn G hodd).B a (-(g : ZMod n)) * (Real.sqrt (d n) * F n G (pN g))) * hsgn

include hn hodd hg hgn in
/-- Lemma 8.1 in the form (8.3): for `v ≡ 2k - n(g+1) (mod 2n)` with `|v| Ω < n (Ω - g)`,
`û_{-g}(k) = -ω₂ e^{-πigZ/Ω} Γ_{-g/2}(Z)` with `Z = -Ωv/(2n)`. -/
theorem neg_column (k v : ℤ) (hv : (2 * n : ℤ) ∣ v - (2 * k - n * (g + 1)))
    (hvres : |(v : ℝ)| * (ω₁ n + ω₂ n) < n * (ω₁ n + ω₂ n - g)) :
    ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
        * (toCoeffData n hn G hodd).B a (-(g : ZMod n))
      = -(ω₂ n : ℂ) * Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n))
        * Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd0 := sqrt_d_ne_zero n
  have hFp := F_int_ne_zero n hn G (pN g)
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
  have hθn := theta_period_neg n hn hodd g k v hv
  obtain ⟨ε, hε0, hε1⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨hint0, hint1, hE1⟩ := neg_strip n hn G hodd g hg hgn (θL n v) hθ ε hε0 hε1
  obtain ⟨hJ1, hE3⟩ := neg_two_gamma n hn G g hg hgn v hvres ε hε0 hε1
  have hE2 := neg_line n hn G hodd g hg (θL n v) hθn ε hε0 hε1 hint0 hint1 hJ1
  have hE5 := neg_residue_sum n hn G hodd g hg hgn k v hv
  have hsin := two_sin_mul_γ_neg n hn G (pN g) (by simp only [pN]; omega)
  have hγ : G.γ (-((pN g : ℤ) : ℂ)) = G.γ g := by congr 1; simp [pN]
  rw [hγ] at hsin
  have hsqrt : (Real.sqrt (ω₁ n * ω₂ n) : ℂ) = ω₂ n * Real.sqrt (d n) := by
    rw [sqrt_Ω]; push_cast; ring
  have hsgn : (-1 : ℂ) ^ (pN g) = (-1) ^ g := by
    rw [← zpow_natCast]
    apply neg_one_zpow_congr
    simp only [pN]; push_cast
    generalize (g : ZMod 2) = y
    revert y; decide
  set û := ∑ a : ZMod n, ZMod.stdAddChar (-(a * (k : ZMod n)))
    * (toCoeffData n hn G hodd).B a (-(g : ZMod n)) with hû
  set LJ₁ := lineIntegral (fun z => Complex.exp (-I * (θL n v) * z) * J1 n G (pN g) 0 0 z) (-ε)
    with hLJ₁
  set Γ := Γr G.γ (ω₁ n) (ω₂ n) (rL g) (yL n v) with hΓ
  set e := Complex.exp (-π * I * g * yL n v / (ω₁ n * ω₂ n)) with he
  set s := Complex.sin (π * (pN g) / ω₁ n) with hs
  set Sres := ∑ a : ZMod n, (-1) ^ (a.val : ℤ) * Complex.exp (-I * (θL n v) * ((a.val : ℤ) : ℂ))
    * Rz n G (pN g) ((a.val : ℤ) : ℂ) with hSres
  have hC0 : (2 * π * I * ((-1 : ℂ) ^ g * Real.sqrt (d n) * F n G (pN g))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hd0) hFp)
  apply mul_left_cancel₀ hC0
  linear_combination (-(2 * π * I)) * hE5 - hE1 + hE2 + (-4 * π * s) * hE3
    + (-4 * π * s * I * e * Γ * G.γ g) * hsqrt
    + (-(2 * π * I) * (ω₂ n : ℂ) * Real.sqrt (d n) * e * Γ) * hsin
    + (-(2 * π * I) * (ω₂ n : ℂ) * Real.sqrt (d n) * e * Γ * F n G (pN g)) * hsgn

end neg

end Concrete
end HaagerupIzumi
