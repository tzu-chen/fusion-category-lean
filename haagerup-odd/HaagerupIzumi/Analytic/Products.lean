module

public import HaagerupIzumi.Analytic.Windows

@[expose] public section

/-!
# The two-ratio kernel (Section 6.2–6.3)

The kernel `K(z) = π e^{-iθz} R_p(z) R_q(z+s) / sin(π z)` of (6.4), the
four-gamma functions `J₁, J₂` of (6.5), the two-ratio difference identity
(Lemma 6.2), the residues of `K` at the integers, and its decay on strips.
-/

open Complex Real Filter Topology Set

namespace HaagerupIzumi
namespace Concrete

open Periods

variable (n : ℕ) (hn : 1 ≤ n) (G : HypGamma (ω₁ n) (ω₂ n))

/-! ### Trigonometric identities for integer labels -/

omit hn G in
lemma cos_int_mul_pi' (m : ℤ) : Complex.cos (m * π) = (-1) ^ m := by
  rw [show ((m : ℂ) * π) = (((m * π : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Real.cos_int_mul_pi]
  push_cast; ring

omit hn G in
lemma sin_add_int_mul_pi' (x : ℂ) (m : ℤ) : Complex.sin (x + m * π) = (-1) ^ m * Complex.sin x := by
  rw [Complex.sin_add, Complex.sin_int_mul_pi, cos_int_mul_pi']; ring

omit hn G in
lemma sin_sub_int_mul_pi' (x : ℂ) (m : ℤ) : Complex.sin (x - m * π) = (-1) ^ m * Complex.sin x := by
  rw [Complex.sin_sub, Complex.sin_int_mul_pi, cos_int_mul_pi']; ring

omit hn G in
lemma neg_one_zpow_sq (m : ℤ) : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul]
  exact Even.neg_one_zpow ⟨m, by ring⟩

omit hn G in
/-- The identity (2.6) for an integer label. -/
lemma trig_identity_int (p : ℤ) (z : ℂ) :
    (-1) ^ p * Complex.sin (π * (z - p) / ω₂ n) * Complex.sin (π * z / ω₁ n)
      - Complex.sin (π * (z - p) / ω₁ n) * Complex.sin (π * z / ω₂ n)
      = Complex.sin (π * p / ω₁ n) * Complex.sin (π * z) := by
  have hω₁ : (ω₁ n : ℂ) ≠ 0 := by exact_mod_cast (ω₁_pos n).ne'
  have hω₂ : (ω₂ n : ℂ) ≠ 0 := by exact_mod_cast (ω₂_pos n).ne'
  have hΩ : (ω₁ n : ℂ) * ω₂ n = ω₁ n + ω₂ n := by exact_mod_cast ω₁_mul_ω₂ n
  have e1 : (π : ℂ) * (z - p) / ω₂ n = (π * z / ω₂ n + π * p / ω₁ n) - p * π := by
    field_simp
    linear_combination (p : ℂ) * hΩ
  have e2 : (π : ℂ) * (z - p) / ω₁ n = π * z / ω₁ n - π * p / ω₁ n := by ring
  have e3 : (π : ℂ) * z = π * z / ω₁ n + π * z / ω₂ n := by
    field_simp
    linear_combination z * hΩ
  rw [e1, e2]
  conv_rhs => rw [e3]
  rw [sin_sub_int_mul_pi', Complex.sin_add, Complex.sin_sub, Complex.sin_add]
  have hsq := neg_one_zpow_sq p
  linear_combination (Complex.sin (π * z / ω₂ n) * Complex.cos (π * p / ω₁ n)
    * Complex.sin (π * z / ω₁ n) + Complex.cos (π * z / ω₂ n) * Complex.sin (π * p / ω₁ n)
    * Complex.sin (π * z / ω₁ n)) * hsq

/-! ### The single-ratio identities for integer labels -/

omit hn in
/-- `R_p(z) = γ(ω₂ + z - p) γ(ω₁ - z)` (reflection). -/
lemma Rz_refl (p : ℤ) (z : ℂ) (h3 : (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n))
    (h4 : (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n)) :
    Rz n G p z = G.γ ((ω₂ n : ℂ) + (z - p)) * G.γ (ω₁ n - z) := by
  have := G.reflect _ h3 h4
  rw [show (ω₁ n : ℂ) + ω₂ n - (ω₂ n + z) = ω₁ n - z by ring] at this
  rw [Rz, div_eq_mul_inv, inv_eq_of_mul_eq_one_right this]

omit hn in
/-- `R_p(z + n) = γ(ω₁ + z - p) γ(ω₂ - z)` (reflection). -/
lemma Rz_add_n (p : ℤ) (z : ℂ) (h5 : (ω₁ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n))
    (h6 : (ω₁ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n)) :
    Rz n G p (z + n) = G.γ ((ω₁ n : ℂ) + (z - p)) * G.γ (ω₂ n - z) := by
  have hω : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  have := G.reflect _ h5 h6
  rw [show (ω₁ n : ℂ) + ω₂ n - (ω₁ n + z) = ω₂ n - z by ring] at this
  rw [Rz, show (ω₂ n : ℂ) + (z + n - p) = ω₁ n + (z - p) by rw [hω]; ring,
    show (ω₂ n : ℂ) + (z + n) = ω₁ n + z by rw [hω]; ring, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right this]

omit hn in
/-- The single-ratio identity: `(-1)^p R_p(z+n) - R_p(z) = -4 sin(πp/ω₁) sin(πz) γ(z-p) γ(-z)`. -/
theorem ratio_shift (p : ℤ) (z : ℂ)
    (h1 : z - p ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : -z ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n)) (h4 : (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n))
    (h5 : (ω₁ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n)) (h6 : (ω₁ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n)) :
    (-1) ^ p * Rz n G p (z + n) - Rz n G p z
      = -4 * Complex.sin (π * p / ω₁ n) * Complex.sin (π * z) * G.γ (z - p) * G.γ (-z) := by
  rw [Rz_refl n G p z h3 h4, Rz_add_n n G p z h5 h6]
  have hA : G.γ ((ω₂ n : ℂ) + (z - p)) = 2 * Complex.sin (π * (z - p) / ω₁ n) * G.γ (z - p) := by
    rw [add_comm]; exact G.shift₂ _ h1
  have hA' : G.γ ((ω₁ n : ℂ) + (z - p)) = 2 * Complex.sin (π * (z - p) / ω₂ n) * G.γ (z - p) := by
    rw [add_comm]; exact G.shift₁ _ h1
  have hB : G.γ ((ω₁ n : ℂ) - z) = 2 * Complex.sin (π * (-z) / ω₂ n) * G.γ (-z) := by
    rw [show (ω₁ n : ℂ) - z = -z + ω₁ n by ring]; exact G.shift₁ _ h2
  have hB' : G.γ ((ω₂ n : ℂ) - z) = 2 * Complex.sin (π * (-z) / ω₁ n) * G.γ (-z) := by
    rw [show (ω₂ n : ℂ) - z = -z + ω₂ n by ring]; exact G.shift₂ _ h2
  rw [hA, hA', hB, hB', show (π : ℂ) * (-z) / ω₂ n = -(π * z / ω₂ n) by ring,
    show (π : ℂ) * (-z) / ω₁ n = -(π * z / ω₁ n) by ring, Complex.sin_neg, Complex.sin_neg]
  have htrig := trig_identity_int n p z
  linear_combination (-4 * G.γ (z - p) * G.γ (-z)) * htrig

/-! ### The two-ratio kernel and the four-gamma functions -/

/-- The kernel (6.4): `K(z) = π e^{-iθz} R_p(z) R_q(z+s) / sin(πz)`. -/
noncomputable def K2 (p q s : ℤ) (θ : ℝ) (z : ℂ) : ℂ :=
  π * Complex.exp (-I * θ * z) / Complex.sin (π * z) * (Rz n G p z * Rz n G q (z + s))

/-- `J₁(z) = γ(-z) γ(z-p) γ(ω₂-z-s) γ(ω₁+z+s-q)`, formula (6.5). -/
noncomputable def J1 (p q s : ℤ) (z : ℂ) : ℂ :=
  G.γ (-z) * G.γ (z - p) * G.γ (ω₂ n - z - s) * G.γ (ω₁ n + z + s - q)

/-- `J₂(z) = γ(ω₁-z) γ(ω₂+z-p) γ(-z-s) γ(z+s-q)`, formula (6.5). -/
noncomputable def J2 (p q s : ℤ) (z : ℂ) : ℂ :=
  G.γ (ω₁ n - z) * G.γ (ω₂ n + z - p) * G.γ (-z - s) * G.γ (z + s - q)

/-- The eleven regularity conditions under which the difference identity is proved. -/
def K2Cond (p q s : ℤ) (z : ℂ) : Prop :=
  z - p ∉ poleSet (ω₁ n) (ω₂ n) ∧ -z ∉ poleSet (ω₁ n) (ω₂ n) ∧
  (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n) ∧ (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n) ∧
  (ω₁ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n) ∧ (ω₁ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n) ∧
  (z + s) - q ∉ poleSet (ω₁ n) (ω₂ n) ∧ -(z + s) ∉ poleSet (ω₁ n) (ω₂ n) ∧
  (ω₂ n : ℂ) + (z + s) ∉ poleSet (ω₁ n) (ω₂ n) ∧ (ω₂ n : ℂ) + (z + s) ∉ zeroSet (ω₁ n) (ω₂ n) ∧
  (ω₁ n : ℂ) + (z + s) ∉ poleSet (ω₁ n) (ω₂ n) ∧ (ω₁ n : ℂ) + (z + s) ∉ zeroSet (ω₁ n) (ω₂ n) ∧
  Complex.sin (π * z) ≠ 0

omit hn in
/-- Lemma 6.2: the two-ratio difference identity. -/
theorem K2_shift (hodd : Odd n) (p q s : ℤ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -((-1) ^ (p + q))) (z : ℂ) (hc : K2Cond n p q s z) :
    K2 n G p q s θ (z + n) - K2 n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  have hexp : Complex.exp (-I * θ * (z + n)) = Complex.exp (-I * θ * z) * (-((-1) ^ (p + q))) := by
    rw [← hθ, ← Complex.exp_add]; congr 1; ring
  have hsin : Complex.sin (π * (z + n)) = -Complex.sin (π * z) := by
    rw [show (π : ℂ) * (z + n) = π * z + n * π by ring, sin_add_nat_mul_pi', hodd.neg_one_pow]
    ring
  have hsin_s : Complex.sin (π * (z + s)) = (-1) ^ s * Complex.sin (π * z) := by
    rw [show (π : ℂ) * (z + s) = π * z + s * π by ring, sin_add_int_mul_pi']
  have hp := ratio_shift n G p z h1 h2 h3 h4 h5 h6
  have hq := ratio_shift n G q (z + s) h7 h8 h9 h10 h11 h12
  have hRq := Rz_add_n n G q (z + s) h11 h12
  have hRp := Rz_refl n G p z h3 h4
  have hsq : ((-1 : ℂ) ^ q) ^ 2 = 1 := neg_one_zpow_sq q
  have hpq : (-1 : ℂ) ^ (p + q) = (-1) ^ p * (-1) ^ q :=
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) p q
  have hRq' : Rz n G q (z + s + n) = G.γ (ω₁ n + z + s - q) * G.γ (ω₂ n - z - s) := by
    rw [hRq]; congr 1 <;> congr 1 <;> ring
  have hRp' : Rz n G p z = G.γ (ω₂ n + z - p) * G.γ (ω₁ n - z) := by
    rw [hRp]; congr 1 <;> congr 1 <;> ring
  rw [hsin_s, neg_add', hRq'] at hq
  rw [hRp'] at hp
  unfold K2 J1 J2
  rw [show z + n + s = (z + s) + n by ring, hexp, hsin, hpq, hRq', hRp']
  field_simp
  linear_combination ((-1) ^ q * (G.γ (ω₁ n + z + s - q) * G.γ (ω₂ n - z - s))) * hp
    + (G.γ (ω₂ n + z - p) * G.γ (ω₁ n - z)) * hq

/-! ### Residues of the two-ratio kernel at the integers -/

omit hn G in
/-- The residue of `π / sin(π z)` at an integer `a` is `(-1)^a`. -/
lemma tendsto_pi_div_sin_int (a : ℤ) :
    Tendsto (fun z : ℂ => (z - a) * (π / Complex.sin (π * z))) (𝓝[≠] (a : ℂ)) (𝓝 ((-1) ^ a)) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (π * (-1) ^ a) (a : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) π (a : ℂ) := by
      simpa using (hasDerivAt_id (a : ℂ)).const_mul (π : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * a) * π) (a : ℂ) :=
      (Complex.hasDerivAt_sin ((π : ℂ) * a)).comp (a : ℂ) h1
    rw [show (π : ℂ) * a = a * π by ring, cos_int_mul_pi'] at h2
    convert h2 using 1; ring
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : (π : ℂ) * (-1) ^ a ≠ 0 := mul_ne_zero hπ (zpow_ne_zero _ (by norm_num))
  have hs' : Tendsto (fun z : ℂ => Complex.sin (π * z) / (z - a)) (𝓝[≠] (a : ℂ))
      (𝓝 (π * (-1) ^ a)) := by
    have hfa : Complex.sin ((π : ℂ) * a) = 0 := by
      rw [show (π : ℂ) * a = a * π by ring]; exact Complex.sin_int_mul_pi a
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [slope, vsub_eq_sub, smul_eq_mul, hfa, sub_zero]
    rw [div_eq_inv_mul]
  have := (hs'.inv₀ hne).const_mul (π : ℂ)
  have hsq := neg_one_zpow_sq a
  rw [show (π : ℂ) * ((π : ℂ) * (-1) ^ a)⁻¹ = (-1) ^ a by
    field_simp; linear_combination (-1 : ℂ) * hsq] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [inv_div]; ring

omit hn in
lemma Rz_continuousAt (p : ℤ) (w : ℂ) (hp1 : (ω₂ n : ℂ) + (w - p) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0) :
    ContinuousAt (Rz n G p) w := by
  unfold Rz
  refine ContinuousAt.div ?_ ?_ hne
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + (z - p)) (G.continuousAt _ hp1)
      (by fun_prop)
  · exact ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + z) (G.continuousAt _ hp2)
      (by fun_prop)

omit hn in
lemma Rz_differentiableAt (p : ℤ) (w : ℂ) (hp1 : (ω₂ n : ℂ) + (w - p) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0) :
    DifferentiableAt ℂ (Rz n G p) w := by
  unfold Rz
  refine DifferentiableAt.div ?_ ?_ hne
  · exact (G.differentiableAt _ hp1).comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + (z - p)) w)
  · exact (G.differentiableAt _ hp2).comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + z) w)

include hn in
lemma Rz_continuousAt_int (p a : ℤ) : ContinuousAt (Rz n G p) (a : ℂ) := by
  apply Rz_continuousAt
  · have := ω₂_add_int_not_pole n hn (a - p); push_cast at this; exact this
  · exact ω₂_add_int_not_pole n hn a
  · exact ω₂_add_int_ne_zero n hn G a

include hn in
/-- The residue of `K` at an integer `a`, (6.6). -/
theorem K2_residue_int (p q s : ℤ) (θ : ℝ) (a : ℤ) :
    HasResidue (K2 n G p q s θ) a
      ((-1) ^ a * Complex.exp (-I * θ * a) * (Rz n G p a * Rz n G q (a + s))) := by
  have h1 := tendsto_pi_div_sin_int a
  have hc1 := Rz_continuousAt_int n hn G p a
  have hc2 : ContinuousAt (fun z : ℂ => Rz n G q (z + s)) (a : ℂ) := by
    have := Rz_continuousAt_int n hn G q (a + s)
    push_cast at this
    exact ContinuousAt.comp (f := fun z : ℂ => z + s) this (by fun_prop)
  have h2 : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * (Rz n G p z * Rz n G q (z + s)))
      (𝓝[≠] (a : ℂ)) (𝓝 (Complex.exp (-I * θ * a) * (Rz n G p a * Rz n G q (a + s)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul (hc1.mul hc2)
  unfold HasResidue
  have := h1.mul h2
  rw [← mul_assoc] at this
  refine this.congr' ?_
  filter_upwards with z
  unfold K2; ring

/-! ### Regularity of the kernel -/

omit hn in
lemma K2_differentiableAt (p q s : ℤ) (θ : ℝ) (w : ℂ)
    (hp1 : (ω₂ n : ℂ) + (w - p) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + w ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + w) ≠ 0)
    (hq1 : (ω₂ n : ℂ) + ((w + s) - q) ∉ poleSet (ω₁ n) (ω₂ n))
    (hq2 : (ω₂ n : ℂ) + (w + s) ∉ poleSet (ω₁ n) (ω₂ n)) (hne' : G.γ ((ω₂ n : ℂ) + (w + s)) ≠ 0)
    (hsin : Complex.sin (π * w) ≠ 0) : DifferentiableAt ℂ (K2 n G p q s θ) w := by
  unfold K2
  refine DifferentiableAt.mul (DifferentiableAt.div ?_ ?_ hsin) ?_
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => (π : ℂ) * Complex.exp (-I * θ * z)).differentiableAt
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.sin (π * z)).differentiableAt
  · refine (Rz_differentiableAt n G p w hp1 hp2 hne).mul ?_
    exact (Rz_differentiableAt n G q (w + s) hq1 hq2 hne').comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z + s) w)

omit hn in
lemma K2_shift_continuousAt (p q s : ℤ) (θ : ℝ) (w : ℂ)
    (hp1 : (ω₂ n : ℂ) + ((w + n) - p) ∉ poleSet (ω₁ n) (ω₂ n))
    (hp2 : (ω₂ n : ℂ) + (w + n) ∉ poleSet (ω₁ n) (ω₂ n)) (hne : G.γ ((ω₂ n : ℂ) + (w + n)) ≠ 0)
    (hq1 : (ω₂ n : ℂ) + ((w + n + s) - q) ∉ poleSet (ω₁ n) (ω₂ n))
    (hq2 : (ω₂ n : ℂ) + (w + n + s) ∉ poleSet (ω₁ n) (ω₂ n))
    (hne' : G.γ ((ω₂ n : ℂ) + (w + n + s)) ≠ 0)
    (hsin : Complex.sin (π * (w + n)) ≠ 0) :
    ContinuousAt (fun z => K2 n G p q s θ (z + n)) w := by
  have hR1 := Rz_continuousAt n G p (w + n) hp1 hp2 hne
  have hR2 := Rz_continuousAt n G q (w + n + s) hq1 hq2 hne'
  have hR1' : ContinuousAt (fun z : ℂ => Rz n G p (z + n)) w :=
    ContinuousAt.comp (f := fun z : ℂ => z + n) hR1 (by fun_prop)
  have hR2' : ContinuousAt (fun z : ℂ => Rz n G q (z + n + s)) w :=
    ContinuousAt.comp (f := fun z : ℂ => z + n + s) hR2 (by fun_prop)
  simp only [K2]
  refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ hsin) (hR1'.mul hR2')
  · exact (by fun_prop : Continuous fun z : ℂ => (π : ℂ) * Complex.exp (-I * θ * (z + n))).continuousAt
  · exact (by fun_prop : Continuous fun z : ℂ => Complex.sin (π * (z + n))).continuousAt

omit hn in
/-- The difference identity holds on a punctured neighbourhood of every point. -/
lemma K2_shift_eventually (hodd : Odd n) (p q s : ℤ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -((-1) ^ (p + q))) (w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, K2 n G p q s θ (z + n) - K2 n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hP := eventually_not_mem_poleSet hω₁ hω₂
  have hZ := eventually_not_mem_zeroSet hω₁ hω₂
  have e1 := (tendsto_punctured_of_injective (continuous_sub_right (p : ℂ)) sub_left_injective
    w).eventually (hP (w - p))
  have e2 := (tendsto_punctured_of_injective continuous_neg neg_injective w).eventually
    (hP (-w))
  have e3 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) w).eventually (hP ((ω₂ n : ℂ) + w))
  have e4 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) w).eventually (hZ ((ω₂ n : ℂ) + w))
  have e5 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) w).eventually (hP ((ω₁ n : ℂ) + w))
  have e6 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) w).eventually (hZ ((ω₁ n : ℂ) + w))
  have e7 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => z + s - q)
    (fun x y hxy => by simpa using hxy) w).eventually (hP (w + s - q))
  have e8 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => -(z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP (-(w + s)))
  have e9 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP ((ω₂ n : ℂ) + (w + s)))
  have e10 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hZ ((ω₂ n : ℂ) + (w + s)))
  have e11 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₁ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP ((ω₁ n : ℂ) + (w + s)))
  have e12 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₁ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hZ ((ω₁ n : ℂ) + (w + s)))
  have e13 := eventually_sin_ne_zero w
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13] with z h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 h11 h12 h13
  exact K2_shift n G hodd p q s θ hθ z ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-! ### Decay of the kernel on strips (Step 2 of Proposition 6.3) -/

omit hn in
/-- The ratio bound for `R_p` with an integer label, on a closed strip: for `|Im z| ≥ T`,
`‖R_p(z)‖ ≤ C exp(-π p |Im z| / Ω)`. -/
lemma Rz_bound (p : ℤ) (a b : ℝ) :
    ∃ C T : ℝ, 0 < T ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
      ‖Rz n G p z‖ ≤ C * Real.exp (-(π * p / (ω₁ n * ω₂ n)) * |z.im|) := by
  obtain ⟨C, T, hT, hC⟩ := G.ratio_bound (-p) (a + ω₂ n) (b + ω₂ n)
  refine ⟨C, T, hT, ?_⟩
  intro z hza hzb hzT
  have him : z.im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hzT; linarith
  set z' : ℂ := (ω₂ n : ℂ) + z with hz'
  have hz'im : z'.im = z.im := by simp [hz']
  have hz're : z'.re = ω₂ n + z.re := by simp [hz']
  have hp1 : z' ∉ poleSet (ω₁ n) (ω₂ n) := not_mem_poleSet_of_im_ne_zero (by rw [hz'im]; exact him)
  have hp2 : z' + ((-p : ℝ) : ℂ) ∉ poleSet (ω₁ n) (ω₂ n) :=
    not_mem_poleSet_of_im_ne_zero (by simp [hz'im, him])
  have hz'0 : G.γ z' ≠ 0 :=
    G.ne_zero _ hp1 (not_mem_zeroSet_of_im_ne_zero (by rw [hz'im]; exact him))
  have hratio := hC z' (by rw [hz're]; linarith) (by rw [hz're]; linarith) (by rw [hz'im]; exact hzT)
    hp1 hp2
  rw [hz'im] at hratio
  unfold Rz
  rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hz'0)]
  have : (ω₂ n : ℂ) + (z - p) = z' + ((-p : ℝ) : ℂ) := by rw [hz']; push_cast; ring
  rw [this]
  have hE : Real.exp (π * (-(p : ℝ)) * |z.im| / (ω₁ n * ω₂ n))
      = Real.exp (-(π * p / (ω₁ n * ω₂ n)) * |z.im|) := by congr 1; ring
  rw [hE] at hratio
  exact hratio

omit hn in
/-- Step 2: exponential bounds for `K` on a closed strip, with decay rate
`π - |θ| + π (p + q) / Ω`. -/
theorem K2_bound (p q s : ℤ) (θ : ℝ) (a b : ℝ) :
    ∃ M T : ℝ, 0 < T ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
      ‖K2 n G p q s θ z‖ ≤ M * Real.exp (-(π - |θ| + π * (p + q) / (ω₁ n * ω₂ n)) * |z.im|) := by
  obtain ⟨C₁, T₁, hT₁, hC₁⟩ := Rz_bound n G p a b
  obtain ⟨C₂, T₂, hT₂, hC₂⟩ := Rz_bound n G q (a + s) (b + s)
  refine ⟨4 * π * C₁ * C₂, max (max T₁ T₂) 1, lt_max_of_lt_right one_pos, ?_⟩
  intro z hza hzb hzT
  have hT1' : T₁ ≤ |z.im| := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hzT)
  have hT2' : T₂ ≤ |z.im| := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hzT)
  have h1' : 1 ≤ |z.im| := le_trans (le_max_right _ _) hzT
  have hR1 := hC₁ z hza hzb hT1'
  have hzs_re : (z + s).re = z.re + s := by simp
  have hzs_im : (z + s).im = z.im := by simp
  have hR2 := hC₂ (z + s) (by rw [hzs_re]; linarith) (by rw [hzs_re]; linarith) (by rw [hzs_im]; exact hT2')
  rw [hzs_im] at hR2
  have hexp : ‖Complex.exp (-I * θ * z)‖ ≤ Real.exp (|θ| * |z.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (-I * θ * z).re = θ * z.im := by simp
    rw [this]
    calc θ * z.im ≤ |θ * z.im| := le_abs_self _
      _ = |θ| * |z.im| := abs_mul _ _
  have hsin : Real.exp (π * |z.im|) / 4 ≤ ‖Complex.sin (π * z)‖ := by
    have hpi := Real.pi_gt_three
    have := norm_sin_ge ((π : ℂ) * z) (by
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith)
    simpa [abs_mul, abs_of_pos Real.pi_pos] using this
  have hsin0 : Complex.sin (π * z) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsin
    have := Real.exp_pos (π * |z.im|); linarith
  have hC₁0 : 0 ≤ C₁ := by
    by_contra hneg; push_neg at hneg
    have : C₁ * Real.exp (-(π * p / (ω₁ n * ω₂ n)) * |z.im|) < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith [norm_nonneg (Rz n G p z)]
  have hC₂0 : 0 ≤ C₂ := by
    by_contra hneg; push_neg at hneg
    have : C₂ * Real.exp (-(π * q / (ω₁ n * ω₂ n)) * |z.im|) < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith [norm_nonneg (Rz n G q (z + s))]
  have hpos4 : 0 < Real.exp (π * |z.im|) / 4 := by positivity
  unfold K2
  rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc π * ‖Complex.exp (-I * θ * z)‖ / ‖Complex.sin (π * z)‖ * (‖Rz n G p z‖ * ‖Rz n G q (z + s)‖)
      ≤ π * Real.exp (|θ| * |z.im|) / (Real.exp (π * |z.im|) / 4)
        * ((C₁ * Real.exp (-(π * p / (ω₁ n * ω₂ n)) * |z.im|))
          * (C₂ * Real.exp (-(π * q / (ω₁ n * ω₂ n)) * |z.im|))) := by
        gcongr
    _ = 4 * π * C₁ * C₂ * Real.exp (-(π - |θ| + π * (p + q) / (ω₁ n * ω₂ n)) * |z.im|) := by
        have hω : ω₁ n * ω₂ n ≠ 0 := (mul_pos (ω₁_pos n) (ω₂_pos n)).ne'
        rw [show Real.exp (-(π - |θ| + π * (p + q) / (ω₁ n * ω₂ n)) * |z.im|)
            = Real.exp (|θ| * |z.im|) / Real.exp (π * |z.im|)
              * (Real.exp (-(π * p / (ω₁ n * ω₂ n)) * |z.im|)
                * Real.exp (-(π * q / (ω₁ n * ω₂ n)) * |z.im|)) by
          rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]; congr 1; field_simp; ring]
        field_simp
        try ring

/-! ### Choosing a line that avoids the poles -/

omit hn G in
/-- The values `c + r ω₁ + s ω₂` below a bound form a finite set. -/
lemma finite_lattice_le (c M : ℝ) :
    {ε : ℝ | ∃ r s : ℕ, ε = c + r * ω₁ n + s * ω₂ n ∧ ε ≤ M}.Finite := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hsub : {ε : ℝ | ∃ r s : ℕ, ε = c + r * ω₁ n + s * ω₂ n ∧ ε ≤ M} ⊆
      (fun p : ℕ × ℕ => c + (p.1 : ℝ) * ω₁ n + (p.2 : ℝ) * ω₂ n) ''
        ((Finset.range (⌈(M - c) / ω₁ n⌉₊ + 1) ×ˢ Finset.range (⌈(M - c) / ω₂ n⌉₊ + 1) :
          Finset (ℕ × ℕ))) := by
    rintro ε ⟨r, s, rfl, hM⟩
    refine ⟨(r, s), ?_, rfl⟩
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    have hr : (r : ℝ) ≤ (M - c) / ω₁ n := by
      rw [le_div_iff₀ hω₁]; nlinarith [mul_nonneg (Nat.cast_nonneg s) hω₂.le]
    have hs : (s : ℝ) ≤ (M - c) / ω₂ n := by
      rw [le_div_iff₀ hω₂]; nlinarith [mul_nonneg (Nat.cast_nonneg r) hω₁.le]
    have hr' : (r : ℝ) ≤ ⌈(M - c) / ω₁ n⌉₊ := hr.trans (Nat.le_ceil _)
    have hs' : (s : ℝ) ≤ ⌈(M - c) / ω₂ n⌉₊ := hs.trans (Nat.le_ceil _)
    exact ⟨Nat.lt_succ_of_le (by exact_mod_cast hr'), Nat.lt_succ_of_le (by exact_mod_cast hs')⟩
  exact ((Finset.finite_toSet _).image _).subset hsub

omit hn G in
/-- The values `c - (r ω₁ + s ω₂)` above a bound form a finite set. -/
lemma finite_lattice_ge (c M : ℝ) :
    {ε : ℝ | ∃ r s : ℕ, ε = c - (r * ω₁ n + s * ω₂ n) ∧ M ≤ ε}.Finite := by
  have := finite_lattice_le n (-c) (-M)
  have hsub : {ε : ℝ | ∃ r s : ℕ, ε = c - (r * ω₁ n + s * ω₂ n) ∧ M ≤ ε} ⊆
      (fun x : ℝ => -x) '' {ε : ℝ | ∃ r s : ℕ, ε = -c + r * ω₁ n + s * ω₂ n ∧ ε ≤ -M} := by
    rintro ε ⟨r, s, rfl, hM⟩
    exact ⟨-(c - (r * ω₁ n + s * ω₂ n)), ⟨r, s, by ring, by linarith⟩, by ring⟩
  exact (this.image _).subset hsub

omit hn G in
/-- There is `ε ∈ (0, ε₀)` such that the line `Re z = -ε` avoids all the lattices
`c + (r ω₁ + s ω₂)` and `c - (r ω₁ + s ω₂)` with `c` in a finite set. -/
lemma exists_eps (ε₀ : ℝ) (hε₀ : 0 < ε₀) (cs : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧
      (∀ c ∈ cs, ∀ r s : ℕ, ε ≠ c + (r * ω₁ n + s * ω₂ n)) ∧
      (∀ c ∈ cs, ∀ r s : ℕ, ε ≠ c - (r * ω₁ n + s * ω₂ n)) := by
  classical
  set B : Set ℝ := (⋃ c ∈ cs, {ε : ℝ | ∃ r s : ℕ, ε = c + r * ω₁ n + s * ω₂ n ∧ ε ≤ ε₀})
    ∪ (⋃ c ∈ cs, {ε : ℝ | ∃ r s : ℕ, ε = c - (r * ω₁ n + s * ω₂ n) ∧ 0 ≤ ε}) with hB
  have hBfin : B.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact Set.Finite.biUnion cs.finite_toSet (fun c _ => finite_lattice_le n c ε₀)
    · exact Set.Finite.biUnion cs.finite_toSet (fun c _ => finite_lattice_ge n c 0)
  obtain ⟨ε, hε, hεB⟩ := (Set.Ioo_infinite hε₀).exists_notMem_finite hBfin
  refine ⟨ε, hε.1, hε.2, ?_, ?_⟩
  · intro c hc r s heq
    apply hεB
    refine Or.inl (Set.mem_iUnion₂.2 ⟨c, hc, r, s, by rw [heq]; ring, ?_⟩)
    linarith [hε.2]
  · intro c hc r s heq
    apply hεB
    exact Or.inr (Set.mem_iUnion₂.2 ⟨c, hc, r, s, heq, hε.1.le⟩)

omit hn G in
/-- Points of the line `Re z = -ε` are not in `c + poleSet` when `ε ≠ c + (r ω₁ + s ω₂)`. -/
lemma line_not_pole (c ε t : ℝ) (hε : ∀ r s : ℕ, ε ≠ c + (r * ω₁ n + s * ω₂ n)) :
    (c : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ poleSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have hre := congrArg Complex.re hrs
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    neg_re, natCast_re, natCast_im, add_zero] at hre
  exact hε r s (by linarith)

omit hn G in
/-- Points of the line `Re z = -ε` are not in `c + zeroSet` when
`ε ≠ (c - ω₁ - ω₂) - (r ω₁ + s ω₂)`. -/
lemma line_not_zero (c ε t : ℝ) (hε : ∀ r s : ℕ, ε ≠ (c - ω₁ n - ω₂ n) - (r * ω₁ n + s * ω₂ n)) :
    (c : ℂ) + (((-ε : ℝ) : ℂ) + t * I) ∉ zeroSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have hre := congrArg Complex.re hrs
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    natCast_re, natCast_im, add_zero] at hre
  exact hε r s (by linarith)

omit hn G in
/-- Points `-(c + z)` for `z` on the line `Re z = -ε` are not poles when
`ε ≠ c - (r ω₁ + s ω₂)`. -/
lemma line_neg_not_pole (c ε t : ℝ) (hε : ∀ r s : ℕ, ε ≠ c - (r * ω₁ n + s * ω₂ n)) :
    -((c : ℂ) + (((-ε : ℝ) : ℂ) + t * I)) ∉ poleSet (ω₁ n) (ω₂ n) := by
  rintro ⟨r, s, hrs⟩
  have hre := congrArg Complex.re hrs
  simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, natCast_re, natCast_im, add_zero] at hre
  exact hε r s (by linarith)

/-! ### Residues at the crossed poles -/

omit hn in
/-- The residue of `K` at a crossed pole, from the difference identity. -/
theorem K2_residue_of_shift (p q s : ℤ) (θ : ℝ) (w ρ₁ ρ₂ : ℂ)
    (hev : ∀ᶠ z in 𝓝[≠] w, K2 n G p q s θ (z + n) - K2 n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z))
    (hc : ContinuousAt (fun z => K2 n G p q s θ (z + n)) w)
    (h1 : HasResidueGen (fun z => Complex.exp (-I * θ * z) * J1 n G p q s z) w ρ₁)
    (h2 : HasResidueGen (fun z => Complex.exp (-I * θ * z) * J2 n G p q s z) w ρ₂) :
    HasResidueGen (K2 n G p q s θ) w
      (4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * ρ₁
        + (-1) ^ s * Complex.sin (π * q / ω₁ n) * ρ₂)) := by
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  refine ⟨4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * c₁
    + (-1) ^ s * Complex.sin (π * q / ω₁ n) * c₂), ?_⟩
  have hlim0 : Tendsto (fun z : ℂ => (z - w) * K2 n G p q s θ (z + n)) (𝓝[≠] w) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => (z - w) * K2 n G p q s θ (z + n)) (𝓝 w)
        (𝓝 ((w - w) * K2 n G p q s θ (w + n))) :=
      ((continuous_id.sub continuous_const).continuousAt).mul hc
    simp only [sub_self, zero_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have key := hlim0.add ((hc₁.const_mul (4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n)))).add
    (hc₂.const_mul (4 * π * ((-1) ^ s * Complex.sin (π * q / ω₁ n)))))
  simp only [zero_add] at key
  have e : 4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * ρ₁
      + (-1) ^ s * Complex.sin (π * q / ω₁ n) * ρ₂)
      = 4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n)) * ρ₁
        + 4 * π * ((-1) ^ s * Complex.sin (π * q / ω₁ n)) * ρ₂ := by ring
  rw [e]
  refine key.congr' ?_
  filter_upwards [hev] with z hz
  have : K2 n G p q s θ z = K2 n G p q s θ (z + n) + 4 * π * Complex.exp (-I * θ * z)
      * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
        + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
    linear_combination -hz
  rw [this]; ring

omit hn in
/-- The residue function of `e^{-iθz} J₁` at a pole of `γ(z - p)`. -/
noncomputable def ρJ1 (p q s : ℤ) (θ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-I * θ * w) * G.γ (-w) * G.residue (w - p) * G.γ (ω₂ n - w - s)
    * G.γ (ω₁ n + w + s - q)

omit hn in
/-- The residue function of `e^{-iθz} J₂` at a pole of `γ(ω₂ + z - p)`. -/
noncomputable def ρJ2 (p q s : ℤ) (θ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.residue (ω₂ n + w - p) * G.γ (-w - s)
    * G.γ (w + s - q)

omit hn in
theorem J1_residue (p q s : ℤ) (θ : ℝ) (w : ℂ) (hp : w - p ∈ poleSet (ω₁ n) (ω₂ n))
    (h1 : -w ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : (ω₂ n : ℂ) - w - s ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : (ω₁ n : ℂ) + w + s - q ∉ poleSet (ω₁ n) (ω₂ n)) :
    HasResidue (fun z => Complex.exp (-I * θ * z) * J1 n G p q s z) w (ρJ1 n G p q s θ w) := by
  have hA : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * G.γ (-z) * G.γ (ω₂ n - z - s)
      * G.γ (ω₁ n + z + s - q)) (𝓝[≠] w)
      (𝓝 (Complex.exp (-I * θ * w) * G.γ (-w) * G.γ (ω₂ n - w - s) * G.γ (ω₁ n + w + s - q))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    refine (((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul
      (ContinuousAt.comp (f := fun z : ℂ => -z) (G.continuousAt _ h1) (by fun_prop))).mul
      (ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) - z - s) (G.continuousAt _ h2)
        (by fun_prop)) |>.mul
      (ContinuousAt.comp (f := fun z : ℂ => (ω₁ n : ℂ) + z + s - q) (G.continuousAt _ h3)
        (by fun_prop))
  have hB : Tendsto (fun z : ℂ => ((z - p) - (w - p)) * G.γ (z - p)) (𝓝[≠] w)
      (𝓝 (G.residue (w - p))) :=
    (G.hasResidue (w - p) hp).comp
      (tendsto_punctured_of_injective (continuous_sub_right (p : ℂ)) sub_left_injective w)
  unfold HasResidue
  rw [show ρJ1 n G p q s θ w = Complex.exp (-I * θ * w) * G.γ (-w) * G.γ (ω₂ n - w - s)
    * G.γ (ω₁ n + w + s - q) * G.residue (w - p) by unfold ρJ1; ring]
  refine (hA.mul hB).congr' ?_
  filter_upwards with z
  simp only [J1]; ring

omit hn in
theorem J2_residue (p q s : ℤ) (θ : ℝ) (w : ℂ) (hp : (ω₂ n : ℂ) + w - p ∈ poleSet (ω₁ n) (ω₂ n))
    (h1 : (ω₁ n : ℂ) - w ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : -w - s ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : w + s - q ∉ poleSet (ω₁ n) (ω₂ n)) :
    HasResidue (fun z => Complex.exp (-I * θ * z) * J2 n G p q s z) w (ρJ2 n G p q s θ w) := by
  have hA : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * G.γ (ω₁ n - z) * G.γ (-z - s)
      * G.γ (z + s - q)) (𝓝[≠] w)
      (𝓝 (Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.γ (-w - s) * G.γ (w + s - q))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    refine (((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul
      (ContinuousAt.comp (f := fun z : ℂ => (ω₁ n : ℂ) - z) (G.continuousAt _ h1) (by fun_prop))).mul
      (ContinuousAt.comp (f := fun z : ℂ => -z - s) (G.continuousAt _ h2) (by fun_prop)) |>.mul
      (ContinuousAt.comp (f := fun z : ℂ => z + s - q) (G.continuousAt _ h3) (by fun_prop))
  have hB : Tendsto (fun z : ℂ => ((ω₂ n + z - p) - (ω₂ n + w - p)) * G.γ (ω₂ n + z - p)) (𝓝[≠] w)
      (𝓝 (G.residue (ω₂ n + w - p))) :=
    (G.hasResidue (ω₂ n + w - p) hp).comp
      (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + z - p)
        (fun x y hxy => by simpa using hxy) w)
  unfold HasResidue
  rw [show ρJ2 n G p q s θ w = Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.γ (-w - s)
    * G.γ (w + s - q) * G.residue (ω₂ n + w - p) by unfold ρJ2; ring]
  refine (hA.mul hB).congr' ?_
  filter_upwards with z
  simp only [J2]; ring

omit hn in
/-- The residue function of `e^{-iθz} J₂` at a pole of the last factor `γ(z + s - q)`. -/
noncomputable def ρJ2' (p q s : ℤ) (θ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.γ (ω₂ n + w - p) * G.γ (-w - s)
    * G.residue (w + s - q)

omit hn in
theorem J2_residue' (p q s : ℤ) (θ : ℝ) (w : ℂ) (hp : w + s - q ∈ poleSet (ω₁ n) (ω₂ n))
    (h1 : (ω₁ n : ℂ) - w ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : (ω₂ n : ℂ) + w - p ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : -w - s ∉ poleSet (ω₁ n) (ω₂ n)) :
    HasResidue (fun z => Complex.exp (-I * θ * z) * J2 n G p q s z) w (ρJ2' n G p q s θ w) := by
  have hA : Tendsto (fun z : ℂ => Complex.exp (-I * θ * z) * G.γ (ω₁ n - z) * G.γ (ω₂ n + z - p)
      * G.γ (-z - s)) (𝓝[≠] w)
      (𝓝 (Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.γ (ω₂ n + w - p) * G.γ (-w - s))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    refine (((Complex.continuous_exp.comp (by fun_prop : Continuous fun z : ℂ => -I * θ * z))
      |>.continuousAt).mul
      (ContinuousAt.comp (f := fun z : ℂ => (ω₁ n : ℂ) - z) (G.continuousAt _ h1) (by fun_prop))).mul
      (ContinuousAt.comp (f := fun z : ℂ => (ω₂ n : ℂ) + z - p) (G.continuousAt _ h2)
        (by fun_prop)) |>.mul
      (ContinuousAt.comp (f := fun z : ℂ => -z - s) (G.continuousAt _ h3) (by fun_prop))
  have hB : Tendsto (fun z : ℂ => ((z + s - q) - (w + s - q)) * G.γ (z + s - q)) (𝓝[≠] w)
      (𝓝 (G.residue (w + s - q))) :=
    (G.hasResidue (w + s - q) hp).comp
      (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => z + s - q)
        (fun x y hxy => by simpa using hxy) w)
  unfold HasResidue
  rw [show ρJ2' n G p q s θ w = Complex.exp (-I * θ * w) * G.γ (ω₁ n - w) * G.γ (ω₂ n + w - p)
    * G.γ (-w - s) * G.residue (w + s - q) by unfold ρJ2'; ring]
  refine (hA.mul hB).congr' ?_
  filter_upwards with z
  simp only [J2]; ring

/-! ### Gamma factors as `AtMostSimple` factors -/

omit hn in
/-- `z ↦ γ(c + z)` is differentiable on a punctured neighbourhood of every point. -/
lemma eventually_differentiableAt_γ_add (c w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ (fun z => G.γ (c + z)) z := by
  have := (tendsto_punctured_of_injective (continuous_const_add c) (add_right_injective c)
    w).eventually (eventually_not_mem_poleSet (ω₁_pos n) (ω₂_pos n) (c + w))
  filter_upwards [this] with z hz
  exact (G.differentiableAt _ hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c + z) z)

omit hn in
/-- `z ↦ γ(c - z)` is differentiable on a punctured neighbourhood of every point. -/
lemma eventually_differentiableAt_γ_sub (c w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ (fun z => G.γ (c - z)) z := by
  have := (tendsto_punctured_of_injective (continuous_const.sub continuous_id) sub_right_injective
    w).eventually (eventually_not_mem_poleSet (ω₁_pos n) (ω₂_pos n) (c - w))
  filter_upwards [this] with z hz
  exact (G.differentiableAt _ hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c - z) z)

omit hn in
/-- `z ↦ γ(c + z)` has at most a simple pole at every point. -/
lemma atMostSimple_γ_add (c w : ℂ) : AtMostSimple (fun z => G.γ (c + z)) w := by
  by_cases hw : c + w ∈ poleSet (ω₁ n) (ω₂ n)
  · refine Or.inr ⟨⟨G.residue (c + w), ?_⟩, eventually_differentiableAt_γ_add n G c w⟩
    have := (G.hasResidue (c + w) hw).comp
      (tendsto_punctured_of_injective (continuous_const_add c) (add_right_injective c) w)
    unfold HasResidue
    refine this.congr' ?_
    filter_upwards with z
    simp only [Function.comp]; ring
  · exact Or.inl ((G.differentiableAt _ hw).comp w
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c + z) w))

omit hn in
lemma differentiableAt_γ_add (c w : ℂ) (hw : c + w ∉ poleSet (ω₁ n) (ω₂ n)) :
    DifferentiableAt ℂ (fun z => G.γ (c + z)) w :=
  (G.differentiableAt _ hw).comp w (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c + z) w)

omit hn in
lemma differentiableAt_γ_sub (c w : ℂ) (hw : c - w ∉ poleSet (ω₁ n) (ω₂ n)) :
    DifferentiableAt ℂ (fun z => G.γ (c - z)) w :=
  (G.differentiableAt _ hw).comp w (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => c - z) w)

/-! ### Translation of line integrals and residues -/

omit n hn G in
/-- `∫ f(z - c)` along `Re z = σ` equals `∫ f` along `Re z = σ - c`. -/
lemma lineIntegral_comp_sub (f : ℂ → ℂ) (σ c : ℝ) :
    lineIntegral (fun z => f (z - c)) σ = lineIntegral f (σ - c) := by
  unfold lineIntegral
  congr 1; funext t; congr 2; push_cast; ring

omit n hn G in
lemma lineIntegral_const_mul (f : ℂ → ℂ) (σ : ℝ) (a : ℂ) :
    lineIntegral (fun z => a * f z) σ = a * lineIntegral f σ := by
  unfold lineIntegral
  rw [← MeasureTheory.integral_const_mul]
  congr 1; funext t; ring

omit n hn G in
lemma hasResidueGen_comp_sub {f : ℂ → ℂ} {w ρ : ℂ} (h : HasResidueGen f w ρ) (c : ℂ) :
    HasResidueGen (fun z => f (z - c)) (w + c) ρ := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hmap := tendsto_punctured_of_injective (continuous_sub_right c) sub_left_injective (w + c)
  rw [show w + c - c = w by ring] at hmap
  have := hk.comp hmap
  refine this.congr' ?_
  filter_upwards with z
  simp only [Function.comp]; ring_nf

omit n hn G in
lemma hasResidueGen_const_mul {f : ℂ → ℂ} {w ρ : ℂ} (h : HasResidueGen f w ρ) (a : ℂ) :
    HasResidueGen (fun z => a * f z) w (a * ρ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨a * k, ?_⟩
  have := hk.const_mul a
  refine this.congr' ?_
  filter_upwards with z
  ring

omit n hn G in
lemma hasResidueGen_congr_fun {f g : ℂ → ℂ} {w ρ : ℂ} (h : HasResidueGen f w ρ)
    (hfg : ∀ z, f z = g z) : HasResidueGen g w ρ := by
  have : f = g := funext hfg
  rw [← this]; exact h

/-! ### The kernel in product form

`K2` has removable singularities (with junk values) where `γ(ω₂ + z + s)` has a pole; the
product form `K2'` obtained by reflection is the function used in the residue theorem. -/

/-- The kernel in product form: `π e^{-iθz} / sin(πz) · γ(ω₂+z-p) γ(ω₁-z) · γ(ω₂+z+s-q) γ(ω₁-z-s)`. -/
noncomputable def K2' (p q s : ℤ) (θ : ℝ) (z : ℂ) : ℂ :=
  π * Complex.exp (-I * θ * z) / Complex.sin (π * z)
    * ((G.γ (ω₂ n + z - p) * G.γ (ω₁ n - z)) * (G.γ (ω₂ n + (z + s) - q) * G.γ (ω₁ n - (z + s))))

omit hn in
lemma K2'_eq_K2 (p q s : ℤ) (θ : ℝ) (z : ℂ)
    (h3 : (ω₂ n : ℂ) + z ∉ poleSet (ω₁ n) (ω₂ n)) (h4 : (ω₂ n : ℂ) + z ∉ zeroSet (ω₁ n) (ω₂ n))
    (h9 : (ω₂ n : ℂ) + (z + s) ∉ poleSet (ω₁ n) (ω₂ n))
    (h10 : (ω₂ n : ℂ) + (z + s) ∉ zeroSet (ω₁ n) (ω₂ n)) :
    K2' n G p q s θ z = K2 n G p q s θ z := by
  unfold K2' K2
  rw [Rz_refl n G p z h3 h4, Rz_refl n G q (z + s) h9 h10]
  congr 2
  · congr 2; ring
  · congr 2; ring

omit hn in
/-- Lemma 6.2 for the product form. -/
theorem K2'_shift (hodd : Odd n) (p q s : ℤ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -((-1) ^ (p + q))) (z : ℂ) (hc : K2Cond n p q s z) :
    K2' n G p q s θ (z + n) - K2' n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  have hω : (ω₁ n : ℂ) = n + ω₂ n := by rw [ω₁_eq]; push_cast; ring
  rw [K2'_eq_K2 n G p q s θ z h3 h4 h9 h10, K2'_eq_K2 n G p q s θ (z + n)
    (by rw [show (ω₂ n : ℂ) + (z + n) = ω₁ n + z by rw [hω]; ring]; exact h5)
    (by rw [show (ω₂ n : ℂ) + (z + n) = ω₁ n + z by rw [hω]; ring]; exact h6)
    (by rw [show (ω₂ n : ℂ) + (z + n + s) = ω₁ n + (z + s) by rw [hω]; ring]; exact h11)
    (by rw [show (ω₂ n : ℂ) + (z + n + s) = ω₁ n + (z + s) by rw [hω]; ring]; exact h12)]
  exact K2_shift n G hodd p q s θ hθ z ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

omit hn in
lemma K2'_shift_eventually (hodd : Odd n) (p q s : ℤ) (θ : ℝ)
    (hθ : Complex.exp (-I * θ * n) = -((-1) ^ (p + q))) (w : ℂ) :
    ∀ᶠ z in 𝓝[≠] w, K2' n G p q s θ (z + n) - K2' n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hP := eventually_not_mem_poleSet hω₁ hω₂
  have hZ := eventually_not_mem_zeroSet hω₁ hω₂
  have e1 := (tendsto_punctured_of_injective (continuous_sub_right (p : ℂ)) sub_left_injective
    w).eventually (hP (w - p))
  have e2 := (tendsto_punctured_of_injective continuous_neg neg_injective w).eventually
    (hP (-w))
  have e3 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) w).eventually (hP ((ω₂ n : ℂ) + w))
  have e4 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) w).eventually (hZ ((ω₂ n : ℂ) + w))
  have e5 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) w).eventually (hP ((ω₁ n : ℂ) + w))
  have e6 := (tendsto_punctured_of_injective (continuous_const_add (ω₁ n : ℂ))
    (add_right_injective _) w).eventually (hZ ((ω₁ n : ℂ) + w))
  have e7 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => z + s - q)
    (fun x y hxy => by simpa using hxy) w).eventually (hP (w + s - q))
  have e8 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => -(z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP (-(w + s)))
  have e9 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP ((ω₂ n : ℂ) + (w + s)))
  have e10 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hZ ((ω₂ n : ℂ) + (w + s)))
  have e11 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₁ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hP ((ω₁ n : ℂ) + (w + s)))
  have e12 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₁ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) w).eventually (hZ ((ω₁ n : ℂ) + (w + s)))
  have e13 := eventually_sin_ne_zero w
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13] with z h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 h11 h12 h13
  exact K2'_shift n G hodd p q s θ hθ z ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

include hn in
/-- The residue of the product-form kernel at an integer `a`, (6.6). -/
theorem K2'_residue_int (p q s : ℤ) (θ : ℝ) (a : ℤ) :
    HasResidue (K2' n G p q s θ) a
      ((-1) ^ a * Complex.exp (-I * θ * a) * (Rz n G p a * Rz n G q (a + s))) := by
  have hres := K2_residue_int n hn G p q s θ a
  have hω₁ := ω₁_pos n
  have hω₂ := ω₂_pos n
  have hP := eventually_not_mem_poleSet hω₁ hω₂
  have hZ := eventually_not_mem_zeroSet hω₁ hω₂
  have e3 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) (a : ℂ)).eventually (hP ((ω₂ n : ℂ) + a))
  have e4 := (tendsto_punctured_of_injective (continuous_const_add (ω₂ n : ℂ))
    (add_right_injective _) (a : ℂ)).eventually (hZ ((ω₂ n : ℂ) + a))
  have e9 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) (a : ℂ)).eventually (hP ((ω₂ n : ℂ) + (a + s)))
  have e10 := (tendsto_punctured_of_injective (by fun_prop : Continuous fun z : ℂ => (ω₂ n : ℂ) + (z + s))
    (fun x y hxy => by simpa using hxy) (a : ℂ)).eventually (hZ ((ω₂ n : ℂ) + (a + s)))
  unfold HasResidue at hres ⊢
  refine hres.congr' ?_
  filter_upwards [e3, e4, e9, e10] with z h3 h4 h9 h10
  rw [K2'_eq_K2 n G p q s θ z h3 h4 h9 h10]

omit hn in
lemma K2'_differentiableAt (p q s : ℤ) (θ : ℝ) (w : ℂ)
    (h1 : (ω₂ n : ℂ) + w - p ∉ poleSet (ω₁ n) (ω₂ n)) (h2 : (ω₁ n : ℂ) - w ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : (ω₂ n : ℂ) + (w + s) - q ∉ poleSet (ω₁ n) (ω₂ n))
    (h4 : (ω₁ n : ℂ) - (w + s) ∉ poleSet (ω₁ n) (ω₂ n))
    (hsin : Complex.sin (π * w) ≠ 0) : DifferentiableAt ℂ (K2' n G p q s θ) w := by
  unfold K2'
  refine DifferentiableAt.mul (DifferentiableAt.div ?_ ?_ hsin) ?_
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => (π : ℂ) * Complex.exp (-I * θ * z)).differentiableAt
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.sin (π * z)).differentiableAt
  · refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (DifferentiableAt.mul ?_ ?_)
    · exact (G.differentiableAt _ h1).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + z - p) w)
    · exact (G.differentiableAt _ h2).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₁ n : ℂ) - z) w)
    · exact (G.differentiableAt _ h3).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₂ n : ℂ) + (z + s) - q) w)
    · exact (G.differentiableAt _ h4).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (ω₁ n : ℂ) - (z + s)) w)

omit hn in
lemma K2'_shift_continuousAt (p q s : ℤ) (θ : ℝ) (w : ℂ)
    (h1 : (ω₂ n : ℂ) + (w + n) - p ∉ poleSet (ω₁ n) (ω₂ n))
    (h2 : (ω₁ n : ℂ) - (w + n) ∉ poleSet (ω₁ n) (ω₂ n))
    (h3 : (ω₂ n : ℂ) + (w + n + s) - q ∉ poleSet (ω₁ n) (ω₂ n))
    (h4 : (ω₁ n : ℂ) - (w + n + s) ∉ poleSet (ω₁ n) (ω₂ n))
    (hsin : Complex.sin (π * (w + n)) ≠ 0) :
    ContinuousAt (fun z => K2' n G p q s θ (z + n)) w :=
  ContinuousAt.comp (f := fun z : ℂ => z + n)
    (K2'_differentiableAt n G p q s θ (w + n) h1 h2 h3 h4 hsin).continuousAt (by fun_prop)

omit hn in
/-- Step 2 for the product form: the same decay bound as `K2_bound`. -/
theorem K2'_bound (p q s : ℤ) (θ : ℝ) (a b : ℝ) :
    ∃ M T : ℝ, 0 < T ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
      ‖K2' n G p q s θ z‖ ≤ M * Real.exp (-(π - |θ| + π * (p + q) / (ω₁ n * ω₂ n)) * |z.im|) := by
  obtain ⟨M, T, hT, hM⟩ := K2_bound n G p q s θ a b
  refine ⟨M, T, hT, ?_⟩
  intro z hza hzb hzT
  have him : z.im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hzT; linarith
  rw [K2'_eq_K2 n G p q s θ z (not_mem_poleSet_of_im_ne_zero (by simp [him]))
    (not_mem_zeroSet_of_im_ne_zero (by simp [him])) (not_mem_poleSet_of_im_ne_zero (by simp [him]))
    (not_mem_zeroSet_of_im_ne_zero (by simp [him]))]
  exact hM z hza hzb hzT

omit hn in
/-- The residue of the product-form kernel at a crossed pole. -/
theorem K2'_residue_of_shift (p q s : ℤ) (θ : ℝ) (w ρ₁ ρ₂ : ℂ)
    (hev : ∀ᶠ z in 𝓝[≠] w, K2' n G p q s θ (z + n) - K2' n G p q s θ z
      = -4 * π * Complex.exp (-I * θ * z) * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
          + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z))
    (hc : ContinuousAt (fun z => K2' n G p q s θ (z + n)) w)
    (h1 : HasResidueGen (fun z => Complex.exp (-I * θ * z) * J1 n G p q s z) w ρ₁)
    (h2 : HasResidueGen (fun z => Complex.exp (-I * θ * z) * J2 n G p q s z) w ρ₂) :
    HasResidueGen (K2' n G p q s θ) w
      (4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * ρ₁
        + (-1) ^ s * Complex.sin (π * q / ω₁ n) * ρ₂)) := by
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  refine ⟨4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * c₁
    + (-1) ^ s * Complex.sin (π * q / ω₁ n) * c₂), ?_⟩
  have hlim0 : Tendsto (fun z : ℂ => (z - w) * K2' n G p q s θ (z + n)) (𝓝[≠] w) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => (z - w) * K2' n G p q s θ (z + n)) (𝓝 w)
        (𝓝 ((w - w) * K2' n G p q s θ (w + n))) :=
      ((continuous_id.sub continuous_const).continuousAt).mul hc
    simp only [sub_self, zero_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have key := hlim0.add ((hc₁.const_mul (4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n)))).add
    (hc₂.const_mul (4 * π * ((-1) ^ s * Complex.sin (π * q / ω₁ n)))))
  simp only [zero_add] at key
  have e : 4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * ρ₁
      + (-1) ^ s * Complex.sin (π * q / ω₁ n) * ρ₂)
      = 4 * π * ((-1) ^ q * Complex.sin (π * p / ω₁ n)) * ρ₁
        + 4 * π * ((-1) ^ s * Complex.sin (π * q / ω₁ n)) * ρ₂ := by ring
  rw [e]
  refine key.congr' ?_
  filter_upwards [hev] with z hz
  have : K2' n G p q s θ z = K2' n G p q s θ (z + n) + 4 * π * Complex.exp (-I * θ * z)
      * ((-1) ^ q * Complex.sin (π * p / ω₁ n) * J1 n G p q s z
        + (-1) ^ s * Complex.sin (π * q / ω₁ n) * J2 n G p q s z) := by
    linear_combination -hz
  rw [this]; ring

end Concrete
end HaagerupIzumi
