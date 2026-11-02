module

public import HaagerupIzumi.Analytic.Residue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section

open MeasureTheory

/-!
# The hyperbolic gamma function as an interface

Fact 2.3 and Fact 2.5 of the expanded proof, packaged as structures. `HypGammaCore`
contains the local gamma identities and the ratio bound; `HypGamma` extends it
with the two-gamma and four-gamma integral identities. Every
analytic argument in the conditional odd-order theorem is carried out for
an arbitrary `G : HypGamma ω₁ ω₂`. `GammaCore.lean` constructs the complete
`HypGammaCore` from the regularized integral for the prescribed periods.
The integral identities in the extending `HypGamma` structure remain to
be constructed.

Conventions. `γ` is a total function `ℂ → ℂ`; its values on the pole set are
junk. The pole set is `{-(r ω₁ + s ω₂)}` and the zero set is
`{ω₁ + ω₂ + r ω₁ + s ω₂}` for naturals `r, s`. All poles are recorded as
simple, with residues given by a function `residue`; this is the situation for
periods with irrational ratio, which is the only case used (`ω₁/ω₂ = d`). The asymptotic statement is
recorded in the form actually used, namely the growth bound on ratios
(Lemma 2.4). The two-gamma integral is recorded along a vertical line with
the residues of the poles that the line does not separate added back
(Section 2.1, "continuation across crossed poles"); this is the form in which
Belousov–Sarkissian–Spiridonov's separating-contour prescription is used.

The four-gamma kernel `K₄` of Section 7 is likewise part of the interface: its
line characterization (2.2), the elementary identities (7.6)–(7.7), the Euler
transformation (Lemma 7.3) and the four-term identity (Lemma 7.4) are recorded
as properties. In the paper these are derived from the two-gamma transform
(2.18), the convolution theorem, and analytic continuation in the parameters;
that continuation argument is not formalized here.
-/

open Complex Filter Topology Set Real

namespace HaagerupIzumi

/-- The pole lattice `-(r ω₁ + s ω₂)`. -/
def poleSet (ω₁ ω₂ : ℝ) : Set ℂ := {z | ∃ r s : ℕ, z = -((r : ℂ) * ω₁ + (s : ℂ) * ω₂)}

/-- The zero lattice `ω₁ + ω₂ + r ω₁ + s ω₂`. -/
def zeroSet (ω₁ ω₂ : ℝ) : Set ℂ :=
  {z | ∃ r s : ℕ, z = (ω₁ : ℂ) + ω₂ + (r : ℂ) * ω₁ + (s : ℂ) * ω₂}

/-! ### The four-gamma kernel `K₄` -/

/-- `U = Ω/4 + (r + s)/2` of the centered kernel (7.1). -/
noncomputable def k4U (ω₁ ω₂ : ℝ) (r s : ℂ) : ℂ := ((ω₁ + ω₂ : ℝ) : ℂ) / 4 + (r + s) / 2

/-- `V = Ω/4 + (r - s)/2` of the centered kernel (7.1). -/
noncomputable def k4V (ω₁ ω₂ : ℝ) (r s : ℂ) : ℂ := ((ω₁ + ω₂ : ℝ) : ℂ) / 4 + (r - s) / 2

/-- The integrand of `K₄(r,s,x,y)`, formula (7.2). -/
noncomputable def k4Integrand (γ : ℂ → ℂ) (ω₁ ω₂ : ℝ) (r s x y z : ℂ) : ℂ :=
  Complex.exp (2 * π * I * y * z / (ω₁ * ω₂)) * γ (k4U ω₁ ω₂ r s + z) * γ (k4U ω₁ ω₂ r s - z)
    * γ (k4V ω₁ ω₂ r s + z + x) * γ (k4V ω₁ ω₂ r s - z - x)

/-- No left pole of the integrand of `K₄(r,s,x,·)` coincides with a right pole: the four
opposite-parameter sums `2U, 2V, U + V ∓ x` are not in `-(ω₁ ℕ + ω₂ ℕ)`. -/
def K4NoPinch (ω₁ ω₂ : ℝ) (r s x : ℂ) : Prop :=
  2 * k4U ω₁ ω₂ r s ∉ poleSet ω₁ ω₂ ∧ 2 * k4V ω₁ ω₂ r s ∉ poleSet ω₁ ω₂ ∧
  k4U ω₁ ω₂ r s + k4V ω₁ ω₂ r s - x ∉ poleSet ω₁ ω₂ ∧
  k4U ω₁ ω₂ r s + k4V ω₁ ω₂ r s + x ∉ poleSet ω₁ ω₂

/-- The convergence condition (7.4): `|Re y| < Ω/2 - Re r`. -/
def K4Conv (ω₁ ω₂ : ℝ) (r y : ℂ) : Prop := |y.re| < (ω₁ + ω₂) / 2 - r.re

/-- `Γ_r(v) = γ(Ω/2 + r + v) γ(Ω/2 + r - v)`, formula (7.3). -/
noncomputable def Γr (γ : ℂ → ℂ) (ω₁ ω₂ : ℝ) (r v : ℂ) : ℂ :=
  γ (((ω₁ + ω₂ : ℝ) : ℂ) / 2 + r + v) * γ (((ω₁ + ω₂ : ℝ) : ℂ) / 2 + r - v)

/-- The local hyperbolic gamma properties and the vertical-strip ratio bound.
The integral identities used by the odd-order construction belong to `HypGamma`. -/
structure HypGammaCore (ω₁ ω₂ : ℝ) where
  /-- the function -/
  γ : ℂ → ℂ
  pos₁ : 0 < ω₁
  pos₂ : 0 < ω₂
  /-- holomorphic away from the poles -/
  differentiableOn : DifferentiableOn ℂ γ (poleSet ω₁ ω₂)ᶜ
  /-- nonvanishing away from poles and zeros -/
  ne_zero : ∀ z, z ∉ poleSet ω₁ ω₂ → z ∉ zeroSet ω₁ ω₂ → γ z ≠ 0
  /-- vanishing on the zero set -/
  eq_zero : ∀ z, z ∈ zeroSet ω₁ ω₂ → γ z = 0
  /-- first shift identity -/
  shift₁ : ∀ z, z ∉ poleSet ω₁ ω₂ → γ (z + ω₁) = 2 * Complex.sin (π * z / ω₂) * γ z
  /-- second shift identity -/
  shift₂ : ∀ z, z ∉ poleSet ω₁ ω₂ → γ (z + ω₂) = 2 * Complex.sin (π * z / ω₁) * γ z
  /-- reflection -/
  reflect : ∀ z, z ∉ poleSet ω₁ ω₂ → z ∉ zeroSet ω₁ ω₂ → γ z * γ (ω₁ + ω₂ - z) = 1
  /-- residue at the origin -/
  residue_zero : HasResidue γ 0 (Real.sqrt (ω₁ * ω₂) / (2 * π))
  /-- the residues at the poles -/
  residue : ℂ → ℂ
  /-- every pole is simple, with residue `residue w` -/
  hasResidue : ∀ w ∈ poleSet ω₁ ω₂, HasResidue γ w (residue w)
  /-- real and positive on `(0, ω₁ + ω₂)` -/
  real_pos : ∀ x : ℝ, 0 < x → x < ω₁ + ω₂ → 0 < (γ x).re ∧ (γ x).im = 0
  /-- real on the real axis -/
  real_axis : ∀ x : ℝ, (γ x).im = 0
  /-- growth of ratios along vertical lines (Lemma 2.4), uniformly on bounded strips -/
  ratio_bound : ∀ c a b : ℝ, ∃ C T : ℝ, 0 < T ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
    z ∉ poleSet ω₁ ω₂ → z + c ∉ poleSet ω₁ ω₂ →
    ‖γ (z + c)‖ ≤ C * Real.exp (π * c * |z.im| / (ω₁ * ω₂)) * ‖γ z‖

/-- The hyperbolic gamma core together with the two-gamma and four-gamma integral identities. -/
structure HypGamma (ω₁ ω₂ : ℝ) extends HypGammaCore ω₁ ω₂ where
  /-- the two-gamma Fourier integral (Belousov–Sarkissian–Spiridonov (2.17)) along the line
  `Re z = σ`, with the crossed left poles added back. Hypotheses: the exponent parameter is in
  the convergence range, all right poles `h + r ω₁ + s ω₂` lie strictly to the right of the line,
  no left pole coincides with a right pole, the line passes through no left pole, and `S` is the
  finite set of left poles `-f - r ω₁ - s ω₂` to the right of the line, with residues `ρ`. -/
  two_gamma : ∀ (f h α : ℂ) (σ : ℝ) (S : Finset ℂ) (ρ : ℂ → ℂ),
    0 < α.re → α.re < (ω₁ + ω₂ - h - f).re → σ < h.re →
    (∀ r s r' s' : ℕ, -f - r * ω₁ - s * ω₂ ≠ h + r' * ω₁ + s' * ω₂) →
    (∀ r s : ℕ, (-f - r * ω₁ - s * ω₂).re ≠ σ) →
    (∀ w, w ∈ S ↔ (∃ r s : ℕ, w = -f - r * ω₁ - s * ω₂) ∧ σ < w.re) →
    (∀ w ∈ S, HasResidue (fun z => Complex.exp (π * I * z * (2 * α + h + f - ω₁ - ω₂) / (ω₁ * ω₂))
      * γ (f + z) * γ (h - z)) w (ρ w)) →
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (π * I * (σ + t * I) * (2 * α + h + f - ω₁ - ω₂)
      / (ω₁ * ω₂)) * γ (f + (σ + t * I)) * γ (h - (σ + t * I))) ∧
    lineIntegral (fun z => Complex.exp (π * I * z * (2 * α + h + f - ω₁ - ω₂) / (ω₁ * ω₂))
      * γ (f + z) * γ (h - z)) σ + 2 * π * I * ∑ w ∈ S, ρ w
    = I * Real.sqrt (ω₁ * ω₂) * Complex.exp (π * I / (2 * ω₁ * ω₂) * (h - f) * (2 * α + h + f - ω₁ - ω₂))
      * γ α * γ (ω₁ + ω₂ - h - f - α) * γ (f + h)
  /-- the four-gamma kernel `K₄(r,s,x,y)` of Section 7: the integral (7.2) over a separating
  contour, continued meromorphically in the parameters -/
  K4 : ℂ → ℂ → ℂ → ℂ → ℂ
  /-- the value of `K₄` through a vertical line: the line integral plus `2πi` times the residues
  at the left poles to the right of the line, minus `2πi` times the residues at the right poles to
  the left of the line (formula (2.2)); hypotheses: convergence, no pinch, the line passes through
  no pole, `SL`/`SR` are the crossed left/right poles, with residues `ρL`/`ρR` -/
  K4_line : ∀ (r s x y : ℂ) (σ : ℝ) (SL SR : Finset ℂ) (ρL ρR : ℂ → ℂ),
    K4Conv ω₁ ω₂ r y → K4NoPinch ω₁ ω₂ r s x →
    (∀ a b : ℕ, (-k4U ω₁ ω₂ r s - a * ω₁ - b * ω₂).re ≠ σ) →
    (∀ a b : ℕ, (-k4V ω₁ ω₂ r s - x - a * ω₁ - b * ω₂).re ≠ σ) →
    (∀ a b : ℕ, (k4U ω₁ ω₂ r s + a * ω₁ + b * ω₂).re ≠ σ) →
    (∀ a b : ℕ, (k4V ω₁ ω₂ r s - x + a * ω₁ + b * ω₂).re ≠ σ) →
    (∀ w, w ∈ SL ↔ ((∃ a b : ℕ, w = -k4U ω₁ ω₂ r s - a * ω₁ - b * ω₂) ∨
        (∃ a b : ℕ, w = -k4V ω₁ ω₂ r s - x - a * ω₁ - b * ω₂)) ∧ σ < w.re) →
    (∀ w, w ∈ SR ↔ ((∃ a b : ℕ, w = k4U ω₁ ω₂ r s + a * ω₁ + b * ω₂) ∨
        (∃ a b : ℕ, w = k4V ω₁ ω₂ r s - x + a * ω₁ + b * ω₂)) ∧ w.re < σ) →
    (∀ w ∈ SL, HasResidueGen (k4Integrand γ ω₁ ω₂ r s x y) w (ρL w)) →
    (∀ w ∈ SR, HasResidueGen (k4Integrand γ ω₁ ω₂ r s x y) w (ρR w)) →
    MeasureTheory.Integrable (fun t : ℝ => k4Integrand γ ω₁ ω₂ r s x y (σ + t * I)) ∧
    lineIntegral (k4Integrand γ ω₁ ω₂ r s x y) σ + 2 * π * I * ∑ w ∈ SL, ρL w
      - 2 * π * I * ∑ w ∈ SR, ρR w = I * Real.sqrt (ω₁ * ω₂) * K4 r s x y
  /-- evenness (7.6) -/
  K4_even : ∀ r s x y : ℂ, K4Conv ω₁ ω₂ r y → K4NoPinch ω₁ ω₂ r s x →
    K4 r s x y = K4 r s (-x) (-y)
  /-- the shift identity (7.7) -/
  K4_swap : ∀ r s x y : ℂ, K4Conv ω₁ ω₂ r y → K4NoPinch ω₁ ω₂ r s x →
    K4 r s x y = Complex.exp (π * I * y * (s - x) / (ω₁ * ω₂)) * K4 r x s y
  /-- the Euler transformation (Lemma 7.3), in the form `Γ_r(y) K₄(r,·) = Γ_r(s) Γ_r(x) K₄(-r,·)` -/
  K4_euler : ∀ r s x y : ℂ, K4Conv ω₁ ω₂ r y → K4Conv ω₁ ω₂ (-r) y →
    K4NoPinch ω₁ ω₂ r s x → K4NoPinch ω₁ ω₂ (-r) s x →
    Γr γ ω₁ ω₂ r y * K4 r s x y = Γr γ ω₁ ω₂ r s * Γr γ ω₁ ω₂ r x * K4 (-r) s x y
  /-- the four-term identity (Lemma 7.4), for periods with `ω₁ - ω₂ = n` and
  `ω₁ * ω₂ = ω₁ + ω₂`, at the parameters
  `R = g/2`, `X = (n+g)/2 + l`, `Y = (n+g)/2 + h` of (7.13) -/
  K4_four_term : ∀ (n g h l : ℕ) (Z : ℂ), ω₁ - ω₂ = n → ω₁ * ω₂ = ω₁ + ω₂ →
    1 ≤ g → 1 ≤ h → g + h < n → 1 ≤ l →
    l ≤ h → |Z.re| < (ω₁ + ω₂ - g) / 2 →
    K4NoPinch ω₁ ω₂ ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l) (((n + g : ℂ)) / 2 + h + ω₂) →
    K4NoPinch ω₁ ω₂ ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l) (((n + g : ℂ)) / 2 + h - ω₁) →
    K4NoPinch ω₁ ω₂ ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l - ω₁) (((n + g : ℂ)) / 2 + h) →
    K4NoPinch ω₁ ω₂ ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l + ω₂) (((n + g : ℂ)) / 2 + h) →
    0 = Complex.sin (π * h / ω₁) * K4 ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l) (((n + g : ℂ)) / 2 + h + ω₂) Z
      + (-1) ^ (g + l + 1) * Complex.sin (π * (g + h : ℕ) / ω₁)
        * Complex.exp (-2 * π * I * Z * ω₁ / (ω₁ * ω₂))
        * K4 ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l) (((n + g : ℂ)) / 2 + h - ω₁) Z
      + (-1) ^ (g + h) * Complex.sin (π * (g + l : ℕ) / ω₁)
        * Complex.exp (-π * I * Z * ω₁ / (ω₁ * ω₂))
        * K4 ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l - ω₁) (((n + g : ℂ)) / 2 + h) Z
      - Complex.sin (π * l / ω₁) * Complex.exp (-π * I * Z * ω₂ / (ω₁ * ω₂))
        * K4 ((g : ℂ) / 2) (((n + g : ℂ)) / 2 + l + ω₂) (((n + g : ℂ)) / 2 + h) Z

namespace HypGamma

variable {ω₁ ω₂ : ℝ} (G : HypGamma ω₁ ω₂)

lemma poleSet_def (z : ℂ) : z ∈ poleSet ω₁ ω₂ ↔ ∃ r s : ℕ, z = -((r : ℂ) * ω₁ + (s : ℂ) * ω₂) :=
  Iff.rfl

lemma zeroSet_def (z : ℂ) :
    z ∈ zeroSet ω₁ ω₂ ↔ ∃ r s : ℕ, z = (ω₁ : ℂ) + ω₂ + (r : ℂ) * ω₁ + (s : ℂ) * ω₂ :=
  Iff.rfl

/-- A point with positive real part is not a pole. -/
lemma not_mem_poleSet_of_re_pos (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) {z : ℂ} (hz : 0 < z.re) :
    z ∉ poleSet ω₁ ω₂ := by
  rintro ⟨r, s, rfl⟩
  simp only [neg_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
    sub_zero] at hz
  have : (0 : ℝ) ≤ r * ω₁ + s * ω₂ := by positivity
  linarith

/-- A point with real part less than `ω₁ + ω₂` is not a zero. -/
lemma not_mem_zeroSet_of_re_lt (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) {z : ℂ} (hz : z.re < ω₁ + ω₂) :
    z ∉ zeroSet ω₁ ω₂ := by
  rintro ⟨r, s, rfl⟩
  simp only [add_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
    sub_zero] at hz
  have : (0 : ℝ) ≤ r * ω₁ + s * ω₂ := by positivity
  linarith

/-- The pole set meets every bounded set in a finite set. -/
lemma poleSet_inter_finite (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (M : ℝ) :
    (poleSet ω₁ ω₂ ∩ Metric.closedBall 0 M).Finite := by
  classical
  have hsub : poleSet ω₁ ω₂ ∩ Metric.closedBall 0 M ⊆
      (fun p : ℕ × ℕ => -((p.1 : ℂ) * ω₁ + (p.2 : ℂ) * ω₂)) ''
        ((Finset.range (⌈M / ω₁⌉₊ + 1) ×ˢ Finset.range (⌈M / ω₂⌉₊ + 1) : Finset (ℕ × ℕ))) := by
    rintro z ⟨⟨r, s, rfl⟩, hz⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hre : ‖-((r : ℂ) * ω₁ + (s : ℂ) * ω₂)‖ = r * ω₁ + s * ω₂ := by
      rw [norm_neg]
      have : ((r : ℂ) * ω₁ + (s : ℂ) * ω₂) = ((r * ω₁ + s * ω₂ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hre] at hz
    refine ⟨(r, s), ?_, rfl⟩
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    have hr : (r : ℝ) ≤ M / ω₁ := by
      rw [le_div_iff₀ hω₁]; nlinarith [mul_nonneg (Nat.cast_nonneg s) hω₂.le]
    have hs : (s : ℝ) ≤ M / ω₂ := by
      rw [le_div_iff₀ hω₂]; nlinarith [mul_nonneg (Nat.cast_nonneg r) hω₁.le]
    have hr' : (r : ℝ) ≤ ⌈M / ω₁⌉₊ := hr.trans (Nat.le_ceil _)
    have hs' : (s : ℝ) ≤ ⌈M / ω₂⌉₊ := hs.trans (Nat.le_ceil _)
    exact ⟨Nat.lt_succ_of_le (by exact_mod_cast hr'), Nat.lt_succ_of_le (by exact_mod_cast hs')⟩
  exact ((Finset.finite_toSet _).image _).subset hsub

/-- The pole set is closed. -/
lemma poleSet_isClosed (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) : IsClosed (poleSet ω₁ ω₂) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  have hfin := poleSet_inter_finite hω₁ hω₂ (‖z‖ + 1)
  refine ⟨Metric.ball z 1 \ (poleSet ω₁ ω₂ ∩ Metric.closedBall 0 (‖z‖ + 1)), ?_,
    Metric.isOpen_ball.sdiff hfin.isClosed, ?_⟩
  · rintro w ⟨hw, hw'⟩ hwP
    apply hw'
    refine ⟨hwP, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have := Metric.mem_ball.mp hw
    calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by rw [dist_eq_norm] at this; linarith
  · exact ⟨Metric.mem_ball_self one_pos, fun h => hz h.1⟩

end HypGamma

namespace HypGammaCore

variable {ω₁ ω₂ : ℝ} (G : HypGammaCore ω₁ ω₂)

/-- `γ` is differentiable at every non-pole. -/
lemma differentiableAt (z : ℂ) (hz : z ∉ poleSet ω₁ ω₂) : DifferentiableAt ℂ G.γ z :=
  G.differentiableOn.differentiableAt
    ((HypGamma.poleSet_isClosed G.pos₁ G.pos₂).isOpen_compl.mem_nhds hz)

/-- `γ` is continuous at every non-pole. -/
lemma continuousAt (z : ℂ) (hz : z ∉ poleSet ω₁ ω₂) : ContinuousAt G.γ z :=
  (G.differentiableAt z hz).continuousAt

/-- The value of the residue function at the origin. -/
lemma residue_zero_eq : G.residue 0 = Real.sqrt (ω₁ * ω₂) / (2 * π) :=
  tendsto_nhds_unique (G.hasResidue 0 ⟨0, 0, by simp⟩) G.residue_zero

end HypGammaCore

namespace HypGamma

variable {ω₁ ω₂ : ℝ} (G : HypGamma ω₁ ω₂)

/-- `γ` is differentiable at every non-pole. -/
lemma differentiableAt (z : ℂ) (hz : z ∉ poleSet ω₁ ω₂) : DifferentiableAt ℂ G.γ z :=
  G.toHypGammaCore.differentiableAt z hz

/-- `γ` is continuous at every non-pole. -/
lemma continuousAt (z : ℂ) (hz : z ∉ poleSet ω₁ ω₂) : ContinuousAt G.γ z :=
  G.toHypGammaCore.continuousAt z hz

/-- The value of the residue function at the origin. -/
lemma residue_zero_eq : G.residue 0 = Real.sqrt (ω₁ * ω₂) / (2 * π) :=
  G.toHypGammaCore.residue_zero_eq

end HypGamma

/-! ### Isolation of poles and zeros -/

/-- A nonreal point is not a pole. -/
lemma not_mem_poleSet_of_im_ne_zero {ω₁ ω₂ : ℝ} {z : ℂ} (hz : z.im ≠ 0) : z ∉ poleSet ω₁ ω₂ := by
  rintro ⟨r, s, rfl⟩; apply hz; simp

/-- A nonreal point is not a zero. -/
lemma not_mem_zeroSet_of_im_ne_zero {ω₁ ω₂ : ℝ} {z : ℂ} (hz : z.im ≠ 0) : z ∉ zeroSet ω₁ ω₂ := by
  rintro ⟨r, s, rfl⟩; apply hz; simp

lemma mem_zeroSet_iff {ω₁ ω₂ : ℝ} (z : ℂ) :
    z ∈ zeroSet ω₁ ω₂ ↔ (ω₁ : ℂ) + ω₂ - z ∈ poleSet ω₁ ω₂ := by
  constructor
  · rintro ⟨r, s, rfl⟩; exact ⟨r, s, by ring⟩
  · rintro ⟨r, s, h⟩; exact ⟨r, s, by linear_combination -h⟩

/-- A continuous injection maps punctured neighbourhoods to punctured neighbourhoods. -/
lemma tendsto_punctured_of_injective {φ : ℂ → ℂ} (hφ : Continuous φ) (hinj : Function.Injective φ)
    (p : ℂ) : Tendsto φ (𝓝[≠] p) (𝓝[≠] (φ p)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_nhdsWithin_of_tendsto_nhds (hφ.tendsto p), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact fun h => hz (hinj h)

/-- Points of the pole set are isolated: a punctured neighbourhood of any point avoids it. -/
lemma eventually_not_mem_poleSet {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ poleSet ω₁ ω₂ := by
  have hfin : ((poleSet ω₁ ω₂ ∩ Metric.closedBall p 1) \ {p}).Finite := by
    apply Set.Finite.diff
    apply (HypGamma.poleSet_inter_finite hω₁ hω₂ (‖p‖ + 1)).subset
    rintro z ⟨hz, hz'⟩
    refine ⟨hz, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz'
    calc ‖z‖ = ‖p + (z - p)‖ := by ring_nf
      _ ≤ ‖p‖ + ‖z - p‖ := norm_add_le _ _
      _ ≤ ‖p‖ + 1 := by linarith
  have h1 : ∀ᶠ z in 𝓝 p, z ∉ (poleSet ω₁ ω₂ ∩ Metric.closedBall p 1) \ {p} :=
    hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  have h2 : ∀ᶠ z in 𝓝 p, z ∈ Metric.closedBall p 1 := Metric.closedBall_mem_nhds p one_pos
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
    with z hz1 hz2 hz3
  intro hz
  exact hz1 ⟨⟨hz, hz2⟩, hz3⟩

/-- Points of the zero set are isolated. -/
lemma eventually_not_mem_zeroSet {ω₁ ω₂ : ℝ} (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ zeroSet ω₁ ω₂ := by
  have := (tendsto_punctured_of_injective (continuous_const.sub continuous_id)
    (sub_right_injective) p).eventually (eventually_not_mem_poleSet hω₁ hω₂ ((ω₁ : ℂ) + ω₂ - p))
  filter_upwards [this] with z hz
  rw [mem_zeroSet_iff]; exact hz

end HaagerupIzumi
