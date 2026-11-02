module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic

@[expose] public section

/-!
# Residue calculus on rectangles and strips

The contour-integration infrastructure of Section 2.1 of the expanded proof,
built from the Cauchy–Goursat theorem for rectangles in Mathlib.

* `rectBoundary f z w` is the counterclockwise boundary integral of `f` over
  the rectangle with opposite corners `z` and `w` (Mathlib's convention).
* `rectBoundary_inv_sub`: the boundary integral of `(ζ - p)⁻¹` is `2 π I` when
  `p` is in the interior.
* `rectBoundary_eq_sum_residues`: the residue theorem for a rectangle with
  finitely many simple poles.
* `strip_residues`: the version for an infinite vertical strip with an
  exponentially decaying integrand (formula (2.1) of the expanded proof).
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral Real

namespace HaagerupIzumi

/-- The residue of `Φ` at `w`, when `Φ` has (at most) a simple pole there: the limit of
`(z - w) Φ z`. -/
def HasResidue (Φ : ℂ → ℂ) (w ρ : ℂ) : Prop :=
  Tendsto (fun z => (z - w) * Φ z) (𝓝[≠] w) (𝓝 ρ)

/-- `f` has at `w` a pole of order at most two with residue `ρ`: for some `c`,
`(z - w) f z - c / (z - w) → ρ`. Simple poles are the case `c = 0`. -/
def HasResidueGen (f : ℂ → ℂ) (w ρ : ℂ) : Prop :=
  ∃ c : ℂ, Tendsto (fun z => (z - w) * f z - c * (z - w)⁻¹) (𝓝[≠] w) (𝓝 ρ)

lemma HasResidue.hasResidueGen {f : ℂ → ℂ} {w ρ : ℂ} (h : HasResidue f w ρ) :
    HasResidueGen f w ρ :=
  ⟨0, by simp only [zero_mul, sub_zero]; exact h⟩

/-- A function with a simple pole, differentiable on a punctured neighbourhood, has a
removable singularity after subtracting the principal part. -/
lemma HasResidue.tendsto_sub_principal {f : ℂ → ℂ} {w ρ : ℂ} (h : HasResidue f w ρ)
    (hd : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ f z) :
    ∃ c : ℂ, Tendsto (fun z => f z - ρ * (z - w)⁻¹) (𝓝[≠] w) (𝓝 c) := by
  set φ : ℂ → ℂ := fun z => f z - ρ * (z - w)⁻¹ with hφ
  have hs : {z : ℂ | z ≠ w → DifferentiableAt ℂ f z} ∈ 𝓝 w := by
    have := eventually_nhdsWithin_iff.1 hd
    exact this
  have hdφ : DifferentiableOn ℂ φ ({z : ℂ | z ≠ w → DifferentiableAt ℂ f z} \ {w}) := by
    intro z hz
    have hzw : z ≠ w := hz.2
    have h1 : DifferentiableAt ℂ f z := hz.1 hzw
    exact ((h1.sub (((differentiableAt_id.sub_const w).inv (sub_ne_zero.2 hzw)).const_mul ρ))
      ).differentiableWithinAt
  have ho : (fun z => φ z - φ w) =o[𝓝[≠] w] fun z => (z - w)⁻¹ := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h1 : Tendsto (fun z => (z - w) * φ z) (𝓝[≠] w) (𝓝 0) := by
        have : Tendsto (fun z => (z - w) * f z - ρ) (𝓝[≠] w) (𝓝 (ρ - ρ)) :=
          h.sub tendsto_const_nhds
        rw [sub_self] at this
        refine this.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [hφ]
        field_simp [sub_ne_zero.2 hz]
      have h2 : Tendsto (fun z => (z - w) * φ w) (𝓝[≠] w) (𝓝 0) := by
        have : Tendsto (fun z => (z - w) * φ w) (𝓝 w) (𝓝 ((w - w) * φ w)) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto w
        simp at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      have := h1.sub h2
      simp only [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [div_inv_eq_mul]; ring
    · filter_upwards [self_mem_nhdsWithin] with z hz h0
      exact absurd h0 (inv_ne_zero (sub_ne_zero.2 hz))
  have hdiff := Complex.differentiableOn_update_limUnder_of_isLittleO hs hdφ ho
  have hc := (hdiff.differentiableAt hs).continuousAt
  refine ⟨limUnder (𝓝[≠] w) φ, ?_⟩
  have := tendsto_nhdsWithin_of_tendsto_nhds (s := {w}ᶜ) hc.tendsto
  rw [Function.update_self] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [Function.update_of_ne hz]

/-- The product of two functions with simple poles at `w` has a pole of order at most two. -/
lemma HasResidue.mul_hasResidueGen {f₁ f₂ : ℂ → ℂ} {w ρ₁ ρ₂ : ℂ}
    (h₁ : HasResidue f₁ w ρ₁) (h₂ : HasResidue f₂ w ρ₂)
    (hd₁ : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ f₁ z)
    (hd₂ : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ f₂ z) :
    ∃ ρ, HasResidueGen (fun z => f₁ z * f₂ z) w ρ := by
  obtain ⟨c₁, hc₁⟩ := h₁.tendsto_sub_principal hd₁
  obtain ⟨c₂, hc₂⟩ := h₂.tendsto_sub_principal hd₂
  refine ⟨ρ₁ * c₂ + ρ₂ * c₁, ρ₁ * ρ₂, ?_⟩
  -- `(z-w) f₁ f₂ - ρ₁ρ₂/(z-w) = ρ₁ g₂ + ρ₂ g₁ + (z-w) g₁ g₂` with `g_i = f_i - ρ_i/(z-w)`
  have hg : Tendsto (fun z => ρ₁ * (f₂ z - ρ₂ * (z - w)⁻¹) + ρ₂ * (f₁ z - ρ₁ * (z - w)⁻¹)
      + (z - w) * ((f₁ z - ρ₁ * (z - w)⁻¹) * (f₂ z - ρ₂ * (z - w)⁻¹)))
      (𝓝[≠] w) (𝓝 (ρ₁ * c₂ + ρ₂ * c₁ + 0)) := by
    refine ((hc₂.const_mul ρ₁).add (hc₁.const_mul ρ₂)).add ?_
    have h0 : Tendsto (fun z : ℂ => z - w) (𝓝[≠] w) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => z - w) (𝓝 w) (𝓝 (w - w)) :=
        (continuous_id.sub continuous_const).tendsto w
      rw [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have := h0.mul (hc₁.mul hc₂)
    simpa using this
  rw [add_zero] at hg
  refine hg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzw : z - w ≠ 0 := sub_ne_zero.2 hz
  field_simp
  ring

/-- The product of a function with a pole of order at most two and a function differentiable
at `w` has a pole of order at most two. -/
lemma HasResidueGen.mul_differentiableAt {f g : ℂ → ℂ} {w ρ : ℂ} (hf : HasResidueGen f w ρ)
    (hg : DifferentiableAt ℂ g w) : ∃ ρ', HasResidueGen (fun z => f z * g z) w ρ' := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨ρ * g w + c * deriv g w, c * g w, ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope.1 hg.hasDerivAt
  have hgc : Tendsto g (𝓝[≠] w) (𝓝 (g w)) :=
    tendsto_nhdsWithin_of_tendsto_nhds hg.continuousAt.tendsto
  have key : Tendsto (fun z => ((z - w) * f z - c * (z - w)⁻¹) * g z + c * slope g w z)
      (𝓝[≠] w) (𝓝 (ρ * g w + c * deriv g w)) :=
    (hc.mul hgc).add (hslope.const_mul c)
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzw : z - w ≠ 0 := sub_ne_zero.2 hz
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  field_simp
  ring

/-- A factor which is either regular at `w`, or has a simple pole at `w` and is differentiable on
a punctured neighbourhood. -/
def AtMostSimple (f : ℂ → ℂ) (w : ℂ) : Prop :=
  DifferentiableAt ℂ f w ∨
    ((∃ ρ, HasResidue f w ρ) ∧ ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ f z)

lemma AtMostSimple.of_differentiableAt {f : ℂ → ℂ} {w : ℂ} (h : DifferentiableAt ℂ f w) :
    AtMostSimple f w := Or.inl h

/-- A regular function has residue `0`. -/
lemma HasResidue.of_continuousAt {f : ℂ → ℂ} {w : ℂ} (h : ContinuousAt f w) : HasResidue f w 0 := by
  unfold HasResidue
  have : Tendsto (fun z => (z - w) * f z) (𝓝 w) (𝓝 ((w - w) * f w)) :=
    ((continuous_id.sub continuous_const).continuousAt).mul h
  simp only [sub_self, zero_mul] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- The product of a function with a simple pole and a function continuous at `w`. -/
lemma HasResidue.mul_continuousAt {f g : ℂ → ℂ} {w ρ : ℂ} (hf : HasResidue f w ρ)
    (hg : ContinuousAt g w) : HasResidue (fun z => f z * g z) w (ρ * g w) := by
  unfold HasResidue at hf ⊢
  have := hf.mul (tendsto_nhdsWithin_of_tendsto_nhds hg.tendsto)
  refine this.congr' ?_
  filter_upwards with z; ring

lemma HasResidue.continuousAt_mul {f g : ℂ → ℂ} {w ρ : ℂ} (hg : HasResidue g w ρ)
    (hf : ContinuousAt f w) : HasResidue (fun z => f z * g z) w (f w * ρ) := by
  unfold HasResidue at hg ⊢
  have := (tendsto_nhdsWithin_of_tendsto_nhds hf.tendsto).mul hg
  refine this.congr' ?_
  filter_upwards with z; ring

/-- Existence of a generalized residue for a product of two factors with at most simple poles. -/
lemma exists_hasResidueGen_mul {f g : ℂ → ℂ} {w : ℂ} (hf : AtMostSimple f w)
    (hg : AtMostSimple g w) : ∃ ρ, HasResidueGen (fun z => f z * g z) w ρ := by
  rcases hf with hf | ⟨⟨ρf, hρf⟩, hdf⟩ <;> rcases hg with hg | ⟨⟨ρg, hρg⟩, hdg⟩
  · exact ⟨0, (HasResidue.of_continuousAt (hf.continuousAt.mul hg.continuousAt)).hasResidueGen⟩
  · exact ⟨f w * ρg, (hρg.continuousAt_mul hf.continuousAt).hasResidueGen⟩
  · exact ⟨ρf * g w, (hρf.mul_continuousAt hg.continuousAt).hasResidueGen⟩
  · exact hρf.mul_hasResidueGen hρg hdf hdg

/-- A product with at most simple poles in each factor is again at most simple, when at most one
factor is singular; used for the regular factors. -/
lemma AtMostSimple.mul_differentiableAt {f g : ℂ → ℂ} {w : ℂ} (hf : AtMostSimple f w)
    (hg : DifferentiableAt ℂ g w) (hg' : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ g z) :
    AtMostSimple (fun z => f z * g z) w := by
  rcases hf with hf | ⟨⟨ρ, hρ⟩, hd⟩
  · exact Or.inl (hf.mul hg)
  · refine Or.inr ⟨⟨ρ * g w, hρ.mul_continuousAt hg.continuousAt⟩, ?_⟩
    filter_upwards [hd, hg'] with z h1 h2
    exact h1.mul h2

lemma AtMostSimple.differentiableAt_mul {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f w)
    (hf' : ∀ᶠ z in 𝓝[≠] w, DifferentiableAt ℂ f z) (hg : AtMostSimple g w) :
    AtMostSimple (fun z => f z * g z) w := by
  rcases hg with hg | ⟨⟨ρ, hρ⟩, hd⟩
  · exact Or.inl (hf.mul hg)
  · refine Or.inr ⟨⟨f w * ρ, hρ.continuousAt_mul hf.continuousAt⟩, ?_⟩
    filter_upwards [hd, hf'] with z h1 h2
    exact h2.mul h1

/-- The integral of `Φ` along the upward vertical line `Re z = σ`, with the measure `dz`
(so that `dz = I dt`). -/
noncomputable def lineIntegral (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  ∫ t : ℝ, Φ (σ + t * I) * I

/-- The counterclockwise boundary integral over the rectangle with corners `z` and `w`,
in the form used by Mathlib's Cauchy–Goursat theorem. -/
noncomputable def rectBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x in z.re..w.re, f (x + z.im * I)) - (∫ x in z.re..w.re, f (x + w.im * I))
    + I • (∫ y in z.im..w.im, f (w.re + y * I)) - I • (∫ y in z.im..w.im, f (z.re + y * I))

/-- Cauchy–Goursat for a rectangle, off a countable set (Mathlib). -/
theorem rectBoundary_eq_zero (f : ℂ → ℂ) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (hd : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectBoundary f z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs hc hd

/-- A point `p` lies in the open rectangle with corners `z, w` (with `z.re < w.re`,
`z.im < w.im`). -/
def InOpenRect (p z w : ℂ) : Prop :=
  z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im

/-- The closed rectangle. -/
def closedRect (z w : ℂ) : Set ℂ := Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im

lemma mem_closedRect {p z w : ℂ} :
    p ∈ closedRect z w ↔ (z.re ≤ p.re ∧ p.re ≤ w.re) ∧ (z.im ≤ p.im ∧ p.im ≤ w.im) := by
  simp [closedRect, Complex.mem_reProdIm, Set.mem_Icc]

lemma isOpen_inOpenRect (z w : ℂ) : IsOpen {p : ℂ | InOpenRect p z w} := by
  have h1 : IsOpen {p : ℂ | z.re < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {p : ℂ | p.re < w.re} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {p : ℂ | z.im < p.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {p : ℂ | p.im < w.im} := isOpen_lt Complex.continuous_im continuous_const
  have : {p : ℂ | InOpenRect p z w} = {p | z.re < p.re} ∩ {p | p.re < w.re} ∩ {p | z.im < p.im}
      ∩ {p | p.im < w.im} := by
    ext p; simp [InOpenRect, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

lemma InOpenRect.mem_closedRect {p z w : ℂ} (h : InOpenRect p z w) : p ∈ closedRect z w := by
  rw [HaagerupIzumi.mem_closedRect]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩

/-! ### The boundary integral of `1/(ζ - p)` -/

/-- A horizontal segment integral of `1/(x + c)`, when the segment avoids the branch cut. -/
lemma integral_inv_add_horizontal (a b : ℝ) (c : ℂ)
    (hc : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c ∈ slitPlane) :
    ∫ x in a..b, ((x : ℂ) + c)⁻¹ = log (b + c) - log (a + c) := by
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => log ((x : ℂ) + c)) (((x : ℂ) + c)⁻¹) x := by
    intro x hx
    have h1 : HasDerivAt (fun ζ : ℂ => ζ + c) 1 (x : ℂ) := (hasDerivAt_id _).add_const c
    have h2 := (h1.clog (hc x hx)).comp_ofReal
    simpa [one_div] using h2
  rw [integral_eq_sub_of_hasDerivAt hd]
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro x hx
  exact slitPlane_ne_zero (hc x hx)

/-- A vertical segment integral of `1/(c + y I)`, using the branch `log (s ·)` with `s = ±1`. -/
lemma integral_inv_add_vertical (a b : ℝ) (c s : ℂ) (hs : s = 1 ∨ s = -1)
    (hc : ∀ y ∈ Set.uIcc a b, s * (c + (y : ℂ) * I) ∈ slitPlane) :
    ∫ y in a..b, (c + (y : ℂ) * I)⁻¹
      = -I * (log (s * (c + b * I)) - log (s * (c + a * I))) := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hd : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -I * log (s * (c + (y : ℂ) * I))) ((c + (y : ℂ) * I)⁻¹) y := by
    intro y hy
    have h1 : HasDerivAt (fun ζ : ℂ => s * (c + ζ * I)) (s * I) (y : ℂ) := by
      have := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add c).const_mul s
      simpa using this
    have h2 := ((h1.clog (hc y hy)).const_mul (-I)).comp_ofReal
    have hne : c + (y : ℂ) * I ≠ 0 := by
      intro h0
      have := hc y hy
      rw [h0, mul_zero] at this
      exact slitPlane_ne_zero this rfl
    convert h2 using 1
    field_simp
    ring_nf
    simp [I_sq]
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    intro h0
    have := hc y hy
    rw [h0, mul_zero] at this
    exact slitPlane_ne_zero this rfl

/-- The boundary integral of `(ζ - p)⁻¹` over a rectangle containing `p` is `2 π I`. -/
theorem rectBoundary_inv_sub {p z w : ℂ} (hp : InOpenRect p z w) :
    rectBoundary (fun ζ => (ζ - p)⁻¹) z w = 2 * π * I := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  -- the four corners relative to `p`
  set c₁ : ℂ := z.re + z.im * I - p with hc₁
  set c₂ : ℂ := w.re + z.im * I - p with hc₂
  set c₃ : ℂ := w.re + w.im * I - p with hc₃
  set c₄ : ℂ := z.re + w.im * I - p with hc₄
  have i₁ : (∫ x in z.re..w.re, ((x : ℂ) + z.im * I - p)⁻¹) = log c₂ - log c₁ := by
    have : (∫ x in z.re..w.re, ((x : ℂ) + z.im * I - p)⁻¹)
        = ∫ x in z.re..w.re, ((x : ℂ) + (z.im * I - p))⁻¹ := by
      congr 1; ext x; ring_nf
    rw [this, integral_inv_add_horizontal]
    · congr 1 <;> congr 1 <;> ring
    · intro x _
      rw [mem_slitPlane_iff]
      right
      simp
      linarith
  have i₂ : (∫ x in z.re..w.re, ((x : ℂ) + w.im * I - p)⁻¹) = log c₃ - log c₄ := by
    have : (∫ x in z.re..w.re, ((x : ℂ) + w.im * I - p)⁻¹)
        = ∫ x in z.re..w.re, ((x : ℂ) + (w.im * I - p))⁻¹ := by
      congr 1; ext x; ring_nf
    rw [this, integral_inv_add_horizontal]
    · congr 1 <;> congr 1 <;> ring
    · intro x _
      rw [mem_slitPlane_iff]
      right
      simp
      linarith
  have i₃ : (∫ y in z.im..w.im, ((w.re : ℂ) + y * I - p)⁻¹) = -I * (log c₃ - log c₂) := by
    have : (∫ y in z.im..w.im, ((w.re : ℂ) + y * I - p)⁻¹)
        = ∫ y in z.im..w.im, (((w.re : ℂ) - p) + y * I)⁻¹ := by
      congr 1; ext y; ring_nf
    rw [this, integral_inv_add_vertical _ _ _ 1 (Or.inl rfl)]
    · simp only [one_mul]
      congr 1; congr 1 <;> congr 1 <;> ring
    · intro y _
      rw [mem_slitPlane_iff]
      left
      simp
      linarith
  have i₄ : (∫ y in z.im..w.im, ((z.re : ℂ) + y * I - p)⁻¹) = -I * (log (-c₄) - log (-c₁)) := by
    have : (∫ y in z.im..w.im, ((z.re : ℂ) + y * I - p)⁻¹)
        = ∫ y in z.im..w.im, (((z.re : ℂ) - p) + y * I)⁻¹ := by
      congr 1; ext y; ring_nf
    rw [this, integral_inv_add_vertical _ _ _ (-1) (Or.inr rfl)]
    · congr 1; congr 1 <;> congr 1 <;> ring
    · intro y _
      rw [mem_slitPlane_iff]
      left
      simp
      linarith
  -- the two jumps of the logarithm
  have j₄ : log c₄ - log (-c₄) = π * I := by
    have him : 0 < c₄.im := by simp [hc₄]; linarith
    simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos him]
    push_cast; ring
  have j₁ : log (-c₁) - log c₁ = π * I := by
    have him : c₁.im < 0 := by simp [hc₁]; linarith
    simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg him]
    push_cast; ring
  unfold rectBoundary
  simp only [smul_eq_mul]
  rw [i₁, i₂, i₃, i₄]
  have hI : I * I = -1 := I_mul_I
  linear_combination j₄ + j₁ + (-(log c₃ - log c₂) + (log (-c₄) - log (-c₁))) * hI

/-- A horizontal segment integral of `1/(x + c)^2`. -/
lemma integral_inv_add_sq_horizontal (a b : ℝ) (c : ℂ)
    (hc : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c ≠ 0) :
    ∫ x in a..b, (((x : ℂ) + c)⁻¹) ^ 2 = -((b : ℂ) + c)⁻¹ + ((a : ℂ) + c)⁻¹ := by
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => -((x : ℂ) + c)⁻¹) ((((x : ℂ) + c)⁻¹) ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun ζ : ℂ => ζ + c) 1 (x : ℂ) := (hasDerivAt_id _).add_const c
    have h2 := ((h1.inv (hc x hx)).neg).comp_ofReal
    convert h2 using 1
    · funext x; simp [one_div]
    · rw [inv_pow]; ring
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    exact (ContinuousOn.inv₀ (by fun_prop) (fun x hx => hc x hx)).pow 2

/-- A vertical segment integral of `1/(c + y I)^2`. -/
lemma integral_inv_add_sq_vertical (a b : ℝ) (c : ℂ)
    (hc : ∀ y ∈ Set.uIcc a b, c + (y : ℂ) * I ≠ 0) :
    ∫ y in a..b, ((c + (y : ℂ) * I)⁻¹) ^ 2 = I * ((c + b * I)⁻¹ - (c + a * I)⁻¹) := by
  have hd : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => I * (c + (y : ℂ) * I)⁻¹) (((c + (y : ℂ) * I)⁻¹) ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun ζ : ℂ => c + ζ * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add c
    have h2 := ((h1.inv (hc y hy)).const_mul I).comp_ofReal
    convert h2 using 1
    · funext y; simp
    · have hI : I * I = -1 := I_mul_I
      rw [inv_pow]
      linear_combination ((c + (y : ℂ) * I) ^ 2)⁻¹ * hI
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    exact (ContinuousOn.inv₀ (by fun_prop) (fun y hy => hc y hy)).pow 2

/-- The boundary integral of `(ζ - p)⁻²` over a rectangle containing `p` vanishes. -/
theorem rectBoundary_inv_sub_sq {p z w : ℂ} (hp : InOpenRect p z w) :
    rectBoundary (fun ζ => ((ζ - p)⁻¹) ^ 2) z w = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have i₁ : (∫ x in z.re..w.re, (((x : ℂ) + z.im * I - p)⁻¹) ^ 2)
      = -((w.re : ℂ) + (z.im * I - p))⁻¹ + ((z.re : ℂ) + (z.im * I - p))⁻¹ := by
    have : (∫ x in z.re..w.re, (((x : ℂ) + z.im * I - p)⁻¹) ^ 2)
        = ∫ x in z.re..w.re, (((x : ℂ) + (z.im * I - p))⁻¹) ^ 2 := by
      congr 1; ext x; ring_nf
    rw [this, integral_inv_add_sq_horizontal]
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this; linarith
  have i₂ : (∫ x in z.re..w.re, (((x : ℂ) + w.im * I - p)⁻¹) ^ 2)
      = -((w.re : ℂ) + (w.im * I - p))⁻¹ + ((z.re : ℂ) + (w.im * I - p))⁻¹ := by
    have : (∫ x in z.re..w.re, (((x : ℂ) + w.im * I - p)⁻¹) ^ 2)
        = ∫ x in z.re..w.re, (((x : ℂ) + (w.im * I - p))⁻¹) ^ 2 := by
      congr 1; ext x; ring_nf
    rw [this, integral_inv_add_sq_horizontal]
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this; linarith
  have i₃ : (∫ y in z.im..w.im, (((w.re : ℂ) + y * I - p)⁻¹) ^ 2)
      = I * ((((w.re : ℂ) - p) + w.im * I)⁻¹ - (((w.re : ℂ) - p) + z.im * I)⁻¹) := by
    have : (∫ y in z.im..w.im, (((w.re : ℂ) + y * I - p)⁻¹) ^ 2)
        = ∫ y in z.im..w.im, ((((w.re : ℂ) - p) + y * I)⁻¹) ^ 2 := by
      congr 1; ext y; ring_nf
    rw [this, integral_inv_add_sq_vertical]
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this; linarith
  have i₄ : (∫ y in z.im..w.im, (((z.re : ℂ) + y * I - p)⁻¹) ^ 2)
      = I * ((((z.re : ℂ) - p) + w.im * I)⁻¹ - (((z.re : ℂ) - p) + z.im * I)⁻¹) := by
    have : (∫ y in z.im..w.im, (((z.re : ℂ) + y * I - p)⁻¹) ^ 2)
        = ∫ y in z.im..w.im, ((((z.re : ℂ) - p) + y * I)⁻¹) ^ 2 := by
      congr 1; ext y; ring_nf
    rw [this, integral_inv_add_sq_vertical]
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this; linarith
  unfold rectBoundary
  simp only [smul_eq_mul]
  rw [i₁, i₂, i₃, i₄]
  have e1 : (w.re : ℂ) + (z.im * I - p) = ((w.re : ℂ) - p) + z.im * I := by ring
  have e2 : (z.re : ℂ) + (z.im * I - p) = ((z.re : ℂ) - p) + z.im * I := by ring
  have e3 : (w.re : ℂ) + (w.im * I - p) = ((w.re : ℂ) - p) + w.im * I := by ring
  have e4 : (z.re : ℂ) + (w.im * I - p) = ((z.re : ℂ) - p) + w.im * I := by ring
  rw [e1, e2, e3, e4]
  have hI : I * I = -1 := I_mul_I
  linear_combination ((((w.re : ℂ) - p) + w.im * I)⁻¹ - (((w.re : ℂ) - p) + z.im * I)⁻¹
    - (((z.re : ℂ) - p) + w.im * I)⁻¹ + (((z.re : ℂ) - p) + z.im * I)⁻¹) * hI

/-! ### Linearity of the boundary integral -/

/-- The four side integrands are interval integrable. -/
def SidesIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

/-- A point of the boundary of the rectangle. -/
def OnBoundary (ζ z w : ℂ) : Prop :=
  ζ ∈ closedRect z w ∧ (ζ.im = z.im ∨ ζ.im = w.im ∨ ζ.re = z.re ∨ ζ.re = w.re)

lemma OnBoundary.not_inOpenRect {ζ z w : ℂ} (h : OnBoundary ζ z w) : ¬ InOpenRect ζ z w := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases h.2 with h | h | h | h <;> linarith

lemma sidesIntegrable_of_continuousAt {f : ℂ → ℂ} {z w : ℂ} (hzw : z.re ≤ w.re ∧ z.im ≤ w.im)
    (hf : ∀ ζ, OnBoundary ζ z w → ContinuousAt f ζ) : SidesIntegrable f z w := by
  have key : ∀ (g : ℝ → ℂ) (a b : ℝ), (∀ x ∈ Set.uIcc a b, ContinuousAt g x) →
      IntervalIntegrable g volume a b := fun g a b hg =>
    (ContinuousOn.intervalIntegrable (fun x hx => (hg x hx).continuousWithinAt))
  refine ⟨key _ _ _ ?_, key _ _ _ ?_, key _ _ _ ?_, key _ _ _ ?_⟩
  · intro x hx
    rw [Set.uIcc_of_le hzw.1] at hx
    refine (hf _ ⟨?_, Or.inl (by simp)⟩).comp (by fun_prop)
    rw [mem_closedRect]; simp; exact ⟨hx, hzw.2⟩
  · intro x hx
    rw [Set.uIcc_of_le hzw.1] at hx
    refine (hf _ ⟨?_, Or.inr (Or.inl (by simp))⟩).comp (by fun_prop)
    rw [mem_closedRect]; simp; exact ⟨hx, hzw.2⟩
  · intro y hy
    rw [Set.uIcc_of_le hzw.2] at hy
    refine (hf _ ⟨?_, Or.inr (Or.inr (Or.inr (by simp)))⟩).comp (by fun_prop)
    rw [mem_closedRect]; simp; exact ⟨hzw.1, hy⟩
  · intro y hy
    rw [Set.uIcc_of_le hzw.2] at hy
    refine (hf _ ⟨?_, Or.inr (Or.inr (Or.inl (by simp)))⟩).comp (by fun_prop)
    rw [mem_closedRect]; simp; exact ⟨hzw.1, hy⟩

lemma rectBoundary_sub {f g : ℂ → ℂ} {z w : ℂ} (hf : SidesIntegrable f z w)
    (hg : SidesIntegrable g z w) :
    rectBoundary (fun ζ => f ζ - g ζ) z w = rectBoundary f z w - rectBoundary g z w := by
  unfold rectBoundary
  rw [integral_sub hf.1 hg.1, integral_sub hf.2.1 hg.2.1, integral_sub hf.2.2.1 hg.2.2.1,
    integral_sub hf.2.2.2 hg.2.2.2]
  simp only [smul_eq_mul]; ring

lemma rectBoundary_add {f g : ℂ → ℂ} {z w : ℂ} (hf : SidesIntegrable f z w)
    (hg : SidesIntegrable g z w) :
    rectBoundary (fun ζ => f ζ + g ζ) z w = rectBoundary f z w + rectBoundary g z w := by
  unfold rectBoundary
  rw [integral_add hf.1 hg.1, integral_add hf.2.1 hg.2.1, integral_add hf.2.2.1 hg.2.2.1,
    integral_add hf.2.2.2 hg.2.2.2]
  simp only [smul_eq_mul]; ring

lemma rectBoundary_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundary (fun ζ => c * f ζ) z w = c * rectBoundary f z w := by
  unfold rectBoundary
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]; ring

lemma rectBoundary_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z w : ℂ)
    (hf : ∀ i ∈ s, SidesIntegrable (f i) z w) :
    rectBoundary (fun ζ => ∑ i ∈ s, f i ζ) z w = ∑ i ∈ s, rectBoundary (f i) z w := by
  unfold rectBoundary
  rw [integral_finsetSum (fun i hi => (hf i hi).1), integral_finsetSum (fun i hi => (hf i hi).2.1),
    integral_finsetSum (fun i hi => (hf i hi).2.2.1),
    integral_finsetSum (fun i hi => (hf i hi).2.2.2)]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-! ### The residue theorem on a rectangle -/

/-- Near a point `p` of a finite set `S` there are no other points of `S`. -/
lemma eventually_not_mem_erase (S : Finset ℂ) (p : ℂ) :
    ∀ᶠ ζ in 𝓝 p, ζ ∉ (S.erase p : Set ℂ) := by
  have hcl : IsClosed (S.erase p : Set ℂ) := (S.erase p).finite_toSet.isClosed
  exact hcl.isOpen_compl.mem_nhds (by simp)

/-- The residue theorem for a rectangle: `f` is differentiable on the closed rectangle except at
the points of a finite set `S` of interior points, at each of which it has a simple pole with
residue `ρ p`. -/
theorem rectBoundary_eq_sum_residues_gen (f : ℂ → ℂ) (z w : ℂ) (hzw : z.re < w.re ∧ z.im < w.im)
    (S : Finset ℂ) (hS : ∀ p ∈ S, InOpenRect p z w) (ρ : ℂ → ℂ)
    (hres : ∀ p ∈ S, HasResidueGen f p (ρ p))
    (hd : ∀ x ∈ closedRect z w \ ↑S, DifferentiableAt ℂ f x) :
    rectBoundary f z w = 2 * π * I * ∑ p ∈ S, ρ p := by
  classical
  choose! c hc using hres
  -- the function with the principal parts removed
  set g : ℂ → ℂ := fun ζ => f ζ - ∑ p ∈ S, (ρ p * (ζ - p)⁻¹ + c p * ((ζ - p)⁻¹) ^ 2) with hg
  have hgd : ∀ x ∈ closedRect z w \ ↑S, DifferentiableAt ℂ g x := by
    intro x hx
    refine (hd x hx).sub (DifferentiableAt.fun_sum fun p hp => ?_)
    have hne : x - p ≠ 0 := sub_ne_zero.2 (fun h => hx.2 (h ▸ hp))
    exact (((differentiableAt_id.sub_const p).inv hne).const_mul _).add
      ((((differentiableAt_id.sub_const p).inv hne).pow 2).const_mul _)
  -- the boundary avoids `S`
  have hbS : ∀ ζ, OnBoundary ζ z w → ζ ∉ (S : Set ℂ) := fun ζ hζ hζS =>
    hζ.not_inOpenRect (hS ζ hζS)
  -- `g` extended continuously to the points of `S`
  set g' : ℂ → ℂ := fun ζ => if ζ ∈ S then limUnder (𝓝[≠] ζ) g else g ζ with hg'
  have hg'_eq : ∀ ζ, ζ ∉ S → g' ζ = g ζ := fun ζ hζ => by simp [hg', hζ]
  -- continuity of `g'` at the points of the closed rectangle
  have hcont : ∀ ζ ∈ closedRect z w, ContinuousAt g' ζ := by
    intro ζ hζ
    by_cases hζS : ζ ∈ S
    · -- removable singularity
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hS ζ hζS
      have hU : {q : ℂ | InOpenRect q z w} ∩ (S.erase ζ : Set ℂ)ᶜ ∈ 𝓝 ζ := by
        refine Filter.inter_mem ((isOpen_inOpenRect z w).mem_nhds ⟨hp1, hp2, hp3, hp4⟩) ?_
        exact eventually_not_mem_erase S ζ
      set U := {q : ℂ | InOpenRect q z w} ∩ (S.erase ζ : Set ℂ)ᶜ with hUdef
      have hdU : DifferentiableOn ℂ g (U \ {ζ}) := by
        intro q hq
        apply (hgd q ?_).differentiableWithinAt
        refine ⟨hq.1.1.mem_closedRect, ?_⟩
        intro hqS
        have : q ∈ (S.erase ζ : Set ℂ) := by
          simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
          exact ⟨hqS, hq.2⟩
        exact hq.1.2 this
      have ho : (fun q => g q - g ζ) =o[𝓝[≠] ζ] fun q => (q - ζ)⁻¹ := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · -- `(q - ζ) (g q - g ζ) → 0`
          have hlim : Tendsto (fun q => (q - ζ) * g q) (𝓝[≠] ζ) (𝓝 0) := by
            have hsum : ∀ q, q ≠ ζ → (q - ζ) * g q
                = ((q - ζ) * f q - c ζ * (q - ζ)⁻¹) - ρ ζ
                  - ∑ p ∈ S.erase ζ, (ρ p * ((q - ζ) * (q - p)⁻¹)
                    + c p * ((q - ζ) * ((q - p)⁻¹) ^ 2)) := by
              intro q hq
              simp only [hg]
              have hqζ : q - ζ ≠ 0 := sub_ne_zero.2 hq
              rw [← Finset.add_sum_erase S _ hζS, mul_sub, mul_add, Finset.mul_sum]
              have e1 : (q - ζ) * (ρ ζ * (q - ζ)⁻¹ + c ζ * ((q - ζ)⁻¹) ^ 2)
                  = ρ ζ + c ζ * (q - ζ)⁻¹ := by
                field_simp
              rw [e1]
              have e2 : ∑ x ∈ S.erase ζ, (q - ζ) * (ρ x * (q - x)⁻¹ + c x * ((q - x)⁻¹) ^ 2)
                  = ∑ p ∈ S.erase ζ, (ρ p * ((q - ζ) * (q - p)⁻¹)
                    + c p * ((q - ζ) * ((q - p)⁻¹) ^ 2)) := by
                apply Finset.sum_congr rfl; intro p _; ring
              rw [e2]; ring
            have h1 : Tendsto (fun q => ((q - ζ) * f q - c ζ * (q - ζ)⁻¹) - ρ ζ
                - ∑ p ∈ S.erase ζ, (ρ p * ((q - ζ) * (q - p)⁻¹)
                    + c p * ((q - ζ) * ((q - p)⁻¹) ^ 2))) (𝓝[≠] ζ) (𝓝 0) := by
              have hA := hc ζ hζS
              have hB : Tendsto (fun q => ∑ p ∈ S.erase ζ, (ρ p * ((q - ζ) * (q - p)⁻¹)
                  + c p * ((q - ζ) * ((q - p)⁻¹) ^ 2))) (𝓝[≠] ζ) (𝓝 0) := by
                have h0 : (0 : ℂ) = ∑ p ∈ S.erase ζ, (ρ p * ((ζ - ζ) * (ζ - p)⁻¹)
                    + c p * ((ζ - ζ) * ((ζ - p)⁻¹) ^ 2)) := by simp
                rw [h0]
                apply tendsto_nhdsWithin_of_tendsto_nhds
                apply tendsto_finset_sum
                intro p hp
                have hpζ : ζ - p ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hp).symm
                exact ((continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).mul
                  ((continuousAt_id.sub continuousAt_const).inv₀ hpζ))).add
                  (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).mul
                  (((continuousAt_id.sub continuousAt_const).inv₀ hpζ).pow 2)))).tendsto
              have := (hA.sub (tendsto_const_nhds (x := ρ ζ))).sub hB
              simpa using this
            exact h1.congr' (by
              filter_upwards [self_mem_nhdsWithin] with q hq
              rw [hsum q hq])
          have h2 : Tendsto (fun q => (q - ζ) * g ζ) (𝓝[≠] ζ) (𝓝 0) := by
            have : Tendsto (fun q => (q - ζ) * g ζ) (𝓝 ζ) (𝓝 ((ζ - ζ) * g ζ)) :=
              ((continuous_id.sub continuous_const).mul continuous_const).tendsto ζ
            simp at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          have := hlim.sub h2
          simp only [sub_zero] at this
          refine this.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with q hq
          rw [div_inv_eq_mul]; ring
        · filter_upwards [self_mem_nhdsWithin] with q hq h0
          exact absurd h0 (inv_ne_zero (sub_ne_zero.2 hq))
      have hdiff := Complex.differentiableOn_update_limUnder_of_isLittleO hU hdU ho
      have hcU : ContinuousAt (Function.update g ζ (limUnder (𝓝[≠] ζ) g)) ζ :=
        (hdiff.differentiableAt hU).continuousAt
      refine hcU.congr ?_
      filter_upwards [hU] with q hq
      by_cases hqζ : q = ζ
      · subst hqζ; simp [hg', hζS]
      · have hqS : q ∉ S := by
          intro h
          exact hq.2 (by simp [Finset.coe_erase, h, hqζ])
        rw [Function.update_of_ne hqζ, hg'_eq q hqS]
    · have : g' =ᶠ[𝓝 ζ] g := by
        have hcl : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
        filter_upwards [hcl.isOpen_compl.mem_nhds hζS] with q hq
        exact hg'_eq q hq
      exact ((hgd ζ ⟨hζ, hζS⟩).continuousAt).congr this.symm
  -- differentiability of `g'` off `S`
  have hdiff' : ∀ x ∈ closedRect z w \ ↑S, DifferentiableAt ℂ g' x := by
    intro x hx
    have : g' =ᶠ[𝓝 x] g := by
      have hcl : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds hx.2] with q hq
      exact hg'_eq q hq
    exact (hgd x hx).congr_of_eventuallyEq this
  -- Cauchy–Goursat for `g'`
  have hzero : rectBoundary g' z w = 0 := by
    apply rectBoundary_eq_zero g' z w S S.countable_toSet
    · rw [Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le]
      exact fun ζ hζ => (hcont ζ hζ).continuousWithinAt
    · intro x hx
      apply hdiff'
      rw [min_eq_left hzw.1.le, max_eq_right hzw.1.le, min_eq_left hzw.2.le,
        max_eq_right hzw.2.le] at hx
      refine ⟨?_, hx.2⟩
      rw [mem_closedRect]
      have := (Complex.mem_reProdIm.1 hx.1)
      exact ⟨⟨this.1.1.le, this.1.2.le⟩, ⟨this.2.1.le, this.2.2.le⟩⟩
  -- `g'` and `g` agree on the boundary
  have hgg' : rectBoundary g' z w = rectBoundary g z w := by
    unfold rectBoundary
    have e : ∀ (a b : ℝ) (φ : ℝ → ℂ), (∀ x ∈ Set.uIcc a b, OnBoundary (φ x) z w) →
        ∫ x in a..b, g' (φ x) = ∫ x in a..b, g (φ x) := by
      intro a b φ hφ
      apply integral_congr
      intro x hx
      exact hg'_eq _ (hbS _ (hφ x hx))
    rw [e _ _ (fun x : ℝ => (x : ℂ) + z.im * I), e _ _ (fun x : ℝ => (x : ℂ) + w.im * I),
      e _ _ (fun y : ℝ => (w.re : ℂ) + y * I), e _ _ (fun y : ℝ => (z.re : ℂ) + y * I)]
    all_goals
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [mem_closedRect]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
          add_im, mul_im, zero_add, add_zero]
        first
          | (rw [Set.uIcc_of_le hzw.1.le] at hx; exact ⟨hx, ⟨le_rfl, hzw.2.le⟩⟩)
          | (rw [Set.uIcc_of_le hzw.1.le] at hx; exact ⟨hx, ⟨hzw.2.le, le_rfl⟩⟩)
          | (rw [Set.uIcc_of_le hzw.2.le] at hx; exact ⟨⟨hzw.1.le, le_rfl⟩, hx⟩)
          | (rw [Set.uIcc_of_le hzw.2.le] at hx; exact ⟨⟨le_rfl, hzw.1.le⟩, hx⟩)
      · simp
  -- linearity
  have hfS : SidesIntegrable f z w :=
    sidesIntegrable_of_continuousAt ⟨hzw.1.le, hzw.2.le⟩
      (fun ζ hζ => (hd ζ ⟨hζ.1, hbS ζ hζ⟩).continuousAt)
  have hpS : ∀ p ∈ S, SidesIntegrable (fun ζ => ρ p * (ζ - p)⁻¹ + c p * ((ζ - p)⁻¹) ^ 2) z w := by
    intro p hp
    apply sidesIntegrable_of_continuousAt ⟨hzw.1.le, hzw.2.le⟩
    intro ζ hζ
    have hne : ζ - p ≠ 0 := sub_ne_zero.2 (fun h => hbS ζ hζ (h ▸ hp))
    exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hne)).add
      (continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).inv₀ hne).pow 2))
  have hsumS : SidesIntegrable (fun ζ => ∑ p ∈ S, (ρ p * (ζ - p)⁻¹ + c p * ((ζ - p)⁻¹) ^ 2)) z w := by
    apply sidesIntegrable_of_continuousAt ⟨hzw.1.le, hzw.2.le⟩
    intro ζ hζ
    refine tendsto_finset_sum _ (fun p hp => ?_)
    have hne : ζ - p ≠ 0 := sub_ne_zero.2 (fun h => hbS ζ hζ (h ▸ hp))
    exact ((continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hne)).add
      (continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).inv₀ hne).pow 2))).tendsto
  have hpS1 : ∀ p ∈ S, SidesIntegrable (fun ζ => ρ p * (ζ - p)⁻¹) z w := by
    intro p hp
    apply sidesIntegrable_of_continuousAt ⟨hzw.1.le, hzw.2.le⟩
    intro ζ hζ
    have hne : ζ - p ≠ 0 := sub_ne_zero.2 (fun h => hbS ζ hζ (h ▸ hp))
    exact continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hne)
  have hpS2 : ∀ p ∈ S, SidesIntegrable (fun ζ => c p * ((ζ - p)⁻¹) ^ 2) z w := by
    intro p hp
    apply sidesIntegrable_of_continuousAt ⟨hzw.1.le, hzw.2.le⟩
    intro ζ hζ
    have hne : ζ - p ≠ 0 := sub_ne_zero.2 (fun h => hbS ζ hζ (h ▸ hp))
    exact continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).inv₀ hne).pow 2)
  have hlin : rectBoundary g z w = rectBoundary f z w - 2 * π * I * ∑ p ∈ S, ρ p := by
    rw [hg, rectBoundary_sub hfS hsumS, rectBoundary_finset_sum S _ z w hpS]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [rectBoundary_add (hpS1 p hp) (hpS2 p hp), rectBoundary_const_mul,
      rectBoundary_const_mul, rectBoundary_inv_sub (hS p hp), rectBoundary_inv_sub_sq (hS p hp)]
    ring
  rw [hgg', hlin] at hzero
  linear_combination hzero

/-- The residue theorem for a rectangle with simple poles. -/
theorem rectBoundary_eq_sum_residues (f : ℂ → ℂ) (z w : ℂ) (hzw : z.re < w.re ∧ z.im < w.im)
    (S : Finset ℂ) (hS : ∀ p ∈ S, InOpenRect p z w) (ρ : ℂ → ℂ)
    (hres : ∀ p ∈ S, HasResidue f p (ρ p))
    (hd : ∀ x ∈ closedRect z w \ ↑S, DifferentiableAt ℂ f x) :
    rectBoundary f z w = 2 * π * I * ∑ p ∈ S, ρ p :=
  rectBoundary_eq_sum_residues_gen f z w hzw S hS ρ (fun p hp => (hres p hp).hasResidueGen) hd

/-! ### The strip version -/

/-- `t ↦ M exp (-c |t|)` is integrable for `c > 0`. -/
lemma integrable_const_mul_exp_neg_mul_abs (M c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => M * Real.exp (-c * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [abs_of_pos (Set.mem_Ioi.1 ht)]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Iic 0) := by
    have h3 := h1.comp_neg
    rw [Set.neg_Ioi, neg_zero] at h3
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    refine h3.congr_fun (fun t _ => ?_) measurableSet_Iio
    simp
  have := (h2.union h1)
  rw [Set.Iic_union_Ioi, integrableOn_univ] at this
  exact this.const_mul M

/-- The residue theorem on the closed strip `a ≤ Re ζ ≤ b`: `f` is differentiable there except at
the points of a finite set `S` of interior points with `|Im p| < T`, where it has simple poles, and
`f` decays exponentially on the strip for `|Im ζ| ≥ T`. Then the two vertical line integrals are
convergent and their difference is `2 π I` times the sum of the residues. -/
theorem strip_residues_gen (f : ℂ → ℂ) (a b : ℝ) (hab : a < b) (S : Finset ℂ) (T : ℝ) (hT : 0 < T)
    (hS : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ |p.im| < T) (ρ : ℂ → ℂ)
    (hres : ∀ p ∈ S, HasResidueGen f p (ρ p))
    (hd : ∀ ζ, a ≤ ζ.re → ζ.re ≤ b → ζ ∉ S → DifferentiableAt ℂ f ζ)
    (M c : ℝ) (hc : 0 < c)
    (hbound : ∀ ζ, a ≤ ζ.re → ζ.re ≤ b → T ≤ |ζ.im| → ‖f ζ‖ ≤ M * Real.exp (-c * |ζ.im|)) :
    Integrable (fun t : ℝ => f (a + t * I)) ∧ Integrable (fun t : ℝ => f (b + t * I)) ∧
    lineIntegral f b - lineIntegral f a = 2 * π * I * ∑ p ∈ S, ρ p := by
  have hre : ∀ (σ t : ℝ), ((σ : ℂ) + t * I).re = σ := by intro σ t; simp
  have him : ∀ (σ t : ℝ), ((σ : ℂ) + t * I).im = t := by intro σ t; simp
  -- integrability along vertical lines
  have hvert : ∀ σ : ℝ, a ≤ σ → σ ≤ b → (∀ t : ℝ, (σ : ℂ) + t * I ∉ S) →
      Integrable (fun t : ℝ => f (σ + t * I)) := by
    intro σ hσa hσb hσS
    have hcont : Continuous (fun t : ℝ => f (σ + t * I)) := by
      rw [continuous_iff_continuousAt]; intro t
      exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I)
        (hd _ (by rw [hre]; exact hσa) (by rw [hre]; exact hσb) (hσS t)).continuousAt (by fun_prop)
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
      hcont.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨by linarith, hT.le⟩)
    set M' := max M (B * Real.exp (c * T)) with hM'
    have hglob : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ M' * Real.exp (-c * |t|) := by
      intro t
      by_cases ht : T ≤ |t|
      · have := hbound (σ + t * I) (by rw [hre]; exact hσa) (by rw [hre]; exact hσb)
          (by rw [him]; exact ht)
        rw [him] at this
        calc ‖f (σ + t * I)‖ ≤ M * Real.exp (-c * |t|) := this
          _ ≤ M' * Real.exp (-c * |t|) := by gcongr; exact le_max_left _ _
      · push_neg at ht
        have hmem : t ∈ Icc (-T) T := abs_le.1 ht.le |> fun h => ⟨h.1, h.2⟩
        have h1 := hB t hmem
        have h2 : Real.exp (-c * T) ≤ Real.exp (-c * |t|) := by
          apply Real.exp_le_exp.2; nlinarith
        calc ‖f (σ + t * I)‖ ≤ B := h1
          _ = B * Real.exp (c * T) * Real.exp (-c * T) := by
              rw [mul_assoc, ← Real.exp_add]; simp
          _ ≤ B * Real.exp (c * T) * Real.exp (-c * |t|) := by gcongr
          _ ≤ M' * Real.exp (-c * |t|) := by gcongr; exact le_max_right _ _
    exact (integrable_const_mul_exp_neg_mul_abs M' c hc).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hglob)
  have hSa : ∀ t : ℝ, (a : ℂ) + t * I ∉ S := fun t h => by
    have := (hS _ h).1; rw [hre] at this; exact lt_irrefl _ this
  have hSb : ∀ t : ℝ, (b : ℂ) + t * I ∉ S := fun t h => by
    have := (hS _ h).2.1; rw [hre] at this; exact lt_irrefl _ this
  have hia := hvert a le_rfl hab.le hSa
  have hib := hvert b hab.le le_rfl hSb
  refine ⟨hia, hib, ?_⟩
  -- the rectangle identity for every `R > T`
  have hrect : ∀ R : ℝ, T < R →
      rectBoundary f (Complex.mk a (-R)) (Complex.mk b R) = 2 * π * I * ∑ p ∈ S, ρ p := by
    intro R hR
    apply rectBoundary_eq_sum_residues_gen f _ _ ⟨hab, by simp; linarith⟩ S _ ρ hres
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [mem_closedRect] at hx1
      exact hd x hx1.1.1 hx1.1.2 hx2
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hS p hp
      have := abs_lt.1 h3
      exact ⟨h1, h2, by simp; linarith, by simp; linarith⟩
  -- unfolding the rectangle boundary
  have hunf : ∀ R : ℝ, rectBoundary f (Complex.mk a (-R)) (Complex.mk b R)
      = (∫ x in a..b, f (x + ((-R : ℝ) : ℂ) * I)) - (∫ x in a..b, f (x + (R : ℂ) * I))
        + I • (∫ y in (-R)..R, f (b + y * I)) - I • (∫ y in (-R)..R, f (a + y * I)) :=
    fun R => rfl
  -- horizontal sides vanish in the limit
  have hexp0 : Tendsto (fun R : ℝ => M * Real.exp (-c * R) * |b - a|) atTop (𝓝 0) := by
    have := ((Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hc))).const_mul M).mul_const |b - a|
    simpa using this
  have hH : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun R : ℝ => ∫ x in a..b, f (x + ((s * R : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro s hs
    refine squeeze_zero_norm' ?_ hexp0
    filter_upwards [eventually_gt_atTop T] with R hR
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab.le] at hx
    have hsR : |s * R| = R := by
      rcases hs with rfl | rfl <;> simp [abs_of_pos (hT.trans hR)]
    have := hbound (x + ((s * R : ℝ) : ℂ) * I) (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
      (by rw [him, hsR]; exact hR.le)
    rw [him, hsR] at this
    exact this
  have hH1 := hH (-1) (Or.inr rfl)
  have hH2 := hH 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hH1 hH2
  -- vertical sides converge to the line integrals
  have hV3 : Tendsto (fun R : ℝ => I • ∫ y in (-R)..R, f (b + y * I)) atTop
      (𝓝 (I • ∫ t : ℝ, f (b + t * I))) :=
    (intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hV4 : Tendsto (fun R : ℝ => I • ∫ y in (-R)..R, f (a + y * I)) atTop
      (𝓝 (I • ∫ t : ℝ, f (a + t * I))) :=
    (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hlim : Tendsto (fun R : ℝ => rectBoundary f (Complex.mk a (-R)) (Complex.mk b R)) atTop
      (𝓝 (0 - 0 + I • (∫ t : ℝ, f (b + t * I)) - I • (∫ t : ℝ, f (a + t * I)))) := by
    simp only [hunf]
    exact ((hH1.sub hH2).add hV3).sub hV4
  have hconst : Tendsto (fun R : ℝ => rectBoundary f (Complex.mk a (-R)) (Complex.mk b R)) atTop
      (𝓝 (2 * π * I * ∑ p ∈ S, ρ p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop T] with R hR
    exact (hrect R hR).symm
  have key := tendsto_nhds_unique hconst hlim
  unfold lineIntegral
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, key]
  simp only [smul_eq_mul]; ring

/-- The strip theorem with simple poles. -/
theorem strip_residues (f : ℂ → ℂ) (a b : ℝ) (hab : a < b) (S : Finset ℂ) (T : ℝ) (hT : 0 < T)
    (hS : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ |p.im| < T) (ρ : ℂ → ℂ)
    (hres : ∀ p ∈ S, HasResidue f p (ρ p))
    (hd : ∀ ζ, a ≤ ζ.re → ζ.re ≤ b → ζ ∉ S → DifferentiableAt ℂ f ζ)
    (M c : ℝ) (hc : 0 < c)
    (hbound : ∀ ζ, a ≤ ζ.re → ζ.re ≤ b → T ≤ |ζ.im| → ‖f ζ‖ ≤ M * Real.exp (-c * |ζ.im|)) :
    Integrable (fun t : ℝ => f (a + t * I)) ∧ Integrable (fun t : ℝ => f (b + t * I)) ∧
    lineIntegral f b - lineIntegral f a = 2 * π * I * ∑ p ∈ S, ρ p :=
  strip_residues_gen f a b hab S T hT hS ρ (fun p hp => (hres p hp).hasResidueGen) hd M c hc hbound

end HaagerupIzumi
