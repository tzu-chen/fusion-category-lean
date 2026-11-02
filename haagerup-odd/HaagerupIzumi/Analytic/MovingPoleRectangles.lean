module

public import HaagerupIzumi.Analytic.GammaTwoContour
import all Mathlib.Data.Complex.Basic

/-!
# Fixed rectangles for continuously moving isolated pole clusters

Each pole family moves by a continuous translation. Around an isolated base
point, a fixed square contains exactly the translates of that base point and
has no poles on its boundary. The spacing estimate also gives disjoint
rectangles around different base points, including coincident labels within
one cluster.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology

namespace HaagerupIzumi.MovingPoleRectangles

def lower (p : ℂ) (ε : ℝ) : ℂ := ⟨p.re - ε, p.im - ε⟩
def upper (p : ℂ) (ε : ℝ) : ℂ := ⟨p.re + ε, p.im + ε⟩

lemma lower_lt_upper (p : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (lower p ε).re < (upper p ε).re ∧ (lower p ε).im < (upper p ε).im := by
  simp only [lower, upper]
  constructor <;> linarith

lemma norm_sub_le_of_mem_closedRect {p z : ℂ} {ε : ℝ}
    (hz : z ∈ closedRect (lower p ε) (upper p ε)) : ‖z - p‖ ≤ 2 * ε := by
  rw [mem_closedRect] at hz
  simp only [lower, upper] at hz
  have hre : |(z - p).re| ≤ ε := by
    rw [sub_re, abs_le]
    constructor <;> linarith [hz.1.1, hz.1.2]
  have him : |(z - p).im| ≤ ε := by
    rw [sub_im, abs_le]
    constructor <;> linarith [hz.2.1, hz.2.2]
  exact (norm_le_abs_re_add_abs_im (z - p)).trans (by linarith)

lemma inOpenRect_add_of_norm_lt (p d : ℂ) {ε : ℝ} (hd : ‖d‖ < ε) :
    InOpenRect (p + d) (lower p ε) (upper p ε) := by
  have hre := abs_lt.mp ((abs_re_le_norm d).trans_lt hd)
  have him := abs_lt.mp ((abs_im_le_norm d).trans_lt hd)
  simp only [InOpenRect, lower, upper, add_re, add_im]
  exact ⟨by linarith [hre.1], by linarith [hre.2],
    by linarith [him.1], by linarith [him.2]⟩

/-- Isolated finite families admit one common quantitative isolation radius
at any chosen point, whether or not the point belongs to every family. -/
lemma exists_isolation_radius {ι : Type*} [Fintype ι] (S : ι → Set ℂ) (p : ℂ)
    (hiso : ∀ i, ∀ᶠ z in 𝓝[≠] p, z ∉ S i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i q, q ∈ S i → q ≠ p → 8 * ε ≤ ‖q - p‖ := by
  have hev : ∀ᶠ z in 𝓝 p, ∀ i, z ∈ S i → z = p := by
    rw [Filter.eventually_all]
    intro i
    have hi := eventually_nhdsWithin_iff.mp (hiso i)
    filter_upwards [hi] with z hz hzS
    by_contra hzp
    exact hz hzp hzS
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ / 8, by positivity, ?_⟩
  intro i q hq hqp
  have hn : δ ≤ ‖q - p‖ := by
    by_contra h
    have hqball : q ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_not_ge h
    exact hqp (hball hqball i hq)
  linarith

/-- A fixed square captures exactly the original point of each continuously
translated family. In particular its boundary stays clear of all poles. -/
theorem exists_fixed_rectangle {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (S : ι → Set ℂ) (d : ι → X → ℂ) (x₀ : X) (p : ℂ)
    (hiso : ∀ i, ∀ᶠ z in 𝓝[≠] p, z ∉ S i)
    (hd : ∀ i, ContinuousAt (d i) x₀) (hd₀ : ∀ i, d i x₀ = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i q, q ∈ S i → q ≠ p → 8 * ε ≤ ‖q - p‖) ∧
      ∀ᶠ x in 𝓝 x₀,
        (∀ i, InOpenRect (p + d i x) (lower p ε) (upper p ε)) ∧
        (∀ i q, q ∈ S i →
          (q + d i x ∈ closedRect (lower p ε) (upper p ε) ↔ q = p)) ∧
        (∀ i q, q ∈ S i → ¬ OnBoundary (q + d i x) (lower p ε) (upper p ε)) := by
  obtain ⟨ε, hε, hsep⟩ := exists_isolation_radius S p hiso
  refine ⟨ε, hε, hsep, ?_⟩
  have hsmall : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖d i x‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have hi := (hd i).eventually (Metric.ball_mem_nhds (d i x₀) hε)
    simpa only [hd₀ i, Metric.mem_ball, dist_zero_right] using hi
  filter_upwards [hsmall] with x hx
  have hopen : ∀ i, InOpenRect (p + d i x) (lower p ε) (upper p ε) :=
    fun i => inOpenRect_add_of_norm_lt p (d i x) (hx i)
  have hcapture : ∀ i q, q ∈ S i →
      (q + d i x ∈ closedRect (lower p ε) (upper p ε) ↔ q = p) := by
    intro i q hq
    constructor
    · intro hqrect
      by_contra hqp
      have hnorm : ‖q - p‖ < 3 * ε := by
        calc
          ‖q - p‖ = ‖(q + d i x - p) - d i x‖ := by congr 1; ring
          _ ≤ ‖q + d i x - p‖ + ‖d i x‖ := norm_sub_le _ _
          _ < 3 * ε := by
            have hrect := norm_sub_le_of_mem_closedRect hqrect
            linarith [hx i]
      have hfar := hsep i q hq hqp
      linarith
    · rintro rfl
      exact (hopen i).mem_closedRect
  refine ⟨hopen, hcapture, ?_⟩
  intro i q hq hboundary
  have hqp := (hcapture i q hq).mp hboundary.1
  subst q
  exact hboundary.not_inOpenRect (hopen i)

/-- The quantitative radii above make rectangles around distinct clusters
disjoint as sets, not merely disjoint in their enclosed pole lists. -/
lemma closedRect_disjoint {p q : ℂ} {ε δ : ℝ} (hpq : p ≠ q)
    (hε : 8 * ε ≤ ‖q - p‖) (hδ : 8 * δ ≤ ‖q - p‖) :
    Disjoint (closedRect (lower p ε) (upper p ε))
      (closedRect (lower q δ) (upper q δ)) := by
  apply Set.disjoint_left.mpr
  intro z hz hp
  have hpz := norm_sub_le_of_mem_closedRect hz
  have hqz := norm_sub_le_of_mem_closedRect hp
  have hd : ‖q - p‖ ≤ 2 * ε + 2 * δ := by
    calc
      ‖q - p‖ = ‖(z - p) - (z - q)‖ := by congr 1; ring
      _ ≤ ‖z - p‖ + ‖z - q‖ := norm_sub_le _ _
      _ ≤ 2 * ε + 2 * δ := by linarith
  have hpos : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  linarith

end HaagerupIzumi.MovingPoleRectangles
