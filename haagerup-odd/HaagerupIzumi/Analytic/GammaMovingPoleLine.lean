module

public import HaagerupIzumi.Analytic.GammaMovingPoleRectangles
public import HaagerupIzumi.Analytic.MovingPoleClusters
import all Mathlib.Data.Complex.Basic

/-! # A fixed vertical line for nearby moving gamma poles -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaMovingPoleRectangles

/-- Finite right tails prevent any new crossing from arriving from infinity
under a sufficiently small translation. -/
lemma eventually_crossing_iff {X : Type*} [TopologicalSpace X]
    (S : Set ℂ) (σ : ℝ) (hfin : {q ∈ S | σ - 1 < q.re}.Finite)
    (hσ : ∀ q ∈ S, q.re ≠ σ) (d : X → ℂ) (x₀ : X)
    (hd : ContinuousAt d x₀) (hd₀ : d x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, ∀ q ∈ S,
      (σ < (q + d x).re ↔ σ < q.re) ∧ (q + d x).re ≠ σ := by
  have hlocal : ∀ q ∈ {q ∈ S | σ - 1 < q.re},
      ∀ᶠ x in 𝓝 x₀, (σ < (q + d x).re ↔ σ < q.re) ∧ (q + d x).re ≠ σ := by
    intro q hq
    have hc : Tendsto (fun x => (q + d x).re) (𝓝 x₀) (𝓝 q.re) := by
      have hc' := Complex.continuous_re.continuousAt.comp (x := x₀) (f := fun x => q + d x)
        (continuousAt_const.add hd)
      simpa only [Function.comp_def, hd₀, add_zero] using hc'.tendsto
    by_cases hqσ : σ < q.re
    · filter_upwards [hc.eventually (lt_mem_nhds hqσ)] with x hx
      exact ⟨iff_of_true hx hqσ, ne_of_gt hx⟩
    · have hqσ' : q.re < σ := lt_of_le_of_ne (le_of_not_gt hqσ) (hσ q hq.1)
      filter_upwards [hc.eventually (gt_mem_nhds hqσ')] with x hx
      exact ⟨iff_of_false (not_lt_of_ge hx.le) hqσ, ne_of_lt hx⟩
  have hall := hfin.eventually_all.mpr hlocal
  have hsmall : ∀ᶠ x in 𝓝 x₀, ‖d x‖ < 1 := by
    simpa only [hd₀, Metric.mem_ball, dist_zero_right] using
      hd.eventually (Metric.ball_mem_nhds (d x₀) zero_lt_one)
  filter_upwards [hall, hsmall] with x hx hdx
  intro q hq
  by_cases hqF : σ - 1 < q.re
  · exact hx q ⟨hq, hqF⟩
  · have hqle : q.re ≤ σ - 1 := le_of_not_gt hqF
    have hdre : (d x).re < 1 := (le_abs_self _).trans_lt ((abs_re_le_norm _).trans_lt hdx)
    have hqσ : q.re < σ := by linarith
    have hqxσ : (q + d x).re < σ := by simp only [add_re]; linarith
    exact ⟨iff_of_false (not_lt_of_ge hqxσ.le) (not_lt_of_ge hqσ.le), ne_of_lt hqxσ⟩

theorem eventually_left_crossing_iff {X : Type*} [TopologicalSpace X]
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (L : Fin 2 → X → ℂ) (x₀ : X) (σ : ℝ)
    (hL : ∀ i, ContinuousAt (L i) x₀)
    (hσ : ∀ i q, q ∈ leftFamily a b (L i x₀) → q.re ≠ σ) :
    ∀ᶠ x in 𝓝 x₀, ∀ i q, q ∈ leftFamily a b (L i x₀) →
      (σ < (q + (L i x₀ - L i x)).re ↔ σ < q.re) ∧
        (q + (L i x₀ - L i x)).re ≠ σ := by
  rw [Filter.eventually_all]
  intro i
  exact eventually_crossing_iff (leftFamily a b (L i x₀)) σ
    (GammaK4Contour.leftFamily_crossed_finite (hb.trans_le hba) hb (L i x₀) (σ - 1))
    (hσ i) (fun x => L i x₀ - L i x) x₀ (continuousAt_const.sub (hL i)) (sub_self _)

theorem eventually_right_above {X : Type*} [TopologicalSpace X]
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (R : Fin 2 → X → ℂ) (x₀ : X) (σ : ℝ)
    (hR : ∀ i, ContinuousAt (R i) x₀) (hσ : ∀ i, σ < (R i x₀).re) :
    ∀ᶠ x in 𝓝 x₀, ∀ i z, z ∈ rightFamily a b (R i x) → σ < z.re := by
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, σ < (R i x).re := by
    rw [Filter.eventually_all]
    intro i
    exact (Complex.continuous_re.continuousAt.comp (hR i)).eventually (lt_mem_nhds (hσ i))
  filter_upwards [hev] with x hx
  intro i z hz
  exact (hx i).trans_le (GammaK4Contour.rightFamily_re_ge (hb.trans_le hba) hb hz)

def crossedLeftPoints (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (L : Fin 2 → ℂ) (σ : ℝ) : Finset ℂ := by
  classical
  exact Finset.univ.biUnion (fun i : Fin 2 => GammaTwoFourier.crossedLeft a b hb hba (L i) σ)

lemma mem_crossedLeftPoints (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (L : Fin 2 → ℂ) (σ : ℝ) (z : ℂ) :
    z ∈ crossedLeftPoints a b hb hba L σ ↔ ∃ i, z ∈ leftFamily a b (L i) ∧ σ < z.re := by
  classical
  simp only [crossedLeftPoints, Finset.mem_biUnion, Finset.mem_univ, true_and,
    GammaTwoFourier.mem_crossedLeft]

end HaagerupIzumi.GammaMovingPoleRectangles
