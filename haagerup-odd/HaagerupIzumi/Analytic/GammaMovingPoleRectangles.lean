module

public import HaagerupIzumi.Analytic.MovingPoleRectangles
import all Mathlib.Data.Complex.Basic

/-! # Fixed pole-cluster rectangles for four continuously moving gamma offsets -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaMovingPoleRectangles

abbrev Index := Fin 2 ⊕ Fin 2

def family (a b : ℝ) (L R : Fin 2 → ℂ) : Index → Set ℂ
  | .inl i => leftFamily a b (L i)
  | .inr i => rightFamily a b (R i)

def displacement {X : Type*} (L R : Fin 2 → X → ℂ) (x₀ : X) : Index → X → ℂ
  | .inl i => fun x => L i x₀ - L i x
  | .inr i => fun x => R i x - R i x₀

lemma displacement_zero {X : Type*} (L R : Fin 2 → X → ℂ) (x₀ : X) (i : Index) :
    displacement L R x₀ i x₀ = 0 := by
  cases i <;> simp [displacement]

lemma displacement_continuousAt {X : Type*} [TopologicalSpace X]
    (L R : Fin 2 → X → ℂ) (x₀ : X)
    (hL : ∀ i, ContinuousAt (L i) x₀) (hR : ∀ i, ContinuousAt (R i) x₀) (i : Index) :
    ContinuousAt (displacement L R x₀ i) x₀ := by
  cases i with
  | inl i => exact continuousAt_const.sub (hL i)
  | inr i => exact (hR i).sub continuousAt_const

lemma mem_family_translate {X : Type*} (a b : ℝ) (L R : Fin 2 → X → ℂ)
    (x₀ x : X) (i : Index) (q : ℂ) :
    q + displacement L R x₀ i x ∈ family a b (fun j => L j x) (fun j => R j x) i ↔
      q ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i := by
  cases i with
  | inl i =>
    change L i x + (q + (L i x₀ - L i x)) ∈ poleLattice a b ↔
      L i x₀ + q ∈ poleLattice a b
    rw [show L i x + (q + (L i x₀ - L i x)) = L i x₀ + q by ring]
  | inr i =>
    change R i x - (q + (R i x - R i x₀)) ∈ poleLattice a b ↔
      R i x₀ - q ∈ poleLattice a b
    rw [show R i x - (q + (R i x - R i x₀)) = R i x₀ - q by ring]

lemma family_isolated (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (L R : Fin 2 → ℂ) (p : ℂ) (i : Index) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ family a b L R i := by
  cases i with
  | inl i =>
    filter_upwards [GammaTwoFourier.eventually_not_mem_families a b hb hba (L i) 0 p]
      with z hz
    exact fun h => hz (Or.inl h)
  | inr i =>
    filter_upwards [GammaTwoFourier.eventually_not_mem_families a b hb hba 0 (R i) p]
      with z hz
    exact fun h => hz (Or.inr h)

/-- The generic rectangle theorem applies to arbitrary continuous left and
right gamma offsets. The family index retains coincident labels; the point
set of each cluster can subsequently be formed with `Finset.image`. -/
theorem exists_fixed_rectangle {X : Type*} [TopologicalSpace X]
    (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (L R : Fin 2 → X → ℂ) (x₀ : X) (p : ℂ)
    (hL : ∀ i, ContinuousAt (L i) x₀) (hR : ∀ i, ContinuousAt (R i) x₀) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i q, q ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i → q ≠ p →
        8 * ε ≤ ‖q - p‖) ∧
      ∀ᶠ x in 𝓝 x₀,
        (∀ i, InOpenRect (p + displacement L R x₀ i x)
          (MovingPoleRectangles.lower p ε) (MovingPoleRectangles.upper p ε)) ∧
        (∀ i q, q ∈ family a b (fun j => L j x₀) (fun j => R j x₀) i →
          (q + displacement L R x₀ i x ∈ closedRect
            (MovingPoleRectangles.lower p ε) (MovingPoleRectangles.upper p ε) ↔ q = p)) ∧
        (∀ i z, z ∈ family a b (fun j => L j x) (fun j => R j x) i →
          ¬ OnBoundary z (MovingPoleRectangles.lower p ε) (MovingPoleRectangles.upper p ε)) := by
  obtain ⟨ε, hε, hsep, hev⟩ := MovingPoleRectangles.exists_fixed_rectangle
    (family a b (fun j => L j x₀) (fun j => R j x₀)) (displacement L R x₀) x₀ p
    (family_isolated a b hb hba _ _ p) (displacement_continuousAt L R x₀ hL hR)
    (displacement_zero L R x₀)
  refine ⟨ε, hε, hsep, ?_⟩
  filter_upwards [hev] with x hx
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro i z hz
  have hbase : z - displacement L R x₀ i x ∈
      family a b (fun j => L j x₀) (fun j => R j x₀) i := by
    apply (mem_family_translate a b L R x₀ x i _).mp
    simpa only [sub_add_cancel] using hz
  simpa only [sub_add_cancel] using hx.2.2 i (z - displacement L R x₀ i x) hbase

end HaagerupIzumi.GammaMovingPoleRectangles
