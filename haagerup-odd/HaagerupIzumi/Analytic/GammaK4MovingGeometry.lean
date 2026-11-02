module

public import HaagerupIzumi.Analytic.GammaMovingPoleCorrections
public import HaagerupIzumi.Analytic.MovingPoleCorrectionSum
public import HaagerupIzumi.Analytic.GammaK4Line
public import HaagerupIzumi.Analytic.GammaKernelRegularity
import all Mathlib.Data.Complex.Basic

/-! # Moving pole geometry of the Euler scaling family -/

@[expose] public section
noncomputable section

open Complex Set Filter Topology
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaMovingPoleRectangles

namespace HaagerupIzumi.GammaK4Contour

def scaledLeftOffsets (a b : ℝ) (r s x : ℂ) : Fin 2 → ℂ → ℂ :=
  ![fun t => k4U a b (t * r) (t * s), fun t => k4V a b (t * r) (t * s) + t * x]

def scaledRightOffsets (a b : ℝ) (r s x : ℂ) : Fin 2 → ℂ → ℂ :=
  ![fun t => k4U a b (t * r) (t * s), fun t => k4V a b (t * r) (t * s) - t * x]

lemma continuous_scaledLeftOffsets (a b : ℝ) (r s x : ℂ) (i : Fin 2) :
    Continuous (scaledLeftOffsets a b r s x i) := by
  fin_cases i
  · change Continuous (fun t : ℂ => k4U a b (t * r) (t * s))
    unfold k4U; fun_prop
  · change Continuous (fun t : ℂ => k4V a b (t * r) (t * s) + t * x)
    unfold k4V; fun_prop

lemma continuous_scaledRightOffsets (a b : ℝ) (r s x : ℂ) (i : Fin 2) :
    Continuous (scaledRightOffsets a b r s x i) := by
  fin_cases i
  · change Continuous (fun t : ℂ => k4U a b (t * r) (t * s))
    unfold k4U; fun_prop
  · change Continuous (fun t : ℂ => k4V a b (t * r) (t * s) - t * x)
    unfold k4V; fun_prop

lemma mem_leftPoles_scaled (a b : ℝ) (r s x t z : ℂ) :
    z ∈ leftPoles a b (t * r) (t * s) (t * x) ↔
      ∃ i, z ∈ leftFamily a b (scaledLeftOffsets a b r s x i t) := by
  rw [Fin.exists_fin_two]
  rfl

lemma mem_rightPoles_scaled (a b : ℝ) (r s x t z : ℂ) :
    z ∈ rightPoles a b (t * r) (t * s) (t * x) ↔
      ∃ i, z ∈ rightFamily a b (scaledRightOffsets a b r s x i t) := by
  rw [Fin.exists_fin_two]
  rfl

lemma mem_scaled_families (a b : ℝ) (r s x t z : ℂ) :
    (∃ i, z ∈ family a b (fun j => scaledLeftOffsets a b r s x j t)
      (fun j => scaledRightOffsets a b r s x j t) i) ↔
    z ∈ leftPoles a b (t * r) (t * s) (t * x) ∪ rightPoles a b (t * r) (t * s) (t * x) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i => exact Or.inl ((mem_leftPoles_scaled a b r s x t z).mpr ⟨i, hi⟩)
    | inr i => exact Or.inr ((mem_rightPoles_scaled a b r s x t z).mpr ⟨i, hi⟩)
  · rintro (hz | hz)
    · obtain ⟨i, hi⟩ := (mem_leftPoles_scaled a b r s x t z).mp hz
      exact ⟨.inl i, hi⟩
    · obtain ⟨i, hi⟩ := (mem_rightPoles_scaled a b r s x t z).mp hz
      exact ⟨.inr i, hi⟩

lemma scaled_families_disjoint (a b : ℝ) (r s x t : ℂ)
    (hnp : K4NoPinch a b (t * r) (t * s) (t * x)) (i j : Fin 2) :
    Disjoint (leftFamily a b (scaledLeftOffsets a b r s x i t))
      (rightFamily a b (scaledRightOffsets a b r s x j t)) := by
  apply (noPinch_disjoint hnp).mono
  · intro z hz
    exact (mem_leftPoles_scaled a b r s x t z).mpr ⟨i, hz⟩
  · intro z hz
    exact (mem_rightPoles_scaled a b r s x t z).mpr ⟨j, hz⟩

lemma crossedLeft_eq_points (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x t : ℂ) (σ : ℝ) :
    crossedLeft a b hb hba (t * r) (t * s) (t * x) σ =
      crossedLeftPoints a b hb hba (fun i => scaledLeftOffsets a b r s x i t) σ := by
  ext z
  rw [mem_crossedLeft, mem_crossedLeftPoints, mem_leftPoles_scaled]
  constructor
  · rintro ⟨⟨i, hi⟩, hσ⟩
    exact ⟨i, hi, hσ⟩
  · rintro ⟨i, hi, hσ⟩
    exact ⟨⟨i, hi⟩, hσ⟩

lemma eventually_scaled_conv (a b : ℝ) (r y t₀ : ℂ)
    (hc : K4Conv a b (t₀ * r) (t₀ * y)) :
    ∀ᶠ t in 𝓝 t₀, K4Conv a b (t * r) (t * y) := by
  have hopen : IsOpen {t : ℂ | K4Conv a b (t * r) (t * y)} := by
    unfold K4Conv
    exact isOpen_lt (by fun_prop) (by fun_prop)
  exact hopen.mem_nhds hc

lemma eventually_scaled_noPinch (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x t₀ : ℂ)
    (hnp : K4NoPinch a b (t₀ * r) (t₀ * s) (t₀ * x)) :
    ∀ᶠ t in 𝓝 t₀, K4NoPinch a b (t * r) (t * s) (t * x) := by
  have hp : IsOpen ((poleSet a b)ᶜ) := (HypGamma.poleSet_isClosed (hb.trans_le hba) hb).isOpen_compl
  have h₁ : ∀ᶠ t in 𝓝 t₀, 2 * k4U a b (t * r) (t * s) ∉ poleSet a b := by
    exact (show ContinuousAt (fun t : ℂ => 2 * k4U a b (t * r) (t * s)) t₀ by
      unfold k4U; fun_prop).eventually (hp.mem_nhds hnp.1)
  have h₂ : ∀ᶠ t in 𝓝 t₀, 2 * k4V a b (t * r) (t * s) ∉ poleSet a b := by
    exact (show ContinuousAt (fun t : ℂ => 2 * k4V a b (t * r) (t * s)) t₀ by
      unfold k4V; fun_prop).eventually (hp.mem_nhds hnp.2.1)
  have h₃ : ∀ᶠ t in 𝓝 t₀,
      k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) - t * x ∉ poleSet a b := by
    exact (show ContinuousAt (fun t : ℂ =>
      k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) - t * x) t₀ by
      unfold k4U k4V; fun_prop).eventually (hp.mem_nhds hnp.2.2.1)
  have h₄ : ∀ᶠ t in 𝓝 t₀,
      k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) + t * x ∉ poleSet a b := by
    exact (show ContinuousAt (fun t : ℂ =>
      k4U a b (t * r) (t * s) + k4V a b (t * r) (t * s) + t * x) t₀ by
      unfold k4U k4V; fun_prop).eventually (hp.mem_nhds hnp.2.2.2)
  filter_upwards [h₁, h₂, h₃, h₄] with t ht₁ ht₂ ht₃ ht₄
  exact ⟨ht₁, ht₂, ht₃, ht₄⟩

end HaagerupIzumi.GammaK4Contour
