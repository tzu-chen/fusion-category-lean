import FusionCategory.Basic
import FusionCategory.System
import FusionCategory.PseudoUnitary
import FusionCategory.PFDim
import FusionCategory.Examples.Fibonacci
import FusionCategory.Examples.Ising
import FusionCategory.Examples.Ostrik
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

namespace FusionCategory.Examples

open FusionCategory

theorem fibonacci_pfUnique_instance : PFUnique FibonacciRing FibonacciFPData := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 2) = 1 := by
    have h := hv_one (by omega)
    have : (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 2) (1 : Fin 2)
  simp only [Fin.sum_univ_two] at h11
  have hN101 : (FibonacciRing.N 1 0 1 : ℕ) = 1 := by simp [FibonacciRing, fibN]
  have hN111 : (FibonacciRing.N 1 1 1 : ℕ) = 1 := by simp [FibonacciRing, fibN]
  have h11p : v (0 : Fin 2) + v (1 : Fin 2) = v (1 : Fin 2) * v (1 : Fin 2) := by
    rw [hN101, hN111] at h11; simp at h11; linarith
  have hv1_sq : v (1 : Fin 2) ^ 2 = v (1 : Fin 2) + 1 := by nlinarith [h11p, hv0]
  have hv1_eq_phi : v (1 : Fin 2) = phi := phi_unique _ (hv_pos 1) hv1_sq
  ext i; fin_cases i
  · simp [hv0, FibonacciFPData, fibFPdim]
  · simp [hv1_eq_phi, FibonacciFPData, fibFPdim, phi]

theorem ising_pfUnique_instance : PFUnique IsingRing IsingFPData := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 3) = 1 := by
    have h := hv_one (by omega)
    have : (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 3) (1 : Fin 3)
  simp only [Fin.sum_univ_three] at h11
  have hN101 : (IsingRing.N 1 0 1 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN111 : (IsingRing.N 1 1 1 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hN121 : (IsingRing.N 1 2 1 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hv1_eq : v (1 : Fin 3) = 1 := by
    have h11' := h11
    rw [hN101, hN111, hN121] at h11'
    simp at h11'
    have hv1_sq : v 1 ^ 2 = 1 := by linarith [hv0]
    nlinarith [sq_nonneg (v 1 - 1), hv1_sq, hv_pos 1]
  have h22 := heig (2 : Fin 3) (2 : Fin 3)
  simp only [Fin.sum_univ_three] at h22
  have hN202 : (IsingRing.N 2 0 2 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN212 : (IsingRing.N 2 1 2 : ℕ) = 1 := by simp [IsingRing, isingN]
  have hN222 : (IsingRing.N 2 2 2 : ℕ) = 0 := by simp [IsingRing, isingN]
  have hv2_sq : v (2 : Fin 3) ^ 2 = 2 := by
    have h22' := h22
    rw [hN202, hN212, hN222] at h22'
    simp at h22'
    linarith [hv0, hv1_eq]
  have hv2_eq : v (2 : Fin 3) = Real.sqrt 2 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [sq_nonneg (v 2 - Real.sqrt 2), hv2_sq, hsq, Real.sqrt_nonneg 2, hv_pos 2]
  ext i; fin_cases i
  · simp [hv0, IsingFPData, isingFPdim]
  · simp [hv1_eq, IsingFPData, isingFPdim]
  · simp [hv2_eq, IsingFPData, isingFPdim]

theorem k2210_pfUnique_instance : PFUnique K2210Ring K2210FPData := by
  intro v hv_pos hv_one heig
  have hv0 : v (0 : Fin 3) = 1 := by
    have h := hv_one (by omega)
    have : (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this] at h; exact h
  have h11 := heig (1 : Fin 3) (1 : Fin 3)
  simp only [Fin.sum_univ_three] at h11
  have hN101 : (K2210Ring.N 1 0 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN111 : (K2210Ring.N 1 1 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN121 : (K2210Ring.N 1 2 1 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have h12 := heig (1 : Fin 3) (2 : Fin 3)
  simp only [Fin.sum_univ_three] at h12
  have hN102 : (K2210Ring.N 1 0 2 : ℕ) = 0 := by simp [K2210Ring, k2210N]
  have hN112 : (K2210Ring.N 1 1 2 : ℕ) = 1 := by simp [K2210Ring, k2210N]
  have hN122 : (K2210Ring.N 1 2 2 : ℕ) = 0 := by simp [K2210Ring, k2210N]
  have hv2_eq : v (2 : Fin 3) = 1 := by
    have h12' := h12
    rw [hN102, hN112, hN122] at h12'
    simp at h12'
    have hmul : v 1 * (v 2 - 1) = 0 := by nlinarith
    have hor : v 1 = 0 ∨ v 2 - 1 = 0 := mul_eq_zero.mp hmul
    cases hor with
    | inl h => exact absurd h (ne_of_gt (hv_pos 1))
    | inr h => linarith
  have hv1_eq : v (1 : Fin 3) = 2 := by
    have h11' := h11
    rw [hN101, hN111, hN121] at h11'
    simp at h11'
    rw [hv0, hv2_eq] at h11'
    have h_eq : v 1 * v 1 - v 1 - 2 = 0 := by linarith
    have h_factor : (v 1 - 2) * (v 1 + 1) = 0 := by nlinarith [sq_nonneg (v 1)]
    have hor : v 1 - 2 = 0 ∨ v 1 + 1 = 0 := mul_eq_zero.mp h_factor
    cases hor with
    | inl h => linarith
    | inr h => linarith [hv_pos 1]
  ext i; fin_cases i
  · simp [hv0, K2210FPData, k2210FPdim]
  · simp [hv1_eq, K2210FPData, k2210FPdim]
  · simp [hv2_eq, K2210FPData, k2210FPdim]

theorem pfUnique_transport {n : ℕ} {R R' : FusionRing n} (hEq : R = R')
    {h : R.FPData} (hPF : PFUnique R h) :
    PFUnique R' (hEq ▸ h) := by
  intro v hv_pos hv_one heig
  have heig' : ∀ i k_, (∑ j : Fin n, (R.N i j k_ : ℝ) * v j) = v i * v k_ := by
    intro i k_
    have h1 := heig i k_
    rw [← hEq] at h1
    exact h1
  have hv_eq : v = h.fpdim := hPF v hv_pos hv_one heig'
  have hfp_eq : h.fpdim = (hEq ▸ h).fpdim := by cases hEq; rfl
  rw [hfp_eq] at hv_eq
  exact hv_eq

theorem fibonacci_pseudoUnitary_spherical
    {k : Type} [Field k] [Algebra ℝ k]
    (S : FusionSystem 2 k) (hRing : S.ring = FibonacciRing)
    (d : CategoricalDimData S) (hPU : IsPseudoUnitary d (hRing.symm ▸ FibonacciFPData))
    (hPos : ∀ i, d.dim i ≠ 0) :
    ∃ (P : PivotalStructure S), IsSpherical P :=
  unitary_is_spherical (hRing.symm ▸ FibonacciFPData) (pfUnique_transport hRing.symm fibonacci_pfUnique_instance) d hPU hPos (by omega)

theorem ising_pseudoUnitary_spherical
    {k : Type} [Field k] [Algebra ℝ k]
    (S : FusionSystem 3 k) (hRing : S.ring = IsingRing)
    (d : CategoricalDimData S) (hPU : IsPseudoUnitary d (hRing.symm ▸ IsingFPData))
    (hPos : ∀ i, d.dim i ≠ 0) :
    ∃ (P : PivotalStructure S), IsSpherical P :=
  unitary_is_spherical (hRing.symm ▸ IsingFPData) (pfUnique_transport hRing.symm ising_pfUnique_instance) d hPU hPos (by omega)

theorem k2210_pseudoUnitary_spherical
    {k : Type} [Field k] [Algebra ℝ k]
    (S : FusionSystem 3 k) (hRing : S.ring = K2210Ring)
    (d : CategoricalDimData S) (hPU : IsPseudoUnitary d (hRing.symm ▸ K2210FPData))
    (hPos : ∀ i, d.dim i ≠ 0) :
    ∃ (P : PivotalStructure S), IsSpherical P :=
  unitary_is_spherical (hRing.symm ▸ K2210FPData) (pfUnique_transport hRing.symm k2210_pfUnique_instance) d hPU hPos (by omega)

end FusionCategory.Examples
