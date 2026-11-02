module

public import HaagerupIzumi.Coefficients
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Complex.Basic

/-!
# Small certificates for hypothesis ablation

These are local logical tests, not counterexamples to Evans–Gannon.
The polynomial theorem is used in `HaagerupIzumi.eq_zero_of_dft_block`.
The second test unbundles `CoeffData` so its `hWne` field is not assumed.
Check from the project root with:
`lake env lean docs/ablation/AssumptionAblationPilot.lean`
-/

@[expose] public section

namespace HaagerupIzumi.AssumptionAblationPilot

/-- Removing only injectivity from the root-count theorem permits a nonzero
polynomial with more indexed root samples than its degree. -/
theorem repeated_root_counterexample :
    ∃ (p : Polynomial ℂ) (f : Fin 2 → ℂ),
      (∀ i, p.eval (f i) = 0) ∧
      p.natDegree < Fintype.card (Fin 2) ∧
      p ≠ 0 ∧ ¬ Function.Injective f := by
  refine ⟨Polynomial.X, fun _ => 0, ?_, ?_, Polynomial.X_ne_zero, ?_⟩
  · intro i
    simp
  · simp
  · intro hf
    have h : (0 : Fin 2) = 1 := hf rfl
    norm_num at h

/-- `CoeffData.hWne` follows from the other three propositional fields.
Consequently no counterexample can violate only that field. -/
theorem nonvanishing_of_remaining_coeff_hypotheses
    {n : ℕ} {K : Type*} [Field K] (δ : K) (W : ZMod n → K)
    (hδ : δ ^ 2 = n * δ + 1) (hW0 : W 0 = -1)
    (hrec : ∀ a, a ≠ 0 → W a * W (-a) = δ) :
    ∀ a, W a ≠ 0 := by
  have hδne : δ ≠ 0 := by
    intro hz
    rw [hz] at hδ
    norm_num at hδ
  intro a
  by_cases ha : a = 0
  · subst a
    rw [hW0]
    exact neg_ne_zero.mpr one_ne_zero
  · intro hz
    have h := hrec a ha
    rw [hz, zero_mul] at h
    exact hδne h.symm

end HaagerupIzumi.AssumptionAblationPilot

#print axioms HaagerupIzumi.AssumptionAblationPilot.repeated_root_counterexample
#print axioms HaagerupIzumi.AssumptionAblationPilot.nonvanishing_of_remaining_coeff_hypotheses
