module

public import HaagerupIzumi.Analytic.GammaConcrete
public import HaagerupIzumi.Analytic.GammaPoleResidues
public import HaagerupIzumi.Analytic.ResidueAlgebra

/-!
# Constructing the hyperbolic-gamma core

Every local identity, residue, and ratio estimate is supplied by the explicit
regularized integral and its finite-product continuation. The two-gamma and
four-gamma integral identities belong to the later `HypGamma` construction.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi

namespace GammaContinuation

/-- The complete local hyperbolic-gamma interface for ordered irrational
positive periods, constructed from the regularized integral. -/
def core (a b : ℝ) (hb : 0 < b) (hba : b < a) (hirr : Irrational (a / b)) :
    HypGammaCore a b where
  γ := gamma a b hb hba.le
  pos₁ := hb.trans hba
  pos₂ := hb
  differentiableOn := by
    intro z hz
    exact (gamma_differentiableAt a b hb hba.le z hz).differentiableWithinAt
  ne_zero := fun z hp hz => gamma_ne_zero a b hb hba.le z hp hz
  eq_zero := fun z hz => gamma_eq_zero a b hb hba.le z hz
  shift₁ := by
    intro z hz
    exact gamma_shift₁ a b hb hba.le z hz
  shift₂ := by
    intro z hz
    exact gamma_shift₂ a b hb hba.le z hz
  reflect := fun z hp hz => gamma_reflection a b hb hba.le z hp hz
  residue_zero := gamma_residue_zero a b hb hba.le
  residue := residueValue (gamma a b hb hba.le)
  hasResidue := by
    intro p hp
    obtain ⟨ρ, _, hρ⟩ := gamma_has_nonzero_residue a b hb hba.le hirr p hp
    rw [residueValue_eq hρ.hasResidueGen]
    exact hρ
  real_pos := fun x hx₀ hx₁ => gamma_real_pos a b hb hba.le x hx₀ hx₁
  real_axis := fun x => gamma_real_axis a b hb hba.le x
  ratio_bound := by
    intro c L U
    obtain ⟨C, T, hT, hbound⟩ := ratio_bound hb hba c L U
    exact ⟨C, T, hT, fun z hL hU hz _ _ => hbound z hL hU hz⟩

end GammaContinuation

/-- The concrete core required by the odd-order Evans–Gannon construction.
It has no assumed hyperbolic-gamma properties. -/
def ruijsenaarsCore (n : ℕ) (hn : 1 ≤ n) : HypGammaCore (Periods.ω₁ n) (Periods.ω₂ n) :=
  GammaContinuation.core _ _ (Periods.ω₂_pos n) (Periods.ω₂_lt_ω₁ n hn)
    (Periods.irrational_period_ratio n hn)

@[simp] lemma ruijsenaarsCore_gamma (n : ℕ) (hn : 1 ≤ n) :
    (ruijsenaarsCore n hn).γ = ruijsenaarsGamma n hn := rfl

end HaagerupIzumi
