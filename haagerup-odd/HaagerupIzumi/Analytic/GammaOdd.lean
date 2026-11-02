module

public import HaagerupIzumi.Analytic.GammaFull
public import HaagerupIzumi.Analytic.Cubics

/-!
# Connecting the actual gamma construction to the odd-order theorem

These assembly theorems retain the explicit Euler premise of `GammaFull`.
They check the complete connection to the existing Evans–Gannon proof, ready
for specialization with the final Euler theorem.
-/

@[expose] public section
noncomputable section

namespace HaagerupIzumi

def ConcreteEulerIdentity (n : ℕ) (hn : 1 ≤ n) : Prop :=
  GammaContinuation.EulerIdentity (Periods.ω₁ n) (Periods.ω₂ n) (Periods.ω₂_pos n)
    (Periods.ω₂_lt_ω₁ n hn).le

def ruijsenaarsHypGammaOfEuler (n : ℕ) (hn : 1 ≤ n) (hEuler : ConcreteEulerIdentity n hn) :
    HypGamma (Periods.ω₁ n) (Periods.ω₂ n) :=
  GammaContinuation.hypGammaOfEuler _ _ (Periods.ω₂_pos n) (Periods.ω₂_lt_ω₁ n hn)
    (Periods.irrational_period_ratio n hn) hEuler

@[simp] lemma ruijsenaarsHypGammaOfEuler_gamma (n : ℕ) (hn : 1 ≤ n)
    (hEuler : ConcreteEulerIdentity n hn) :
    (ruijsenaarsHypGammaOfEuler n hn hEuler).γ = ruijsenaarsGamma n hn := rfl

def ruijsenaarsCoeffDataOfEuler (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (hEuler : ConcreteEulerIdentity n hn) : CoeffData n ℂ :=
  Concrete.toCoeffData n hn (ruijsenaarsHypGammaOfEuler n hn hEuler) hodd

theorem EGEquations_ruijsenaars_of_euler (n : ℕ) [NeZero n] (hn : 1 ≤ n) (hodd : Odd n)
    (hEuler : ConcreteEulerIdentity n hn) :
    (ruijsenaarsCoeffDataOfEuler n hn hodd hEuler).EGEquations :=
  Concrete.EGEquations_concrete n hn (ruijsenaarsHypGammaOfEuler n hn hEuler) hodd

theorem exists_EGEquations_of_euler (n : ℕ) [NeZero n] (hn : 1 ≤ n) (hodd : Odd n)
    (hEuler : ConcreteEulerIdentity n hn) : ∃ D : CoeffData n ℂ, D.EGEquations :=
  ⟨ruijsenaarsCoeffDataOfEuler n hn hodd hEuler, EGEquations_ruijsenaars_of_euler n hn hodd hEuler⟩

end HaagerupIzumi
