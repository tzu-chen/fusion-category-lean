module

public import HaagerupIzumi.Analytic.GammaOdd
public import HaagerupIzumi.Analytic.GammaK4EulerInterface

/-!
# The constructed hyperbolic gamma and the odd-order Evans–Gannon theorem

Every hyperbolic-gamma property is proved for the regularized integral and
its continuation. The resulting coefficient data satisfy the Evans–Gannon
equations for every odd natural number, without analytic assumptions.
-/

@[expose] public section
noncomputable section

namespace HaagerupIzumi

namespace GammaContinuation

/-- The full hyperbolic-gamma interface constructed for positive ordered
periods with irrational ratio. -/
def hypGamma (a b : ℝ) (hb : 0 < b) (hba : b < a) (hirr : Irrational (a / b)) :
    HypGamma a b :=
  hypGammaOfEuler a b hb hba hirr (GammaK4Contour.K4_euler a b hb hba.le hirr)

@[simp] lemma hypGamma_gamma (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) : (hypGamma a b hb hba hirr).γ = gamma a b hb hba.le := rfl

@[simp] lemma hypGamma_K4 (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) :
    (hypGamma a b hb hba hirr).K4 = GammaK4Contour.K4 a b hb hba.le := rfl

end GammaContinuation

/-- The fully proved gamma interface at the odd-order construction's periods. -/
def ruijsenaarsHypGamma (n : ℕ) (hn : 1 ≤ n) : HypGamma (Periods.ω₁ n) (Periods.ω₂ n) :=
  GammaContinuation.hypGamma _ _ (Periods.ω₂_pos n) (Periods.ω₂_lt_ω₁ n hn)
    (Periods.irrational_period_ratio n hn)

@[simp] lemma ruijsenaarsHypGamma_gamma (n : ℕ) (hn : 1 ≤ n) :
    (ruijsenaarsHypGamma n hn).γ = ruijsenaarsGamma n hn := rfl

/-- The explicit odd-order coefficient data, using the constructed gamma. -/
def ruijsenaarsCoeffData (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) : CoeffData n ℂ :=
  Concrete.toCoeffData n hn (ruijsenaarsHypGamma n hn) hodd

@[simp] lemma ruijsenaarsCoeffData_delta (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    (ruijsenaarsCoeffData n hn hodd).δ = (Periods.δ n : ℂ) := rfl

/-- All Evans–Gannon equations hold for the actual odd-order construction. -/
theorem EGEquations_ruijsenaars (n : ℕ) [NeZero n] (hn : 1 ≤ n) (hodd : Odd n) :
    (ruijsenaarsCoeffData n hn hodd).EGEquations :=
  Concrete.EGEquations_concrete n hn (ruijsenaarsHypGamma n hn) hodd

/-- Every odd natural number has coefficient data satisfying all the
Evans–Gannon equations. The required nonzero instance follows from oddness. -/
theorem exists_EGEquations_odd (n : ℕ) (hodd : Odd n) :
    letI : NeZero n := ⟨hodd.pos.ne'⟩
    ∃ D : CoeffData n ℂ, D.EGEquations := by
  letI : NeZero n := ⟨hodd.pos.ne'⟩
  exact ⟨ruijsenaarsCoeffData n hodd.pos hodd, EGEquations_ruijsenaars n hodd.pos hodd⟩

end HaagerupIzumi
