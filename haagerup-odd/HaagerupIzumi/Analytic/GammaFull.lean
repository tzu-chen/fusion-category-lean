module

public import HaagerupIzumi.Analytic.GammaCore
public import HaagerupIzumi.Analytic.GammaTwoGammaInterface
public import HaagerupIzumi.Analytic.GammaK4Interface
public import HaagerupIzumi.Analytic.GammaK4FourTermInterface

/-!
# Assembling the concrete hyperbolic-gamma interface

This assembly lemma takes the Euler transformation explicitly. All remaining
fields are supplied by the proved integral construction, contour identities,
and four-term relation. The final construction can apply it once the Euler
parameter-continuation theorem is available.
-/

@[expose] public section
noncomputable section

namespace HaagerupIzumi.GammaContinuation

/-- The Euler identity for the actual gamma and actual corrected contour. -/
def EulerIdentity (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) : Prop :=
  ∀ r s x y : ℂ, K4Conv a b r y → K4Conv a b (-r) y →
    K4NoPinch a b r s x → K4NoPinch a b (-r) s x →
    Γr (gamma a b hb hba) a b r y * GammaK4Contour.K4 a b hb hba r s x y =
      Γr (gamma a b hb hba) a b r s * Γr (gamma a b hb hba) a b r x *
        GammaK4Contour.K4 a b hb hba (-r) s x y

/-- Assembly from the actual construction and its Euler identity. The only
additional premise is stated explicitly as `EulerIdentity`. -/
def hypGammaOfEuler (a b : ℝ) (hb : 0 < b) (hba : b < a) (hirr : Irrational (a / b))
    (hEuler : EulerIdentity a b hb hba.le) : HypGamma a b where
  toHypGammaCore := core a b hb hba hirr
  two_gamma := GammaTwoFourier.two_gamma_explicit a b hb hba.le hirr
  K4 := GammaK4Contour.K4 a b hb hba.le
  K4_line := GammaK4Contour.K4_line_explicit a b hb hba.le hirr
  K4_even := GammaK4Contour.K4_even a b hb hba.le hirr
  K4_swap := GammaK4Contour.K4_swap a b hb hba.le hirr
  K4_euler := hEuler
  K4_four_term := GammaK4Contour.K4_four_term a b hb hba.le hirr

@[simp] lemma hypGammaOfEuler_gamma (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) (hEuler : EulerIdentity a b hb hba.le) :
    (hypGammaOfEuler a b hb hba hirr hEuler).γ = gamma a b hb hba.le := rfl

@[simp] lemma hypGammaOfEuler_K4 (a b : ℝ) (hb : 0 < b) (hba : b < a)
    (hirr : Irrational (a / b)) (hEuler : EulerIdentity a b hb hba.le) :
    (hypGammaOfEuler a b hb hba hirr hEuler).K4 = GammaK4Contour.K4 a b hb hba.le := rfl

end HaagerupIzumi.GammaContinuation
