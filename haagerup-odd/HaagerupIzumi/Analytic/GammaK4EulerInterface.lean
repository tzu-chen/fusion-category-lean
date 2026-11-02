module

public import HaagerupIzumi.Analytic.GammaK4Euler
public import HaagerupIzumi.Analytic.GammaK4ParameterHolomorphic

/-! # The unconditional Euler transformation for the constructed gamma -/

@[expose] public section
noncomputable section

open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

/-- The complete Euler field of the hyperbolic-gamma interface, proved
for the actual gamma function and the actual corrected four-gamma contour. -/
theorem K4_euler (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (r s x y : ℂ)
    (hconv : K4Conv a b r y) (hconv' : K4Conv a b (-r) y)
    (hnp : K4NoPinch a b r s x) (hnp' : K4NoPinch a b (-r) s x) :
    Γr (gamma a b hb hba) a b r y * K4 a b hb hba r s x y =
      Γr (gamma a b hb hba) a b r s * Γr (gamma a b hb hba) a b r x *
        K4 a b hb hba (-r) s x y := by
  have hba' := periods_strictly_ordered a b hb hba hirr
  exact K4_euler_of_scaled_holomorphic hb hba' hirr
    (differentiableAt_K4_scaled hb hba' hirr) r s x y hconv hconv' hnp hnp'

end HaagerupIzumi.GammaK4Contour
