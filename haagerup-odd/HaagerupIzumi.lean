module

-- Algebraic half: coefficient data, cubic residuals, and their completion.
public import HaagerupIzumi.Coefficients
public import HaagerupIzumi.Residuals
public import HaagerupIzumi.Quartic
public import HaagerupIzumi.Factorization
public import HaagerupIzumi.Boundary
public import HaagerupIzumi.Balanced
public import HaagerupIzumi.Degenerate
public import HaagerupIzumi.Interpolation
public import HaagerupIzumi.Reflection
public import HaagerupIzumi.FourierReduction
public import HaagerupIzumi.Completion
-- Analytic half, for any object satisfying the `HypGamma` interface.
public import HaagerupIzumi.Analytic.HypGamma
public import HaagerupIzumi.Analytic.Periods
public import HaagerupIzumi.Analytic.Sampling
public import HaagerupIzumi.Analytic.ColumnFourier
public import HaagerupIzumi.Analytic.Residue
public import HaagerupIzumi.Analytic.Windows
public import HaagerupIzumi.Analytic.Products
public import HaagerupIzumi.Analytic.LeftProduct
public import HaagerupIzumi.Analytic.RightProduct
public import HaagerupIzumi.Analytic.NegColumn
public import HaagerupIzumi.Analytic.Restricted
public import HaagerupIzumi.Analytic.Cubics
-- Construction of the hyperbolic gamma function and the main theorem.
public import HaagerupIzumi.Analytic.GammaCore
public import HaagerupIzumi.Analytic.GammaK4Interface
public import HaagerupIzumi.Analytic.GammaK4FourTermInterface
public import HaagerupIzumi.Analytic.GammaFourierEvaluation
public import HaagerupIzumi.Analytic.GammaTwoContourCenter
public import HaagerupIzumi.Analytic.GammaTwoDecay
public import HaagerupIzumi.Analytic.GammaConstruction

/-!
# The odd-order Evans–Gannon theorem

Umbrella module and default Lake target. Its imports reach the whole odd-order
development, whose main theorem is `HaagerupIzumi.exists_EGEquations_odd` in
`Analytic/GammaConstruction`. See `README.md` for the module map.
-/

@[expose] public section
