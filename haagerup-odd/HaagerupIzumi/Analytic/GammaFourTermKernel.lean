module

import all Mathlib.Data.Complex.Basic

public import HaagerupIzumi.Analytic.GammaLocalFactors

/-!
# The pointwise four-term identity

The elementary sine identity behind Chapter 7 yields an exact finite
difference of a four-gamma product. This file establishes the identity
before contour integration, using the proved shifts of the explicit gamma
function. The normalization relation between the periods is needed only
when the integer-label coefficients are specialized.
-/

@[expose] public section

noncomputable section

open Complex

namespace HaagerupIzumi.GammaContinuation

def periodSin (a : ℝ) (z : ℂ) : ℂ := Complex.sin (Real.pi * z / a)

lemma periodSin_add (a : ℝ) (x y : ℂ) :
    periodSin a (x + y) = periodSin a x * Complex.cos (Real.pi * y / a) +
      Complex.cos (Real.pi * x / a) * periodSin a y := by
  unfold periodSin
  rw [show (Real.pi : ℂ) * (x + y) / a = Real.pi * x / a + Real.pi * y / a by ring,
    Complex.sin_add]

lemma periodSin_sub (a : ℝ) (x y : ℂ) :
    periodSin a (x - y) = periodSin a x * Complex.cos (Real.pi * y / a) -
      Complex.cos (Real.pi * x / a) * periodSin a y := by
  unfold periodSin
  rw [show (Real.pi : ℂ) * (x - y) / a = Real.pi * x / a - Real.pi * y / a by ring,
    Complex.sin_sub]

lemma periodSin_pair (a : ℝ) (x y z : ℂ) :
    periodSin a (y + z) * periodSin a x - periodSin a (x + y) * periodSin a z =
      -periodSin a y * periodSin a (z - x) := by
  rw [periodSin_add, periodSin_add, periodSin_sub]
  ring

lemma fourTerm_sine_identity (a b : ℝ) (ζ η ξ ν lam : ℂ)
    (ha : periodSin a (ξ - ζ) ≠ 0) (hb : periodSin b (ξ - ζ) ≠ 0) :
    (-periodSin a (ζ + ν) / periodSin a (ξ - ζ)) *
        (periodSin a η * periodSin b η * periodSin a ξ) +
      (lam * periodSin b (η + ξ) / periodSin b (ξ - ζ)) *
        (periodSin a ζ * periodSin b ζ * periodSin a ξ) +
      (-lam * periodSin b (ζ + η) / periodSin b (ξ - ζ)) *
        (periodSin a ζ * periodSin a ξ * periodSin b ξ) +
      (periodSin a (ξ + ν) / periodSin a (ξ - ζ)) *
        (periodSin a ζ * periodSin a η * periodSin b η) =
      -periodSin b η * (lam * periodSin a ζ * periodSin a ξ +
        periodSin a η * periodSin a ν) := by
  have hA := periodSin_pair a ζ ν ξ
  have hB := periodSin_pair b ζ η ξ
  rw [add_comm ν ξ] at hA
  calc
    _ = (periodSin a η * periodSin b η / periodSin a (ξ - ζ)) *
          (periodSin a (ξ + ν) * periodSin a ζ -
            periodSin a (ζ + ν) * periodSin a ξ) +
        (lam * periodSin a ζ * periodSin a ξ / periodSin b (ξ - ζ)) *
          (periodSin b (η + ξ) * periodSin b ζ -
            periodSin b (ζ + η) * periodSin b ξ) := by ring
    _ = _ := by rw [hA, hB]; field_simp; ring

lemma gamma_shift_sum (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (z : ℂ)
    (hz : z ∉ poleLattice a b) :
    gamma a b hb hba (z + a + b) =
      -4 * periodSin a z * periodSin b z * gamma a b hb hba z := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  rw [show z + a + b = (z + b) + a by ring,
    gamma_shift₁ a b hb hba (z + b) (not_mem_poleLattice_add_second hz),
    gamma_shift₂ a b hb hba z hz]
  unfold factor periodSin
  rw [show (Real.pi : ℂ) * (z + b) / b = Real.pi * z / b + Real.pi by field_simp,
    Complex.sin_add_pi]
  ring

/-- The general four-term relation between gamma products. The four
unshifted arguments need only avoid poles; zeros cause no difficulty. -/
theorem fourTerm_product_identity (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (ζ η ξ ν lam : ℂ) (hζ : ζ ∉ poleLattice a b) (hη : η ∉ poleLattice a b)
    (hξ : ξ ∉ poleLattice a b) (hν : ν ∉ poleLattice a b)
    (hDa : periodSin a (ξ - ζ) ≠ 0) (hDb : periodSin b (ξ - ζ) ≠ 0) :
    (-periodSin a (ζ + ν) / periodSin a (ξ - ζ)) *
        (gamma a b hb hba ζ * gamma a b hb hba (η + a + b) *
          gamma a b hb hba (ξ + b) * gamma a b hb hba ν) +
      (lam * periodSin b (η + ξ) / periodSin b (ξ - ζ)) *
        (gamma a b hb hba (ζ + a + b) * gamma a b hb hba η *
          gamma a b hb hba (ξ + b) * gamma a b hb hba ν) +
      (-lam * periodSin b (ζ + η) / periodSin b (ξ - ζ)) *
        (gamma a b hb hba (ζ + b) * gamma a b hb hba η *
          gamma a b hb hba (ξ + a + b) * gamma a b hb hba ν) +
      (periodSin a (ξ + ν) / periodSin a (ξ - ζ)) *
        (gamma a b hb hba (ζ + b) * gamma a b hb hba (η + a + b) *
          gamma a b hb hba ξ * gamma a b hb hba ν) =
      lam * (gamma a b hb hba (ζ + b) * gamma a b hb hba (ξ + b) *
          gamma a b hb hba (η + a) * gamma a b hb hba ν) -
        gamma a b hb hba ζ * gamma a b hb hba ξ *
          gamma a b hb hba (η + a + b) * gamma a b hb hba (ν + b) := by
  rw [gamma_shift_sum a b hb hba η hη, gamma_shift_sum a b hb hba ζ hζ,
    gamma_shift_sum a b hb hba ξ hξ, gamma_shift₂ a b hb hba ξ hξ,
    gamma_shift₂ a b hb hba ζ hζ, gamma_shift₂ a b hb hba ν hν,
    gamma_shift₁ a b hb hba η hη]
  have hs := fourTerm_sine_identity a b ζ η ξ ν lam hDa hDb
  simp only [factor, periodSin] at hs ⊢
  convert congrArg (fun w : ℂ =>
    -8 * gamma a b hb hba ζ * gamma a b hb hba η *
      gamma a b hb hba ξ * gamma a b hb hba ν * w) hs using 1 <;> ring

def fourTermExp (a b : ℝ) (Z z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * Z * z / (a * b))

def fourTermTerm₁ (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) : ℂ :=
  fourTermExp a b Z z * γ (u - b + z) * γ (u - a - z + a + b) *
    γ (v - b + Y + z + b) * γ (v - Y - z)

def fourTermTerm₂ (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) : ℂ :=
  fourTermExp a b Z z * γ (u - b + z + a + b) * γ (u - a - z) *
    γ (v - b + Y + z + b) * γ (v - Y - z)

def fourTermTerm₃ (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) : ℂ :=
  fourTermExp a b Z z * γ (u - b + z + b) * γ (u - a - z) *
    γ (v - b + Y + z + a + b) * γ (v - Y - z)

def fourTermTerm₄ (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) : ℂ :=
  fourTermExp a b Z z * γ (u - b + z + b) * γ (u - a - z + a + b) *
    γ (v - b + Y + z) * γ (v - Y - z)

def fourTermPrimitive (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) : ℂ :=
  fourTermExp a b Z z * γ (u - b + z) * γ (v - b + Y + z) *
    γ (u - a - z + a + b) * γ (v - Y - z + b)

lemma fourTermExp_add (a b : ℝ) (Z z w : ℂ) :
    fourTermExp a b Z (z + w) = fourTermExp a b Z w * fourTermExp a b Z z := by
  unfold fourTermExp
  rw [← Complex.exp_add]
  congr 1
  ring

lemma fourTermPrimitive_shift (γ : ℂ → ℂ) (a b : ℝ) (u v Y Z z : ℂ) :
    fourTermPrimitive γ a b u v Y Z (z + b) =
      fourTermExp a b Z b * fourTermExp a b Z z *
        γ (u - b + z + b) * γ (v - b + Y + z + b) *
          γ (u - a - z + a) * γ (v - Y - z) := by
  unfold fourTermPrimitive
  rw [fourTermExp_add]
  ring_nf

/-- The pointwise primitive identity underlying the four-term contour
relation in Chapter 7. -/
theorem fourTerm_primitive (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (u v Y Z z : ℂ)
    (hζ : u - b + z ∉ poleLattice a b) (hη : u - a - z ∉ poleLattice a b)
    (hξ : v - b + Y + z ∉ poleLattice a b) (hν : v - Y - z ∉ poleLattice a b)
    (hDa : periodSin a (v + Y - u) ≠ 0) (hDb : periodSin b (v + Y - u) ≠ 0) :
    (-periodSin a (u + v - b - Y) / periodSin a (v + Y - u)) *
        fourTermTerm₁ (gamma a b hb hba) a b u v Y Z z +
      (fourTermExp a b Z b * periodSin b (u + v - a - b + Y) /
          periodSin b (v + Y - u)) * fourTermTerm₂ (gamma a b hb hba) a b u v Y Z z +
      (-fourTermExp a b Z b * periodSin b (2 * u - a - b) /
          periodSin b (v + Y - u)) * fourTermTerm₃ (gamma a b hb hba) a b u v Y Z z +
      (periodSin a (2 * v - b) / periodSin a (v + Y - u)) *
        fourTermTerm₄ (gamma a b hb hba) a b u v Y Z z =
      fourTermPrimitive (gamma a b hb hba) a b u v Y Z (z + b) -
        fourTermPrimitive (gamma a b hb hba) a b u v Y Z z := by
  have hD : (v - b + Y + z) - (u - b + z) = v + Y - u := by ring
  have hs := fourTerm_product_identity a b hb hba
    (u - b + z) (u - a - z) (v - b + Y + z) (v - Y - z)
    (fourTermExp a b Z b) hζ hη hξ hν (by rwa [hD]) (by rwa [hD])
  rw [hD, show (u - b + z) + (v - Y - z) = u + v - b - Y by ring,
    show (u - a - z) + (v - b + Y + z) = u + v - a - b + Y by ring,
    show (u - b + z) + (u - a - z) = 2 * u - a - b by ring,
    show (v - b + Y + z) + (v - Y - z) = 2 * v - b by ring] at hs
  rw [fourTermPrimitive_shift]
  unfold fourTermTerm₁ fourTermTerm₂ fourTermTerm₃ fourTermTerm₄ fourTermPrimitive
  convert congrArg (fun w : ℂ => fourTermExp a b Z z * w) hs using 1 <;> ring

end HaagerupIzumi.GammaContinuation
