module

public import HaagerupIzumi.Residuals
public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# The Fourier reduction (Lemma 6.1)

For `g ≠ 0`, the discrete Fourier transform in `k` of the rescaled cubic residual
`𝒞_{g,h}(k,l)` is expressed through the column transform `û_{-g}` and the two product
transforms `S_{g+h,-h,l-h}(-j)` and `S_{-g-l,l,g+h+l}(j)`.
-/

open Finset ZMod

namespace HaagerupIzumi
namespace CoeffData

variable {n : ℕ} [NeZero n] (D : CoeffData n ℂ)

/-- Lemma 6.1 (Fourier reduction), with `u_p(a) = B a p`. -/
theorem fourier_reduction (g h l : ZMod n) (hg : g ≠ 0) (j : ZMod n) :
    dft (fun k => D.Cs g h k l) j
      = stdAddChar (-(g * j)) * ((∑ a, stdAddChar (-(a * j)) * D.B a (-g))
          * (∑ a, stdAddChar (-(a * (-j))) * D.B a (g + h) * D.B (a + (l - h)) (-h))
        - D.τ * stdAddChar (-(l * j))
          * (∑ b, stdAddChar (-(b * j)) * D.B b (-(g + l)) * D.B (b + (g + h + l)) l)) := by
  classical
  -- the triple sum
  have e1 : ∑ k, stdAddChar (-(k * j)) * ∑ m, D.B m (g + h) * D.B g (m + k) * D.B h (m + l)
      = stdAddChar (-(g * j)) * ((∑ a, stdAddChar (-(a * j)) * D.B a (-g))
          * (∑ a, stdAddChar (-(a * (-j))) * D.B a (g + h) * D.B (a + (l - h)) (-h))) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight (g - m)) _ _ (fun k => ?_)
    simp only [Equiv.subRight_apply]
    have hχ : stdAddChar (-(g * j)) * (stdAddChar (-((k - (g - m)) * j))
        * stdAddChar (-(m * (-j)))) = stdAddChar (-(k * j)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    rw [B_eq_u_sub D g (m + k), u_def, B_eq_u_sub D h (m + l), u_def,
      show m + k - g = k - (g - m) by ring, show m + l - h = m + (l - h) by ring, ← hχ]
    ring
  -- the product term
  have e2 : ∑ k, stdAddChar (-(k * j)) * (D.B (g + l) k * D.B (h + k) l)
      = stdAddChar (-(g * j)) * stdAddChar (-(l * j))
        * ∑ b, stdAddChar (-(b * j)) * D.B b (-(g + l)) * D.B (b + (g + h + l)) l := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight (g + l)) _ _ (fun k => ?_)
    simp only [Equiv.subRight_apply]
    have hχ : stdAddChar (-(g * j)) * stdAddChar (-(l * j)) * stdAddChar (-((k - (g + l)) * j))
        = stdAddChar (-(k * j)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    rw [B_eq_u_sub D (g + l) k, u_def, show k - (g + l) + (g + h + l) = h + k by ring, ← hχ]
    ring
  calc dft (fun k => D.Cs g h k l) j
      = ∑ k, (stdAddChar (-(k * j)) * ∑ m, D.B m (g + h) * D.B g (m + k) * D.B h (m + l)
          - D.τ * (stdAddChar (-(k * j)) * (D.B (g + l) k * D.B (h + k) l))) := by
        rw [dft_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [smul_eq_mul, Cs_eq_B, if_neg (fun hc : g = 0 ∧ h = 0 => hg hc.1), mul_zero, add_zero]
        ring
    _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
        ring

end CoeffData
end HaagerupIzumi
