/-
WP2 round 3, member m3, direction D3: the pentagon of the reconstruction.

`LHS_entry`: the three-factor (left-hand) side of the pentagon
`(α_{A,B,C} ▷ D) ≫ α_{A,B⊗C,D} ≫ (A ◁ α_{B,C,D})` collapses entrywise to
`if <four leaves match> then ∑ k, F A B C g e k * F A k D d e h * F B C D h k f else 0`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.PentagonUEntry

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-- The channel normalisation of the three-factor side: the four channels that
survive the collapse are free, and their multiplicities are `0` or `1`. -/
theorem nsmul_LHS (d e f g h C Dw a b kk : Fin n) :
    (S.ring.N kk Dw h) • ((S.ring.N b C kk) • ((S.ring.N a kk e) •
      ((S.ring.N b C kk) • (S.F a b C e g kk * S.F a kk Dw d e h *
        S.F b C Dw h kk f))))
      = S.F a b C e g kk * S.F a kk Dw d e h * S.F b C Dw h kk f := by
  by_cases hF : S.F a b C e g kk * S.F a kk Dw d e h * S.F b C Dw h kk f = 0
  · simp [hF]
  · have h1 : S.F a b C e g kk ≠ 0 := fun hh => hF (by rw [hh, zero_mul, zero_mul])
    have h3 : S.F b C Dw h kk f ≠ 0 := fun hh => hF (by rw [hh, mul_zero])
    obtain ⟨-, -, hbCk, hake⟩ := F_ne_zero_supp S h1
    obtain ⟨-, hkDh, -, -⟩ := F_ne_zero_supp S h3
    rw [N_eq_one S hbCk, N_eq_one S hake, N_eq_one S hkDh, one_smul, one_smul, one_smul,
      one_smul]

end FusionCategory
