import FusionCategory.System

open FusionCategory

universe u

namespace TriangleCheck

variable {n : ℕ} {k : Type u} [Field k]

/-- Helper: the only `x` with `N x 1 j > 0` is `x = j`. -/
theorem right_unit_pos (S : FusionSystem n k) (hn : 0 < n) {a e : Fin n}
    (h : 0 < S.ring.N a ⟨0, hn⟩ e) : a = e := by
  rw [S.ring.right_unit hn a e] at h
  by_contra hne
  simp [hne] at h

/-- Helper: the only `j` with `N 1 1 j > 0` is `j = 1`. -/
theorem left_unit_pos (S : FusionSystem n k) (hn : 0 < n) {j : Fin n}
    (h : 0 < S.ring.N ⟨0, hn⟩ ⟨0, hn⟩ j) : j = ⟨0, hn⟩ := by
  rw [S.ring.left_unit hn ⟨0, hn⟩ j] at h
  by_contra hne
  rw [if_neg (fun h' => hne h'.symm)] at h
  exact lt_irrefl 0 h

/-- The middle-unit entry `t = F^{a 1 c}_d(a,c)` is forced to be `1` by the
pentagon at `(a,1,1,c)` and the inverse law. -/
theorem triangle (S : FusionSystem n k) (hn : 0 < n) (a c d : Fin n)
    (hacd : 0 < S.ring.N a c d) :
    S.F a ⟨0, hn⟩ c d a c = 1 := by
  -- the pentagon at (a, 1, 1, c) with x = a, e = a, i = c, j = c, r = d
  have hp := S.pentagon a ⟨0, hn⟩ ⟨0, hn⟩ c a c c d a
  -- every summand with k ≠ 1 vanishes by support
  have hterm : ∀ kk : Fin n, kk ≠ ⟨0, hn⟩ → S.F a ⟨0, hn⟩ ⟨0, hn⟩ a a kk = 0 := by
    intro kk hk
    refine S.F_support a ⟨0, hn⟩ ⟨0, hn⟩ a a kk ?_
    intro hcon
    exact hk (left_unit_pos S hn hcon.2.2.1)
  have hsum : (∑ kk : Fin n,
        S.F a ⟨0, hn⟩ ⟨0, hn⟩ a a kk * S.F a kk c d a c * S.F ⟨0, hn⟩ ⟨0, hn⟩ c c kk c)
      = S.F a ⟨0, hn⟩ ⟨0, hn⟩ a a ⟨0, hn⟩ * S.F a ⟨0, hn⟩ c d a c *
          S.F ⟨0, hn⟩ ⟨0, hn⟩ c c ⟨0, hn⟩ c := by
    refine Finset.sum_eq_single (⟨0, hn⟩ : Fin n) ?_ ?_
    · intro b _ hb
      rw [hterm b hb, zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at hp
  -- the two unit entries are 1
  have hFu : S.F a ⟨0, hn⟩ ⟨0, hn⟩ a a ⟨0, hn⟩ = 1 := by
    have h1 : 0 < S.ring.N a ⟨0, hn⟩ a := by
      rw [S.ring.right_unit hn a a]; simp
    have := S.F_unit_right hn a ⟨0, hn⟩ a a h1
    simpa using this
  have hFc : S.F ⟨0, hn⟩ ⟨0, hn⟩ c c ⟨0, hn⟩ c = 1 := by
    have h1 : 0 < S.ring.N ⟨0, hn⟩ c c := by
      rw [S.ring.left_unit hn c c]; simp
    have := S.F_unit_left hn ⟨0, hn⟩ c c c h1
    simpa using this
  rw [hFu, hFc] at hp
  -- hp : 1 * t * 1 = t * t
  have htt : S.F a ⟨0, hn⟩ c d a c * S.F a ⟨0, hn⟩ c d a c = S.F a ⟨0, hn⟩ c d a c := by
    simpa using hp.symm
  -- t ≠ 0, from the inverse law at the (1 x 1) block (a,1,c;d)
  have hne : S.F a ⟨0, hn⟩ c d a c ≠ 0 := by
    intro hzero
    have h1 : 0 < S.ring.N ⟨0, hn⟩ c c := by
      rw [S.ring.left_unit hn c c]; simp
    have hcomp := S.Finv_comp a ⟨0, hn⟩ c d c c h1 hacd h1 hacd
    have hsupp : ∀ e : Fin n, e ≠ a → S.Finv a ⟨0, hn⟩ c d c e = 0 := by
      intro e he
      refine S.Finv_support a ⟨0, hn⟩ c d c e ?_
      intro hcon
      exact he (right_unit_pos S hn hcon.2.2.1).symm
    have hsum2 : (∑ e : Fin n, S.Finv a ⟨0, hn⟩ c d c e * S.F a ⟨0, hn⟩ c d e c)
        = S.Finv a ⟨0, hn⟩ c d c a * S.F a ⟨0, hn⟩ c d a c := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro b _ hb
        rw [hsupp b hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum2, hzero, mul_zero] at hcomp
    simp at hcomp
  refine mul_right_cancel₀ hne ?_
  simpa using htt

end TriangleCheck

#print axioms TriangleCheck.triangle
