import FusionCategory.ReconAssocStatements

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k) (X Y Z : FusionMat n k) (d : Fin n)

/-- `blkL`: the `d`-block index of `(X ⊗ Y) ⊗ Z`. -/
abbrev blkL : Type := (tensorObj S (tensorObj S X Y) Z).blk d

/-- `blkR`: the `d`-block index of `X ⊗ (Y ⊗ Z)`. -/
abbrev blkR : Type := (tensorObj S X (tensorObj S Y Z)).blk d

/-! ## 1. The associator entry at matched labels -/

theorem assocEntry_apply_matched
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c) :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
      = (if hx : x = x' then (if hy : y = y' then (if hz : z = z' then
          S.F a b c d e f else 0) else 0) else 0) := by
  simp only [assocEntry]
  simp only [dif_pos trivial]

theorem assocInvEntry_apply_matched
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c) :
    assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
      = (if hx : x = x' then (if hy : y = y' then (if hz : z = z' then
          S.Finv a b c d f e else 0) else 0) else 0) := by
  simp only [assocInvEntry]
  simp only [dif_pos trivial]

theorem assocEntry_exact
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d)) (μ' : Fin (S.ring.N b c f)) :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩ = S.F a b c d e f := by
  rw [assocEntry_apply_matched]
  simp

theorem assocInvEntry_exact
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d)) (μ' : Fin (S.ring.N b c f)) :
    assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ = S.Finv a b c d f e := by
  rw [assocInvEntry_apply_matched]
  simp

/-! ## 2. Zero lemmas -/

theorem assocEntry_zero_a {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : r.2.2.1.1.1 ≠ q.1.1) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  exact dif_neg h

theorem assocEntry_zero_b {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h : r.2.2.1.1.2 ≠ q.2.2.2.1.1) :
    assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  rw [dif_pos h1]
  exact dif_neg h

theorem assocEntry_zero_c {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h2 : r.2.2.1.1.2 = q.2.2.2.1.1)
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  rw [dif_pos h1, dif_pos h2]
  exact dif_neg h

theorem assocInvEntry_zero_a {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : r.2.2.1.1.1 ≠ q.1.1) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  exact dif_neg h

theorem assocInvEntry_zero_b {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h : r.2.2.1.1.2 ≠ q.2.2.2.1.1) :
    assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  rw [dif_pos h1]
  exact dif_neg h

theorem assocInvEntry_zero_c {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h2 : r.2.2.1.1.2 = q.2.2.2.1.1)
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  rw [dif_pos h1, dif_pos h2]
  exact dif_neg h

theorem assocEntry_zero_x
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : x ≠ x') :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ = 0 := by
  rw [assocEntry_apply_matched]
  exact dif_neg h


/-- The `x`-zero lemma with the *middle* labels `b₂, c₂` still free. -/
theorem assocEntry_zero_x_gen
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν₂ : Fin (S.ring.N a f d)) (x₂ : X.blk a)
    (b₂ c₂ : Fin n) (μ₂ : Fin (S.ring.N b₂ c₂ f)) (y₂ : Y.blk b₂) (z₂ : Z.blk c₂)
    (h : x ≠ x₂) :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩ = 0 := by
  simp only [assocEntry]
  simp only [dif_pos trivial]
  by_cases h2 : b = b₂
  · rw [dif_pos h2]
    by_cases h3 : c = c₂
    · rw [dif_pos h3, dif_neg h]
    · rw [dif_neg h3]
  · rw [dif_neg h2]

theorem assocEntry_zero_y
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : y ≠ y') :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ = 0 := by
  rw [assocEntry_apply_matched]
  by_cases hx : x = x'
  · rw [dif_pos hx]
    exact dif_neg h
  · exact dif_neg hx

theorem assocEntry_zero_z
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : z ≠ z') :
    assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
        ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ = 0 := by
  rw [assocEntry_apply_matched]
  by_cases hx : x = x'
  · rw [dif_pos hx]
    by_cases hy : y = y'
    · rw [dif_pos hy]
      exact dif_neg h
    · exact dif_neg hy
  · exact dif_neg hx

theorem assocInvEntry_zero_x
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : x ≠ x') :
    assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ = 0 := by
  rw [assocInvEntry_apply_matched]
  exact dif_neg h

theorem assocInvEntry_zero_y
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : y ≠ y') :
    assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ = 0 := by
  rw [assocInvEntry_apply_matched]
  by_cases hx : x = x'
  · rw [dif_pos hx]
    exact dif_neg h
  · exact dif_neg hx

theorem assocInvEntry_zero_z
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν' : Fin (S.ring.N a f d))
    (x' : X.blk a) (μ' : Fin (S.ring.N b c f)) (y' : Y.blk b) (z' : Z.blk c)
    (h : z ≠ z') :
    assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν', ⟨x', ⟨⟨b, c⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩
        ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ = 0 := by
  rw [assocInvEntry_apply_matched]
  by_cases hx : x = x'
  · rw [dif_pos hx]
    by_cases hy : y = y'
    · rw [dif_pos hy]
      exact dif_neg h
    · exact dif_neg hy
  · exact dif_neg hx


/-! ## 2b. HEq-based zero lemmas and their extraction forms -/

theorem assocEntry_zero_heq_x {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.1.2.2.1 q.2.2.1) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        rw [dif_neg (fun h4 => h ((heq_of_eq h4).trans (eqRec_heq (φ := X.blk) h1.symm q.2.2.1)))]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocEntry_zero_heq_y {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.1.2.2.2 q.2.2.2.2.2.1) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        by_cases h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1)
        · rw [dif_pos h4]
          rw [dif_neg (fun h5 => h ((heq_of_eq h5).trans (eqRec_heq (φ := Y.blk) h2.symm q.2.2.2.2.2.1)))]
        · rw [dif_neg h4]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocEntry_zero_heq_z {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.2 q.2.2.2.2.2.2) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        by_cases h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1)
        · rw [dif_pos h4]
          by_cases h5 : r.2.2.1.2.2.2 = (h2 ▸ q.2.2.2.2.2.1)
          · rw [dif_pos h5]
            rw [dif_neg (fun h6 => h ((heq_of_eq h6).trans (eqRec_heq (φ := Z.blk) h3.symm q.2.2.2.2.2.2)))]
          · rw [dif_neg h5]
        · rw [dif_neg h4]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocEntry_ne_zero_heq_x {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocEntry S X Y Z d r q ≠ 0) : HEq r.2.2.1.2.2.1 q.2.2.1 := by
  by_contra hh
  exact h (assocEntry_zero_heq_x (h := hh))

theorem assocEntry_ne_zero_heq_y {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocEntry S X Y Z d r q ≠ 0) : HEq r.2.2.1.2.2.2 q.2.2.2.2.2.1 := by
  by_contra hh
  exact h (assocEntry_zero_heq_y (h := hh))

theorem assocEntry_ne_zero_heq_z {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocEntry S X Y Z d r q ≠ 0) : HEq r.2.2.2 q.2.2.2.2.2.2 := by
  by_contra hh
  exact h (assocEntry_zero_heq_z (h := hh))

theorem assocInvEntry_zero_heq_x {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.1.2.2.1 q.2.2.1) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        rw [dif_neg (fun h4 => h ((heq_of_eq h4).trans (eqRec_heq (φ := X.blk) h1.symm q.2.2.1)))]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocInvEntry_zero_heq_y {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.1.2.2.2 q.2.2.2.2.2.1) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        by_cases h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1)
        · rw [dif_pos h4]
          rw [dif_neg (fun h5 => h ((heq_of_eq h5).trans (eqRec_heq (φ := Y.blk) h2.symm q.2.2.2.2.2.1)))]
        · rw [dif_neg h4]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocInvEntry_zero_heq_z {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : ¬ HEq r.2.2.2 q.2.2.2.2.2.2) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2]
      by_cases h3 : r.1.2 = q.2.2.2.1.2
      · rw [dif_pos h3]
        by_cases h4 : r.2.2.1.2.2.1 = (h1 ▸ q.2.2.1)
        · rw [dif_pos h4]
          by_cases h5 : r.2.2.1.2.2.2 = (h2 ▸ q.2.2.2.2.2.1)
          · rw [dif_pos h5]
            rw [dif_neg (fun h6 => h ((heq_of_eq h6).trans (eqRec_heq (φ := Z.blk) h3.symm q.2.2.2.2.2.2)))]
          · rw [dif_neg h5]
        · rw [dif_neg h4]
      · rw [dif_neg h3]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

theorem assocInvEntry_ne_zero_heq_x {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocInvEntry S X Y Z d q r ≠ 0) : HEq r.2.2.1.2.2.1 q.2.2.1 := by
  by_contra hh
  exact h (assocInvEntry_zero_heq_x (h := hh))

theorem assocInvEntry_ne_zero_heq_y {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocInvEntry S X Y Z d q r ≠ 0) : HEq r.2.2.1.2.2.2 q.2.2.2.2.2.1 := by
  by_contra hh
  exact h (assocInvEntry_zero_heq_y (h := hh))

theorem assocInvEntry_ne_zero_heq_z {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : assocInvEntry S X Y Z d q r ≠ 0) : HEq r.2.2.2 q.2.2.2.2.2.2 := by
  by_contra hh
  exact h (assocInvEntry_zero_heq_z (h := hh))

/-! ## 3. Small arithmetic tools -/


theorem channel_pos {m : ℕ} (ν : Fin m) : 0 < m := ν.pos

theorem sum_fin_const_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (x : M) (h : m • x = x) :
    (∑ _ : Fin m, x) = x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, h]

theorem nsmul_entry (a b c e f e' : Fin n) (m : ℕ)
    (hm : m = S.ring.N a f d ∨ m = S.ring.N b c f) :
    m • (S.F a b c d e f * S.Finv a b c d f e') = S.F a b c d e f * S.Finv a b c d f e' := by
  by_cases hF : S.F a b c d e f = 0
  · simp [hF]
  · have hsupp : 0 < S.ring.N a b e ∧ 0 < S.ring.N e c d ∧ 0 < S.ring.N b c f ∧
        0 < S.ring.N a f d := by
      by_contra hc
      exact hF (S.F_support a b c d e f hc)
    have hbc : S.ring.N b c f = 1 := le_antisymm (S.mult_free b c f) hsupp.2.2.1
    have haf : S.ring.N a f d = 1 := le_antisymm (S.mult_free a f d) hsupp.2.2.2
    rcases hm with h | h
    · rw [h, haf, one_smul]
    · rw [h, hbc, one_smul]

/-! ## 4. The collapse: the forward composite at matched data -/

theorem collapse_matched
    (e c : Fin n) (ν : Fin (S.ring.N e c d))
    (a b : Fin n) (μ : Fin (S.ring.N a b e)) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (e' : Fin n) (ν' : Fin (S.ring.N e' c d)) (μ' : Fin (S.ring.N a b e')) :
    (∑ a₂ : Fin n, ∑ f : Fin n, ∑ ν₂ : Fin (S.ring.N a₂ f d),
        ∑ x₂ : X.blk a₂, ∑ b₂ : Fin n, ∑ c₂ : Fin n,
        ∑ μ₂ : Fin (S.ring.N b₂ c₂ f), ∑ y₂ : Y.blk b₂, ∑ z₂ : Z.blk c₂,
        (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
            ⟨⟨a₂, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
          * assocInvEntry S X Y Z d
              ⟨⟨a₂, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
              ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩))
      = ∑ f : Fin n, S.F a b c d e f * S.Finv a b c d f e' := by
  refine (Finset.sum_eq_single a ?_ ?_).trans ?_
  · intro a₂ _ ha₂
    have hz : ∀ (f : Fin n) (ν₂ : Fin (S.ring.N a₂ f d)) (x₂ : X.blk a₂) (b₂ : Fin n)
        (c₂ : Fin n) (μ₂ : Fin (S.ring.N b₂ c₂ f)) (y₂ : Y.blk b₂) (z₂ : Z.blk c₂),
        (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
            ⟨⟨a₂, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
          * assocInvEntry S X Y Z d
              ⟨⟨a₂, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
              ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩) = 0 := by
      intro f ν₂ x₂ b₂ c₂ μ₂ y₂ z₂
      rw [assocEntry_zero_a (h := Ne.symm ha₂), zero_mul]
    simp only [hz, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [← sum_fin_const_eq (S.ring.N a f d) (S.F a b c d e f * S.Finv a b c d f e')
      (nsmul_entry (S := S) (d := d) (a := a) (b := b) (c := c) (e := e) (f := f) (e' := e')
      (m := S.ring.N a f d) (hm := Or.inl rfl))]
    refine Finset.sum_congr rfl (fun ν₂ _ => ?_)
    refine (Finset.sum_eq_single x ?_ ?_).trans ?_
    · intro x₂ _ hx₂
      have hz : ∀ (b₂ : Fin n) (c₂ : Fin n) (μ₂ : Fin (S.ring.N b₂ c₂ f))
          (y₂ : Y.blk b₂) (z₂ : Z.blk c₂),
          (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
              ⟨⟨a, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
            * assocInvEntry S X Y Z d
                ⟨⟨a, f⟩, ⟨ν₂, ⟨x₂, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩) = 0 := by
        intro b₂ c₂ μ₂ y₂ z₂
        rw [assocEntry_zero_x_gen (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
          (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z) (f := f)
          (ν₂ := ν₂) (x₂ := x₂) (b₂ := b₂) (c₂ := c₂) (μ₂ := μ₂) (y₂ := y₂) (z₂ := z₂)
          (h := Ne.symm hx₂), zero_mul]
      simp only [hz, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
      · intro b₂ _ hb₂
        have hz : ∀ (c₂ : Fin n) (μ₂ : Fin (S.ring.N b₂ c₂ f))
            (y₂ : Y.blk b₂) (z₂ : Z.blk c₂),
            (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
              * assocInvEntry S X Y Z d
                  ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b₂, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                  ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩) = 0 := by
          intro c₂ μ₂ y₂ z₂
          rw [assocEntry_zero_b (h1 := rfl) (h := Ne.symm hb₂), zero_mul]
        simp only [hz, Finset.sum_const_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
      · refine (Finset.sum_eq_single c ?_ ?_).trans ?_
        · intro c₂ _ hc₂
          have hz : ∀ (μ₂ : Fin (S.ring.N b c₂ f)) (y₂ : Y.blk b) (z₂ : Z.blk c₂),
              (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                  ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                * assocInvEntry S X Y Z d
                    ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b, c₂⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                    ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩) = 0 := by
            intro μ₂ y₂ z₂
            rw [assocEntry_zero_c (h1 := rfl) (h2 := rfl) (h := Ne.symm hc₂), zero_mul]
          simp only [hz, Finset.sum_const_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · rw [← sum_fin_const_eq (S.ring.N b c f) (S.F a b c d e f * S.Finv a b c d f e')
            (nsmul_entry (S := S) (d := d) (a := a) (b := b) (c := c) (e := e) (f := f) (e' := e')
            (m := S.ring.N b c f) (hm := Or.inr rfl))]
          refine Finset.sum_congr rfl (fun μ₂ _ => ?_)
          refine (Finset.sum_eq_single y ?_ ?_).trans ?_
          · intro y₂ _ hy₂
            have hz : ∀ (z₂ : Z.blk c),
                (assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩
                    ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b, c⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                  * assocInvEntry S X Y Z d
                      ⟨⟨a, f⟩, ⟨ν₂, ⟨x, ⟨⟨b, c⟩, ⟨μ₂, y₂, z₂⟩⟩⟩⟩⟩
                      ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩) = 0 := by
              intro z₂
              rw [assocEntry_zero_y (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
                  (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z)
                  (f := f) (ν' := ν₂) (x' := x) (μ' := μ₂) (y' := y₂) (z' := z₂)
                  (h := Ne.symm hy₂), zero_mul]
            simp only [hz, Finset.sum_const_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
          · refine (Finset.sum_eq_single z ?_ ?_).trans ?_
            · intro z₂ _ hz₂
              rw [assocEntry_zero_z (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
                  (ν := ν) (a := a) (b := b) (μ := μ) (x := x) (y := y) (z := z)
                  (f := f) (ν' := ν₂) (x' := x) (μ' := μ₂) (y' := y) (z' := z₂)
                  (h := Ne.symm hz₂), zero_mul]
            · intro h
              exact absurd (Finset.mem_univ _) h
            · rw [assocEntry_exact S X Y Z d e c ν a b μ x y z f ν₂ μ₂,
                assocInvEntry_exact S X Y Z d e' c ν' a b μ' x y z f ν₂ μ₂]



/-- Heterogeneous equality of the `z`-projection from an equality of `blkL`-indices. -/
theorem heqProjZ {u v : blkL S X Y Z d} (h : u = v) : HEq u.2.2.2 v.2.2.2 := by
  cases h; exact HEq.rfl

/-- Heterogeneous equality of the `y`-projection from an equality of `blkL`-indices. -/
theorem heqProjY {u v : blkL S X Y Z d} (h : u = v) :
    HEq u.2.2.1.2.2.2 v.2.2.1.2.2.2 := by
  cases h; exact HEq.rfl

/-- Heterogeneous equality of the `x`-projection from an equality of `blkL`-indices. -/
theorem heqProjX {u v : blkL S X Y Z d} (h : u = v) :
    HEq u.2.2.1.2.2.1 v.2.2.1.2.2.1 := by
  cases h; exact HEq.rfl

/-! ## 5. The forward composite entry, and the matrix identity -/


theorem assoc_mul_apply (r r' : blkL S X Y Z d) :
    (Matrix.of (assocEntry S X Y Z d) * Matrix.of (assocInvEntry S X Y Z d)) r r'
      = if r = r' then 1 else 0 := by
  obtain ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ := r
  obtain ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩ := r'
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · by_cases hc : c = c'
      · by_cases hx : HEq x x'
        · by_cases hy : HEq y y'
          · by_cases hzz : HEq z z'
            · subst ha
              subst hb
              subst hc
              obtain rfl : x = x' := eq_of_heq hx
              obtain rfl : y = y' := eq_of_heq hy
              obtain rfl : z = z' := eq_of_heq hzz
              have hsum : (∑ f : Fin n, S.F a b c d e f * S.Finv a b c d f e')
                  = if e' = e then 1 else 0 := by
                rw [Finset.sum_congr rfl (fun f _ =>
                  mul_comm (S.F a b c d e f) (S.Finv a b c d f e'))]
                exact S.F_comp_inv a b c d e' e (Fin.pos μ') (Fin.pos ν') (Fin.pos μ) (Fin.pos ν)
              by_cases he : e = e'
              · subst he
                have hr : (⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ : blkL S X Y Z d)
                    = ⟨⟨e, c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩ := by
                  have h1 : Subsingleton (Fin (S.ring.N e c d)) := channel_subsingleton S e c d
                  have h2 : Subsingleton (Fin (S.ring.N a b e)) := channel_subsingleton S a b e
                  rw [Subsingleton.elim ν ν', Subsingleton.elim μ μ']
                simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
                rw [collapse_matched S X Y Z d e c ν a b μ x y z e ν' μ', hsum,
                  if_pos rfl, if_pos hr]
              · have hr : (⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ : blkL S X Y Z d)
                    ≠ ⟨⟨e', c⟩, ⟨ν', ⟨⟨⟨a, b⟩, ⟨μ', x, y⟩⟩, z⟩⟩⟩ := by
                  intro hh
                  exact he (congrArg (fun u : blkL S X Y Z d => u.1.1) hh)
                simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
                rw [collapse_matched S X Y Z d e c ν a b μ x y z e' ν' μ', hsum,
                  if_neg (fun hh : e' = e => he hh.symm), if_neg hr]
            · rw [Finset.sum_eq_zero (fun m _ => by
                by_cases hA : assocEntry S X Y Z d
                    ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ m = 0
                · rw [hA, zero_mul]
                · rw [assocInvEntry_zero_heq_z (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
                    (q := m) (h := fun hh => hzz ((assocEntry_ne_zero_heq_z (h := hA)).trans hh.symm)),
                    mul_zero]),
                if_neg (fun hh => hzz (heqProjZ (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (u := ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩) (v := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩) hh))]
          · rw [Finset.sum_eq_zero (fun m _ => by
              by_cases hA : assocEntry S X Y Z d
                  ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ m = 0
              · rw [hA, zero_mul]
              · rw [assocInvEntry_zero_heq_y (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
                  (q := m) (h := fun hh => hy ((assocEntry_ne_zero_heq_y (h := hA)).trans hh.symm)),
                  mul_zero]),
              if_neg (fun hh => hy (heqProjY (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (u := ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩) (v := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩) hh))]
        · rw [Finset.sum_eq_zero (fun m _ => by
            by_cases hA : assocEntry S X Y Z d
                ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩ m = 0
            · rw [hA, zero_mul]
            · rw [assocInvEntry_zero_heq_x (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
                (q := m) (h := fun hh => hx ((assocEntry_ne_zero_heq_x (h := hA)).trans hh.symm)),
                mul_zero]),
            if_neg (fun hh => hx (heqProjX (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (u := ⟨⟨e, c⟩, ⟨ν, ⟨⟨⟨a, b⟩, ⟨μ, x, y⟩⟩, z⟩⟩⟩) (v := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩) hh))]
      · rw [Finset.sum_eq_zero (fun m _ => by
          by_cases h1 : a = m.1.1
          · by_cases h2 : b = m.2.2.2.1.1
            · by_cases h3 : c = m.2.2.2.1.2
              · rw [assocInvEntry_zero_c (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
                  (q := m) (h1 := (ha.symm.trans h1)) (h2 := (hb.symm.trans h2))
                  (h := fun hh => hc (h3.trans hh.symm)), mul_zero]
              · rw [assocEntry_zero_c (h1 := h1) (h2 := h2) (h := h3), zero_mul]
            · rw [assocEntry_zero_b (h1 := h1) (h := h2), zero_mul]
          · rw [assocEntry_zero_a (h := h1), zero_mul]),
          if_neg (fun hh => hc (congrArg (fun u : blkL S X Y Z d => u.1.2) hh))]
    · rw [Finset.sum_eq_zero (fun m _ => by
        by_cases h1 : a = m.1.1
        · by_cases h2 : b = m.2.2.2.1.1
          · rw [assocInvEntry_zero_b (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
              (q := m) (h1 := (ha.symm.trans h1)) (h := fun hh => hb (h2.trans hh.symm)), mul_zero]
          · rw [assocEntry_zero_b (h1 := h1) (h := h2), zero_mul]
        · rw [assocEntry_zero_a (h := h1), zero_mul]),
        if_neg (fun hh => hb (congrArg (fun u : blkL S X Y Z d => u.2.2.1.1.2) hh))]
  · rw [Finset.sum_eq_zero (fun m _ => by
      by_cases h1 : a = m.1.1
      · rw [assocInvEntry_zero_a (r := ⟨⟨e', c'⟩, ⟨ν', ⟨⟨⟨a', b'⟩, ⟨μ', x', y'⟩⟩, z'⟩⟩⟩)
          (q := m) (h := fun hh => ha (h1.trans hh.symm)), mul_zero]
      · rw [assocEntry_zero_a (h := h1), zero_mul]),
      if_neg (fun hh => ha (congrArg (fun u : blkL S X Y Z d => u.2.2.1.1.1) hh))]

theorem assoc_mul (d : Fin n) :
    Matrix.of (assocEntry S X Y Z d) * Matrix.of (assocInvEntry S X Y Z d)
      = (1 : Matrix (blkL S X Y Z d) (blkL S X Y Z d) k) := by
  ext r r'
  rw [assoc_mul_apply S X Y Z d r r', Matrix.one_apply]

/-- First half of `AssociatorIso`: `α ≫ α⁻¹ = 𝟙`. -/
theorem associatorHom_comp_associatorInv :
    associatorHom S X Y Z ≫ associatorInv S X Y Z
      = 𝟙 (tensorObj S (tensorObj S X Y) Z) :=
  funext fun d => assoc_mul S X Y Z d


/-! ## 6. The mirror: `α⁻¹ ≫ α = 𝟙` -/

/-- Prerequisite-free `c`-zero lemma for the associator. -/
theorem assocEntry_zero_c' {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2, dif_neg h]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

/-- Prerequisite-free `c`-zero lemma for the inverse associator. -/
theorem assocInvEntry_zero_c' {r : blkL S X Y Z d} {q : blkR S X Y Z d}
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  by_cases h1 : r.2.2.1.1.1 = q.1.1
  · rw [dif_pos h1]
    by_cases h2 : r.2.2.1.1.2 = q.2.2.2.1.1
    · rw [dif_pos h2, dif_neg h]
    · rw [dif_neg h2]
  · rw [dif_neg h1]

/-- The channel `e ⊗ c → d` does not change the `Finv`-`F` product. -/
theorem nsmul_entry_inv (a b c e f f' : Fin n) (m : ℕ)
    (hm : m = S.ring.N e c d ∨ m = S.ring.N a b e) :
    m • (S.Finv a b c d f e * S.F a b c d e f') = S.Finv a b c d f e * S.F a b c d e f' := by
  by_cases hP : S.Finv a b c d f e * S.F a b c d e f' = 0
  · simp [hP]
  · have hFi : S.Finv a b c d f e ≠ 0 := fun hh => hP (by rw [hh, zero_mul])
    have hsupp : 0 < S.ring.N b c f ∧ 0 < S.ring.N a f d ∧ 0 < S.ring.N a b e ∧
        0 < S.ring.N e c d := by
      by_contra hc
      exact hFi (S.Finv_support a b c d f e hc)
    have hec : S.ring.N e c d = 1 := le_antisymm (S.mult_free e c d) hsupp.2.2.2
    have hab : S.ring.N a b e = 1 := le_antisymm (S.mult_free a b e) hsupp.2.2.1
    rcases hm with h | h
    · rw [h, hec, one_smul]
    · rw [h, hab, one_smul]

/-- **The mirror collapse.** -/
theorem collapse_matched_inv
    (a b c : Fin n) (x : X.blk a) (y : Y.blk b) (z : Z.blk c)
    (f : Fin n) (ν : Fin (S.ring.N a f d)) (μ : Fin (S.ring.N b c f))
    (f' : Fin n) (ν' : Fin (S.ring.N a f' d)) (μ' : Fin (S.ring.N b c f')) :
    (∑ e : Fin n, ∑ c₂ : Fin n, ∑ ν₂ : Fin (S.ring.N e c₂ d),
        ∑ a₂ : Fin n, ∑ b₂ : Fin n, ∑ μ₂ : Fin (S.ring.N a₂ b₂ e),
        ∑ x₂ : X.blk a₂, ∑ y₂ : Y.blk b₂, ∑ z₂ : Z.blk c₂,
        (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
            ⟨⟨e, c₂⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
          * assocEntry S X Y Z d
              ⟨⟨e, c₂⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
              ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩))
      = ∑ e : Fin n, S.Finv a b c d f e * S.F a b c d e f' := by
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine (Finset.sum_eq_single c ?_ ?_).trans ?_
  · intro c₂ _ hc₂
    have hz : ∀ (ν₂ : Fin (S.ring.N e c₂ d)) (a₂ : Fin n) (b₂ : Fin n)
        (μ₂ : Fin (S.ring.N a₂ b₂ e)) (x₂ : X.blk a₂) (y₂ : Y.blk b₂) (z₂ : Z.blk c₂),
        (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
            ⟨⟨e, c₂⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
          * assocEntry S X Y Z d
              ⟨⟨e, c₂⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
              ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩) = 0 := by
      intro ν₂ a₂ b₂ μ₂ x₂ y₂ z₂
      rw [assocEntry_zero_c' (h := hc₂), mul_zero]
    simp only [hz, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [← sum_fin_const_eq (S.ring.N e c d) (S.Finv a b c d f e * S.F a b c d e f')
      (nsmul_entry_inv (S := S) (d := d) (a := a) (b := b) (c := c) (e := e) (f := f) (f' := f')
        (m := S.ring.N e c d) (hm := Or.inl rfl))]
    refine Finset.sum_congr rfl (fun ν₂ _ => ?_)
    refine (Finset.sum_eq_single a ?_ ?_).trans ?_
    · intro a₂ _ ha₂
      have hz : ∀ (b₂ : Fin n) (μ₂ : Fin (S.ring.N a₂ b₂ e)) (x₂ : X.blk a₂)
          (y₂ : Y.blk b₂) (z₂ : Z.blk c),
          (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
              ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
            * assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a₂, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
                ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩) = 0 := by
        intro b₂ μ₂ x₂ y₂ z₂
        rw [assocInvEntry_zero_a (h := ha₂), zero_mul]
      simp only [hz, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · refine (Finset.sum_eq_single b ?_ ?_).trans ?_
      · intro b₂ _ hb₂
        have hz : ∀ (μ₂ : Fin (S.ring.N a b₂ e)) (x₂ : X.blk a) (y₂ : Y.blk b₂)
            (z₂ : Z.blk c),
            (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
                ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
              * assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
                  ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩) = 0 := by
          intro μ₂ x₂ y₂ z₂
          rw [assocInvEntry_zero_b (r := ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b₂⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩)
            (q := ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩) (h1 := rfl) (h := hb₂), zero_mul]
        simp only [hz, Finset.sum_const_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
      · rw [← sum_fin_const_eq (S.ring.N a b e) (S.Finv a b c d f e * S.F a b c d e f')
          (nsmul_entry_inv (S := S) (d := d) (a := a) (b := b) (c := c) (e := e) (f := f)
            (f' := f') (m := S.ring.N a b e) (hm := Or.inr rfl))]
        refine Finset.sum_congr rfl (fun μ₂ _ => ?_)
        refine (Finset.sum_eq_single x ?_ ?_).trans ?_
        · intro x₂ _ hx₂
          have hz : ∀ (y₂ : Y.blk b) (z₂ : Z.blk c),
              (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
                  ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
                * assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b⟩, ⟨μ₂, x₂, y₂⟩⟩, z₂⟩⟩⟩
                    ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩) = 0 := by
            intro y₂ z₂
            rw [assocEntry_zero_x (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
              (ν := ν₂) (a := a) (b := b) (μ := μ₂) (x := x₂) (y := y₂) (z := z₂) (f := f')
              (ν' := ν') (x' := x) (μ' := μ') (y' := y) (z' := z) (h := hx₂), mul_zero]
          simp only [hz, Finset.sum_const_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · refine (Finset.sum_eq_single y ?_ ?_).trans ?_
          · intro y₂ _ hy₂
            have hz : ∀ (z₂ : Z.blk c),
                (assocInvEntry S X Y Z d ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩
                    ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b⟩, ⟨μ₂, x, y₂⟩⟩, z₂⟩⟩⟩
                  * assocEntry S X Y Z d ⟨⟨e, c⟩, ⟨ν₂, ⟨⟨⟨a, b⟩, ⟨μ₂, x, y₂⟩⟩, z₂⟩⟩⟩
                      ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩) = 0 := by
              intro z₂
              rw [assocEntry_zero_y (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
                (ν := ν₂) (a := a) (b := b) (μ := μ₂) (x := x) (y := y₂) (z := z₂) (f := f')
                (ν' := ν') (x' := x) (μ' := μ') (y' := y) (z' := z) (h := hy₂), mul_zero]
            simp only [hz, Finset.sum_const_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
          · refine (Finset.sum_eq_single z ?_ ?_).trans ?_
            · intro z₂ _ hz₂
              rw [assocEntry_zero_z (S := S) (X := X) (Y := Y) (Z := Z) (d := d) (e := e) (c := c)
                (ν := ν₂) (a := a) (b := b) (μ := μ₂) (x := x) (y := y) (z := z₂) (f := f')
                (ν' := ν') (x' := x) (μ' := μ') (y' := y) (z' := z) (h := hz₂), mul_zero]
            · intro h
              exact absurd (Finset.mem_univ _) h
            · rw [assocInvEntry_exact S X Y Z d e c ν₂ a b μ₂ x y z f ν μ,
                assocEntry_exact S X Y Z d e c ν₂ a b μ₂ x y z f' ν' μ']


/-- Heterogeneous equality of the `x`-projection of `blkR`-indices. -/
theorem heqProjRX {u v : blkR S X Y Z d} (h : u = v) : HEq u.2.2.1 v.2.2.1 := by
  cases h; exact HEq.rfl

/-- Heterogeneous equality of the `y`-projection of `blkR`-indices. -/
theorem heqProjRY {u v : blkR S X Y Z d} (h : u = v) :
    HEq u.2.2.2.2.2.1 v.2.2.2.2.2.1 := by
  cases h; exact HEq.rfl

/-- Heterogeneous equality of the `z`-projection of `blkR`-indices. -/
theorem heqProjRZ {u v : blkR S X Y Z d} (h : u = v) :
    HEq u.2.2.2.2.2.2 v.2.2.2.2.2.2 := by
  cases h; exact HEq.rfl

theorem assoc_inv_mul_apply (q q' : blkR S X Y Z d) :
    (Matrix.of (assocInvEntry S X Y Z d) * Matrix.of (assocEntry S X Y Z d)) q q'
      = if q = q' then 1 else 0 := by
  obtain ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ := q
  obtain ⟨⟨a', f'⟩, ⟨ν', ⟨x', ⟨⟨b', c'⟩, ⟨μ', y', z'⟩⟩⟩⟩⟩ := q'
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · by_cases hc : c = c'
      · by_cases hx : HEq x x'
        · by_cases hy : HEq y y'
          · by_cases hzz : HEq z z'
            · subst ha
              subst hb
              subst hc
              obtain rfl : x = x' := eq_of_heq hx
              obtain rfl : y = y' := eq_of_heq hy
              obtain rfl : z = z' := eq_of_heq hzz
              have hsum : (∑ e : Fin n, S.Finv a b c d f e * S.F a b c d e f')
                  = if f = f' then 1 else 0 :=
                S.Finv_comp a b c d f f' (Fin.pos μ) (Fin.pos ν) (Fin.pos μ') (Fin.pos ν')
              by_cases hf : f = f'
              · subst hf
                have hq : (⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ : blkR S X Y Z d)
                    = ⟨⟨a, f⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩ := by
                  have h1 : Subsingleton (Fin (S.ring.N a f d)) := channel_subsingleton S a f d
                  have h2 : Subsingleton (Fin (S.ring.N b c f)) := channel_subsingleton S b c f
                  rw [Subsingleton.elim ν ν', Subsingleton.elim μ μ']
                simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
                rw [collapse_matched_inv S X Y Z d a b c x y z f ν μ f ν' μ', hsum,
                  if_pos rfl, if_pos hq]
              · have hq : (⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ : blkR S X Y Z d)
                    ≠ ⟨⟨a, f'⟩, ⟨ν', ⟨x, ⟨⟨b, c⟩, ⟨μ', y, z⟩⟩⟩⟩⟩ := by
                  intro hh
                  exact hf (congrArg (fun u : blkR S X Y Z d => u.1.2) hh)
                simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
                rw [collapse_matched_inv S X Y Z d a b c x y z f ν μ f' ν' μ', hsum,
                  if_neg hf, if_neg hq]
            · rw [Finset.sum_eq_zero (fun m _ => by
                by_cases hA : assocInvEntry S X Y Z d
                    ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ m = 0
                · rw [hA, zero_mul]
                · rw [assocEntry_zero_heq_z (h := fun hh =>
                    hzz ((assocInvEntry_ne_zero_heq_z (h := hA)).symm.trans hh)), mul_zero]),
                if_neg (fun hh => hzz (heqProjRZ (S := S) (X := X) (Y := Y) (Z := Z) (d := d) hh))]
          · rw [Finset.sum_eq_zero (fun m _ => by
              by_cases hA : assocInvEntry S X Y Z d
                  ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ m = 0
              · rw [hA, zero_mul]
              · rw [assocEntry_zero_heq_y (h := fun hh =>
                  hy ((assocInvEntry_ne_zero_heq_y (h := hA)).symm.trans hh)), mul_zero]),
              if_neg (fun hh => hy (heqProjRY (S := S) (X := X) (Y := Y) (Z := Z) (d := d) hh))]
        · rw [Finset.sum_eq_zero (fun m _ => by
            by_cases hA : assocInvEntry S X Y Z d
                ⟨⟨a, f⟩, ⟨ν, ⟨x, ⟨⟨b, c⟩, ⟨μ, y, z⟩⟩⟩⟩⟩ m = 0
            · rw [hA, zero_mul]
            · rw [assocEntry_zero_heq_x (h := fun hh =>
                hx ((assocInvEntry_ne_zero_heq_x (h := hA)).symm.trans hh)), mul_zero]),
            if_neg (fun hh => hx (heqProjRX (S := S) (X := X) (Y := Y) (Z := Z) (d := d) hh))]
      · rw [Finset.sum_eq_zero (fun m _ => by
          by_cases h1 : m.2.2.1.1.1 = a
          · by_cases h2 : m.2.2.1.1.2 = b
            · by_cases h3 : m.1.2 = c
              · rw [assocEntry_zero_c (h1 := h1.trans ha) (h2 := h2.trans hb)
                  (h := fun hh => hc (h3.symm.trans hh)), mul_zero]
              · rw [assocInvEntry_zero_c' (h := h3), zero_mul]
            · rw [assocInvEntry_zero_b (h1 := h1) (h := h2), zero_mul]
          · rw [assocInvEntry_zero_a (h := h1), zero_mul]),
          if_neg (fun hh => hc (congrArg (fun u : blkR S X Y Z d => u.2.2.2.1.2) hh))]
    · rw [Finset.sum_eq_zero (fun m _ => by
        by_cases h1 : m.2.2.1.1.1 = a
        · by_cases h2 : m.2.2.1.1.2 = b
          · rw [assocEntry_zero_b (h1 := h1.trans ha) (h := fun hh => hb (h2.symm.trans hh)),
              mul_zero]
          · rw [assocInvEntry_zero_b (h1 := h1) (h := h2), zero_mul]
        · rw [assocInvEntry_zero_a (h := h1), zero_mul]),
        if_neg (fun hh => hb (congrArg (fun u : blkR S X Y Z d => u.2.2.2.1.1) hh))]
  · rw [Finset.sum_eq_zero (fun m _ => by
      by_cases h1 : m.2.2.1.1.1 = a
      · rw [assocEntry_zero_a (h := fun hh => ha (h1.symm.trans hh)), mul_zero]
      · rw [assocInvEntry_zero_a (h := h1), zero_mul]),
      if_neg (fun hh => ha (congrArg (fun u : blkR S X Y Z d => u.1.1) hh))]

theorem assoc_inv_mul (d : Fin n) :
    Matrix.of (assocInvEntry S X Y Z d) * Matrix.of (assocEntry S X Y Z d)
      = (1 : Matrix (blkR S X Y Z d) (blkR S X Y Z d) k) := by
  ext q q'
  rw [assoc_inv_mul_apply S X Y Z d q q', Matrix.one_apply]

/-- Second half of `AssociatorIso`: `α⁻¹ ≫ α = 𝟙`. -/
theorem associatorInv_comp_associatorHom :
    associatorInv S X Y Z ≫ associatorHom S X Y Z
      = 𝟙 (tensorObj S X (tensorObj S Y Z)) :=
  funext fun d => assoc_inv_mul S X Y Z d

/-- **`AssociatorIso`** (one of the three frozen statements of `ReconAssocStatements`). -/
theorem associatorIso : AssociatorIso S :=
  ⟨fun X Y Z => associatorHom_comp_associatorInv S X Y Z,
   fun X Y Z => associatorInv_comp_associatorHom S X Y Z⟩

/-- The associator as an `Iso` of the reconstruction — the form a
`MonoidalCategoryStruct` consumes. -/
def associatorIsoIso (X Y Z : FusionMat n k) :
    Iso (tensorObj S (tensorObj S X Y) Z) (tensorObj S X (tensorObj S Y Z)) where
  hom := associatorHom S X Y Z
  inv := associatorInv S X Y Z
  hom_inv_id := associatorHom_comp_associatorInv S X Y Z
  inv_hom_id := associatorInv_comp_associatorHom S X Y Z

@[simp] theorem associatorIsoIso_hom (X Y Z : FusionMat n k) :
    (associatorIsoIso S X Y Z).hom = associatorHom S X Y Z := rfl

@[simp] theorem associatorIsoIso_inv (X Y Z : FusionMat n k) :
    (associatorIsoIso S X Y Z).inv = associatorInv S X Y Z := rfl


end FusionCategory


/-! ## Axiom audit -/


#print axioms FusionCategory.assocEntry_apply_matched
#print axioms FusionCategory.collapse_matched
#print axioms FusionCategory.collapse_matched_inv
#print axioms FusionCategory.assoc_mul
#print axioms FusionCategory.assoc_inv_mul
#print axioms FusionCategory.associatorHom_comp_associatorInv
#print axioms FusionCategory.associatorInv_comp_associatorHom
#print axioms FusionCategory.associatorIso
