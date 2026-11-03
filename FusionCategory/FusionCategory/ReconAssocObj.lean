import FusionCategory.ReconAssocStatements

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]
variable (S : FusionSystem n k)

/-! ## Sum-reindexing tools -/

section SumTools

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable {M : Type*} [AddCommMonoid M]

/-- The outermost two sums commute. -/
theorem swap_outer (f : ι → κ → M) : (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b :=
  Finset.sum_comm

end SumTools

/-- `tensorMul` unfolded. -/
theorem tensorMul_eq (X Y : FusionMat n k) (c : Fin n) :
    tensorMul S X Y c = ∑ a : Fin n, ∑ b : Fin n, S.ring.N a b c * X.m a * Y.m b :=
  tensorObj_m S X Y c

/-- The collected multiplicity of `(X ⊗ Y) ⊗ Z`, indexed by the three leaf labels. -/
theorem tensorMul3_left (X Y Z : FusionMat n k) (d : Fin n) :
    (tensorObj S (tensorObj S X Y) Z).m d
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          X.m a * Y.m b * Z.m c * ∑ e : Fin n, S.ring.N a b e * S.ring.N e c d := by
  have hexp : (tensorObj S (tensorObj S X Y) Z).m d
      = ∑ e : Fin n, ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c := by
    rw [tensorObj_m]
    simp only [tensorMul_eq S X Y, Finset.mul_sum, Finset.sum_mul]
  rw [hexp]
  calc (∑ e : Fin n, ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ e : Fin n,
        S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c := by
        have h1 : (∑ e : Fin n, ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
            = ∑ c : Fin n, ∑ e : Fin n, ∑ a : Fin n, ∑ b : Fin n,
              S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c :=
          Finset.sum_comm
        have h2 : (∑ c : Fin n, ∑ e : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
            = ∑ c : Fin n, ∑ a : Fin n, ∑ e : Fin n, ∑ b : Fin n,
              S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
        have h3 : (∑ c : Fin n, ∑ a : Fin n, ∑ e : Fin n, ∑ b : Fin n,
            S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
            = ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ e : Fin n,
              S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
        have h4 : (∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ e : Fin n,
            S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
            = ∑ a : Fin n, ∑ c : Fin n, ∑ b : Fin n, ∑ e : Fin n,
              S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c :=
          Finset.sum_comm
        have h5 : (∑ a : Fin n, ∑ c : Fin n, ∑ b : Fin n, ∑ e : Fin n,
            S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c)
            = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ e : Fin n,
              S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
        rw [h1, h2, h3, h4, h5]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          X.m a * Y.m b * Z.m c * ∑ e : Fin n, S.ring.N a b e * S.ring.N e c d := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        have h : (X.m a * Y.m b * Z.m c) * (∑ e : Fin n, S.ring.N a b e * S.ring.N e c d)
            = ∑ e : Fin n, S.ring.N e c d * (S.ring.N a b e * X.m a * Y.m b) * Z.m c := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
        exact h.symm

/-- The collected multiplicity of `X ⊗ (Y ⊗ Z)`, indexed by the three leaf labels. -/
theorem tensorMul3_right (X Y Z : FusionMat n k) (d : Fin n) :
    (tensorObj S X (tensorObj S Y Z)).m d
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          X.m a * Y.m b * Z.m c * ∑ f : Fin n, S.ring.N b c f * S.ring.N a f d := by
  have hexp : (tensorObj S X (tensorObj S Y Z)).m d
      = ∑ a : Fin n, ∑ f : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c) := by
    rw [tensorObj_m]
    simp only [tensorMul_eq S Y Z, Finset.mul_sum]
  rw [hexp]
  calc (∑ a : Fin n, ∑ f : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ f : Fin n,
        S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c) := by
        have h1 : (∑ a : Fin n, ∑ f : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c))
            = ∑ a : Fin n, ∑ b : Fin n, ∑ f : Fin n, ∑ c : Fin n,
              S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
        have h2 : (∑ a : Fin n, ∑ b : Fin n, ∑ f : Fin n, ∑ c : Fin n,
            S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c))
            = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ f : Fin n,
              S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
        rw [h1, h2]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          X.m a * Y.m b * Z.m c * ∑ f : Fin n, S.ring.N b c f * S.ring.N a f d := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        have h : (X.m a * Y.m b * Z.m c) * (∑ f : Fin n, S.ring.N b c f * S.ring.N a f d)
            = ∑ f : Fin n, S.ring.N a f d * X.m a * (S.ring.N b c f * Y.m b * Z.m c) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => by ring
        exact h.symm

/-- **The object-level associativity** of the reconstruction: `(X⊗Y)⊗Z` and
`X⊗(Y⊗Z)` have the same multiplicity vector, by the fusion ring's associativity. -/
theorem objectAssociativity : ObjectAssociativity S := by
  intro X Y Z d
  rw [tensorMul3_left S X Y Z, tensorMul3_right S X Y Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [S.ring.associativity a b c d]

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.objectAssociativity
#print axioms FusionCategory.tensorMul3_left
#print axioms FusionCategory.tensorMul3_right
