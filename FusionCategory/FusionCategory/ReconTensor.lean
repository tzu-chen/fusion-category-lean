/-
WP2 round 1, member m3, direction D4 (foundation piece): the tensor of the
reconstruction.

`tensorObj` is the fusion-ring convolution on multiplicity vectors; its block
`c` is the channel-refined index type
`Σ (p : Fin n × Fin n), Fin (N p.1 p.2 c) × X.blk p.1 × Y.blk p.2`,
so `mult_free` makes the channel coordinate a subsingleton.

`tensorHom` is entrywise-diagonal on the label `p` and carries the full block
matrix on the multiplicities (the design note's `i = i'` conjunct is dropped:
it is not functorial — see the board finding).  With `blockDiag` the
bifunctoriality laws are `blockDiag_mul_blockDiag` plus the Kronecker
composition law, with no Σ-bookkeeping at all.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.Recon

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## The Kronecker composition law -/

section Kronecker

variable {l m nn p l' m' nn' p' : Type}
variable [Fintype m] [Fintype p] [Fintype m'] [Fintype p']

/-- `(A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D)`. -/
theorem kroneckerMap_mul (A : Matrix l m k) (B : Matrix nn p k) (C : Matrix m l' k)
    (D : Matrix p nn' k) :
    Matrix.kroneckerMap (· * ·) A B * Matrix.kroneckerMap (· * ·) C D
      = Matrix.kroneckerMap (· * ·) (A * C) (B * D) := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.mul_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end Kronecker

/-! ## The tensor on objects -/

variable (S : FusionSystem n k)

/-- Multiplicity of the tensor: the fusion-ring convolution. -/
def tensorMul (X Y : FusionMat n k) (c : Fin n) : ℕ :=
  ∑ p : Fin n × Fin n, S.ring.N p.1 p.2 c * X.m p.1 * Y.m p.2

/-- The block index type of `X ⊗ Y` at label `c`: the label `p`, its unique
channel, and the multiplicity indices of the two factors. -/
abbrev TensorIdx (X Y : FusionMat n k) (c : Fin n) : Type :=
  Σ (p : Fin n × Fin n), Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2

instance tensorIdxFintype (X Y : FusionMat n k) (c : Fin n) : Fintype (TensorIdx S X Y c) :=
  inferInstanceAs (Fintype (Σ (p : Fin n × Fin n), Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2))

instance tensorIdxDecidableEq (X Y : FusionMat n k) (c : Fin n) : DecidableEq (TensorIdx S X Y c) :=
  inferInstanceAs (DecidableEq (Σ (p : Fin n × Fin n), Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2))

/-- The tensor on objects. -/
abbrev tensorObj (X Y : FusionMat n k) : FusionMat n k where
  m := tensorMul S X Y
  blk c := TensorIdx S X Y c
  fintype_blk c := tensorIdxFintype S X Y c
  decidableEq_blk c := tensorIdxDecidableEq S X Y c
  card_blk c := by
    show Fintype.card (Σ (p : Fin n × Fin n), Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2)
      = ∑ p : Fin n × Fin n, S.ring.N p.1 p.2 c * X.m p.1 * Y.m p.2
    simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
      X.card_blk, Y.card_blk, mul_assoc]

/-- The design note's multiplicity formula, with the two label sums separated. -/
theorem tensorObj_m (X Y : FusionMat n k) (c : Fin n) :
    (tensorObj S X Y).m c = ∑ a : Fin n, ∑ b : Fin n, S.ring.N a b c * X.m a * Y.m b := by
  simp only [tensorObj, tensorMul, Fintype.sum_prod_type]

/-- Multiplicity-freeness makes the channel coordinate a subsingleton. -/
theorem channel_subsingleton (a b c : Fin n) :
    Subsingleton (Fin (S.ring.N a b c)) := by
  have h := S.mult_free a b c
  constructor
  intro x y
  have hx := x.isLt
  have hy := y.isLt
  ext
  omega

/-- Multiplicity-freeness: the number of channels is at most one. -/
theorem card_channel_le_one (a b c : Fin n) :
    Fintype.card (Fin (S.ring.N a b c)) ≤ 1 := by
  simpa using S.mult_free a b c

/-! ## The tensor on morphisms -/

/-- The `(c, p)`-block of the tensor: identity on the (subsingleton) channel
coordinate, Kronecker product of the two factor blocks. -/
def tensorHomBlock {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Fin n) (p : Fin n × Fin n) :
    Matrix (Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2)
      (Fin (S.ring.N p.1 p.2 c) × X'.blk p.1 × Y'.blk p.2) k :=
  Matrix.kroneckerMap (fun a b : k => a * b)
    (1 : Matrix (Fin (S.ring.N p.1 p.2 c)) (Fin (S.ring.N p.1 p.2 c)) k)
    (Matrix.kroneckerMap (fun a b : k => a * b) (f p.1) (g p.2))

/-- The tensor on morphisms: `blockDiag` over the label `p`. -/
def tensorHom {X X' Y Y' : FusionMat n k} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj S X Y ⟶ tensorObj S X' Y' :=
  fun c => blockDiag (fun p : Fin n × Fin n => tensorHomBlock S f g c p)

section Functoriality

variable {X X' X'' Y Y' Y'' : FusionMat n k}

theorem tensorHomBlock_id (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S (𝟙 X) (𝟙 Y) c p
      = (1 : Matrix (Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2)
            (Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2) k) := by
  have hX : (𝟙 X) p.1 = (1 : Matrix (X.blk p.1) (X.blk p.1) k) := rfl
  have hY : (𝟙 Y) p.2 = (1 : Matrix (Y.blk p.2) (Y.blk p.2) k) := rfl
  simp only [tensorHomBlock, hX, hY, Matrix.one_kronecker_one]

theorem tensorHom_id (X Y : FusionMat n k) :
    tensorHom S (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj S X Y) := by
  funext c
  show blockDiag (fun p : Fin n × Fin n => tensorHomBlock S (𝟙 X) (𝟙 Y) c p)
    = (1 : Matrix ((tensorObj S X Y).blk c) ((tensorObj S X Y).blk c) k)
  rw [show (fun p : Fin n × Fin n => tensorHomBlock S (𝟙 X) (𝟙 Y) c p)
      = (fun p : Fin n × Fin n =>
          (1 : Matrix (Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2)
                (Fin (S.ring.N p.1 p.2 c) × X.blk p.1 × Y.blk p.2) k))
      from funext (tensorHomBlock_id S c)]
  exact blockDiag_one

theorem tensorHomBlock_comp (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (c : Fin n) (p : Fin n × Fin n) :
    tensorHomBlock S (f ≫ f') (g ≫ g') c p
      = tensorHomBlock S f g c p * tensorHomBlock S f' g' c p := by
  simp only [tensorHomBlock]
  rw [kroneckerMap_mul, kroneckerMap_mul, Matrix.one_mul]
  rfl

theorem tensorHom_comp (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorHom S (f ≫ f') (g ≫ g') = tensorHom S f g ≫ tensorHom S f' g' := by
  funext c
  show blockDiag (fun p : Fin n × Fin n => tensorHomBlock S (f ≫ f') (g ≫ g') c p)
    = blockDiag (fun p : Fin n × Fin n => tensorHomBlock S f g c p)
      * blockDiag (fun p : Fin n × Fin n => tensorHomBlock S f' g' c p)
  rw [blockDiag_mul_blockDiag]
  congr 1
  funext p
  exact tensorHomBlock_comp S f f' g g' c p

end Functoriality

/-- The tensor is a genuine bifunctor `C × C ⥤ C`. -/
def tensorFunctor :
    FusionMat n k × FusionMat n k ⥤ FusionMat n k where
  obj P := tensorObj S P.1 P.2
  map f := tensorHom S f.1 f.2
  map_id P := tensorHom_id S P.1 P.2
  map_comp f g := tensorHom_comp S f.1 g.1 f.2 g.2

/-! ## Whiskers -/

/-- Left whiskering. -/
def whiskerLeft (X : FusionMat n k) {Y Y' : FusionMat n k}
    (g : Y ⟶ Y') : tensorObj S X Y ⟶ tensorObj S X Y' :=
  tensorHom S (𝟙 X) g

/-- Right whiskering. -/
def whiskerRight {X X' : FusionMat n k} (f : X ⟶ X')
    (Y : FusionMat n k) : tensorObj S X Y ⟶ tensorObj S X' Y :=
  tensorHom S f (𝟙 Y)

theorem whiskerLeft_id (X Y : FusionMat n k) :
    whiskerLeft S X (𝟙 Y) = 𝟙 (tensorObj S X Y) :=
  tensorHom_id S X Y

theorem whiskerLeft_comp {X Y Y' Y'' : FusionMat n k} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    whiskerLeft S X g ≫ whiskerLeft S X g' = whiskerLeft S X (g ≫ g') :=
  (by simpa [whiskerLeft] using (tensorHom_comp S (𝟙 X) (𝟙 X) g g').symm)

theorem whiskerRight_id (X Y : FusionMat n k) :
    whiskerRight S (𝟙 X) Y = 𝟙 (tensorObj S X Y) :=
  tensorHom_id S X Y

theorem whiskerRight_comp {X X' X'' Y : FusionMat n k} (f : X ⟶ X') (f' : X' ⟶ X'') :
    whiskerRight S f Y ≫ whiskerRight S f' Y = whiskerRight S (f ≫ f') Y :=
  (by simpa [whiskerRight] using (tensorHom_comp S f f' (𝟙 Y) (𝟙 Y)).symm)

/-! ## The simples, and the tensor of simples -/

/-- The simple object with label `i`. -/
def sim (i : Fin n) : FusionMat n k where
  m j := if j = i then 1 else 0
  blk j := Fin (if j = i then 1 else 0)
  fintype_blk _ := inferInstance
  decidableEq_blk _ := inferInstance
  card_blk _ := by simp

/-- The tensor of two simples carries the fusion coefficient `N a b c`: the
reconstruction computes the system's fusion rules. -/
theorem tensorObj_sim_m (a b c : Fin n) :
    (tensorObj S (sim a) (sim b)).m c = S.ring.N a b c := by
  rw [tensorObj_m]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [sim]
    · intro b' _ hb
      simp [sim, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [sim, ha]
  · intro h; exact absurd (Finset.mem_univ _) h

end FusionCategory
