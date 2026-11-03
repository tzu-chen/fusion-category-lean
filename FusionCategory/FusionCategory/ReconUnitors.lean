/-
WP2 round 2, member m5, direction D4: the unitors and the triangle.

`𝟙 ⊗ X` and `X ⊗ 𝟙` have the multiplicity vector of `X` (`ReconUnit`), so the
unitors are the identity matrices through the *canonical block identification*
of the unit channel: `left_unit` forces the label of every index of the
`c`-block of `𝟙 ⊗ X` to be `(0, c)` and the unit channel is a singleton, so
`TensorIdx 𝟙 X c ≃ X.blk c`.  This file

* proves the index collapse (`leftIdxEquiv`, `rightIdxEquiv`) and their
  evaluation lemmas;
* defines `leftUnitor`, `rightUnitor` as matrices through it, with their
  inverses and the two round trips;
* proves naturality in the second (resp. first) variable;
* proves the triangle identity, consuming `TriangleCheck.triangle` for the
  middle-unit `F`-entry.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconUnit
import FusionCategory.ReconTensorApply
import FusionCategory.ReconAssoc
import FusionCategory.Triangle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## Generic lemmas: sigma collapse and subsingleton products -/

section Generic

/-- A sigma type over a base with a distinguished point whose other fibres are
empty collapses to the distinguished fibre. -/
def sigmaUniqueEquiv {ι : Type} [DecidableEq ι] {β : ι → Type} (i₀ : ι) (γ : Type)
    (e : β i₀ ≃ γ) (h : ∀ i, i ≠ i₀ → IsEmpty (β i)) : (Σ i, β i) ≃ γ where
  toFun s := if hs : s.1 = i₀ then e (hs ▸ s.2) else (h s.1 hs).false s.2 |>.elim
  invFun x := ⟨i₀, e.symm x⟩
  left_inv s := by
    obtain ⟨i, b⟩ := s
    by_cases hs : i = i₀
    · subst hs
      simp
    · simp only [dif_neg hs]
      exact ((h i hs).false b).elim
  right_inv x := by
    simp

/-- A product whose first two factors are nonempty subsingletons collapses to
the third. -/
noncomputable def prodSubsingletonEquiv (α : Type) (β : Type) (γ : Type)
    [Subsingleton α] [Nonempty α] [Subsingleton β] [Nonempty β] : α × β × γ ≃ γ where
  toFun t := t.2.2
  invFun x := ⟨Classical.arbitrary α, ⟨Classical.arbitrary β, x⟩⟩
  left_inv t := by
    obtain ⟨a, b, c⟩ := t
    simp only [Prod.mk.injEq, and_true]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  right_inv x := rfl

end Generic

namespace Units

variable (S : FusionSystem n k)

/-! ## The unit channel: label and fibre facts -/

/-- `N 0 c c = 1`, so the channel at `(0, c, c)` is a nonempty subsingleton. -/
theorem N_unit_self_pos (hn : 0 < n) (c : Fin n) : 0 < S.ring.N ⟨0, hn⟩ c c := by
  rw [S.ring.left_unit hn c c]
  simp

/-- `N c 0 c = 1`. -/
theorem N_self_unit_pos (hn : 0 < n) (c : Fin n) : 0 < S.ring.N c ⟨0, hn⟩ c := by
  rw [S.ring.right_unit hn c c]
  simp

theorem subsingleton_fin_of_le_one {m : ℕ} (h : m ≤ 1) : Subsingleton (Fin m) :=
  ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩

theorem subsingleton_fin_N_unit_self (hn : 0 < n) (c : Fin n) :
    Subsingleton (Fin (S.ring.N ⟨0, hn⟩ c c)) :=
  subsingleton_fin_of_le_one (by have := S.mult_free ⟨0, hn⟩ c c; omega)

theorem subsingleton_fin_N_self_unit (hn : 0 < n) (c : Fin n) :
    Subsingleton (Fin (S.ring.N c ⟨0, hn⟩ c)) :=
  subsingleton_fin_of_le_one (by have := S.mult_free c ⟨0, hn⟩ c; omega)

theorem nonempty_fin_N_unit_self (hn : 0 < n) (c : Fin n) :
    Nonempty (Fin (S.ring.N ⟨0, hn⟩ c c)) :=
  ⟨⟨0, N_unit_self_pos S hn c⟩⟩

/-- The unit block at the unit label is a nonempty subsingleton. -/
theorem subsingleton_unitObj_blk_self (hn : 0 < n) :
    Subsingleton ((unitObj (k := k) hn).blk ⟨0, hn⟩) := by
  have h : (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then 1 else 0) ≤ 1 := by split <;> omega
  exact subsingleton_fin_of_le_one h

theorem nonempty_unitObj_blk_self (hn : 0 < n) :
    Nonempty ((unitObj (k := k) hn).blk ⟨0, hn⟩) :=
  ⟨⟨0, by simp [unitObj]⟩⟩

/-- The unique point of the identity block. -/
def unitPt (hn : 0 < n) : (unitObj (k := k) hn).blk ⟨0, hn⟩ := ⟨0, by simp⟩

/-- The unique channel point of `N 0 c c`. -/
def chanPt (hn : 0 < n) (c : Fin n) : Fin (S.ring.N ⟨0, hn⟩ c c) :=
  ⟨0, N_unit_self_pos S hn c⟩

/-- The unique channel point of `N c 0 c`. -/
def chanPtRight (hn : 0 < n) (c : Fin n) : Fin (S.ring.N c ⟨0, hn⟩ c) :=
  ⟨0, N_self_unit_pos S hn c⟩

/-- Every index of the `c`-block of `𝟙 ⊗ X` carries the label `0` in its first
slot: the unit fibre is empty elsewhere. -/
theorem fst_eq_unit_of_mem (hn : 0 < n) {X : FusionMat n k} {c : Fin n}
    (r : (tensorObj S (unitObj hn) X).blk c) : r.1.1 = ⟨0, hn⟩ := by
  obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
  change p1 = ⟨0, hn⟩
  have h := u.isLt
  by_contra hne
  simp only [unitObj, if_neg hne] at h
  omega

/-- Every index of the `c`-block of `𝟙 ⊗ X` carries the label `c` in its second
slot: `left_unit` kills the other channels. -/
theorem snd_eq_of_mem (hn : 0 < n) {X : FusionMat n k} {c : Fin n}
    (r : (tensorObj S (unitObj hn) X).blk c) : r.1.2 = c := by
  obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
  change p2 = c
  have hp1 : p1 = ⟨0, hn⟩ := fst_eq_unit_of_mem S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
  have h : ν.val < S.ring.N ⟨0, hn⟩ p2 c := by
    have h0 := ν.isLt
    simpa [hp1] using h0
  by_contra hne
  rw [S.ring.left_unit hn p2 c, if_neg hne] at h
  omega

/-- The corresponding fact for `X ⊗ 𝟙`: the second label is `0`. -/
theorem snd_eq_unit_of_mem (hn : 0 < n) {X : FusionMat n k} {c : Fin n}
    (r : (tensorObj S X (unitObj hn)).blk c) : r.1.2 = ⟨0, hn⟩ := by
  obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
  change p2 = ⟨0, hn⟩
  have h := x.isLt
  by_contra hne
  simp only [unitObj, if_neg hne] at h
  omega

/-- The corresponding fact for `X ⊗ 𝟙`: the first label is `c`. -/
theorem fst_eq_of_mem_unit_right (hn : 0 < n) {X : FusionMat n k} {c : Fin n}
    (r : (tensorObj S X (unitObj hn)).blk c) : r.1.1 = c := by
  obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
  change p1 = c
  have h : ν.val < S.ring.N p1 ⟨0, hn⟩ c := by
    have hp2 : p2 = ⟨0, hn⟩ := snd_eq_unit_of_mem S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
    have h0 := ν.isLt
    simpa [hp2] using h0
  by_contra hne
  rw [S.ring.right_unit hn p1 c, if_neg hne] at h
  omega


/-! ## Graph matrices: the transport of the identity along an equivalence -/

section Graph

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The identity transported along an equivalence, as a matrix. -/
def graphMat (e : α ≃ β) : Matrix α β k := fun a b => if e a = b then 1 else 0

/-- The inverse of `graphMat`. -/
def graphMatInv (e : α ≃ β) : Matrix β α k := fun b a => if e a = b then 1 else 0

theorem graphMat_mul_graphMatInv (e : α ≃ β) :
    (graphMat (k := k) e : Matrix α β k) * (graphMatInv (k := k) e : Matrix β α k)
      = (1 : Matrix α α k) := by
  ext a a'
  simp only [graphMat, graphMatInv, Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e a)]
  · simp only [if_true, one_mul]
    by_cases h : a = a'
    · subst h; simp
    · have h2 : ¬ (e a' = e a) := fun hh => h (e.injective.eq_iff.mp hh).symm
      simp [h, h2]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem graphMatInv_mul_graphMat (e : α ≃ β) :
    (graphMatInv (k := k) e : Matrix β α k) * (graphMat (k := k) e : Matrix α β k)
      = (1 : Matrix β β k) := by
  ext b b'
  simp only [graphMat, graphMatInv, Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm b)]
  · rw [Equiv.apply_symm_apply]
    simp
  · intro a _ ha
    rw [if_neg, zero_mul]
    intro h
    exact ha (e.eq_symm_apply.mpr h)
  · intro h
    exact absurd (Finset.mem_univ _) h

end Graph

/-! ## The canonical block identifications for `𝟙 ⊗ X` and `X ⊗ 𝟙` -/

/-- The canonical identification of the `c`-block of `𝟙 ⊗ X` with the `c`-block
of `X`. -/
noncomputable def leftIdxEquiv (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    (tensorObj S (unitObj hn) X).blk c ≃ X.blk c where
  toFun r := if h : r.1.2 = c then h ▸ r.2.2.2 else (h (snd_eq_of_mem S hn r)).elim
  invFun x := ⟨(⟨0, hn⟩, c), chanPt S hn c, unitPt (k := k) hn, x⟩
  left_inv r := by
    obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
    have hp1 : p1 = ⟨0, hn⟩ := fst_eq_unit_of_mem S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
    have hp2 : p2 = c := snd_eq_of_mem S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
    obtain rfl : p1 = ⟨0, hn⟩ := hp1
    obtain rfl : p2 = c := hp2
    simp only [dif_pos rfl, dif_pos trivial]
    haveI := subsingleton_fin_N_unit_self S hn p2
    haveI := subsingleton_unitObj_blk_self (k := k) hn
    refine congrArg (fun t => (⟨(⟨0, hn⟩, p2), t⟩ : (tensorObj S (unitObj hn) X).blk p2)) ?_
    exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv x := by
    simp

/-- The canonical identification of the `c`-block of `X ⊗ 𝟙` with the `c`-block
of `X`. -/
noncomputable def rightIdxEquiv (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    (tensorObj S X (unitObj hn)).blk c ≃ X.blk c where
  toFun r := if h : r.1.1 = c then h ▸ r.2.2.1 else (h (fst_eq_of_mem_unit_right S hn r)).elim
  invFun x := ⟨(c, ⟨0, hn⟩), chanPtRight S hn c, x, unitPt (k := k) hn⟩
  left_inv r := by
    obtain ⟨⟨p1, p2⟩, ν, u, x⟩ := r
    have hp1 : p1 = c := fst_eq_of_mem_unit_right S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
    have hp2 : p2 = ⟨0, hn⟩ := snd_eq_unit_of_mem S hn ⟨(⟨p1, p2⟩), ν, u, x⟩
    obtain rfl : p1 = c := hp1
    obtain rfl : p2 = ⟨0, hn⟩ := hp2
    simp only [dif_pos rfl, dif_pos trivial]
    haveI := subsingleton_fin_N_self_unit S hn p1
    haveI := subsingleton_unitObj_blk_self (k := k) hn
    refine congrArg (fun t => (⟨(p1, ⟨0, hn⟩), t⟩ : (tensorObj S X (unitObj hn)).blk p1)) ?_
    exact Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl (Subsingleton.elim _ _))
  right_inv x := by
    simp

/-- Evaluation of the left block identification at a canonical index. -/
theorem leftIdxEquiv_apply (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N ⟨0, hn⟩ c c)) (u : (unitObj hn).blk ⟨0, hn⟩) (x : X.blk c) :
    leftIdxEquiv S hn X c ⟨(⟨0, hn⟩, c), ν, u, x⟩ = x := by
  show (if h : (c : Fin n) = c then h ▸ x else _) = x
  rw [dif_pos rfl]

/-- Evaluation of the right block identification at a canonical index. -/
theorem rightIdxEquiv_apply (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N c ⟨0, hn⟩ c)) (u : X.blk c) (x : (unitObj hn).blk ⟨0, hn⟩) :
    rightIdxEquiv S hn X c ⟨(c, ⟨0, hn⟩), ν, u, x⟩ = u := by
  show (if h : (c : Fin n) = c then h ▸ u else _) = u
  rw [dif_pos rfl]

/-! ## The unitors -/

/-- The unitor `λ_X : 𝟙 ⊗ X ⟶ X`, blockwise the identity through the canonical
identification. -/
noncomputable def leftUnitor (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S (unitObj hn) X ⟶ X :=
  fun c => graphMat (leftIdxEquiv S hn X c)

/-- Its inverse. -/
noncomputable def leftUnitorInv (hn : 0 < n) (X : FusionMat n k) :
    X ⟶ tensorObj S (unitObj hn) X :=
  fun c => graphMatInv (leftIdxEquiv S hn X c)

/-- The unitor `ρ_X : X ⊗ 𝟙 ⟶ X`. -/
noncomputable def rightUnitor (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S X (unitObj hn) ⟶ X :=
  fun c => graphMat (rightIdxEquiv S hn X c)

/-- Its inverse. -/
noncomputable def rightUnitorInv (hn : 0 < n) (X : FusionMat n k) :
    X ⟶ tensorObj S X (unitObj hn) :=
  fun c => graphMatInv (rightIdxEquiv S hn X c)

theorem leftUnitor_comp_inv (hn : 0 < n) (X : FusionMat n k) :
    leftUnitor S hn X ≫ leftUnitorInv S hn X = 𝟙 (tensorObj S (unitObj hn) X) := by
  funext c
  exact graphMat_mul_graphMatInv (leftIdxEquiv S hn X c)

theorem leftUnitorInv_comp (hn : 0 < n) (X : FusionMat n k) :
    leftUnitorInv S hn X ≫ leftUnitor S hn X = 𝟙 X := by
  funext c
  exact graphMatInv_mul_graphMat (leftIdxEquiv S hn X c)

theorem rightUnitor_comp_inv (hn : 0 < n) (X : FusionMat n k) :
    rightUnitor S hn X ≫ rightUnitorInv S hn X = 𝟙 (tensorObj S X (unitObj hn)) := by
  funext c
  exact graphMat_mul_graphMatInv (rightIdxEquiv S hn X c)

theorem rightUnitorInv_comp (hn : 0 < n) (X : FusionMat n k) :
    rightUnitorInv S hn X ≫ rightUnitor S hn X = 𝟙 X := by
  funext c
  exact graphMatInv_mul_graphMat (rightIdxEquiv S hn X c)

/-- The inverse identification, in canonical form. -/
@[simp] theorem leftIdxEquiv_symm_apply (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (x : X.blk c) :
    (leftIdxEquiv S hn X c).symm x
      = ⟨(⟨0, hn⟩, c), chanPt S hn c, unitPt (k := k) hn, x⟩ := rfl

/-- The inverse identification, in canonical form. -/
@[simp] theorem rightIdxEquiv_symm_apply (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (x : X.blk c) :
    (rightIdxEquiv S hn X c).symm x
      = ⟨(c, ⟨0, hn⟩), chanPtRight S hn c, x, unitPt (k := k) hn⟩ := rfl

/-- The tensor with the unit on the left acts on the block by the given
morphism itself, after the canonical identification.  The proof rewrites both
indices into the canonical form `e.symm (e r)` that the inverse of the block
equivalence provides, so no dependent transport on the index label is needed. -/
theorem tensorHom_unit_left_apply (hn : 0 < n) {X X' : FusionMat n k} (f : X ⟶ X')
    (c : Fin n) (r : (tensorObj S (unitObj hn) X).blk c)
    (y : (tensorObj S (unitObj hn) X').blk c) (x' : X'.blk c)
    (hy : leftIdxEquiv S hn X' c y = x') :
    tensorHom S (𝟙 (unitObj hn)) f c r y = f c (leftIdxEquiv S hn X c r) x' := by
  have hr : r = ⟨(⟨0, hn⟩, c), chanPt S hn c, unitPt (k := k) hn,
      leftIdxEquiv S hn X c r⟩ :=
    (Equiv.symm_apply_apply (leftIdxEquiv S hn X c) r).symm.trans
      (leftIdxEquiv_symm_apply S hn X c _)
  have hy' : y = ⟨(⟨0, hn⟩, c), chanPt S hn c, unitPt (k := k) hn, x'⟩ := by
    rw [← hy]
    exact (Equiv.symm_apply_apply (leftIdxEquiv S hn X' c) y).symm.trans
      (leftIdxEquiv_symm_apply S hn X' c _)
  rw [hr, hy', tensorHom_apply]
  simp only [Prod.fst, Prod.snd]
  rw [leftIdxEquiv_apply]
  simp only [if_true, one_mul]
  rw [show (𝟙 (unitObj hn)) ⟨0, hn⟩
        = (1 : Matrix ((unitObj hn).blk ⟨0, hn⟩) ((unitObj hn).blk ⟨0, hn⟩) k) from rfl]
  haveI := subsingleton_unitObj_blk_self (k := k) hn
  rw [Matrix.one_apply, if_pos (Subsingleton.elim _ _)]
  ring

theorem tensorHom_unit_right_apply (hn : 0 < n) {X X' : FusionMat n k} (f : X ⟶ X')
    (c : Fin n) (r : (tensorObj S X (unitObj hn)).blk c)
    (y : (tensorObj S X' (unitObj hn)).blk c) (x' : X'.blk c)
    (hy : rightIdxEquiv S hn X' c y = x') :
    tensorHom S f (𝟙 (unitObj hn)) c r y = f c (rightIdxEquiv S hn X c r) x' := by
  have hr : r = ⟨(c, ⟨0, hn⟩), chanPtRight S hn c, rightIdxEquiv S hn X c r,
      unitPt (k := k) hn⟩ :=
    (Equiv.symm_apply_apply (rightIdxEquiv S hn X c) r).symm.trans
      (rightIdxEquiv_symm_apply S hn X c _)
  have hy' : y = ⟨(c, ⟨0, hn⟩), chanPtRight S hn c, x', unitPt (k := k) hn⟩ := by
    rw [← hy]
    exact (Equiv.symm_apply_apply (rightIdxEquiv S hn X' c) y).symm.trans
      (rightIdxEquiv_symm_apply S hn X' c _)
  rw [hr, hy', tensorHom_apply]
  simp only [Prod.fst, Prod.snd]
  rw [rightIdxEquiv_apply]
  simp only [if_true, one_mul]
  rw [show (𝟙 (unitObj hn)) ⟨0, hn⟩
        = (1 : Matrix ((unitObj hn).blk ⟨0, hn⟩) ((unitObj hn).blk ⟨0, hn⟩) k) from rfl]
  haveI := subsingleton_unitObj_blk_self (k := k) hn
  rw [Matrix.one_apply, if_pos (Subsingleton.elim _ _)]
  ring

/-- Naturality of the left unitor. -/
theorem whiskerLeft_leftUnitor (hn : 0 < n) {X X' : FusionMat n k} (f : X ⟶ X') :
    whiskerLeft S (unitObj hn) f ≫ leftUnitor S hn X' = leftUnitor S hn X ≫ f := by
  funext c
  ext r x'
  have hL : (whiskerLeft S (unitObj hn) f ≫ leftUnitor S hn X') c r x'
      = tensorHom S (𝟙 (unitObj hn)) f c r ((leftIdxEquiv S hn X' c).symm x') := by
    show (tensorHom S (𝟙 (unitObj hn)) f c * leftUnitor S hn X' c) r x' = _
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((leftIdxEquiv S hn X' c).symm x')]
    · have hone : leftUnitor S hn X' c ((leftIdxEquiv S hn X' c).symm x') x' = 1 := by
        show (if leftIdxEquiv S hn X' c ((leftIdxEquiv S hn X' c).symm x') = x'
          then (1 : k) else 0) = 1
        rw [Equiv.apply_symm_apply, if_pos rfl]
      rw [hone, mul_one]
    · intro y _ hy
      have hzero : leftUnitor S hn X' c y x' = 0 := by
        show (if leftIdxEquiv S hn X' c y = x' then (1 : k) else 0) = 0
        rw [if_neg (fun h => hy (by rw [← h, Equiv.symm_apply_apply]))]
      rw [hzero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (leftUnitor S hn X ≫ f) c r x'
      = f c (leftIdxEquiv S hn X c r) x' := by
    show (leftUnitor S hn X c * f c) r x' = _
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (leftIdxEquiv S hn X c r)]
    · have hone : leftUnitor S hn X c r (leftIdxEquiv S hn X c r) = 1 := by
        show (if leftIdxEquiv S hn X c r = leftIdxEquiv S hn X c r then (1 : k) else 0) = 1
        rw [if_pos rfl]
      rw [hone, one_mul]
    · intro x _ hx
      have hzero : leftUnitor S hn X c r x = 0 := by
        show (if leftIdxEquiv S hn X c r = x then (1 : k) else 0) = 0
        rw [if_neg (fun h => hx h.symm)]
      rw [hzero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR]
  exact tensorHom_unit_left_apply S hn f c r _ x' (Equiv.apply_symm_apply _ _)

/-- Naturality of the right unitor. -/
theorem whiskerRight_rightUnitor (hn : 0 < n) {X X' : FusionMat n k} (f : X ⟶ X') :
    whiskerRight S f (unitObj hn) ≫ rightUnitor S hn X' = rightUnitor S hn X ≫ f := by
  funext c
  ext r x'
  have hL : (whiskerRight S f (unitObj hn) ≫ rightUnitor S hn X') c r x'
      = tensorHom S f (𝟙 (unitObj hn)) c r ((rightIdxEquiv S hn X' c).symm x') := by
    show (tensorHom S f (𝟙 (unitObj hn)) c * rightUnitor S hn X' c) r x' = _
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((rightIdxEquiv S hn X' c).symm x')]
    · have hone : rightUnitor S hn X' c ((rightIdxEquiv S hn X' c).symm x') x' = 1 := by
        show (if rightIdxEquiv S hn X' c ((rightIdxEquiv S hn X' c).symm x') = x'
          then (1 : k) else 0) = 1
        rw [Equiv.apply_symm_apply, if_pos rfl]
      rw [hone, mul_one]
    · intro y _ hy
      have hzero : rightUnitor S hn X' c y x' = 0 := by
        show (if rightIdxEquiv S hn X' c y = x' then (1 : k) else 0) = 0
        rw [if_neg (fun h => hy (by rw [← h, Equiv.symm_apply_apply]))]
      rw [hzero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (rightUnitor S hn X ≫ f) c r x'
      = f c (rightIdxEquiv S hn X c r) x' := by
    show (rightUnitor S hn X c * f c) r x' = _
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (rightIdxEquiv S hn X c r)]
    · have hone : rightUnitor S hn X c r (rightIdxEquiv S hn X c r) = 1 := by
        show (if rightIdxEquiv S hn X c r = rightIdxEquiv S hn X c r then (1 : k) else 0) = 1
        rw [if_pos rfl]
      rw [hone, one_mul]
    · intro x _ hx
      have hzero : rightUnitor S hn X c r x = 0 := by
        show (if rightIdxEquiv S hn X c r = x then (1 : k) else 0) = 0
        rw [if_neg (fun h => hx h.symm)]
      rw [hzero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR]
  exact tensorHom_unit_right_apply S hn f c r _ x' (Equiv.apply_symm_apply _ _)

/-! ## The triangle identity

The triangle `α_{X,𝟙,Y} ≫ (X ◁ λ_Y) = ρ_X ▷ Y` is equivalent, since `X ◁ λ_Y`
is invertible, to the *pointwise* identity
`α_{X,𝟙,Y} = (ρ_X ⊗ 1) ≫ (1 ⊗ λ_Y⁻¹)`.
In that form no sum has to be evaluated: both sides are a single value or zero
at each index pair, and the surviving value is `F e 0 c d e c = 1` by
`TriangleCheck.triangle` (the middle-unit entry). -/

/-- The right unitor at a canonical index. -/
theorem rightUnitor_canon (hn : 0 < n) (X : FusionMat n k) (e : Fin n)
    (μ : Fin (S.ring.N e ⟨0, hn⟩ e)) (x : X.blk e) (u : (unitObj hn).blk ⟨0, hn⟩)
    (x' : X.blk e) :
    rightUnitor S hn X e ⟨(e, ⟨0, hn⟩), μ, x, u⟩ x' = if x = x' then 1 else 0 := by
  show (if rightIdxEquiv S hn X e ⟨(e, ⟨0, hn⟩), μ, x, u⟩ = x' then (1 : k) else 0) = _
  rw [rightIdxEquiv_apply]

/-- The inverse left unitor at a canonical index. -/
theorem leftUnitorInv_canon (hn : 0 < n) (Y : FusionMat n k) (c : Fin n)
    (y : Y.blk c) (μ : Fin (S.ring.N ⟨0, hn⟩ c c)) (u : (unitObj hn).blk ⟨0, hn⟩)
    (y' : Y.blk c) :
    leftUnitorInv S hn Y c y ⟨(⟨0, hn⟩, c), μ, u, y'⟩ = if y' = y then 1 else 0 := by
  show (if leftIdxEquiv S hn Y c ⟨(⟨0, hn⟩, c), μ, u, y'⟩ = y then (1 : k) else 0) = _
  rw [leftIdxEquiv_apply]

/-- The associator at the middle unit, on canonical indices: the entry is the
middle-unit `F`-symbol times the diagonal conditions on the multiplicity
indices. -/
theorem assocEntry_mid_canon (hn : 0 < n) (X Y : FusionMat n k) (d : Fin n) (e c : Fin n)
    (ν : Fin (S.ring.N e c d)) (μ : Fin (S.ring.N e ⟨0, hn⟩ e)) (x : X.blk e)
    (u : (unitObj hn).blk ⟨0, hn⟩) (y : Y.blk c)
    (ν_s : Fin (S.ring.N e c d)) (x_s : X.blk e) (μ_s : Fin (S.ring.N ⟨0, hn⟩ c c))
    (u_s : (unitObj hn).blk ⟨0, hn⟩) (y_s : Y.blk c) :
    assocEntry S X (unitObj hn) Y d
        ⟨(e, c), ν, ⟨(e, ⟨0, hn⟩), μ, x, u⟩, y⟩
        ⟨(e, c), ν_s, x_s, ⟨(⟨0, hn⟩, c), μ_s, u_s, y_s⟩⟩
      = if x = x_s then (if y = y_s then S.F e ⟨0, hn⟩ c d e c else 0) else 0 := by
  haveI := subsingleton_unitObj_blk_self (k := k) hn
  simp only [assocEntry]
  rw [dif_pos trivial, dif_pos trivial, dif_pos trivial]
  by_cases hx : x = x_s
  · by_cases hy : y = y_s
    · rw [dif_pos hx, dif_pos (Subsingleton.elim u u_s), dif_pos hy, if_pos hx, if_pos hy]
    · rw [dif_pos hx, dif_pos (Subsingleton.elim u u_s), dif_neg hy, if_pos hx, if_neg hy]
  · rw [dif_neg hx, if_neg hx]

/-- Vanishing of the middle-unit associator entry when the first labels differ. -/
theorem assocEntry_mid_ne_fst (hn : 0 < n) (X Y : FusionMat n k) (d : Fin n)
    (e c a_s f_s : Fin n) (hea : e ≠ a_s)
    (ν : Fin (S.ring.N e c d)) (μ : Fin (S.ring.N e ⟨0, hn⟩ e)) (x : X.blk e)
    (u : (unitObj hn).blk ⟨0, hn⟩) (y : Y.blk c)
    (ν_s : Fin (S.ring.N a_s f_s d)) (x_s : X.blk a_s) (μ_s : Fin (S.ring.N ⟨0, hn⟩ f_s f_s))
    (u_s : (unitObj hn).blk ⟨0, hn⟩) (y_s : Y.blk f_s) :
    assocEntry S X (unitObj hn) Y d
        ⟨(e, c), ν, ⟨(e, ⟨0, hn⟩), μ, x, u⟩, y⟩
        ⟨(a_s, f_s), ν_s, x_s, ⟨(⟨0, hn⟩, f_s), μ_s, u_s, y_s⟩⟩ = 0 := by
  simp only [assocEntry]
  rw [dif_neg hea]

/-- Vanishing of the middle-unit associator entry when the second labels differ
(the first already agree). -/
theorem assocEntry_mid_ne_snd (hn : 0 < n) (X Y : FusionMat n k) (d : Fin n)
    (e c f_s : Fin n) (hcf : c ≠ f_s)
    (ν : Fin (S.ring.N e c d)) (μ : Fin (S.ring.N e ⟨0, hn⟩ e)) (x : X.blk e)
    (u : (unitObj hn).blk ⟨0, hn⟩) (y : Y.blk c)
    (ν_s : Fin (S.ring.N e f_s d)) (x_s : X.blk e) (μ_s : Fin (S.ring.N ⟨0, hn⟩ f_s f_s))
    (u_s : (unitObj hn).blk ⟨0, hn⟩) (y_s : Y.blk f_s) :
    assocEntry S X (unitObj hn) Y d
        ⟨(e, c), ν, ⟨(e, ⟨0, hn⟩), μ, x, u⟩, y⟩
        ⟨(e, f_s), ν_s, x_s, ⟨(⟨0, hn⟩, f_s), μ_s, u_s, y_s⟩⟩ = 0 := by
  haveI := subsingleton_unitObj_blk_self (k := k) hn
  simp only [assocEntry]
  rw [dif_pos trivial, dif_pos trivial]
  exact dif_neg hcf

theorem assoc_eq_tensorHom_unit_mid (hn : 0 < n) (X Y : FusionMat n k) :
    associatorHom S X (unitObj hn) Y
      = tensorHom S (rightUnitor S hn X) (leftUnitorInv S hn Y) := by
  funext d
  ext r s
  change assocEntry S X (unitObj hn) Y d r s
    = tensorHom S (rightUnitor S hn X) (leftUnitorInv S hn Y) d r s
  obtain ⟨⟨e, c⟩, ν, ⟨⟨a, b⟩, μ, x, u⟩, y⟩ := r
  obtain ⟨⟨a_s, f_s⟩, ν_s, x_s, ⟨⟨b_s, c_s⟩, μ_s, u_s, y_s⟩⟩ := s
  have ha : a = e := fst_eq_of_mem_unit_right S hn ⟨(⟨a, b⟩), μ, x, u⟩
  have hb : b = ⟨0, hn⟩ := snd_eq_unit_of_mem S hn ⟨(⟨a, b⟩), μ, x, u⟩
  have hbs : b_s = ⟨0, hn⟩ := fst_eq_unit_of_mem S hn ⟨(⟨b_s, c_s⟩), μ_s, u_s, y_s⟩
  have hcs : c_s = f_s := snd_eq_of_mem S hn ⟨(⟨b_s, c_s⟩), μ_s, u_s, y_s⟩
  subst ha
  subst hb
  subst hbs
  subst hcs
  have hacd : 0 < S.ring.N a c d := by
    have h := ν.isLt
    simp only [Prod.fst, Prod.snd] at h
    omega
  by_cases hlab : (a, c) = (a_s, c_s)
  · obtain ⟨h1, h2⟩ : a = a_s ∧ c = c_s := by
      simpa only [Prod.mk.injEq] using hlab
    subst h1
    subst h2
    simp only [Prod.fst, Prod.snd]
    rw [assocEntry_mid_canon S hn X Y d a c ν μ x u y ν_s x_s μ_s u_s y_s]
    rw [tensorHom_apply, rightUnitor_canon, leftUnitorInv_canon]
    rw [TriangleCheck.triangle S hn a c d hacd]
    haveI hss : Subsingleton (Fin (S.ring.N (a, c).1 (a, c).2 d)) :=
      channel_subsingleton S a c d
    rw [if_pos (hss.elim ν ν_s), one_mul]
    by_cases hx : x = x_s
    · rw [if_pos hx, if_pos hx, one_mul]
      by_cases hy : y = y_s
      · rw [if_pos hy, if_pos hy.symm]
      · rw [if_neg hy, if_neg (fun h => hy h.symm)]
    · rw [if_neg hx, if_neg hx, zero_mul]
  · have hL : assocEntry S X (unitObj hn) Y d
        ⟨(a, c), ν, ⟨(a, ⟨0, hn⟩), μ, x, u⟩, y⟩
        ⟨(a_s, c_s), ν_s, x_s, ⟨(⟨0, hn⟩, c_s), μ_s, u_s, y_s⟩⟩ = 0 := by
      by_cases he : a = a_s
      · have hcf : c ≠ c_s := fun hc => hlab (by rw [he, hc])
        subst he
        exact assocEntry_mid_ne_snd S hn X Y d a c c_s hcf ν μ x u y ν_s x_s μ_s u_s y_s
      · exact assocEntry_mid_ne_fst S hn X Y d a c a_s c_s he ν μ x u y ν_s x_s μ_s u_s y_s
    rw [hL, tensorHom_apply_ne S (rightUnitor S hn X) (leftUnitorInv S hn Y) d hlab]

/-- The triangle identity of the monoidal structure on the reconstruction. -/
theorem triangle (hn : 0 < n) (X Y : FusionMat n k) :
    associatorHom S X (unitObj hn) Y ≫ whiskerLeft S X (leftUnitor S hn Y)
      = whiskerRight S (rightUnitor S hn X) Y := by
  rw [assoc_eq_tensorHom_unit_mid S hn X Y]
  show tensorHom S (rightUnitor S hn X) (leftUnitorInv S hn Y) ≫
      tensorHom S (𝟙 X) (leftUnitor S hn Y) = tensorHom S (rightUnitor S hn X) (𝟙 Y)
  rw [← tensorHom_comp, Category.comp_id, leftUnitorInv_comp]

/-- The left unitor as an isomorphism. -/
noncomputable def leftUnitorIso (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S (unitObj hn) X ≅ X where
  hom := leftUnitor S hn X
  inv := leftUnitorInv S hn X
  hom_inv_id := leftUnitor_comp_inv S hn X
  inv_hom_id := leftUnitorInv_comp S hn X

/-- The right unitor as an isomorphism. -/
noncomputable def rightUnitorIso (hn : 0 < n) (X : FusionMat n k) :
    tensorObj S X (unitObj hn) ≅ X where
  hom := rightUnitor S hn X
  inv := rightUnitorInv S hn X
  hom_inv_id := rightUnitor_comp_inv S hn X
  inv_hom_id := rightUnitorInv_comp S hn X

end Units

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.sigmaUniqueEquiv
#print axioms FusionCategory.prodSubsingletonEquiv
#print axioms FusionCategory.Units.fst_eq_unit_of_mem
#print axioms FusionCategory.Units.snd_eq_of_mem
#print axioms FusionCategory.Units.fst_eq_of_mem_unit_right
#print axioms FusionCategory.Units.snd_eq_unit_of_mem
#print axioms FusionCategory.Units.leftIdxEquiv
#print axioms FusionCategory.Units.rightIdxEquiv
#print axioms FusionCategory.Units.leftIdxEquiv_apply
#print axioms FusionCategory.Units.rightIdxEquiv_apply
#print axioms FusionCategory.Units.graphMat_mul_graphMatInv
#print axioms FusionCategory.Units.graphMatInv_mul_graphMat
#print axioms FusionCategory.Units.leftUnitor
#print axioms FusionCategory.Units.rightUnitor
#print axioms FusionCategory.Units.leftUnitorInv
#print axioms FusionCategory.Units.rightUnitorInv
#print axioms FusionCategory.Units.leftUnitor_comp_inv
#print axioms FusionCategory.Units.leftUnitorInv_comp
#print axioms FusionCategory.Units.rightUnitor_comp_inv
#print axioms FusionCategory.Units.rightUnitorInv_comp
#print axioms FusionCategory.Units.tensorHom_unit_left_apply
#print axioms FusionCategory.Units.tensorHom_unit_right_apply
#print axioms FusionCategory.Units.whiskerLeft_leftUnitor
#print axioms FusionCategory.Units.whiskerRight_rightUnitor
#print axioms FusionCategory.Units.rightUnitor_canon
#print axioms FusionCategory.Units.leftUnitorInv_canon
#print axioms FusionCategory.Units.assocEntry_mid_canon
#print axioms FusionCategory.Units.assocEntry_mid_ne_fst
#print axioms FusionCategory.Units.assocEntry_mid_ne_snd
#print axioms FusionCategory.Units.assoc_eq_tensorHom_unit_mid
#print axioms FusionCategory.Units.triangle
#print axioms FusionCategory.Units.leftUnitorIso
#print axioms FusionCategory.Units.rightUnitorIso
