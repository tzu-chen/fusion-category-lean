/-
WP2 round 3, member m2, direction D1 (the simple-object layer), part (d)-(e).

On the canonical scaffold `FusionCategory.FusionMat`:

* `biprodObjOf F` — the biproduct of a finite family: the block at label `i` is the
  sigma type `Σ j, (F j).blk i`, so that
  `Hom(W, P) = Π j, Hom(W, F j)` and `Hom(P, W) = Π j, Hom(F j, W)` on the nose;
* `biconeOf`, `biconeOf_total` — the bicone and the `∑ j, π j ≫ ι j = 𝟙` identity, from
  which Mathlib's `hasBiproduct_of_total` gives the biproduct;
* `hasFiniteBiproducts` — `HasFiniteBiproducts (FusionMat n k)`, hence `HasZeroObject`
  and `HasBinaryBiproducts` for free;
* `simProj`/`simIncl` indexed by `Σ i, X.blk i`, the matrix-unit identities
  `∑ p, simProj p ≫ simIncl p = 𝟙 X` and `simProj p ≫ simIncl q = δ`, and
* `decomposition` — `X ≅ ⨁ (fun p : Σ i, X.blk i => sim p.1)`, the second hypothesis of
  `isFusionCategoryOf`, built from those two identities through the abstract biproduct API
  (`biproduct.total`, `biproduct.ι_π_ne`).

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconSimpleSim

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe u

namespace FusionCategory

open CategoryTheory MonoidalCategory CategoryTheory.Limits

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat

/-! ## The biproduct of a finite family -/

section FiniteFamily

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The biproduct object of a finite family `F`: the block at label `i` is the sigma type of
the blocks of the family, so that a morphism out of it is a tuple of morphisms out of the
summands and a morphism into it is a tuple of morphisms into the summands.  An `abbrev`, so
that instance search sees the sigma block type (the `Decidable` instances of the `if`s below
are found only at reducible transparency). -/
abbrev biprodObjOf (F : J → FusionMat n k) : FusionMat n k where
  m i := ∑ j : J, (F j).m i
  blk i := Σ j : J, (F j).blk i
  fintype_blk _ := inferInstance
  decidableEq_blk _ := inferInstance
  card_blk i := by
    simp only [Fintype.card_sigma, card_blk_eq]

/-- The projection onto the `j`-th summand. -/
def biprodπ (F : J → FusionMat n k) (j : J) : biprodObjOf F ⟶ F j :=
  fun i => Matrix.of (fun p s => if p = (⟨j, s⟩ : Σ j' : J, (F j').blk i) then (1 : k) else 0)

/-- The inclusion of the `j`-th summand. -/
def biprodι (F : J → FusionMat n k) (j : J) : F j ⟶ biprodObjOf F :=
  fun i => Matrix.of (fun s p => if p = (⟨j, s⟩ : Σ j' : J, (F j').blk i) then (1 : k) else 0)

theorem biprodι_π_self (F : J → FusionMat n k) (j : J) :
    biprodι F j ≫ biprodπ F j = 𝟙 (F j) := by
  funext i
  ext s s'
  simp only [biprodι, biprodπ, comp_apply_blk, id_apply_blk, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨j, s⟩ : Σ j' : J, (F j').blk i)]
  · rw [if_pos rfl, one_mul]
    have hiff : ((⟨j, s⟩ : Σ j' : J, (F j').blk i) = ⟨j, s'⟩) ↔ s = s' :=
      ⟨fun hh => eq_of_heq (Sigma.mk.injEq _ _ _ _ |>.mp hh).2, fun hh => by rw [hh]⟩
    by_cases hs : s = s'
    · rw [if_pos hs, if_pos (hiff.mpr hs)]
    · rw [if_neg hs, if_neg (fun hh => hs (hiff.mp hh))]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem biprodι_π_ne (F : J → FusionMat n k) {j j' : J} (h : j ≠ j') :
    biprodι F j ≫ biprodπ F j' = 0 := by
  funext i
  ext s s'
  simp only [biprodι, biprodπ, comp_apply_blk, zero_apply_blk, Matrix.mul_apply,
    Matrix.of_apply]
  rw [Finset.sum_eq_zero]
  · rfl
  · intro b _
    by_cases hb : b = (⟨j, s⟩ : Σ j' : J, (F j').blk i)
    · rw [if_pos hb]
      rw [if_neg (fun hq => h (congrArg Sigma.fst (hb.symm.trans hq))), mul_zero]
    · rw [if_neg hb, zero_mul]

/-- The bicone of the finite family: the point with the sigma blocks, with the tuple
projections and inclusions. -/
def biconeOf (F : J → FusionMat n k) : Bicone F where
  pt := biprodObjOf F
  π := biprodπ F
  ι := biprodι F
  ι_π j j' := by
    by_cases h : j = j'
    · subst h
      rw [dif_pos rfl, biprodι_π_self]
      rfl
    · rw [dif_neg h]
      exact biprodι_π_ne F h

theorem sigma_fst_eq {F : J → FusionMat n k} {i : Fin n} {j : J} {s : (F j).blk i}
    {p : Σ j' : J, (F j').blk i} (h : p = ⟨j, s⟩) : p.1 = j := by
  cases h; rfl

theorem sigma_snd_heq {F : J → FusionMat n k} {i : Fin n} {j : J} {s : (F j).blk i}
    {p : Σ j' : J, (F j').blk i} (h : p = ⟨j, s⟩) : HEq p.2 s := by
  cases h; rfl

/-- **The total identity**: `∑ j, π j ≫ ι j = 𝟙` on the bicone — this is what makes it a
bilimit in a preadditive category. -/
theorem add_apply_blk {X Y : FusionMat n k} (f g : X ⟶ Y) (i : Fin n) :
    (f + g) i = f i + g i := rfl

theorem sum_apply_blk {X Y : FusionMat n k} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y))
    (i : Fin n) : (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply_blk, ih]

/-- Pointwise application commutes with finite sums in any `AddCommMonoid`-valued function
space. -/
theorem finset_sum_apply {ι A M : Type*} [AddCommMonoid M] (s : Finset ι) (f : ι → A → M)
    (a : A) : (∑ j ∈ s, f j) a = ∑ j ∈ s, f j a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a' s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact congrArg (fun g : M => f a' a + g) ih

theorem biconeOf_total (F : J → FusionMat n k) :
    ∑ j : J, biprodπ F j ≫ biprodι F j = 𝟙 (biprodObjOf F) := by
  funext i
  rw [show (∑ j : J, biprodπ F j ≫ biprodι F j) i
      = ∑ j : J, (biprodπ F j ≫ biprodι F j) i
      from sum_apply_blk Finset.univ (fun j => biprodπ F j ≫ biprodι F j) i]
  simp only [comp_apply_blk, id_apply_blk]
  ext p q
  rw [show (∑ j : J, biprodπ F j i * biprodι F j i) p
      = ∑ j : J, (biprodπ F j i * biprodι F j i) p
      from finset_sum_apply Finset.univ (fun j => biprodπ F j i * biprodι F j i) p]
  rw [show (∑ j : J, (biprodπ F j i * biprodι F j i) p) q
      = ∑ j : J, (biprodπ F j i * biprodι F j i) p q
      from finset_sum_apply Finset.univ (fun j => (biprodπ F j i * biprodι F j i) p) q]
  simp only [biprodπ, biprodι, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · rw [if_pos (show p = (⟨p.1, p.2⟩ : Σ j : J, (F j).blk i) from (Sigma.eta p).symm)]
      rw [one_mul]
      rw [show (⟨p.1, p.2⟩ : Σ j : J, (F j).blk i) = p from Sigma.eta p]
      simp [eq_comm]
    · intro s _ hs
      rw [if_neg, zero_mul]
      intro hpq
      exact hs (eq_of_heq (sigma_snd_heq hpq)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    rw [Finset.sum_eq_zero]
    intro s _
    rw [if_neg, zero_mul]
    intro hpq
    exact hj (show p.1 = j from by rw [hpq]).symm
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Every finite family has a biproduct.** -/
theorem hasBiproductOf (F : J → FusionMat n k) : HasBiproduct F :=
  hasBiproduct_of_total (biconeOf F) (biconeOf_total F)

end FiniteFamily

/-- **`HasFiniteBiproducts` for the canonical scaffold.** -/
instance hasFiniteBiproducts : HasFiniteBiproducts (FusionMat n k) :=
  ⟨fun _ => ⟨fun F => hasBiproductOf F⟩⟩

/-- The zero object of the reconstruction: the empty biproduct. -/
instance hasZeroObject : HasZeroObject (FusionMat n k) :=
  hasZeroObject_of_hasFiniteBiproducts _

end FusionMat

namespace FusionMat

/-! ## The decomposition of an object into simples -/

section Decomposition

variable (X : FusionMat n k)

/-- The `b`-th copy of the simple `sim i`, as a morphism *out of* `X`. -/
def rowExtract (p : Σ i : Fin n, X.blk i) : X ⟶ sim (k := k) p.1 :=
  simProj X p.1 p.2

/-- The `b`-th copy of the simple `sim i`, as a morphism *into* `X`. -/
def colInsert (p : Σ i : Fin n, X.blk i) : sim (k := k) p.1 ⟶ X :=
  simIncl X p.1 p.2

/-- The matrix units are orthogonal: two of them in the same block. -/
theorem simIncl_comp_simProj_same (i : Fin n) (b b' : X.blk i) :
    simIncl X i b ≫ simProj X i b' = if b = b' then 𝟙 (sim (k := k) i) else 0 := by
  haveI hS : Subsingleton ((sim (k := k) i).blk i) := subsingleton_sim_blk_self i
  by_cases h : b = b'
  · subst h
    rw [if_pos rfl]
    funext c
    by_cases hc : c = i
    · cases hc
      simp only [comp_apply_blk, id_apply_blk, simIncl, simProj, blockMk_self]
      ext u u'
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      rw [Finset.sum_eq_single b]
      · rw [if_pos rfl, one_mul, if_pos (Subsingleton.elim u u')]
      · intro s _ hs
        rw [if_neg hs, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · haveI : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
      simp only [comp_apply_blk, id_apply_blk, simIncl, simProj, blockMk_of_ne hc,
        Matrix.zero_mul]
      exact Subsingleton.elim _ _
  · rw [if_neg h]
    funext c
    by_cases hc : c = i
    · cases hc
      simp only [comp_apply_blk, zero_apply_blk, simIncl, simProj, blockMk_self]
      ext u u'
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply, Pi.zero_apply]
      rw [Finset.sum_eq_single b]
      · rw [if_pos rfl, one_mul, if_neg h]
        rfl
      · intro s _ hs
        rw [if_neg hs, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · haveI : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
      simp only [comp_apply_blk, zero_apply_blk, simIncl, simProj, blockMk_of_ne hc,
        Matrix.zero_mul]

/-- The matrix units are orthogonal: two of them in different blocks. -/
theorem simIncl_comp_simProj_ne {i i' : Fin n} (h : i ≠ i') (b : X.blk i) (b' : X.blk i') :
    simIncl X i b ≫ simProj X i' b' = 0 := by
  funext c
  by_cases hc : c = i
  · subst hc
    have hc' : c ≠ i' := fun hh => h hh
    rw [comp_apply_blk, simIncl, blockMk_self, simProj, blockMk_of_ne hc', Matrix.mul_zero,
      zero_apply_blk]
  · rw [comp_apply_blk, simIncl, blockMk_of_ne hc, Matrix.zero_mul, zero_apply_blk]

/-- `colInsert p ≫ rowExtract p = 𝟙`. -/
theorem colInsert_comp_rowExtract_self (p : Σ i : Fin n, X.blk i) :
    colInsert X p ≫ rowExtract X p = 𝟙 (sim (k := k) p.1) := by
  obtain ⟨i, b⟩ := p
  have h := simIncl_comp_simProj_same X i b b
  rw [if_pos rfl] at h
  exact h

/-- `colInsert q ≫ rowExtract p = 0` for `p ≠ q`. -/
theorem colInsert_comp_rowExtract_of_ne {p q : Σ i : Fin n, X.blk i} (h : q ≠ p) :
    colInsert X q ≫ rowExtract X p = 0 := by
  obtain ⟨i, b⟩ := p
  obtain ⟨i', b'⟩ := q
  by_cases hlab : i' = i
  · cases hlab
    have hbb : b' ≠ b := fun hh => h (by cases hh; rfl)
    have h2 := simIncl_comp_simProj_same X i b' b
    rw [if_neg hbb] at h2
    exact h2
  · exact simIncl_comp_simProj_ne X hlab b' b

/-- Applying a finite sum of matrices at two indices. -/
theorem matrix_sum_apply2 {ι A B : Type} (s : Finset ι) (f : ι → Matrix A B k) (a : A)
    (b : B) : (∑ j ∈ s, f j) a b = ∑ j ∈ s, f j a b := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a' s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show f a' a b + (∑ x ∈ s, f x) a b = f a' a b + ∑ x ∈ s, f x a b
      rw [ih]

/-- **Resolution of the identity**: `X` is the sum of its matrix units, one per block point. -/
theorem sum_rowExtract_comp_colInsert :
    ∑ p : (Σ i : Fin n, X.blk i), rowExtract X p ≫ colInsert X p = 𝟙 X := by
  funext c
  rw [show (∑ p : (Σ i : Fin n, X.blk i), rowExtract X p ≫ colInsert X p) c
      = ∑ p : (Σ i : Fin n, X.blk i), (rowExtract X p ≫ colInsert X p) c
      from sum_apply_blk Finset.univ _ c]
  rw [Fintype.sum_sigma]
  simp only [id_apply_blk]
  rw [Finset.sum_eq_single c]
  · ext s s'
    rw [matrix_sum_apply2 Finset.univ _ s s']
    rw [Matrix.one_apply]
    rw [Finset.sum_eq_single s]
    · simp only [comp_apply_blk, rowExtract, colInsert, simProj, simIncl, blockMk_self,
        Matrix.mul_apply, Matrix.of_apply]
      simp [card_sim_blk_self c, eq_comm]
    · intro b _ hb
      simp only [comp_apply_blk, rowExtract, colInsert, simProj, simIncl, blockMk_self,
        Matrix.mul_apply, Matrix.of_apply]
      simp [Ne.symm hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · intro i₀ _ hi
    rw [Finset.sum_eq_zero]
    intro b _
    rw [comp_apply_blk, rowExtract, simProj, blockMk_of_ne (Ne.symm hi), Matrix.zero_mul]
  · intro hh; exact absurd (Finset.mem_univ _) hh

end Decomposition

end FusionMat

namespace FusionMat

/-- **The second `isFusionCategoryOf` hypothesis**: every object of the reconstruction is a
finite biproduct of simples, `X ≅ ⨁_p sim p.1` over the block points `p : Σ i, X.blk i`. -/
theorem decomposition (X : FusionMat n k) :
    ∃ (m : ℕ) (f : Fin m → FusionMat n k), (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f) := by
  classical
  set ι := Σ i : Fin n, (X).blk i with hι
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  refine ⟨Fintype.card ι, fun j => sim (k := k) (e j).1, fun j => simple_sim _, ?_⟩
  have hsum : ∑ j : Fin (Fintype.card ι), (rowExtract X (e j) ≫ colInsert X (e j))
      = 𝟙 X := by
    rw [show (∑ j : Fin (Fintype.card ι), (rowExtract X (e j) ≫ colInsert X (e j)))
        = ∑ p : ι, (rowExtract X p ≫ colInsert X p) from
      Fintype.sum_equiv e _ _ (fun j => rfl)]
    exact sum_rowExtract_comp_colInsert X
  refine ⟨{ hom := biproduct.lift (fun j => rowExtract X (e j))
            inv := biproduct.desc (fun j => colInsert X (e j))
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [biproduct.lift_desc]
    exact hsum
  · apply biproduct.hom_ext'
    intro q
    rw [← Category.assoc, biproduct.ι_desc, Category.comp_id, biproduct.lift_eq]
    rw [CategoryTheory.Preadditive.comp_sum]
    rw [Finset.sum_eq_single q]
    · rw [← Category.assoc, colInsert_comp_rowExtract_self, Category.id_comp]
    · intro j _ hj
      rw [← Category.assoc, colInsert_comp_rowExtract_of_ne X (p := e j) (q := e q)
        (fun hh => hj (e.injective hh.symm)), zero_comp]
    · intro hh; exact absurd (Finset.mem_univ _) hh

/-- **The two `isFusionCategoryOf` hypotheses, as one conjunction.** -/
theorem simples_fin_and_decomposition :
    (∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
        ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i)) ∧
      (∀ X : FusionMat n k, ∃ (m : ℕ) (f : Fin m → FusionMat n k),
        (∀ i, Simple (f i)) ∧ Nonempty (X ≅ ⨁ f)) :=
  ⟨simples_fin, decomposition⟩

/-- **The `IsFusionCategory` assembly, with the simple-object layer discharged.**

`FusionCategory.isFusionCategoryOf` (ReconFusionProps) asks for four instance arguments and
three properties.  The two `Prop` fields that the simple-object layer owns — finitely many
simples and the decomposition of every object — are now THEOREMS of the canonical scaffold
(`FusionMat.simples_fin`, `FusionMat.decomposition`), and `HasFiniteBiproducts` is the instance
`FusionMat.hasFiniteBiproducts`.  So the predicate reduces to exactly:

* a `MonoidalCategory` instance (D2 naturality + D3 pentagon + D4 unitors),
* a `RigidCategory` instance (D4 snakes),
* `End 𝟙 ≃+* k` (`end_unit`), which `endUnitEquiv` supplies once `𝟙 = unitObj hn`. -/
theorem isFusionCategory_of_instances
    [MonoidalCategory (FusionMat n k)] [MonoidalPreadditive (FusionMat n k)]
    [RigidCategory (FusionMat n k)]
    (end_unit : Nonempty (End (𝟙_ (FusionMat n k)) ≃+* k)) :
    IsFusionCategory k (FusionMat n k) :=
  isFusionCategoryOf end_unit simples_fin decomposition

end FusionMat

/-! ## Axiom audit -/

#print axioms FusionMat.hasFiniteBiproducts
#print axioms FusionMat.biconeOf_total
#print axioms FusionMat.sum_rowExtract_comp_colInsert
#print axioms FusionMat.decomposition
#print axioms FusionMat.simples_fin_and_decomposition
#print axioms FusionMat.isFusionCategory_of_instances
#print axioms FusionMat.simIncl_comp_simProj_same
#print axioms FusionMat.colInsert_comp_rowExtract_of_ne

end FusionCategory
