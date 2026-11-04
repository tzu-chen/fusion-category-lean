/-
WP2 round 3, member m2, direction D1 (the simple-object layer), part (a)-(c).

On the CANONICAL scaffold `FusionCategory.FusionMat` (block-carrying objects
`m : Fin n → ℕ`, `blk : Fin n → Type`, `Hom X Y = ∀ i, Matrix (X.blk i) (Y.blk i) k`):

* `simple_sim` : Mathlib's mono-based `Simple (sim i)`.  The matrix content is
  `not_mono_of_block_eq_zero` (a mono cannot vanish on a nonempty block),
  `not_mono_of_nontrivial_blk` (a mono into `sim i` cannot have a block with two
  coordinates) and `isIso_of_mono_of_ne_zero` (a mono into `sim i` lives in one
  1 × 1 block, and a nonzero 1 × 1 block is invertible);
* `simple_iff_exists_sim` : `Simple X ↔ ∃ i, Nonempty (X ≅ sim i)`, the honest
  iso-form on the block model (two objects with the same `m` and different `blk`
  types are isomorphic, so object equality is the wrong statement);
* `simples_fin` : the `isFusionCategoryOf` hypothesis naming the simples.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.ReconFusionProps
import FusionCategory.ReconTraceCorrespondence

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u

namespace FusionCategory

open CategoryTheory CategoryTheory.Limits

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat

/-! ## The componentwise calculus of the block category

`Hom X Y` is `∀ i, Matrix (X.blk i) (Y.blk i) k` and the category structure is
componentwise, so every one of these is `rfl`. -/

@[simp] theorem comp_apply_blk {X Y Z : FusionMat n k} (f : X ⟶ Y) (g : Y ⟶ Z) (i : Fin n) :
    (f ≫ g) i = f i * g i := rfl

@[simp] theorem id_apply_blk (X : FusionMat n k) (i : Fin n) : (𝟙 X) i = 1 := rfl

@[simp] theorem zero_apply_blk {X Y : FusionMat n k} (i : Fin n) :
    ((0 : X ⟶ Y) i) = 0 := rfl

/-! ## Cardinality of the block types -/

theorem card_blk_eq (X : FusionMat n k) (i : Fin n) : Fintype.card (X.blk i) = X.m i :=
  X.card_blk i

theorem isEmpty_blk_of_m_eq_zero {X : FusionMat n k} {i : Fin n} (h : X.m i = 0) :
    IsEmpty (X.blk i) :=
  Fintype.card_eq_zero_iff.mp (by rw [card_blk_eq, h])

theorem m_eq_zero_of_isEmpty_blk {X : FusionMat n k} {i : Fin n} (h : IsEmpty (X.blk i)) :
    X.m i = 0 := by
  rw [← card_blk_eq, Fintype.card_eq_zero_iff]
  exact h

theorem nonempty_blk_iff {X : FusionMat n k} {i : Fin n} : Nonempty (X.blk i) ↔ 0 < X.m i := by
  rw [← Fintype.card_pos_iff, card_blk_eq]

theorem subsingleton_blk_of_m_le_one {X : FusionMat n k} {i : Fin n} (h : X.m i ≤ 1) :
    Subsingleton (X.blk i) :=
  Fintype.card_le_one_iff_subsingleton.mp (by rw [card_blk_eq]; exact h)

theorem m_le_one_of_subsingleton_blk {X : FusionMat n k} {i : Fin n}
    (h : Subsingleton (X.blk i)) : X.m i ≤ 1 := by
  rw [← card_blk_eq]
  exact Fintype.card_le_one_iff_subsingleton.mpr h

/-- A matrix whose *column* index type is empty is a subsingleton. -/
theorem subsingleton_matrix_of_isEmpty_col {A B : Type} [IsEmpty B] :
    Subsingleton (Matrix A B k) :=
  ⟨fun f g => by
    funext a b
    exact (IsEmpty.false b).elim⟩

/-- A matrix whose *row* index type is empty is a subsingleton. -/
theorem subsingleton_matrix_of_isEmpty_row {A B : Type} [IsEmpty A] :
    Subsingleton (Matrix A B k) :=
  ⟨fun f g => by
    funext a
    exact (IsEmpty.false a).elim⟩

/-! ## The simples' block structure -/

theorem sim_m_self (i : Fin n) : (sim (k := k) i).m i = 1 := by
  simp [sim]

theorem sim_m_of_ne {i j : Fin n} (h : j ≠ i) : (sim (k := k) i).m j = 0 := by
  simp [sim, h]

theorem sim_m_pos (i : Fin n) : 0 < (sim (k := k) i).m i := by
  rw [sim_m_self]; norm_num

theorem card_sim_blk_self (i : Fin n) : Fintype.card ((sim (k := k) i).blk i) = 1 := by
  rw [card_blk_eq, sim_m_self]

theorem card_sim_blk_of_ne {i j : Fin n} (h : j ≠ i) :
    Fintype.card ((sim (k := k) i).blk j) = 0 := by
  rw [card_blk_eq, sim_m_of_ne h]

theorem isEmpty_sim_blk_of_ne {i j : Fin n} (h : j ≠ i) : IsEmpty ((sim (k := k) i).blk j) :=
  Fintype.card_eq_zero_iff.mp (card_sim_blk_of_ne h)

theorem subsingleton_sim_blk_self (i : Fin n) : Subsingleton ((sim (k := k) i).blk i) :=
  Fintype.card_le_one_iff_subsingleton.mp (by rw [card_sim_blk_self])

theorem nonempty_sim_blk_self (i : Fin n) : Nonempty ((sim (k := k) i).blk i) :=
  Fintype.card_pos_iff.mp (by rw [card_sim_blk_self]; norm_num)

/-! ## Single-block morphisms -/

/-- The morphism which is `M` on the block `c` and zero everywhere else. -/
def blockMk {X Y : FusionMat n k} (c : Fin n) (M : Matrix (X.blk c) (Y.blk c) k) : X ⟶ Y :=
  fun d => if h : d = c then h.symm ▸ M else 0

@[simp] theorem blockMk_self {X Y : FusionMat n k} (c : Fin n)
    (M : Matrix (X.blk c) (Y.blk c) k) : blockMk (X := X) (Y := Y) c M c = M := by
  simp [blockMk]

theorem blockMk_of_ne {X Y : FusionMat n k} {c d : Fin n} (h : d ≠ c)
    (M : Matrix (X.blk c) (Y.blk c) k) : blockMk (X := X) (Y := Y) c M d = 0 := by
  simp [blockMk, h]

theorem blockMk_eq_zero_iff {X Y : FusionMat n k} (c : Fin n)
    (M : Matrix (X.blk c) (Y.blk c) k) : blockMk (X := X) (Y := Y) c M = 0 ↔ M = 0 := by
  constructor
  · intro h
    have := congrFun h c
    rwa [blockMk_self, Pi.zero_apply] at this
  · intro h
    funext d
    by_cases hd : d = c
    · subst hd; rw [blockMk_self, h]; rfl
    · rw [blockMk_of_ne hd]; rfl

/-- A nonzero single-block endomorphism is a nonzero morphism. -/
theorem blockMk_ne_zero {Y : FusionMat n k} (c : Fin n) {M : Matrix (Y.blk c) (Y.blk c) k}
    (hM : M ≠ 0) : blockMk (X := Y) (Y := Y) c M ≠ 0 :=
  fun h0 => hM ((blockMk_eq_zero_iff c M).mp h0)

/-- The identity of a nonempty block, as a morphism carried by that block alone, is nonzero. -/
theorem blockMk_one_ne_zero {Y : FusionMat n k} (c : Fin n) (hY : 0 < Y.m c) :
    blockMk (X := Y) (Y := Y) c (1 : Matrix (Y.blk c) (Y.blk c) k) ≠ 0 := by
  intro h0
  have h : (1 : Matrix (Y.blk c) (Y.blk c) k) = 0 := (blockMk_eq_zero_iff c _).mp h0
  obtain ⟨r⟩ := nonempty_blk_iff.mpr hY
  have h1 : (1 : Matrix (Y.blk c) (Y.blk c) k) r r = 0 := by rw [h]; rfl
  rw [Matrix.one_apply, if_pos rfl] at h1
  exact one_ne_zero h1

/-- The identity of a simple is a nonzero endomorphism. -/
theorem id_sim_ne_zero (i : Fin n) :
    (𝟙 (sim (k := k) i) : sim (k := k) i ⟶ sim (k := k) i) ≠ 0 := by
  intro h
  have h' := congrFun (congrFun (congrFun h i) (simPt (k := k) i)) (simPt (k := k) i)
  simp only [id_apply_blk, Matrix.one_apply] at h'
  exact one_ne_zero h'

/-! ## Monomorphisms into a simple -/

/-- A split monomorphism is a monomorphism. -/
theorem mono_of_comp_eq_id {A B : FusionMat n k} {f : A ⟶ B} {p : B ⟶ A}
    (h : f ≫ p = 𝟙 A) : Mono f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z g hg
  calc g = g ≫ 𝟙 A := (Category.comp_id g).symm
    _ = g ≫ (f ≫ p) := by rw [h]
    _ = (g ≫ f) ≫ p := (Category.assoc g f p).symm
    _ = 0 := by rw [hg, zero_comp]

/-- A morphism vanishing on a nonempty block is not a monomorphism. -/
theorem not_mono_of_block_eq_zero {Y Z : FusionMat n k} {f : Y ⟶ Z} (c : Fin n)
    (hY : 0 < Y.m c) (hf : f c = 0) : ¬ Mono f := by
  intro hmono
  rw [Preadditive.mono_iff_cancel_zero] at hmono
  have hg : blockMk (X := Y) (Y := Y) c (1 : Matrix (Y.blk c) (Y.blk c) k) ≠ 0 :=
    blockMk_one_ne_zero c hY
  have hgf : blockMk (X := Y) (Y := Y) c (1 : Matrix (Y.blk c) (Y.blk c) k) ≫ f = 0 := by
    funext d
    by_cases hd : d = c
    · subst hd
      rw [comp_apply_blk, blockMk_self, hf, Matrix.mul_zero, zero_apply_blk]
    · rw [comp_apply_blk, blockMk_of_ne hd, zero_apply_blk, Matrix.zero_mul]
  exact hg (hmono Y _ hgf)

/-- **The matrix content of `Simple (sim i)`**: if the `i`-block of `Y` has two distinct
coordinates, a nonzero `f : Y ⟶ sim i` is not a monomorphism — the row `(v r₁, -v r₀)` kills
the column `f i`. -/
theorem not_mono_of_nontrivial_blk (i : Fin n) (Y : FusionMat n k)
    (f : Y ⟶ sim (k := k) i) (hnt : ∃ a b : Y.blk i, a ≠ b) (hf : f i ≠ 0) :
    ¬ Mono f := by
  classical
  have hsub : Subsingleton ((sim (k := k) i).blk i) := subsingleton_sim_blk_self i
  have hfs : ∀ (r : Y.blk i) (s : (sim (k := k) i).blk i),
      f i r s = f i r (simPt (k := k) i) := by
    intro r s
    rw [hsub.elim s (simPt (k := k) i)]
  have hne : ∃ r : Y.blk i, f i r (simPt (k := k) i) ≠ 0 := by
    by_contra hc
    have hc' : ∀ r, f i r (simPt (k := k) i) = 0 := fun r =>
      by_contra fun h => hc ⟨r, h⟩
    exact hf (by funext r s; rw [hfs]; exact hc' r)
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨a, b, hab⟩ := hnt
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Y.blk i, r₁ ≠ a₀ := by
    by_cases ha : a = a₀
    · exact ⟨b, fun h => hab (ha.trans h.symm)⟩
    · exact ⟨a, ha⟩
  set v : Y.blk i → k := fun t => f i t (simPt (k := k) i) with hv
  set M : Matrix (Y.blk i) (Y.blk i) k :=
    fun r t => if r = r₁ then ((if t = a₀ then v r₁ else 0) + (if t = r₁ then -(v a₀) else 0))
      else 0 with hM
  have hkey : ∀ (a : Y.blk i) (c : k), ∑ t : Y.blk i, ((if t = a then c else 0) : k) * v t
      = c * v a := by
    intro a c
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hMv : M * f i = 0 := by
    ext r s
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have hstep : ∑ j : Y.blk i, M r j * f i j s = ∑ j : Y.blk i, M r j * v j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfs j s]
    rw [hstep]
    by_cases hr' : r = r₁
    · rw [hr']
      simp only [hM, if_pos rfl, add_mul, Finset.sum_add_distrib]
      rw [hkey a₀ (v r₁), hkey r₁ (-(v a₀))]
      ring
    · simp [hM, hr']
  have hMne : M ≠ 0 := by
    intro h0
    have h2 := congrArg (fun N : Matrix (Y.blk i) (Y.blk i) k => N r₁ r₁) h0
    simp only [hM, Matrix.zero_apply, if_pos rfl] at h2
    rw [if_neg hr₁, zero_add] at h2
    exact ha₀ (neg_eq_zero.mp h2)
  intro hmono
  rw [Preadditive.mono_iff_cancel_zero] at hmono
  have hg : blockMk (X := Y) (Y := Y) i M ≠ 0 := blockMk_ne_zero i hMne
  have hgf : blockMk (X := Y) (Y := Y) i M ≫ f = 0 := by
    funext d
    by_cases hd : d = i
    · subst hd
      rw [comp_apply_blk, blockMk_self, hMv, zero_apply_blk]
    · rw [comp_apply_blk, blockMk_of_ne hd, zero_apply_blk, Matrix.zero_mul]
  exact hg (hmono Y _ hgf)

/-- A monomorphism into `sim i` forces every other block of its source to be empty. -/
theorem isEmpty_blk_of_mono_to_sim (i : Fin n) (Y : FusionMat n k) (f : Y ⟶ sim (k := k) i)
    (hmono : Mono f) {c : Fin n} (hc : c ≠ i) : IsEmpty (Y.blk c) := by
  classical
  rw [← Fintype.card_eq_zero_iff]
  by_contra hcard
  have hpos : 0 < Y.m c := by
    rw [← card_blk_eq]; exact Nat.pos_of_ne_zero hcard
  haveI hEc : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
  have hfc : f c = 0 := Subsingleton.elim _ _
  by_cases h2 : 2 ≤ Y.m i
  · by_cases hfi : f i = 0
    · exact not_mono_of_block_eq_zero i (by omega) hfi hmono
    · obtain ⟨r₀, r₁, hr⟩ :=
        (Fintype.one_lt_card_iff.mp (by rw [card_blk_eq]; omega) : ∃ a b : Y.blk i, a ≠ b)
      exact not_mono_of_nontrivial_blk i Y f ⟨r₀, r₁, hr⟩ hfi hmono
  · have hlt : Y.m i < 2 := by omega
    exact not_mono_of_block_eq_zero c hpos hfc hmono

/-- **The matrix content of `Simple (sim i)`, invertible form**: a nonzero monomorphism
`f : Y ⟶ sim i` lives in the `i`-block alone, that block of `Y` is a singleton, and a nonzero
`1 × 1` matrix is invertible. -/
theorem isIso_of_mono_of_ne_zero (i : Fin n) (Y : FusionMat n k) (f : Y ⟶ sim (k := k) i)
    (hmono : Mono f) (hf : f ≠ 0) : IsIso f := by
  classical
  have hvanish : ∀ c, c ≠ i → IsEmpty (Y.blk c) := fun c hc =>
    isEmpty_blk_of_mono_to_sim i Y f hmono hc
  have hf0 : ∀ c, c ≠ i → f c = 0 := by
    intro c hc
    haveI : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
    exact Subsingleton.elim _ _
  have hfi : f i ≠ 0 := by
    intro h0
    apply hf
    funext c
    by_cases hc : c = i
    · subst hc; exact h0
    · rw [hf0 c hc, zero_apply_blk]
  have hsub : Subsingleton (Y.blk i) := by
    by_contra hns
    haveI hnt : Nontrivial (Y.blk i) := not_subsingleton_iff_nontrivial.mp hns
    obtain ⟨r₀, r₁, hr⟩ := exists_pair_ne (Y.blk i)
    exact not_mono_of_nontrivial_blk i Y f ⟨r₀, r₁, hr⟩ hfi hmono
  have hpos : 0 < Y.m i := by
    rcases Nat.eq_zero_or_pos (Y.m i) with h | h
    · exfalso
      haveI : IsEmpty (Y.blk i) := isEmpty_blk_of_m_eq_zero h
      exact hfi (Subsingleton.elim _ _)
    · exact h
  obtain ⟨r₀⟩ := nonempty_blk_iff.mpr hpos
  have hsubS : Subsingleton ((sim (k := k) i).blk i) := subsingleton_sim_blk_self i
  have hfs : ∀ (r : Y.blk i) (s : (sim (k := k) i).blk i),
      f i r s = f i r₀ (simPt (k := k) i) := by
    intro r s
    rw [hsub.elim r r₀, hsubS.elim s (simPt (k := k) i)]
  set a : k := f i r₀ (simPt (k := k) i) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    exact hfi (by funext r s; rw [hfs]; exact h0)
  let W : Matrix ((sim (k := k) i).blk i) (Y.blk i) k := fun _ _ => a⁻¹
  have hW : ∀ (x : (sim (k := k) i).blk i) (y : Y.blk i), W x y = a⁻¹ := fun _ _ => rfl
  refine ⟨blockMk (X := sim (k := k) i) (Y := Y) i W, ?_, ?_⟩
  · funext c
    by_cases hc : c = i
    · cases hc
      rw [comp_apply_blk, blockMk_self, id_apply_blk]
      ext r s
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [hW]
      rw [Finset.sum_eq_single (simPt (k := k) i)]
      · rw [hfs r (simPt (k := k) i), ha_def, mul_inv_cancel₀ ha,
          if_pos (show r = s from hsub.elim r s)]
      · intro b _ hb
        exact absurd (hsubS.elim b (simPt (k := k) i)) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    · haveI : IsEmpty (Y.blk c) := hvanish c hc
      rw [comp_apply_blk, blockMk_of_ne hc, Matrix.mul_zero, id_apply_blk]
      exact Subsingleton.elim _ _
  · funext c
    by_cases hc : c = i
    · cases hc
      rw [comp_apply_blk, blockMk_self, id_apply_blk]
      ext r s
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [hW]
      rw [Finset.sum_eq_single r₀]
      · rw [hfs r₀ s, ha_def, inv_mul_cancel₀ ha, if_pos (show r = s from hsubS.elim r s)]
      · intro b _ hb
        exact absurd (hsub.elim b r₀) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    · haveI : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
      rw [comp_apply_blk, blockMk_of_ne hc, Matrix.zero_mul, id_apply_blk]
      exact Subsingleton.elim _ _

/-- **`Simple (sim i)`** for the canonical scaffold — Mathlib's mono-based `Simple`. -/
instance simple_sim (i : Fin n) : Simple (sim (k := k) i) where
  mono_isIso_iff_nonzero {Y} f _ :=
    ⟨fun hiso h0 => by
        have h2 : (inv f : sim (k := k) i ⟶ Y) ≫ f = 0 := by
          nth_rewrite 2 [h0]
          exact comp_zero
        exact id_sim_ne_zero i ((IsIso.inv_hom_id f).symm.trans h2),
      fun hne => isIso_of_mono_of_ne_zero i Y f ‹Mono f› hne⟩

/-! ## The converse: a simple object is a `sim i`

The honest form on the block model is isomorphism, not equality: `X.blk i` may be any one-element
type where `(sim i).blk i` is `Fin 1`, and the two objects are then isomorphic. -/

/-- The inclusion of the `r`-th coordinate of the `i`-block: a split monomorphism `sim i ⟶ X`. -/
def simIncl (X : FusionMat n k) (i : Fin n) (r : X.blk i) : sim (k := k) i ⟶ X :=
  blockMk i (Matrix.of (fun _ s => if s = r then (1 : k) else 0))

/-- The projection onto the `r`-th coordinate of the `i`-block; it splits `simIncl`. -/
def simProj (X : FusionMat n k) (i : Fin n) (r : X.blk i) : X ⟶ sim (k := k) i :=
  blockMk i (Matrix.of (fun s _ => if s = r then (1 : k) else 0))

theorem simIncl_comp_simProj (X : FusionMat n k) (i : Fin n) (r : X.blk i) :
    simIncl X i r ≫ simProj X i r = 𝟙 (sim (k := k) i) := by
  haveI hS : Subsingleton ((sim (k := k) i).blk i) := subsingleton_sim_blk_self i
  funext c
  by_cases hc : c = i
  · cases hc
    simp only [comp_apply_blk, id_apply_blk, simIncl, simProj, blockMk_self]
    ext u u'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single r]
    · simp [Subsingleton.elim u u']
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ r) h
  · haveI : IsEmpty ((sim (k := k) i).blk c) := isEmpty_sim_blk_of_ne hc
    simp only [comp_apply_blk, id_apply_blk, simIncl, simProj, blockMk_of_ne hc, Matrix.zero_mul]
    exact Subsingleton.elim _ _

theorem simIncl_ne_zero (X : FusionMat n k) (i : Fin n) (r : X.blk i) :
    simIncl X i r ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (congrFun h0 i) (simPt (k := k) i)) r
  simp only [simIncl, blockMk_self, Matrix.of_apply] at h
  exact one_ne_zero h

/-- **The simple objects of the reconstruction are exactly the `sim i`**, in iso form. -/
theorem simple_iff_exists_sim (X : FusionMat n k) :
    Simple X ↔ ∃ i : Fin n, Nonempty (X ≅ sim (k := k) i) := by
  constructor
  · intro hX
    have hsome : ∃ i : Fin n, Nonempty (X.blk i) := by
      by_contra hc
      haveI hi : ∀ i, IsEmpty (X.blk i) := fun i => not_nonempty_iff.mp (fun h => hc ⟨i, h⟩)
      have hid : (𝟙 X : X ⟶ X) = 0 := by
        funext c
        exact Subsingleton.elim _ _
      have hne : (𝟙 X : X ⟶ X) ≠ 0 := (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp inferInstance
      exact hne hid
    obtain ⟨i, ⟨r⟩⟩ := hsome
    refine ⟨i, ?_⟩
    haveI hmono : Mono (simIncl X i r) := mono_of_comp_eq_id (simIncl_comp_simProj X i r)
    have hne : simIncl X i r ≠ 0 := simIncl_ne_zero X i r
    have hiso : IsIso (simIncl X i r) := isIso_of_mono_of_nonzero hne
    exact ⟨(asIso (simIncl X i r)).symm⟩
  · rintro ⟨i, ⟨e⟩⟩
    exact Simple.of_iso e

/-- **The first `isFusionCategoryOf` hypothesis**: finitely many simples, witnessed by the family
`sim : Fin n → FusionMat n k`, with every simple isomorphic to one of them. -/
theorem simples_fin :
    ∃ (N : ℕ) (f : Fin N → FusionMat n k), (∀ i, Simple (f i)) ∧
      ∀ Y : FusionMat n k, Simple Y → ∃ i : Fin N, Nonempty (Y ≅ f i) :=
  ⟨n, fun i => sim (k := k) i, fun i => simple_sim i,
    fun Y hY => (simple_iff_exists_sim Y).mp hY⟩

end FusionMat

/-! ## Axiom audit -/

#print axioms FusionMat.simple_sim
#print axioms FusionMat.simple_iff_exists_sim
#print axioms FusionMat.simples_fin
#print axioms FusionMat.isIso_of_mono_of_ne_zero
#print axioms FusionMat.not_mono_of_nontrivial_blk
#print axioms FusionMat.isEmpty_blk_of_mono_to_sim

end FusionCategory
