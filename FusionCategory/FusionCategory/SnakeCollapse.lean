import FusionCategory.ReconSnake

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

namespace FusionMat
variable (S : FusionSystem n k)

/-! ## The canonical unit-channel elements -/

/-- the canonical element of the unit channel `N c (dual c) 0 = 1`. -/
def chR (hn : 0 < n) (c : Fin n) : Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩) :=
  ⟨0, by rw [S.ring.dual_coeff hn c (S.ring.dual c), if_pos rfl]; exact Nat.one_pos⟩

/-- the canonical element of the unit channel `N (dual c) c 0 = 1`. -/
def chR' (hn : 0 < n) (c : Fin n) : Fin (S.ring.N (S.ring.dual c) c ⟨0, hn⟩) :=
  ⟨0, by
    rw [S.ring.dual_coeff hn (S.ring.dual c) c, if_pos (S.ring.dual_dual c).symm]
    exact Nat.one_pos⟩

/-- The canonical identification `X.blk c ≃ X*.blk (c*)`, as a transport. -/
abbrev dvi (hn : 0 < n) (X : FusionMat n k) (c : Fin n) (j : X.blk c) :
    (dual S X).blk (S.ring.dual c) :=
  show (dual S X).blk (S.ring.dual c) from
    (show X.blk (S.ring.dual (S.ring.dual c)) from ((S.ring.dual_dual c).symm ▸ j))

theorem sum_chR (hn : 0 < n) (c : Fin n)
    (f : Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩) → k) :
    ∑ i, f i = f (chR S hn c) := by
  classical
  have hsub : Subsingleton (Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩)) :=
    channel_subsingleton S c (S.ring.dual c) ⟨0, hn⟩
  exact Finset.sum_eq_single _ (fun b _ hb => absurd (Subsingleton.elim b _) hb)
    (fun h => absurd (Finset.mem_univ _) h)

theorem sum_chR' (hn : 0 < n) (c : Fin n)
    (f : Fin (S.ring.N (S.ring.dual c) c ⟨0, hn⟩) → k) :
    ∑ i, f i = f (chR' S hn c) := by
  classical
  have hsub : Subsingleton (Fin (S.ring.N (S.ring.dual c) c ⟨0, hn⟩)) :=
    channel_subsingleton S (S.ring.dual c) c ⟨0, hn⟩
  exact Finset.sum_eq_single _ (fun b _ hb => absurd (Subsingleton.elim b _) hb)
    (fun h => absurd (Finset.mem_univ _) h)

/-! ## Transport calculus -/

theorem transport_self {X : FusionMat n k} {a : Fin n} (h : a = a) (x : X.blk a) :
    (h ▸ x) = x := by cases h; rfl

theorem transport_transport_symm {X : FusionMat n k} {a b : Fin n} (h : a = b) (x : X.blk b) :
    (h ▸ (h.symm ▸ x) : X.blk b) = x := by cases h; rfl

theorem transport_symm_transport {X : FusionMat n k} {a b : Fin n} (h : a = b) (x : X.blk a) :
    (h.symm ▸ (h ▸ x) : X.blk a) = x := by cases h; rfl

theorem transport_inj {X : FusionMat n k} {a b : Fin n} (h : a = b) {x y : X.blk a}
    (e : (h ▸ x) = (h ▸ y)) : x = y := by cases h; exact e

/-! ## The associator entry at matched labels, and the label zero lemmas -/

theorem assocEntry_apply_matched (X Y Z : FusionMat n k) (d : Fin n)
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

theorem assocEntry_zero_b' (X Y Z : FusionMat n k) (d : Fin n)
    {r : (tensorObj S (tensorObj S X Y) Z).blk d}
    {q : (tensorObj S X (tensorObj S Y Z)).blk d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h : r.2.2.1.1.2 ≠ q.2.2.2.1.1) :
    assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  rw [dif_pos h1]
  exact dif_neg h

theorem assocEntry_zero_c' (X Y Z : FusionMat n k) (d : Fin n)
    {r : (tensorObj S (tensorObj S X Y) Z).blk d}
    {q : (tensorObj S X (tensorObj S Y Z)).blk d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h2 : r.2.2.1.1.2 = q.2.2.2.1.1)
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  rw [dif_pos h1, dif_pos h2]
  exact dif_neg h

/-! ## The evaluation and coevaluation entries at the unit channel -/

theorem coev_snake_entry (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩))
    (s : X.blk c) (t : (dual S X).blk (S.ring.dual c)) :
    coev S hn X ⟨0, hn⟩ (unitBlk hn)
        ⟨(c, S.ring.dual c), (ν, s, t)⟩
      = if s = ((S.ring.dual_dual c) ▸ t) then S.coev c else 0 :=
  coev_apply_of_eq S hn X ⟨0, hn⟩ (p := (c, S.ring.dual c)) (h := (S.ring.dual_dual c).symm)
    ν s t (unitBlk hn)

theorem ev_snake_entry (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν' : Fin (S.ring.N (S.ring.dual c) c ⟨0, hn⟩))
    (s' : (dual S X).blk (S.ring.dual c)) (t' : X.blk c) :
    ev S hn X ⟨0, hn⟩
        ⟨(S.ring.dual c, c), (ν', s', t')⟩ (unitBlk hn)
      = if s' = dvi S hn X c t' then S.ev c else 0 :=
  ev_apply_of_eq S hn X ⟨0, hn⟩ (p := (S.ring.dual c, c)) (h := (S.ring.dual_dual c).symm)
    ν' s' t' (unitBlk hn)

theorem assocEntry_zero_a' (X Y Z : FusionMat n k) (d : Fin n)
    {r : (tensorObj S (tensorObj S X Y) Z).blk d}
    {q : (tensorObj S X (tensorObj S Y Z)).blk d} (h : r.2.2.1.1.1 ≠ q.1.1) :
    assocEntry S X Y Z d r q = 0 := by
  simp only [assocEntry]
  exact dif_neg h

/-- **The inner collapse**: the sum over the unit-channel index of `X* ⊗ X` is a
delta. -/
theorem inner_sum (hn : 0 < n) (X : FusionMat n k) (c : Fin n) {j j' : X.blk c}
    {ν : Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩)} {s : X.blk c}
    {t : (dual S X).blk (S.ring.dual c)} :
    (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
      assocEntry S X (dual S X) X c
        ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, S.ring.dual c), (ν, s, t)⟩, j)⟩
        ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', w)⟩ *
      (ev S hn X ⟨0, hn⟩) w (unitBlk hn))
    = if s = j' then
        (if t = dvi S hn X c j then
          S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.ev c else 0)
      else 0 := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (a := S.ring.dual c)]
  · rw [Finset.sum_eq_single (a := c)]
    · rw [sum_chR' S hn c]
      simp only [assocEntry_apply_matched S X (dual S X) X c ⟨0, hn⟩ c (unitChL S hn c)
        c (S.ring.dual c) ν s t j ⟨0, hn⟩ (unitChR S hn c) j' (chR' S hn c)]
      simp only [ev_snake_entry S hn X c (chR' S hn c)]
      rw [Finset.sum_eq_single (a := t)]
      · rw [Finset.sum_eq_single (a := j)]
        · split_ifs with h1 h2 <;> simp_all
        · intro t' _ ht'
          rw [dif_neg (fun hc : j = t' => ht' hc.symm)]
          split_ifs <;> ring
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro s' _ hs'
        have hz : ∀ (t' : X.blk c),
            (if hx : s = j' then (if hy : t = s' then (if hz : j = t' then
              S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ else 0) else 0) else 0) *
              (if s' = dvi S hn X c t' then S.ev c else 0) = 0 := by
          intro t'
          rw [dif_neg (fun hc : t = s' => hs' hc.symm)]
          split_ifs <;> ring
        simp only [hz, Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro q4 _ hq4
      have hz : ∀ (ν' : Fin (S.ring.N (S.ring.dual c) q4 ⟨0, hn⟩))
          (s' : (dual S X).blk (S.ring.dual c)) (t' : X.blk q4),
          assocEntry S X (dual S X) X c
            ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, S.ring.dual c), (ν, s, t)⟩, j)⟩
            ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', ⟨(S.ring.dual c, q4), (ν', s', t')⟩)⟩ *
          ev S hn X ⟨0, hn⟩ ⟨(S.ring.dual c, q4), (ν', s', t')⟩ (unitBlk hn) = 0 := by
        intro ν' s' t'
        rw [assocEntry_zero_c' S X (dual S X) X c rfl rfl (Ne.symm hq4)]
        ring
      simp only [hz, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro q3 _ hq3
    have hz : ∀ (q4 : Fin n) (ν' : Fin (S.ring.N q3 q4 ⟨0, hn⟩))
        (s' : (dual S X).blk q3) (t' : X.blk q4),
        assocEntry S X (dual S X) X c
          ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, S.ring.dual c), (ν, s, t)⟩, j)⟩
          ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', ⟨(q3, q4), (ν', s', t')⟩)⟩ *
        ev S hn X ⟨0, hn⟩ ⟨(q3, q4), (ν', s', t')⟩ (unitBlk hn) = 0 := by
      intro q4 ν' s' t'
      rw [assocEntry_zero_b' S X (dual S X) X c rfl (Ne.symm hq3)]
      ring
    simp only [hz, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The double-sum collapse of the left snake.** -/
theorem snake_double (hn : 0 < n) (X : FusionMat n k) (c : Fin n) (j j' : X.blk c) :
    (∑ au : (tensorObj S X (dual S X)).blk ⟨0, hn⟩,
      (coev S hn X ⟨0, hn⟩) (unitBlk hn) au *
        (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
          assocEntry S X (dual S X) X c ⟨(⟨0, hn⟩, c), (unitChL S hn c, au, j)⟩
            ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', w)⟩ *
          (ev S hn X ⟨0, hn⟩) w (unitBlk hn)))
      = if j = j' then 1 else 0 := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (a := c)]
  · rw [Finset.sum_eq_single (a := S.ring.dual c)]
    · rw [sum_chR S hn c]
      simp only [inner_sum S hn X c]
      rw [Finset.sum_eq_single (a := j')]
      · rw [Finset.sum_eq_single (a := dvi S hn X c j)]
        · rw [coev_snake_entry S hn X c (chR S hn c) j']
          simp only [dvi, transport_transport_symm]
          by_cases hjj : j = j'
          · rw [if_pos hjj.symm, if_pos hjj]
            simp
            rw [← S.snake_left hn c]
            ring
          · rw [if_neg (fun hc : j' = j => hjj hc.symm), if_neg hjj]
            simp
        · intro t _ ht
          rw [if_neg ht]
          split_ifs <;> ring
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        have hz : ∀ (t : (dual S X).blk (S.ring.dual c)),
            coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(c, S.ring.dual c), (chR S hn c, s, t)⟩ *
              (if s = j' then (if t = dvi S hn X c j then
                S.F c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.ev c else 0) else 0) = 0 := by
          intro t
          rw [if_neg hs]
          ring
        simp only [hz, Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p4 _ hp4
      have hne : c ≠ S.ring.dual p4 := by
        intro hc
        exact hp4 ((congrArg S.ring.dual hc).trans (S.ring.dual_dual p4)).symm
      have hz : ∀ (ν : Fin (S.ring.N c p4 ⟨0, hn⟩)) (s : X.blk c)
          (t : (dual S X).blk p4),
          coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(c, p4), (ν, s, t)⟩ *
            (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
              assocEntry S X (dual S X) X c
                ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, p4), (ν, s, t)⟩, j)⟩
                ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', w)⟩ *
              (ev S hn X ⟨0, hn⟩) w (unitBlk hn)) = 0 := by
        intro ν s t
        rw [coev_apply_of_ne S hn X ⟨0, hn⟩ (p := (c, p4)) hne ν s t (unitBlk hn), zero_mul]
      simp only [hz, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p3 _ hp3
    have hz : ∀ (p4 : Fin n) (ν : Fin (S.ring.N p3 p4 ⟨0, hn⟩)) (s : X.blk p3)
        (t : (dual S X).blk p4),
        coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(p3, p4), (ν, s, t)⟩ *
          (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
            assocEntry S X (dual S X) X c
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(p3, p4), (ν, s, t)⟩, j)⟩
              ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j', w)⟩ *
            (ev S hn X ⟨0, hn⟩) w (unitBlk hn)) = 0 := by
      intro p4 ν s t
      rw [Finset.sum_eq_zero (fun w _ => ?_), mul_zero]
      rw [assocEntry_zero_a' S X (dual S X) X c hp3]
      ring
    simp only [hz, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The entry of the left snake composite.** -/
theorem snakeLeft_entry (hn : 0 < n) (X : FusionMat n k) (c : Fin n) (j j' : X.blk c) :
    (whiskerRight S (coev S hn X) X ≫ associatorHom S X (dual S X) X
        ≫ whiskerLeft S X (ev S hn X) ≫ rightUnitor S hn X) c
        (unitIdxL S hn X c j) j' = (leftUnitor S hn X) c (unitIdxL S hn X c j) j' := by
  have hcomp : (whiskerRight S (coev S hn X) X ≫ associatorHom S X (dual S X) X
        ≫ whiskerLeft S X (ev S hn X) ≫ rightUnitor S hn X) c
      = tensorHom S (coev S hn X) (𝟙 X) c
          * (associatorHom S X (dual S X) X c * absorbedEv S hn X c) := rfl
  rw [hcomp, coevTensor_assoc_absorbedEv]
  rw [Finset.sum_congr rfl (fun a _ => by rw [assoc_mul_absorbedEv])]
  rw [snake_double, leftUnitor_eq]
  by_cases h : j = j'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (unitIdxL_injective S hn X c hc))]

/-- **The left snake equation** (the frozen `FusionMat.SnakeLeft`). -/
theorem snakeLeft_holds : SnakeLeft S := by
  intro hn X
  funext c
  ext r j'
  obtain ⟨j, rfl⟩ := eq_unitIdxL_of S hn X c r
  exact snakeLeft_entry S hn X c j j'

/-! ## The right snake: matched entry, zero lemmas, unit-channel entries -/

theorem assocInvEntry_apply_matched (X Y Z : FusionMat n k) (d : Fin n)
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

theorem assocInvEntry_zero_a' (X Y Z : FusionMat n k) (d : Fin n)
    {q : (tensorObj S X (tensorObj S Y Z)).blk d}
    {r : (tensorObj S (tensorObj S X Y) Z).blk d} (h : r.2.2.1.1.1 ≠ q.1.1) :
    assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  exact dif_neg h

theorem assocInvEntry_zero_b' (X Y Z : FusionMat n k) (d : Fin n)
    {q : (tensorObj S X (tensorObj S Y Z)).blk d}
    {r : (tensorObj S (tensorObj S X Y) Z).blk d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h : r.2.2.1.1.2 ≠ q.2.2.2.1.1) :
    assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  rw [dif_pos h1]
  exact dif_neg h

theorem assocInvEntry_zero_c' (X Y Z : FusionMat n k) (d : Fin n)
    {q : (tensorObj S X (tensorObj S Y Z)).blk d}
    {r : (tensorObj S (tensorObj S X Y) Z).blk d}
    (h1 : r.2.2.1.1.1 = q.1.1) (h2 : r.2.2.1.1.2 = q.2.2.2.1.1)
    (h : r.1.2 ≠ q.2.2.2.1.2) : assocInvEntry S X Y Z d q r = 0 := by
  simp only [assocInvEntry]
  rw [dif_pos h1, dif_pos h2]
  exact dif_neg h

/-- The coevaluation entry for the right snake: both labels are reflexive. -/
theorem coev_snake_entryR (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N (S.ring.dual c) c ⟨0, hn⟩))
    (x : X.blk (S.ring.dual c)) (y : (dual S X).blk c) :
    coev S hn X ⟨0, hn⟩ (unitBlk hn)
        ⟨(S.ring.dual c, c), (ν, x, y)⟩
      = if x = (show X.blk (S.ring.dual c) from y) then S.coev (S.ring.dual c) else 0 :=
  coev_apply_of_eq S hn X ⟨0, hn⟩ (p := (S.ring.dual c, c)) (h := rfl) ν x y (unitBlk hn)

/-- The evaluation entry for the right snake. -/
theorem ev_snake_entryR (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν' : Fin (S.ring.N c (S.ring.dual c) ⟨0, hn⟩))
    (s : (dual S X).blk c) (t : X.blk (S.ring.dual c)) :
    ev S hn X ⟨0, hn⟩ ⟨(c, S.ring.dual c), (ν', s, t)⟩ (unitBlk hn)
      = if s = (show (dual S X).blk c from t) then S.ev (S.ring.dual c) else 0 :=
  ev_apply_of_eq S hn X ⟨0, hn⟩ (p := (c, S.ring.dual c)) (h := rfl) ν' s t (unitBlk hn)
/-- The evaluation whiskered on the left, with the left unitor absorbed (right snake). -/
abbrev absorbedEvR (hn : 0 < n) (X : FusionMat n k) (c : Fin n) :
    Matrix ((tensorObj S (tensorObj S (dual S X) X) (dual S X)).blk c)
      ((dual S X).blk c) k :=
  tensorHom S (ev S hn X) (𝟙 (dual S X)) c * leftUnitor S hn (dual S X) c

theorem absorbedEvR_apply_canon (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (ν : Fin (S.ring.N ⟨0, hn⟩ c c)) (x : (tensorObj S (dual S X) X).blk ⟨0, hn⟩)
    (y : (dual S X).blk c) (j : (dual S X).blk c) :
    absorbedEvR S hn X c ⟨(⟨0, hn⟩, c), (ν, x, y)⟩ j
      = (if ν = unitChL S hn c then
          (if y = j then (ev S hn X ⟨0, hn⟩) x (unitBlk hn) else 0) else 0) := by
  rw [absorbedEvR, mul_leftUnitor S hn (dual S X) c]
  show tensorHom S (ev S hn X) (𝟙 (dual S X)) c ⟨(⟨0, hn⟩, c), (ν, x, y)⟩
      ⟨(⟨0, hn⟩, c), (unitChL S hn c, unitBlk hn, j)⟩ = _
  rw [tensorHom_apply]
  rw [show ((𝟙 (dual S X) : dual S X ⟶ dual S X) c) y j = if y = j then 1 else 0
    from Matrix.one_apply]
  split_ifs <;> ring

theorem absorbedEvR_apply_ne (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {b : (tensorObj S (tensorObj S (dual S X) X) (dual S X)).blk c}
    (h : b.1 ≠ (⟨0, hn⟩, c)) (j : (dual S X).blk c) :
    absorbedEvR S hn X c b j = 0 := by
  rw [absorbedEvR, mul_leftUnitor]
  show (tensorHom S (ev S hn X) (𝟙 (dual S X)) c) b (unitIdxL S hn (dual S X) c j) = 0
  rw [tensorHom, blockDiag]
  exact dif_neg h

/-- **Step 2 of the right snake**: the inverse associator against the absorbed
evaluation. -/
theorem assocInv_mul_absorbedEvR (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (a : (tensorObj S (dual S X) (tensorObj S X (dual S X))).blk c)
    (j' : (dual S X).blk c) :
    (associatorInv S (dual S X) X (dual S X) c * absorbedEvR S hn X c) a j'
      = ∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
          assocInvEntry S (dual S X) X (dual S X) c a
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, w, j')⟩
            * ((ev S hn X ⟨0, hn⟩) w (unitBlk hn)) := by
  rw [Matrix.mul_apply]
  simp only [associatorInv, Matrix.of_apply]
  rw [sum_tensorBlk S (tensorObj S (dual S X) X) (dual S X) c
    (fun b => assocInvEntry S (dual S X) X (dual S X) c a b * absorbedEvR S hn X c b j')]
  rw [Finset.sum_eq_single ((⟨0, hn⟩, c) : Fin n × Fin n)]
  · rw [Finset.sum_eq_single (unitChL S hn c)]
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Finset.sum_eq_single j']
      · rw [absorbedEvR_apply_canon, if_pos rfl, if_pos rfl]
      · intro y _ hy
        rw [absorbedEvR_apply_canon, if_pos rfl, if_neg hy, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ν _ hν
      refine Finset.sum_eq_zero (fun x _ => ?_)
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [absorbedEvR_apply_canon, if_neg hν, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero (fun ν _ => ?_)
    refine Finset.sum_eq_zero (fun x _ => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    have hne : (⟨p, (ν, x, y)⟩ :
        (tensorObj S (tensorObj S (dual S X) X) (dual S X)).blk c).1 ≠ (⟨0, hn⟩, c) := by
      simpa using hp
    rw [absorbedEvR_apply_ne (h := hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
/-- The entry of `𝟙 X* ⊗ coev X` at the canonical index. -/
theorem coev_whisker_apply_canon (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : (dual S X).blk c) (ν : Fin (S.ring.N c ⟨0, hn⟩ c))
    (x : (dual S X).blk c) (y : (tensorObj S X (dual S X)).blk ⟨0, hn⟩) :
    tensorHom S (𝟙 (dual S X)) (coev S hn X) c
        (unitIdxR S hn (dual S X) c j) ⟨(c, ⟨0, hn⟩), (ν, x, y)⟩
      = (if unitChR S hn c = ν then
          (if j = x then (coev S hn X ⟨0, hn⟩) (unitBlk hn) y else 0) else 0) := by
  have hrow : unitIdxR S hn (dual S X) c j
      = ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, unitBlk hn)⟩ := rfl
  rw [hrow, tensorHom_apply]
  rw [show ((𝟙 (dual S X) : dual S X ⟶ dual S X) c) j x = if j = x then 1 else 0
    from Matrix.one_apply]
  split_ifs <;> ring

/-- The entry of `𝟙 X* ⊗ coev X` off the canonical label pair. -/
theorem coev_whisker_apply_ne (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j : (dual S X).blk c) {p : Fin n × Fin n} (hp : p ≠ (c, ⟨0, hn⟩))
    (ν : Fin (S.ring.N p.1 p.2 c)) (x : (dual S X).blk p.1)
    (y : (tensorObj S X (dual S X)).blk p.2) :
    tensorHom S (𝟙 (dual S X)) (coev S hn X) c
        (unitIdxR S hn (dual S X) c j) ⟨p, (ν, x, y)⟩ = 0 := by
  rw [tensorHom, blockDiag]
  have h' : (unitIdxR S hn (dual S X) c j).1 ≠ p := by
    rw [show (unitIdxR S hn (dual S X) c j).1 = (c, ⟨0, hn⟩) from rfl]
    exact Ne.symm hp
  exact dif_neg h'

/-- **Step 1 of the right snake**: the outer `coev ⊗ 𝟙` collapse. -/
theorem coevWhisker_mul (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (Z : Matrix ((tensorObj S (dual S X) (tensorObj S X (dual S X))).blk c)
      ((dual S X).blk c) k) (j j' : (dual S X).blk c) :
    (tensorHom S (𝟙 (dual S X)) (coev S hn X) c * Z)
        (unitIdxR S hn (dual S X) c j) j'
      = ∑ au : (tensorObj S X (dual S X)).blk ⟨0, hn⟩,
          (coev S hn X ⟨0, hn⟩) (unitBlk hn) au
            * Z ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, au)⟩ j' := by
  rw [Matrix.mul_apply]
  rw [sum_tensorBlk S (dual S X) (tensorObj S X (dual S X)) c
    (fun a => tensorHom S (𝟙 (dual S X)) (coev S hn X) c
      (unitIdxR S hn (dual S X) c j) a * Z a j')]
  rw [Finset.sum_eq_single ((c, ⟨0, hn⟩) : Fin n × Fin n)]
  · rw [Finset.sum_eq_single (unitChR S hn c)]
    · rw [Finset.sum_eq_single j]
      · refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [coev_whisker_apply_canon, if_pos rfl, if_pos rfl]
      · intro x' _ hx
        refine Finset.sum_eq_zero (fun y _ => ?_)
        rw [coev_whisker_apply_canon, if_pos rfl, if_neg (fun hc : j = x' => hx hc.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ν _ hν
      refine Finset.sum_eq_zero (fun x _ => ?_)
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [coev_whisker_apply_canon, if_neg (fun hc : unitChR S hn c = ν => hν hc.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero (fun ν _ => ?_)
    refine Finset.sum_eq_zero (fun x _ => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [coev_whisker_apply_ne S hn X c j hp]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h
/-- **The inner collapse of the right snake**: the sum over the unit-channel index
of `X* ⊗ X` is a delta. -/
theorem inner_sumR (hn : 0 < n) (X : FusionMat n k) (c : Fin n) {j j' : (dual S X).blk c}
    {p3 : Fin n} {ν : Fin (S.ring.N p3 c ⟨0, hn⟩)} {x : X.blk p3}
    {y : (dual S X).blk c} :
    (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
      assocInvEntry S (dual S X) X (dual S X) c
        ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, c), (ν, x, y)⟩)⟩
        ⟨(⟨0, hn⟩, c), (unitChL S hn c, w, j')⟩ *
      (ev S hn X ⟨0, hn⟩) w (unitBlk hn))
    = if hp3 : p3 = S.ring.dual c then
        (if j' = y then
          (if j = (show (dual S X).blk c from
              (show X.blk (S.ring.dual c) from (hp3 ▸ x))) then
            S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.ev (S.ring.dual c)
            else 0) else 0)
      else 0 := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ((c : Fin n))]
  · rw [Finset.sum_eq_single (S.ring.dual c)]
    · rw [sum_chR S hn c]
      by_cases hp3 : p3 = S.ring.dual c
      · subst hp3
        have key : ∀ (s : (dual S X).blk c) (t : X.blk (S.ring.dual c)),
            assocInvEntry S (dual S X) X (dual S X) c
              ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(S.ring.dual c, c), (ν, x, y)⟩)⟩
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, S.ring.dual c), (chR S hn c, s, t)⟩, j')⟩ *
            ev S hn X ⟨0, hn⟩ ⟨(c, S.ring.dual c), (chR S hn c, s, t)⟩ (unitBlk hn)
            = (if s = j then (if t = x then (if j' = y then
                S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ else 0) else 0) else 0) *
              (if s = (show (dual S X).blk c from t) then S.ev (S.ring.dual c) else 0) := by
          intro s t
          rw [assocInvEntry_apply_matched S (dual S X) X (dual S X) c ⟨0, hn⟩ c
            (unitChL S hn c) c (S.ring.dual c) (chR S hn c) s t j' ⟨0, hn⟩
            (unitChR S hn c) j ν x y]
          rw [ev_snake_entryR S hn X c (chR S hn c)]
          split_ifs <;> ring
        simp only [key]
        rw [Finset.sum_eq_single (a := j)]
        · rw [Finset.sum_eq_single (a := x)]
          · simp only [transport_self]
            split_ifs <;> ring
          · intro t _ ht
            rw [if_neg (fun hc : t = x => ht hc)]
            split_ifs <;> ring
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro s _ hs
          have hz : ∀ (t : X.blk (S.ring.dual c)),
              (if s = j then (if t = x then (if j' = y then
                  S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ else 0) else 0) else 0) *
                (if s = (show (dual S X).blk c from t) then
                  S.ev (S.ring.dual c) else 0) = 0 := by
            intro t
            rw [if_neg hs]
            ring
          simp only [hz, Finset.sum_const_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hz : ∀ (s : (dual S X).blk c) (t : X.blk (S.ring.dual c)),
            assocInvEntry S (dual S X) X (dual S X) c
              ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, c), (ν, x, y)⟩)⟩
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, S.ring.dual c), (chR S hn c, s, t)⟩, j')⟩ *
            ev S hn X ⟨0, hn⟩ ⟨(c, S.ring.dual c), (chR S hn c, s, t)⟩ (unitBlk hn) = 0 := by
          intro s t
          rw [assocInvEntry_zero_b' S (dual S X) X (dual S X) c rfl (Ne.symm hp3)]
          ring
        simp only [hz, Finset.sum_const_zero]
        rw [dif_neg hp3]
    · intro p6 _ hp6
      have hne : p6 ≠ S.ring.dual c := by
        intro hc
        exact hp6 hc
      have hz : ∀ (ν' : Fin (S.ring.N c p6 ⟨0, hn⟩)) (s : (dual S X).blk c)
          (t : X.blk p6),
          assocInvEntry S (dual S X) X (dual S X) c
            ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, c), (ν, x, y)⟩)⟩
            ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(c, p6), (ν', s, t)⟩, j')⟩ *
          ev S hn X ⟨0, hn⟩ ⟨(c, p6), (ν', s, t)⟩ (unitBlk hn) = 0 := by
        intro ν' s t
        rw [ev_apply_of_ne S hn X ⟨0, hn⟩ (p := (c, p6)) hne ν' s t (unitBlk hn)]
        ring
      simp only [hz, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p5 _ hp5
    have hz : ∀ (p6 : Fin n) (ν' : Fin (S.ring.N p5 p6 ⟨0, hn⟩))
        (s : (dual S X).blk p5) (t : X.blk p6),
        assocInvEntry S (dual S X) X (dual S X) c
          ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, c), (ν, x, y)⟩)⟩
          ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(p5, p6), (ν', s, t)⟩, j')⟩ *
        ev S hn X ⟨0, hn⟩ ⟨(p5, p6), (ν', s, t)⟩ (unitBlk hn) = 0 := by
      intro p6 ν' s t
      rw [assocInvEntry_zero_a' S (dual S X) X (dual S X) c hp5]
      ring
    simp only [hz, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The final scalar identity of the right snake. -/
theorem rightSnake_delta (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j j' : (dual S X).blk c) :
    (if j = j' then S.coev (S.ring.dual c) else 0) *
      (S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.ev (S.ring.dual c))
      = if j = j' then 1 else 0 := by
  have hsn : S.coev (S.ring.dual c) * S.ev (S.ring.dual c)
      * S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
    have h := S.snake_right hn (S.ring.dual c)
    rwa [S.ring.dual_dual c] at h
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl, if_pos rfl, ← hsn]
    ring
  · rw [if_neg hjj, if_neg hjj]
    ring

/-- **The double-sum collapse of the right snake.** -/
theorem snake_doubleR (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j j' : (dual S X).blk c) :
    (∑ au : (tensorObj S X (dual S X)).blk ⟨0, hn⟩,
      (coev S hn X ⟨0, hn⟩) (unitBlk hn) au *
        (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
          assocInvEntry S (dual S X) X (dual S X) c
              ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, au)⟩
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, w, j')⟩ *
          (ev S hn X ⟨0, hn⟩) w (unitBlk hn)))
      = if j = j' then 1 else 0 := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (a := S.ring.dual c)]
  · rw [Finset.sum_eq_single (a := c)]
    · rw [sum_chR' S hn c]
      simp only [inner_sumR S hn X c, dif_pos trivial]
      rw [Finset.sum_eq_single (a := (show X.blk (S.ring.dual c) from j))]
      · rw [Finset.sum_eq_single (a := (show (dual S X).blk c from j'))]
        · rw [coev_snake_entryR S hn X c (chR' S hn c) j j']
          simp only [if_true]
          exact rightSnake_delta S hn X c j j'
        · intro y _ hy
          rw [if_neg (fun hc : j' = y => hy hc.symm)]
          ring
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x _ hx
        have hz : ∀ (y : (dual S X).blk c),
            coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(S.ring.dual c, c), (chR' S hn c, x, y)⟩ *
              (if j' = y then (if j = (show (dual S X).blk c from x) then
                S.Finv c (S.ring.dual c) c c ⟨0, hn⟩ ⟨0, hn⟩ * S.ev (S.ring.dual c)
                else 0) else 0) = 0 := by
          intro y
          rw [if_neg (fun hc : j = (show (dual S X).blk c from x) => hx hc.symm)]
          split_ifs <;> ring
        simp only [hz, Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p4 _ hp4
      have hne : S.ring.dual c ≠ S.ring.dual p4 := by
        intro hc
        have h1 := congrArg S.ring.dual hc
        rw [show S.ring.dual (S.ring.dual c) = c from S.ring.dual_dual c,
          show S.ring.dual (S.ring.dual p4) = p4 from S.ring.dual_dual p4] at h1
        exact hp4 h1.symm
      have hz : ∀ (ν : Fin (S.ring.N (S.ring.dual c) p4 ⟨0, hn⟩))
          (x : X.blk (S.ring.dual c)) (y : (dual S X).blk p4),
          coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(S.ring.dual c, p4), (ν, x, y)⟩ *
            (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
              assocInvEntry S (dual S X) X (dual S X) c
                ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(S.ring.dual c, p4), (ν, x, y)⟩)⟩
                ⟨(⟨0, hn⟩, c), (unitChL S hn c, w, j')⟩ *
              (ev S hn X ⟨0, hn⟩) w (unitBlk hn)) = 0 := by
        intro ν x y
        rw [coev_apply_of_ne S hn X ⟨0, hn⟩ (p := (S.ring.dual c, p4)) hne ν x y (unitBlk hn)]
        ring
      simp only [hz, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p3 _ hp3
    have hz : ∀ (p4 : Fin n) (ν : Fin (S.ring.N p3 p4 ⟨0, hn⟩)) (x : X.blk p3)
        (y : (dual S X).blk p4),
        coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(p3, p4), (ν, x, y)⟩ *
          (∑ w : (tensorObj S (dual S X) X).blk ⟨0, hn⟩,
            assocInvEntry S (dual S X) X (dual S X) c
              ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, p4), (ν, x, y)⟩)⟩
              ⟨(⟨0, hn⟩, c), (unitChL S hn c, w, j')⟩ *
            (ev S hn X ⟨0, hn⟩) w (unitBlk hn)) = 0 := by
      intro p4 ν x y
      by_cases hcoev : coev S hn X ⟨0, hn⟩ (unitBlk hn) ⟨(p3, p4), (ν, x, y)⟩ = 0
      · rw [hcoev]
        ring
      · rw [Finset.sum_eq_zero (fun w _ => ?_), mul_zero]
        obtain ⟨⟨p5, p6⟩, ⟨ν', s, t⟩⟩ := w
        by_cases hA : assocInvEntry S (dual S X) X (dual S X) c
            ⟨(c, ⟨0, hn⟩), (unitChR S hn c, j, ⟨(p3, p4), (ν, x, y)⟩)⟩
            ⟨(⟨0, hn⟩, c), (unitChL S hn c, ⟨(p5, p6), (ν', s, t)⟩, j')⟩ = 0
        · rw [hA]
          ring
        · by_cases hev : ev S hn X ⟨0, hn⟩ ⟨(p5, p6), (ν', s, t)⟩ (unitBlk hn) = 0
          · rw [hev]
            ring
          · exfalso
            have h1 : p5 = c := by
              by_contra hc
              exact hA (assocInvEntry_zero_a' S (dual S X) X (dual S X) c hc)
            have hevp : p6 = S.ring.dual p5 := by
              by_contra hc
              exact hev (ev_apply_of_ne S hn X ⟨0, hn⟩ (p := (p5, p6)) hc ν' s t (unitBlk hn))
            have h2 : p6 = p3 := by
              by_contra hc
              exact hA (assocInvEntry_zero_b' S (dual S X) X (dual S X) c h1 hc)
            exact hp3 (by rw [← h2, hevp, h1])
    simp only [hz, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h


theorem unitIdxR_injective (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    {j j' : X.blk c} (h : unitIdxR S hn X c j = unitIdxR S hn X c j') : j = j' := by
  cases h
  rfl

/-- **The entry of the right snake composite.** -/
theorem snakeRight_entry (hn : 0 < n) (X : FusionMat n k) (c : Fin n)
    (j j' : (dual S X).blk c) :
    (whiskerLeft S (dual S X) (coev S hn X) ≫ associatorInv S (dual S X) X (dual S X)
        ≫ whiskerRight S (ev S hn X) (dual S X) ≫ leftUnitor S hn (dual S X)) c
        (unitIdxR S hn (dual S X) c j) j'
      = (rightUnitor S hn (dual S X)) c (unitIdxR S hn (dual S X) c j) j' := by
  have hcomp : (whiskerLeft S (dual S X) (coev S hn X)
        ≫ associatorInv S (dual S X) X (dual S X)
        ≫ whiskerRight S (ev S hn X) (dual S X) ≫ leftUnitor S hn (dual S X)) c
      = tensorHom S (𝟙 (dual S X)) (coev S hn X) c
          * (associatorInv S (dual S X) X (dual S X) c * absorbedEvR S hn X c) := rfl
  rw [hcomp, coevWhisker_mul]
  rw [Finset.sum_congr rfl (fun a _ => by rw [assocInv_mul_absorbedEvR])]
  rw [snake_doubleR, rightUnitor_eq]
  by_cases h : j = j'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (unitIdxR_injective S hn (dual S X) c hc))]

/-- **The right snake equation** (the frozen `FusionMat.SnakeRight`). -/
theorem snakeRight_holds : SnakeRight S := by
  intro hn X
  funext c
  ext r j'
  obtain ⟨j, rfl⟩ := eq_unitIdxR_of S hn (dual S X) c r
  exact snakeRight_entry S hn X c j j'

/-! ## The snakes in the literature (iso) form -/

/-- The right snake in the literature form
`ρ⁻¹ ≫ (1 ⊗ coev) ≫ α⁻¹ ≫ (ev ⊗ 1) ≫ λ = 𝟙`. -/
def SnakeRightIso (S : FusionSystem n k) : Prop :=
  ∀ (hn : 0 < n) (X : FusionMat n k),
    (rightUnitorIso S hn (dual S X)).inv ≫ whiskerLeft S (dual S X) (coev S hn X)
        ≫ associatorInv S (dual S X) X (dual S X) ≫ whiskerRight S (ev S hn X) (dual S X)
        ≫ (leftUnitorIso S hn (dual S X)).hom = 𝟙 (dual S X)

theorem snakeRight_iff_iso : SnakeRight S ↔ SnakeRightIso S := by
  constructor
  · intro h hn X
    have hS := h hn X
    show (rightUnitorIso S hn (dual S X)).inv ≫ _ = 𝟙 (dual S X)
    rw [rightUnitorIso, leftUnitorIso]
    simp only
    rw [hS]
    exact Iso.inv_hom_id (rightUnitorIso S hn (dual S X))
  · intro h hn X
    have hS := h hn X
    rw [rightUnitorIso, leftUnitorIso] at hS
    simp only at hS
    have h2 := congrArg (fun t => rightUnitor S hn (dual S X) ≫ t) hS
    rw [Category.comp_id] at h2
    rw [← Category.assoc, show rightUnitor S hn (dual S X) ≫ rightUnitorInv S hn (dual S X) = 𝟙 _
      from Iso.hom_inv_id (rightUnitorIso S hn (dual S X)), Category.id_comp] at h2
    exact h2

theorem snakeLeftIso_holds (h : SnakeLeft S) : SnakeLeftIso S := (snakeLeft_iff_iso S).mp h

theorem snakeRightIso_holds (h : SnakeRight S) : SnakeRightIso S := (snakeRight_iff_iso S).mp h


end FusionMat
end FusionCategory


open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeRight_entry
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeRight_holds
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeRight_iff_iso
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeLeftIso_holds
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeRightIso_holds


open FusionCategory in
#print axioms FusionCategory.FusionMat.snake_double
open FusionCategory in
#print axioms FusionCategory.FusionMat.snakeLeft_holds
open FusionCategory in
#print axioms FusionCategory.FusionMat.inner_sumR
open FusionCategory in
#print axioms FusionCategory.FusionMat.snake_doubleR
