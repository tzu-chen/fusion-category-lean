import FusionCategory.Pivotal

/-!
# Fibonacci and Ising as skeletal `FusionSystem`s over `ℝ`

This is the file the two examples were blocked on: for a self-dual simple with a
`2 × 2` associator block, the right snake equation only holds with the inverse
associator (see `System.lean`), and the naive reciprocal reading excluded both
categories.  With that corrected:

* `FibonacciSystem : FusionSystem 2 ℝ` — `τ ⊗ τ = 1 ⊕ τ`,
  `F^{τττ}_τ = [[1/φ, 1], [1/φ, -1/φ]]` (a gauge with entries in `ℚ(φ)`),
  `κ = (1, φ)`;
* `IsingSystem : FusionSystem 3 ℝ` — `σ ⊗ σ = 1 ⊕ ψ`, `σ ⊗ ψ = ψ ⊗ σ = σ`,
  `ψ ⊗ ψ = 1`, `F^{σσσ}_σ = (1/√2)[[1,1],[1,-1]]`, the two signs
  `F^{σψσ}_ψ = F^{ψσψ}_σ = -1` (with all `1 × 1` blocks `+1` the pentagon fails),
  `κ = (1, √2, 1)`;
* for both, `p ≡ 1` is a pivotal structure, it is spherical, and
  `dim = FPdim`.  So these are two genuine witnesses of the conclusion of
  ENO 8.23, over `ℝ`, with no hypothesis beyond the axioms.

The finite checks are done *by computation in ℤ*: every entry is encoded as an
integer pair `(p,q)` denoting `(p + q√d)/2` in `ℚ(√d)`, and `zval` maps the pair
to `ℝ`.  `decide` then verifies the pentagon, the two inverse laws and the two
snakes exactly — no `norm_num` over the reals, no `native_decide`.  The file is
therefore expensive to compile (several minutes); build it on its own with
`lake build FusionCategory.Examples.FibonacciIsing` when iterating on it.
-/

open Matrix Finset BigOperators

namespace FusionCategory


/-! ## A kernel-computable model of `ℚ(√d)`

The associators below have entries in `ℚ(√5)`, resp. `ℚ(√2)`.  To check the
finitely many instances of the pentagon/inverse/snake equations *by computation*
(and not by real-number algebra on 19683 cases), each entry is encoded as a pair
of integers `(p, q)` standing for `(p + q√d)/2`, and the equations are checked in
`ℤ`.  `zval` maps such a pair to the real number it denotes; the lemmas below say
`zval` is additive and that it is multiplicative up to the factor `2` that the
denominator `2` costs. -/

namespace ZP

/-- The real number `(p + q√d)/2` denoted by the pair `(p, q)`. -/
noncomputable def zval (s : ℝ) (x : ℤ × ℤ) : ℝ := ((x.1 : ℝ) + (x.2 : ℝ) * s) / 2

/-- Product in `ℤ[√d]`, on pairs: `(p + q√d)(r + t√d) = (pr + dqt) + (pt + qr)√d`. -/
def Zmul (d : ℤ) (x y : ℤ × ℤ) : ℤ × ℤ :=
  (x.1 * y.1 + d * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The pair denoting `1`, i.e. `(2 + 0√d)/2`. -/
def zone : ℤ × ℤ := (2, 0)

/-- The pair denoting `0`. -/
def zzero : ℤ × ℤ := (0, 0)

/-- `2 • x`. -/
def dbl (x : ℤ × ℤ) : ℤ × ℤ := (2 * x.1, 2 * x.2)

/-- `4 • x`. -/
def quad (x : ℤ × ℤ) : ℤ × ℤ := (4 * x.1, 4 * x.2)

/-- Decidable equality of pairs, in a form the kernel reduces. -/
def peq (x y : ℤ × ℤ) : Bool := (x.1 == y.1) && (x.2 == y.2)

variable {s : ℝ} {d : ℤ}

theorem zval_zzero : zval s zzero = 0 := by
  simp [zval, zzero]

theorem zval_zone : zval s zone = 1 := by
  simp only [zval, zone]
  norm_num

theorem zval_add (x y : ℤ × ℤ) : zval s (x + y) = zval s x + zval s y := by
  simp only [zval, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem zval_dbl (x : ℤ × ℤ) : zval s (dbl x) = 2 * zval s x := by
  simp only [zval, dbl]
  push_cast
  ring

theorem zval_quad (x : ℤ × ℤ) : zval s (quad x) = 4 * zval s x := by
  simp only [zval, quad]
  push_cast
  ring

theorem zval_zmul (hs : s * s = (d : ℝ)) (x y : ℤ × ℤ) :
    zval s (Zmul d x y) = 2 * (zval s x * zval s y) := by
  have hd : (d : ℝ) = s * s := hs.symm
  simp only [zval, Zmul, Prod.fst_add, Prod.snd_add]
  push_cast
  rw [hd]
  ring

theorem zval_two (hs : s * s = (d : ℝ)) (x y : ℤ × ℤ) :
    zval s x * zval s y = zval s (Zmul d x y) / 2 := by
  rw [zval_zmul hs]
  ring

theorem zval_three (hs : s * s = (d : ℝ)) (x y z : ℤ × ℤ) :
    zval s x * zval s y * zval s z = zval s (Zmul d (Zmul d x y) z) / 4 := by
  have h1 := zval_zmul hs (Zmul d x y) z
  have h2 := zval_zmul hs x y
  rw [h1, h2]
  ring

theorem zval_of_peq {x y : ℤ × ℤ} (h : peq x y = true) : zval s x = zval s y := by
  simp only [peq, Bool.and_eq_true, beq_iff_eq] at h
  rw [show x = y from Prod.ext h.1 h.2]

end ZP


/-! ## The Fibonacci fusion system -/

namespace Fibonacci

/-- Fusion rules of Fibonacci: `1 ⊗ a = a`, `τ ⊗ τ = 1 ⊕ τ`. -/
def N (a b c : Fin 2) : ℕ :=
  if a = 0 then (if b = c then 1 else 0)
  else if b = 0 then (if a = c then 1 else 0)
  else 1

/-- Every object is self-dual. -/
def dual (i : Fin 2) : Fin 2 := i

/-- The Fibonacci fusion ring. -/
def ring : FusionRing 2 where
  N := N
  dual := dual
  dual_involutive := fun _ => rfl
  dual_zero := fun _ => rfl
  left_unit := by
    intro _ i j
    show N 0 i j = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N]
  right_unit := by
    intro _ i j
    show N i 0 j = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N]
  dual_coeff := by
    intro _ i j
    show N i j 0 = if j = dual i then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N, dual]
  associativity := by
    intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide
  dual_symm := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [N, dual]

theorem mult_free : ∀ i j kk : Fin 2, N i j kk ≤ 1 := by
  intro i j kk
  fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide

/-- `s = √5`, so that `φ = (1 + √5)/2` and `1/φ = (√5 - 1)/2`. -/
noncomputable def s5 : ℝ := Real.sqrt 5

theorem s5_sq : s5 * s5 = ((5 : ℤ) : ℝ) := by
  rw [s5, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The associator entries as pairs `(p, q)` denoting `(p + q√5)/2`:
`1 ↔ (2,0)`, `1/φ ↔ (-1,1)`, `-1/φ ↔ (1,-1)`.
The only non-trivial block is `F^{τττ}_τ = [[1/φ, 1], [1/φ, -1/φ]]` (rows `e`,
columns `f`); every other supported entry is `1`. -/
def Fpair (a b c d e f : Fin 2) : ℤ × ℤ :=
  if 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if e = 0 ∧ f = 0 then (-1, 1)
       else if e = 0 ∧ f = 1 then (2, 0)
       else if e = 1 ∧ f = 0 then (-1, 1)
       else (1, -1))
     else (2, 0))
  else 0

/-- The inverse associator.  `F^{τττ}_τ = [[1/φ, 1], [1/φ, -1/φ]]` is an
involution (`M² = 1`, `det = -1`) but **not** symmetric, so its inverse is `M`
itself, read in the *same* index order; every other block is `1 × 1` with entry
`1`, where the inverse is read in the swapped order.  (The swapped reading of the
whole associator is refuted by `swapped_Finv_comp_ne_one` below.) -/
def FinvPair (a b c d f e : Fin 2) : ℤ × ℤ :=
  if 0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if f = 0 ∧ e = 0 then (-1, 1)
       else if f = 0 ∧ e = 1 then (2, 0)
       else if f = 1 ∧ e = 0 then (-1, 1)
       else (1, -1))
     else (2, 0))
  else 0

noncomputable def F (a b c d e f : Fin 2) : ℝ := ZP.zval s5 (Fpair a b c d e f)

noncomputable def Finv (a b c d f e : Fin 2) : ℝ := ZP.zval s5 (FinvPair a b c d f e)

/-- `ev = 1`, i.e. the pair `(2,0)`. -/
def evPair (_ : Fin 2) : ℤ × ℤ := (2, 0)

/-- `coev 1 = 1`, `coev τ = φ = (1 + √5)/2`. -/
def coevPair (i : Fin 2) : ℤ × ℤ := if i = 0 then (2, 0) else (1, 1)

theorem coevPair_zero : coevPair 0 = ((2 : ℤ), 0) := by
  simp only [coevPair]
  rfl

theorem coevPair_one : coevPair 1 = ((1 : ℤ), 1) := by
  have h : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [coevPair, if_neg h]

/-! ### The pentagon, checked on all `2^9` label tuples in `ℤ[√5]` -/

/-- Left-hand side of the pentagon, in the pair model. -/
def pentL (a b c d e i j r x : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (ZP.Zmul 5 (Fpair a b c x e 0) (Fpair a 0 d r x j)) (Fpair b c d j 0 i)
  + ZP.Zmul 5 (ZP.Zmul 5 (Fpair a b c x e 1) (Fpair a 1 d r x j)) (Fpair b c d j 1 i)

/-- Right-hand side of the pentagon, in the pair model. -/
def pentR (a b c d e i j r x : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (Fpair e c d r x i) (Fpair a b i r e j)

/-- **The pentagon for Fibonacci** on all `2^9 = 512` label tuples, checked by
`decide` in `ℤ[√5]`.  The left-hand side is a triple product and the right-hand
side a double one, so with the `1/2` built into the encoding the identity reads
`LHS = 2 • RHS`. -/
theorem pent_pair : ∀ a b c d e i j r x : Fin 2,
    ZP.peq (pentL a b c d e i j r x) (ZP.dbl (pentR a b c d e i j r x)) = true := by
  decide

theorem pentagon : ∀ a b c d e i j r x : Fin 2,
    (∑ k : Fin 2, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j := by
  intro a b c d e i j r x
  have hL : (∑ k : Fin 2, F a b c x e k * F a k d r x j * F b c d j k i)
      = ZP.zval s5 (pentL a b c d e i j r x) / 4 := by
    simp only [Fin.sum_univ_two, F, ZP.zval_three s5_sq, pentL]
    rw [← add_div, ← ZP.zval_add]
  have hR : F e c d r x i * F a b i r e j
      = ZP.zval s5 (pentR a b c d e i j r x) / 2 := by
    simp only [F, ZP.zval_two s5_sq, pentR]
  have h := ZP.zval_of_peq (s := s5) (pent_pair a b c d e i j r x)
  rw [hL, hR, h, ZP.zval_dbl]
  ring

/-! ### Unit normalisations -/

theorem unitL_pair : ∀ (b c d f : Fin 2), 0 < N b c f →
    ZP.peq (Fpair 0 b c d b f) (if d = f then ZP.zone else ZP.zzero) = true := by
  decide

theorem F_unit_left : ∀ (hn : 0 < 2) (b c d f : Fin 2), 0 < N b c f →
    F 0 b c d b f = if d = f then 1 else 0 := by
  intro _ b c d f hbcf
  have h := ZP.zval_of_peq (s := s5) (unitL_pair b c d f hbcf)
  simp only [F]
  rw [h]
  by_cases hdf : d = f
  · simp [hdf, ZP.zval_zone]
  · simp [hdf, ZP.zval_zzero]

theorem unitR_pair : ∀ (a b d e : Fin 2), 0 < N a b e →
    ZP.peq (Fpair a b 0 d e b) (if d = e then ZP.zone else ZP.zzero) = true := by
  decide

theorem F_unit_right : ∀ (hn : 0 < 2) (a b d e : Fin 2), 0 < N a b e →
    F a b 0 d e b = if d = e then 1 else 0 := by
  intro _ a b d e habc
  have h := ZP.zval_of_peq (s := s5) (unitR_pair a b d e habc)
  simp only [F]
  rw [h]
  by_cases hde : d = e
  · simp [hde, ZP.zval_zone]
  · simp [hde, ZP.zval_zzero]

/-! ### The two inverse laws -/

theorem finvComp_pair : ∀ a b c d f' f : Fin 2,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    ZP.peq (ZP.Zmul 5 (FinvPair a b c d f' 0) (Fpair a b c d 0 f)
          + ZP.Zmul 5 (FinvPair a b c d f' 1) (Fpair a b c d 1 f))
      (if f' = f then ZP.dbl ZP.zone else ZP.zzero) = true := by
  decide

theorem Finv_comp : ∀ a b c d f' f : Fin 2,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    (∑ e : Fin 2, Finv a b c d f' e * F a b c d e f) = if f' = f then 1 else 0 := by
  intro a b c d f' f h1 h2 h3 h4
  have hp := ZP.zval_of_peq (s := s5) (finvComp_pair a b c d f' f h1 h2 h3 h4)
  have hL : (∑ e : Fin 2, Finv a b c d f' e * F a b c d e f)
      = ZP.zval s5 (ZP.Zmul 5 (FinvPair a b c d f' 0) (Fpair a b c d 0 f)
          + ZP.Zmul 5 (FinvPair a b c d f' 1) (Fpair a b c d 1 f)) / 2 := by
    simp only [Fin.sum_univ_two, Finv, F, ZP.zval_two s5_sq]
    rw [← add_div, ← ZP.zval_add]
  have hR : (if f' = f then (1 : ℝ) else 0)
      = ZP.zval s5 (if f' = f then ZP.dbl ZP.zone else ZP.zzero) / 2 := by
    by_cases hff : f' = f
    · simp [hff, ZP.zval_dbl, ZP.zval_zone]
    · simp [hff, ZP.zval_zzero]
  rw [hL, hR, hp]

theorem compInv_pair : ∀ a b c d e' e : Fin 2,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    ZP.peq (ZP.Zmul 5 (FinvPair a b c d 0 e') (Fpair a b c d e 0)
          + ZP.Zmul 5 (FinvPair a b c d 1 e') (Fpair a b c d e 1))
      (if e' = e then ZP.dbl ZP.zone else ZP.zzero) = true := by
  decide

theorem F_comp_inv : ∀ a b c d e' e : Fin 2,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    (∑ f : Fin 2, Finv a b c d f e' * F a b c d e f) = if e' = e then 1 else 0 := by
  intro a b c d e' e h1 h2 h3 h4
  have hp := ZP.zval_of_peq (s := s5) (compInv_pair a b c d e' e h1 h2 h3 h4)
  have hL : (∑ f : Fin 2, Finv a b c d f e' * F a b c d e f)
      = ZP.zval s5 (ZP.Zmul 5 (FinvPair a b c d 0 e') (Fpair a b c d e 0)
          + ZP.Zmul 5 (FinvPair a b c d 1 e') (Fpair a b c d e 1)) / 2 := by
    simp only [Fin.sum_univ_two, Finv, F, ZP.zval_two s5_sq]
    rw [← add_div, ← ZP.zval_add]
  have hR : (if e' = e then (1 : ℝ) else 0)
      = ZP.zval s5 (if e' = e then ZP.dbl ZP.zone else ZP.zzero) / 2 := by
    by_cases h : e' = e
    · simp [h, ZP.zval_dbl, ZP.zval_zone]
    · simp [h, ZP.zval_zzero]
  rw [hL, hR, hp]

/-! ### The obstruction to the "swapped" inverse associator

The task statement proposes `Finv a b c d f e := F a b c d e f`, i.e. the
*transposed* block.  At `(a,b,c,d) = (τ,τ,τ,τ)` the block is
`M = [[1/φ, 1], [1/φ, -1/φ]]`, which satisfies `M² = 1` and `det M = -1` but is
not symmetric, so `MᵀM ≠ 1`; hence `Finv_comp` fails at `(f',f) = (0,0)`. -/

theorem swapped_Finv_comp_ne_one :
    (∑ e : Fin 2, F 1 1 1 1 e 0 * F 1 1 1 1 e 0) ≠ 1 := by
  have h0 : F 1 1 1 1 0 0 = (Real.sqrt 5 - 1) / 2 := by
    simp only [F, s5, Fpair, N, ZP.zval]
    norm_num
    ring
  have h1 : F 1 1 1 1 1 0 = (Real.sqrt 5 - 1) / 2 := by
    simp only [F, s5, Fpair, N, ZP.zval]
    norm_num
    ring
  rw [Fin.sum_univ_two, h0, h1]
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  intro h
  nlinarith [hs]

/-! ### The snake equations -/

theorem snakeL_pair : ∀ i : Fin 2,
    ZP.peq (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (Fpair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

theorem snakeR_pair : ∀ i : Fin 2,
    ZP.peq (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (FinvPair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

theorem snake_left : ∀ (hn : 0 < 2) (i : Fin 2),
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      * F i (dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro _ i
  have hp := ZP.zval_of_peq (s := s5) (snakeL_pair i)
  have hL : ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
        * ZP.zval s5 (Fpair i i i i 0 0)
      = ZP.zval s5 (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (Fpair i i i i 0 0)) / 4 :=
    ZP.zval_three s5_sq _ _ _
  show ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i) * ZP.zval s5 (Fpair i i i i 0 0) = 1
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

theorem snake_right : ∀ (hn : 0 < 2) (i : Fin 2),
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      * Finv (dual i) i (dual i) (dual i) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro _ i
  have hp := ZP.zval_of_peq (s := s5) (snakeR_pair i)
  have hL : ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
        * ZP.zval s5 (FinvPair i i i i 0 0)
      = ZP.zval s5 (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (FinvPair i i i i 0 0)) / 4 :=
    ZP.zval_three s5_sq _ _ _
  show ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i) * ZP.zval s5 (FinvPair i i i i 0 0) = 1
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

/-! ### The system -/

noncomputable def system : FusionSystem 2 ℝ where
  ring := ring
  mult_free := mult_free
  F := F
  F_support := by
    intro a b c d e f h
    have h' : ¬ (0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d) := h
    simp only [F, Fpair, if_neg h']
    simp [ZP.zval]
  pentagon := pentagon
  F_unit_left := F_unit_left
  F_unit_right := F_unit_right
  Finv := Finv
  Finv_support := by
    intro a b c d f e h
    have h' : ¬ (0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d) := h
    simp only [Finv, FinvPair, if_neg h']
    simp [ZP.zval]
  Finv_comp := Finv_comp
  F_comp_inv := F_comp_inv
  ev := fun i => ZP.zval s5 (evPair i)
  coev := fun i => ZP.zval s5 (coevPair i)
  ev_ne_zero := by
    intro i
    simp only [evPair, ZP.zval]
    norm_num
  coev_ne_zero := by
    intro i
    have hpos : 0 < ZP.zval s5 (coevPair i) := by
      have hs : 0 ≤ s5 := by rw [s5]; exact Real.sqrt_nonneg 5
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with h | h
      · rw [h, coevPair_zero]
        simp only [ZP.zval]
        norm_num
      · rw [h, coevPair_one]
        simp only [ZP.zval]
        linarith
    exact ne_of_gt hpos
  snake_left := snake_left
  snake_right := snake_right
  J := fun _ _ _ => 1
  J_ne_zero := fun _ _ _ _ => one_ne_zero
  J_unit_left := fun _ _ => rfl
  J_unit_right := fun _ _ => rfl
  J_dual := fun _ _ => rfl
  ev_dual := fun i => rfl
  J_coherent := by
    intro a b c d e f _ _ _ _
    simp

/-! ### `kappa`, the pivotal structure, sphericality and dimensions -/

/-- `κ = coev · ev` is `1` on the unit and `φ = (1 + √5)/2` on `τ`. -/
theorem kappa_val : ∀ i : Fin 2,
    system.kappa i = if i = 0 then 1 else (1 + Real.sqrt 5) / 2 := by
  intro i
  show ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      = if i = 0 then 1 else (1 + Real.sqrt 5) / 2
  rw [ZP.zval_two (s := s5) (d := 5) s5_sq]
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with h | h
  · rw [h, coevPair_zero, if_pos rfl]
    simp only [evPair, ZP.Zmul, ZP.zval]
    norm_num
  · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    rw [h, coevPair_one, if_neg h10]
    simp only [evPair, ZP.Zmul, ZP.zval, s5]
    ring

/-- The trivial pivotal structure `p = 1` (possible because `J ≡ 1`). -/
noncomputable def pivotal : PivotalStructure system where
  p := fun _ => 1
  p_unit := fun _ => rfl
  p_mon := by
    intro i j kk _
    simp [system]

theorem spherical : pivotal.IsSpherical :=
  PivotalStructure.spherical_of_selfdual pivotal (by intro i; rfl)

/-- With `p = 1` the categorical dimension is `κ`: `1` and `φ`. -/
theorem dim_val : ∀ i : Fin 2,
    dim pivotal i = if i = 0 then 1 else (1 + Real.sqrt 5) / 2 := by
  intro i
  have h : dim pivotal i = system.kappa i := by
    rw [PivotalStructure.dim_eq]
    simp only [pivotal, PivotalStructure.pVal, Units.val_one, one_mul]
  rw [h, kappa_val]

/-- The pivotal dimensions are the Perron–Frobenius dimensions `1, φ`. -/
theorem dim_val_explicit :
    dim pivotal 0 = 1 ∧ dim pivotal 1 = (1 + Real.sqrt 5) / 2 := by
  constructor <;> rw [dim_val] <;> simp

end Fibonacci

/-! ## The Ising fusion system -/

namespace Ising

/-- Fusion rules: `1 ⊗ a = a`, `σ ⊗ σ = 1 ⊕ ψ`, `σ ⊗ ψ = ψ ⊗ σ = σ`, `ψ ⊗ ψ = 1`. -/
def N (a b c : Fin 3) : ℕ :=
  if a = 0 then (if b = c then 1 else 0)
  else if b = 0 then (if a = c then 1 else 0)
  else if a = 1 ∧ b = 1 then (if c = 0 ∨ c = 2 then 1 else 0)
  else if a = 1 ∧ b = 2 then (if c = 1 then 1 else 0)
  else if a = 2 ∧ b = 1 then (if c = 1 then 1 else 0)
  else if a = 2 ∧ b = 2 then (if c = 0 then 1 else 0)
  else 0

/-- Every object is self-dual. -/
def dual (i : Fin 3) : Fin 3 := i

/-- The Ising fusion ring (`0 = 1`, `1 = σ`, `2 = ψ`). -/
def ring : FusionRing 3 where
  N := N
  dual := dual
  dual_involutive := fun _ => rfl
  dual_zero := fun _ => rfl
  left_unit := by
    intro _ i j
    show N 0 i j = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N]
  right_unit := by
    intro _ i j
    show N i 0 j = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N]
  dual_coeff := by
    intro _ i j
    show N i j 0 = if j = dual i then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [N, dual]
  associativity := by
    intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide
  dual_symm := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [N, dual]

theorem mult_free : ∀ i j kk : Fin 3, N i j kk ≤ 1 := by
  intro i j kk
  fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide

/-- `s = √2`. -/
noncomputable def s2 : ℝ := Real.sqrt 2

theorem s2_sq : s2 * s2 = ((2 : ℤ) : ℝ) := by
  rw [s2, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The associator entries as pairs `(p, q)` denoting `(p + q√2)/2`: `1 ↔ (2,0)`,
`1/√2 ↔ (0,1)`, `-1/√2 ↔ (0,-1)`, `-1 ↔ (-2,0)`.

The only non-trivial block is `F^{σσσ}_σ = (1/√2) [[1, 1], [1, -1]]` in the
channel basis `(1, ψ) = (0, 2)` of `σ ⊗ σ`; it is a symmetric involution.  All
other supported entries are `1` except the two `1 × 1` blocks
`F^{σψσ}_ψ = -1` and `F^{ψσψ}_σ = -1` (at `(e,f) = (σ,σ)`). -/
def Fpair (a b c d e f : Fin 3) : ℤ × ℤ :=
  if 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if (e = 0 ∧ f = 0) ∨ (e = 0 ∧ f = 2) ∨ (e = 2 ∧ f = 0) then (0, 1) else (0, -1))
     else if a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2 ∧ e = 1 ∧ f = 1 then (-2, 0)
     else if a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1 ∧ e = 1 ∧ f = 1 then (-2, 0)
     else (2, 0))
  else 0

/-- The inverse associator: the `σσσσ` block is a symmetric involution, so `Finv`
reads every block in the swapped order. -/
def FinvPair (a b c d f e : Fin 3) : ℤ × ℤ :=
  if 0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if (f = 0 ∧ e = 0) ∨ (f = 0 ∧ e = 2) ∨ (f = 2 ∧ e = 0) then (0, 1) else (0, -1))
     else if a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2 ∧ f = 1 ∧ e = 1 then (-2, 0)
     else if a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1 ∧ f = 1 ∧ e = 1 then (-2, 0)
     else (2, 0))
  else 0

noncomputable def F (a b c d e f : Fin 3) : ℝ := ZP.zval s2 (Fpair a b c d e f)

noncomputable def Finv (a b c d f e : Fin 3) : ℝ := ZP.zval s2 (FinvPair a b c d f e)

/-- `ev = 1`. -/
def evPair (_ : Fin 3) : ℤ × ℤ := (2, 0)

/-- `coev 1 = coev ψ = 1`, `coev σ = √2`. -/
def coevPair (i : Fin 3) : ℤ × ℤ := if i = 1 then (0, 2) else (2, 0)

theorem coevPair_zero : coevPair 0 = ((2 : ℤ), 0) := by
  have h : ¬ ((0 : Fin 3) = 1) := by decide
  simp only [coevPair, if_neg h]

theorem coevPair_one : coevPair 1 = ((0 : ℤ), 2) := by
  simp only [coevPair]
  rfl

theorem coevPair_two : coevPair 2 = ((2 : ℤ), 0) := by
  have h : ¬ ((2 : Fin 3) = 1) := by decide
  simp only [coevPair, if_neg h]

/-! ### The pentagon, checked on all `3^9 = 19683` label tuples in `ℤ[√2]` -/

/-- Left-hand side of the pentagon, in the pair model. -/
def pentL (a b c d e i j r x : Fin 3) : ℤ × ℤ :=
  ZP.Zmul 2 (ZP.Zmul 2 (Fpair a b c x e 0) (Fpair a 0 d r x j)) (Fpair b c d j 0 i)
  + ZP.Zmul 2 (ZP.Zmul 2 (Fpair a b c x e 1) (Fpair a 1 d r x j)) (Fpair b c d j 1 i)
  + ZP.Zmul 2 (ZP.Zmul 2 (Fpair a b c x e 2) (Fpair a 2 d r x j)) (Fpair b c d j 2 i)

/-- Right-hand side of the pentagon, in the pair model. -/
def pentR (a b c d e i j r x : Fin 3) : ℤ × ℤ :=
  ZP.Zmul 2 (Fpair e c d r x i) (Fpair a b i r e j)

/-- **The pentagon for Ising** on all `3^9 = 19683` label tuples, checked by
`decide` in `ℤ[√2]`.  The universal statement is split into the nine slices
`a = i`, `b = j` (3^7 = 2187 tuples each) to keep the kernel reduction small. -/
theorem pent_pair_00 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 0 0 c d e i j r x) (ZP.dbl (pentR 0 0 c d e i j r x)) = true := by
  decide
theorem pent_pair_01 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 0 1 c d e i j r x) (ZP.dbl (pentR 0 1 c d e i j r x)) = true := by
  decide
theorem pent_pair_02 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 0 2 c d e i j r x) (ZP.dbl (pentR 0 2 c d e i j r x)) = true := by
  decide
theorem pent_pair_10 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 1 0 c d e i j r x) (ZP.dbl (pentR 1 0 c d e i j r x)) = true := by
  decide
theorem pent_pair_11 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 1 1 c d e i j r x) (ZP.dbl (pentR 1 1 c d e i j r x)) = true := by
  decide
theorem pent_pair_12 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 1 2 c d e i j r x) (ZP.dbl (pentR 1 2 c d e i j r x)) = true := by
  decide
theorem pent_pair_20 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 2 0 c d e i j r x) (ZP.dbl (pentR 2 0 c d e i j r x)) = true := by
  decide
theorem pent_pair_21 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 2 1 c d e i j r x) (ZP.dbl (pentR 2 1 c d e i j r x)) = true := by
  decide
theorem pent_pair_22 : ∀ c d e i j r x : Fin 3,
    ZP.peq (pentL 2 2 c d e i j r x) (ZP.dbl (pentR 2 2 c d e i j r x)) = true := by
  decide

theorem pent_pair : ∀ a b c d e i j r x : Fin 3,
    ZP.peq (pentL a b c d e i j r x) (ZP.dbl (pentR a b c d e i j r x)) = true := by
  intro a b
  fin_cases a <;> fin_cases b
  exact pent_pair_00
  exact pent_pair_01
  exact pent_pair_02
  exact pent_pair_10
  exact pent_pair_11
  exact pent_pair_12
  exact pent_pair_20
  exact pent_pair_21
  exact pent_pair_22

theorem pentagon : ∀ a b c d e i j r x : Fin 3,
    (∑ k : Fin 3, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j := by
  intro a b c d e i j r x
  have hL : (∑ k : Fin 3, F a b c x e k * F a k d r x j * F b c d j k i)
      = ZP.zval s2 (pentL a b c d e i j r x) / 4 := by
    simp only [Fin.sum_univ_three, F, ZP.zval_three s2_sq, pentL]
    rw [← add_div, ← add_div, ← ZP.zval_add, ← ZP.zval_add]
  have hR : F e c d r x i * F a b i r e j
      = ZP.zval s2 (pentR a b c d e i j r x) / 2 := by
    simp only [F, ZP.zval_two s2_sq, pentR]
  have h := ZP.zval_of_peq (s := s2) (pent_pair a b c d e i j r x)
  rw [hL, hR, h, ZP.zval_dbl]
  ring

/-! ### Unit normalisations -/

theorem unitL_pair : ∀ (b c d f : Fin 3), 0 < N b c f →
    ZP.peq (Fpair 0 b c d b f) (if d = f then ZP.zone else ZP.zzero) = true := by
  decide

theorem F_unit_left : ∀ (hn : 0 < 3) (b c d f : Fin 3), 0 < N b c f →
    F 0 b c d b f = if d = f then 1 else 0 := by
  intro _ b c d f hbcf
  have h := ZP.zval_of_peq (s := s2) (unitL_pair b c d f hbcf)
  simp only [F]
  rw [h]
  by_cases hdf : d = f
  · simp [hdf, ZP.zval_zone]
  · simp [hdf, ZP.zval_zzero]

theorem unitR_pair : ∀ (a b d e : Fin 3), 0 < N a b e →
    ZP.peq (Fpair a b 0 d e b) (if d = e then ZP.zone else ZP.zzero) = true := by
  decide

theorem F_unit_right : ∀ (hn : 0 < 3) (a b d e : Fin 3), 0 < N a b e →
    F a b 0 d e b = if d = e then 1 else 0 := by
  intro _ a b d e habc
  have h := ZP.zval_of_peq (s := s2) (unitR_pair a b d e habc)
  simp only [F]
  rw [h]
  by_cases hde : d = e
  · simp [hde, ZP.zval_zone]
  · simp [hde, ZP.zval_zzero]

/-! ### The two inverse laws -/

theorem finvComp_pair : ∀ a b c d f' f : Fin 3,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    ZP.peq (ZP.Zmul 2 (FinvPair a b c d f' 0) (Fpair a b c d 0 f)
          + ZP.Zmul 2 (FinvPair a b c d f' 1) (Fpair a b c d 1 f)
          + ZP.Zmul 2 (FinvPair a b c d f' 2) (Fpair a b c d 2 f))
      (if f' = f then ZP.dbl ZP.zone else ZP.zzero) = true := by
  decide

theorem Finv_comp : ∀ a b c d f' f : Fin 3,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    (∑ e : Fin 3, Finv a b c d f' e * F a b c d e f) = if f' = f then 1 else 0 := by
  intro a b c d f' f h1 h2 h3 h4
  have hp := ZP.zval_of_peq (s := s2) (finvComp_pair a b c d f' f h1 h2 h3 h4)
  have hL : (∑ e : Fin 3, Finv a b c d f' e * F a b c d e f)
      = ZP.zval s2 (ZP.Zmul 2 (FinvPair a b c d f' 0) (Fpair a b c d 0 f)
          + ZP.Zmul 2 (FinvPair a b c d f' 1) (Fpair a b c d 1 f)
          + ZP.Zmul 2 (FinvPair a b c d f' 2) (Fpair a b c d 2 f)) / 2 := by
    simp only [Fin.sum_univ_three, Finv, F, ZP.zval_two s2_sq]
    rw [← add_div, ← add_div, ← ZP.zval_add, ← ZP.zval_add]
  have hR : (if f' = f then (1 : ℝ) else 0)
      = ZP.zval s2 (if f' = f then ZP.dbl ZP.zone else ZP.zzero) / 2 := by
    by_cases hff : f' = f
    · simp [hff, ZP.zval_dbl, ZP.zval_zone]
    · simp [hff, ZP.zval_zzero]
  rw [hL, hR, hp]

theorem compInv_pair : ∀ a b c d e' e : Fin 3,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    ZP.peq (ZP.Zmul 2 (FinvPair a b c d 0 e') (Fpair a b c d e 0)
          + ZP.Zmul 2 (FinvPair a b c d 1 e') (Fpair a b c d e 1)
          + ZP.Zmul 2 (FinvPair a b c d 2 e') (Fpair a b c d e 2))
      (if e' = e then ZP.dbl ZP.zone else ZP.zzero) = true := by
  decide

theorem F_comp_inv : ∀ a b c d e' e : Fin 3,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    (∑ f : Fin 3, Finv a b c d f e' * F a b c d e f) = if e' = e then 1 else 0 := by
  intro a b c d e' e h1 h2 h3 h4
  have hp := ZP.zval_of_peq (s := s2) (compInv_pair a b c d e' e h1 h2 h3 h4)
  have hL : (∑ f : Fin 3, Finv a b c d f e' * F a b c d e f)
      = ZP.zval s2 (ZP.Zmul 2 (FinvPair a b c d 0 e') (Fpair a b c d e 0)
          + ZP.Zmul 2 (FinvPair a b c d 1 e') (Fpair a b c d e 1)
          + ZP.Zmul 2 (FinvPair a b c d 2 e') (Fpair a b c d e 2)) / 2 := by
    simp only [Fin.sum_univ_three, Finv, F, ZP.zval_two s2_sq]
    rw [← add_div, ← add_div, ← ZP.zval_add, ← ZP.zval_add]
  have hR : (if e' = e then (1 : ℝ) else 0)
      = ZP.zval s2 (if e' = e then ZP.dbl ZP.zone else ZP.zzero) / 2 := by
    by_cases h : e' = e
    · simp [h, ZP.zval_dbl, ZP.zval_zone]
    · simp [h, ZP.zval_zzero]
  rw [hL, hR, hp]

/-! ### The snake equations -/

theorem snakeL_pair : ∀ i : Fin 3,
    ZP.peq (ZP.Zmul 2 (ZP.Zmul 2 (coevPair i) (evPair i)) (Fpair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

theorem snakeR_pair : ∀ i : Fin 3,
    ZP.peq (ZP.Zmul 2 (ZP.Zmul 2 (coevPair i) (evPair i)) (FinvPair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

theorem snake_left : ∀ (hn : 0 < 3) (i : Fin 3),
    ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i)
      * F i (dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro _ i
  have hp := ZP.zval_of_peq (s := s2) (snakeL_pair i)
  have hL : ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i)
        * ZP.zval s2 (Fpair i i i i 0 0)
      = ZP.zval s2 (ZP.Zmul 2 (ZP.Zmul 2 (coevPair i) (evPair i)) (Fpair i i i i 0 0)) / 4 :=
    ZP.zval_three s2_sq _ _ _
  show ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i) * ZP.zval s2 (Fpair i i i i 0 0) = 1
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

theorem snake_right : ∀ (hn : 0 < 3) (i : Fin 3),
    ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i)
      * Finv (dual i) i (dual i) (dual i) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro _ i
  have hp := ZP.zval_of_peq (s := s2) (snakeR_pair i)
  have hL : ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i)
        * ZP.zval s2 (FinvPair i i i i 0 0)
      = ZP.zval s2 (ZP.Zmul 2 (ZP.Zmul 2 (coevPair i) (evPair i)) (FinvPair i i i i 0 0)) / 4 :=
    ZP.zval_three s2_sq _ _ _
  show ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i) * ZP.zval s2 (FinvPair i i i i 0 0) = 1
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

/-! ### The system -/

noncomputable def system : FusionSystem 3 ℝ where
  ring := ring
  mult_free := mult_free
  F := F
  F_support := by
    intro a b c d e f h
    have h' : ¬ (0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d) := h
    simp only [F, Fpair, if_neg h']
    simp [ZP.zval]
  pentagon := pentagon
  F_unit_left := F_unit_left
  F_unit_right := F_unit_right
  Finv := Finv
  Finv_support := by
    intro a b c d f e h
    have h' : ¬ (0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d) := h
    simp only [Finv, FinvPair, if_neg h']
    simp [ZP.zval]
  Finv_comp := Finv_comp
  F_comp_inv := F_comp_inv
  ev := fun i => ZP.zval s2 (evPair i)
  coev := fun i => ZP.zval s2 (coevPair i)
  ev_ne_zero := by
    intro i
    simp only [evPair, ZP.zval]
    norm_num
  coev_ne_zero := by
    intro i
    have hpos : 0 < ZP.zval s2 (coevPair i) := by
      have hs : 0 < s2 := by rw [s2]; exact Real.sqrt_pos.2 (by norm_num)
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with h | h | h
      · rw [h, coevPair_zero]
        simp only [ZP.zval]
        norm_num
      · rw [h, coevPair_one]
        simp only [ZP.zval]
        linarith
      · rw [h, coevPair_two]
        simp only [ZP.zval]
        norm_num
    exact ne_of_gt hpos
  snake_left := snake_left
  snake_right := snake_right
  J := fun _ _ _ => 1
  J_ne_zero := fun _ _ _ _ => one_ne_zero
  J_unit_left := fun _ _ => rfl
  J_unit_right := fun _ _ => rfl
  J_dual := fun _ _ => rfl
  ev_dual := fun i => rfl
  J_coherent := by
    intro a b c d e f _ _ _ _
    simp

/-! ### `kappa`, the pivotal structure, sphericality and dimensions -/

/-- `κ = coev · ev` is `1, √2, 1` on `1, σ, ψ`. -/
theorem kappa_val : ∀ i : Fin 3,
    system.kappa i = if i = 1 then Real.sqrt 2 else 1 := by
  intro i
  show ZP.zval s2 (coevPair i) * ZP.zval s2 (evPair i)
      = if i = 1 then Real.sqrt 2 else 1
  rw [ZP.zval_two (s := s2) (d := 2) s2_sq]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with h | h | h
  · rw [h, coevPair_zero]
    have h10 : ¬ ((0 : Fin 3) = 1) := by decide
    rw [if_neg h10]
    simp only [evPair, ZP.Zmul, ZP.zval]
    norm_num
  · rw [h, coevPair_one, if_pos rfl]
    simp only [evPair, ZP.Zmul, ZP.zval, s2]
    ring
  · rw [h, coevPair_two]
    have h21 : ¬ ((2 : Fin 3) = 1) := by decide
    rw [if_neg h21]
    simp only [evPair, ZP.Zmul, ZP.zval]
    norm_num

/-- The trivial pivotal structure `p = 1`. -/
noncomputable def pivotal : PivotalStructure system where
  p := fun _ => 1
  p_unit := fun _ => rfl
  p_mon := by
    intro i j kk _
    simp [system]

theorem spherical : pivotal.IsSpherical :=
  PivotalStructure.spherical_of_selfdual pivotal (by intro i; rfl)

/-- With `p = 1` the dimension is `κ`: `1, √2, 1`. -/
theorem dim_val : ∀ i : Fin 3,
    dim pivotal i = if i = 1 then Real.sqrt 2 else 1 := by
  intro i
  have h : dim pivotal i = system.kappa i := by
    rw [PivotalStructure.dim_eq]
    simp only [pivotal, PivotalStructure.pVal, Units.val_one, one_mul]
  rw [h, kappa_val]

/-- The pivotal dimensions are the Perron–Frobenius dimensions `1, √2, 1`. -/
theorem dim_val_explicit :
    dim pivotal 0 = 1 ∧ dim pivotal 1 = Real.sqrt 2 ∧ dim pivotal 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [dim_val] <;> simp

end Ising

/-! ## The two systems, under the names requested

`FibonacciSystem : FusionSystem 2 ℝ` and `IsingSystem : FusionSystem 3 ℝ`, with
their pivotal structures, the values of `κ`, sphericality, and
`dim = FPdim`. -/

/-- The Fibonacci fusion system over `ℝ`. -/
noncomputable abbrev FibonacciSystem : FusionSystem 2 ℝ := Fibonacci.system

/-- The Ising fusion system over `ℝ`. -/
noncomputable abbrev IsingSystem : FusionSystem 3 ℝ := Ising.system

/-- The trivial pivotal structure of the Fibonacci system. -/
noncomputable abbrev FibonacciPivotal : PivotalStructure FibonacciSystem := Fibonacci.pivotal

/-- The trivial pivotal structure of the Ising system. -/
noncomputable abbrev IsingPivotal : PivotalStructure IsingSystem := Ising.pivotal

/-- Perron–Frobenius dimensions of Fibonacci: `1, φ`. -/
noncomputable abbrev FPdimFibonacci : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else (1 + Real.sqrt 5) / 2

/-- Perron–Frobenius dimensions of Ising: `1, √2, 1`. -/
noncomputable abbrev FPdimIsing : Fin 3 → ℝ :=
  fun i => if i = 1 then Real.sqrt 2 else 1

/-- `κ = coev · ev` of the Fibonacci system is `1, φ`. -/
theorem FibonacciSystem_kappa (i : Fin 2) : FibonacciSystem.kappa i = FPdimFibonacci i :=
  Fibonacci.kappa_val i

/-- `κ = coev · ev` of the Ising system is `1, √2, 1`. -/
theorem IsingSystem_kappa (i : Fin 3) : IsingSystem.kappa i = FPdimIsing i :=
  Ising.kappa_val i

/-- **The Fibonacci system is spherical** for its trivial pivotal structure. -/
theorem FibonacciSystem_spherical : FibonacciPivotal.IsSpherical := Fibonacci.spherical

/-- **The Ising system is spherical** for its trivial pivotal structure. -/
theorem IsingSystem_spherical : IsingPivotal.IsSpherical := Ising.spherical

/-- `dim = FPdim` for Fibonacci: `1` and `φ`. -/
theorem FibonacciSystem_dim (i : Fin 2) : dim FibonacciPivotal i = FPdimFibonacci i :=
  Fibonacci.dim_val i

/-- `dim = FPdim` for Ising: `1`, `√2`, `1`. -/
theorem IsingSystem_dim (i : Fin 3) : dim IsingPivotal i = FPdimIsing i :=
  Ising.dim_val i

theorem FibonacciSystem_dim_explicit :
    dim FibonacciPivotal 0 = 1 ∧ dim FibonacciPivotal 1 = (1 + Real.sqrt 5) / 2 :=
  Fibonacci.dim_val_explicit

theorem IsingSystem_dim_explicit :
    dim IsingPivotal 0 = 1 ∧ dim IsingPivotal 1 = Real.sqrt 2 ∧ dim IsingPivotal 2 = 1 :=
  Ising.dim_val_explicit

/-- The task statement's Ising block indexing `(e,f) ∈ {(1,1),(1,2),(2,1)}` is off
support: `σ ⊗ σ = 1 ⊕ ψ` does not contain `σ`, and `F_support` forces those
entries to vanish.  (The correct channel basis of `σ ⊗ σ` is `(1, ψ) = (0, 2)`.) -/
theorem ising_sigma_not_mem_sigma_tensor_sigma : Ising.N 1 1 1 = 0 := rfl

/-- Likewise `F σ ψ σ ψ ψ ψ` is off support: `σ ⊗ ψ = σ` does not contain `ψ`. -/
theorem ising_psi_not_mem_sigma_tensor_psi : Ising.N 1 2 2 = 0 := rfl

end FusionCategory
