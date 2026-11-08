import FusionCategory.Coboundary
import FusionCategory.System
import FusionCategory.Examples.Fibonacci
import FusionCategory.Examples.FibonacciIsing
import FusionCategory.DimMult

/-!
# Yang-Lee as a skeletal `FusionSystem` over `ℝ`, and `ENO823` refuted on it

Yang-Lee is the Galois conjugate of Fibonacci: same fusion ring
(`τ ⊗ τ = 1 ⊕ τ`, `FPdim = (1, φ)`), but the associator block

    F^{τττ}_τ = [[-φ, 1], [-φ, φ]]        (instead of [[1/φ, 1], [1/φ, -1/φ]])

which is again an involution with determinant `-1`.  Both snakes hold for
`ev ≡ 1`, `coev_τ = -1/φ`, giving `κ = (1, -1/φ)`.

The point of the example: on the coevaluation channel `(i, i*; 1)` the axiom
`J^{1}_{i i*} = 1` is used, so (K) there reads

    κ_i κ_{i*} = FPdim_i² ,

with no `J` in it.  For Yang-Lee that is `1/φ²` against `φ²`, so **no** choice
of twist makes (K) hold.  Consequently `ENO823` — "there is a spherical pivotal
structure with `dim = FPdim`" — is **false** for this system, by
`dim_eq_twistNorm`: a pivotal structure with `dim = FPdim` would give
`1 = twistNorm 1 1 0 · φ² = φ⁴`.

So the target as stated in `PseudoUnitary.lean` cannot be proved from the axioms
of `FusionSystem`; pseudo-unitarity has to be a hypothesis.  Yang-Lee is not
pseudo-unitary (its unique dimension is negative), and it is the smallest
witness: two labels, `2^9` pentagon tuples.

The checks are the same as in `Examples/FibonacciIsing.lean`: entries are integer
pairs `(p, q)` meaning `(p + q√5)/2`, and `decide` verifies the pentagon, the
unit laws, the two inverse laws and both snakes exactly in `ℤ` — no `norm_num`
over the reals and no `native_decide`.

## What the system does satisfy: the multiplicity hypothesis (M)

`DimMult.lean` carries ENO multiplicativity as an explicit hypothesis,
`DimMultiplicative S` (`Σ_c N a b c · J a b c · κ_c = κ_a κ_b`), and proves ENO
8.23 from `(M) + IsPseudoUnitary + one pivotal structure`.  Yang-Lee is the
system on which the two halves of that antecedent separate cleanly: its twist is
trivial (`J ≡ 1`), so (M) is the statement that `κ` is a character of the
Fibonacci fusion ring, and `κ = (1, -1/φ)` — the *other* root of `x² = x + 1` —
is one.  `mul_pair` verifies the identity on all four label pairs by `decide` in
the integer pair model `ℤ[√5]` (the same idiom as the pentagon and the snakes),
and `kappa_char`, `dimMult`, `kappa_one_sq` transport it to `ℝ`;
`dimMult_and_not_pseudoUnitary` records that (M) holds
while `not_pseudoUnitary` holds, and `abs_dim_le_fpdim` that (M) alone already
gives ENO 8.21's bound `|dim P i| ≤ FPdim_i` for the pivotal structure `p ≡ 1`.
Positivity and the equality `dim = FPdim` are what is missing, and no choice of
`J` supplies them (`not_eno823`): on this system the pseudo-unitarity half of the
hypothesis is doing independent work.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Finset BigOperators

namespace FusionCategory

/-! ## At the trivial twist, (M) is the character condition on `κ`

The three systems below (Yang-Lee and the two pointed `Vec_{Z/2}` witnesses) all
have `J ≡ 1`, and for them the multiplicity hypothesis of `DimMult.lean`
collapses to a statement about `(N, κ)` alone.  Recorded once, generally, so the
three checks are one line each and so the reduction is reusable:
`DimMultiplicative` is *equivalent* to multiplicativity of `κ` when the twist is
trivial.  (Note that the associator does not enter: with `J ≡ 1`, (M) is
insensitive to `F`.) -/
theorem dimMultiplicative_iff_kappa_char {n : ℕ} {k : Type u} [Field k]
    {S : FusionSystem n k} (hJ : ∀ a b c : Fin n, S.J a b c = 1) :
    DimMultiplicative S ↔ ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * S.kappa c) = S.kappa a * S.kappa b := by
  constructor
  · intro hM a b
    simpa only [hJ, mul_one] using hM a b
  · intro h a b
    simpa only [hJ, mul_one] using h a b

namespace YangLee

open FusionCategory.Examples (FibonacciRing FibonacciFPData fibFPdim)

/-- The fusion ring is Fibonacci's: `1 ⊗ a = a`, `τ ⊗ τ = 1 ⊕ τ`. -/
abbrev N (a b c : Fin 2) : ℕ := FibonacciRing.N a b c

/-- Every object is self-dual. -/
abbrev dual (i : Fin 2) : Fin 2 := FibonacciRing.dual i

theorem mult_free : ∀ i j kk : Fin 2, N i j kk ≤ 1 := by
  intro i j kk
  fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide

/-- `s = √5`, so that `φ = (1 + √5)/2`, `-φ = (-1 - √5)/2` and
`-1/φ = (1 - √5)/2`. -/
noncomputable def s5 : ℝ := Real.sqrt 5

theorem s5_sq : s5 * s5 = ((5 : ℤ) : ℝ) := by
  rw [s5, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### The associator, in the pair model of `ℚ(√5)`

The only non-trivial block is `F^{τττ}_τ = [[-φ, 1], [-φ, φ]]` (rows `e`,
columns `f`); every other supported entry is `1`.  Its inverse is itself,
because the block is an involution. -/

/-- `F^{τττ}_τ = [[-φ, 1], [-φ, φ]]`, everything else supported `= 1`. -/
def Fpair (a b c d e f : Fin 2) : ℤ × ℤ :=
  if 0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if e = 0 ∧ f = 0 then (-1, -1)
       else if e = 0 ∧ f = 1 then (2, 0)
       else if e = 1 ∧ f = 0 then (-1, -1)
       else (1, 1))
     else (2, 0))
  else 0

/-- The inverse associator; the block is an involution, so it is the same block
read in the index order `(f, e)`. -/
def FinvPair (a b c d f e : Fin 2) : ℤ × ℤ :=
  if 0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d then
    (if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 then
      (if f = 0 ∧ e = 0 then (-1, -1)
       else if f = 0 ∧ e = 1 then (2, 0)
       else if f = 1 ∧ e = 0 then (-1, -1)
       else (1, 1))
     else (2, 0))
  else 0

noncomputable def F (a b c d e f : Fin 2) : ℝ := ZP.zval s5 (Fpair a b c d e f)

noncomputable def Finv (a b c d f e : Fin 2) : ℝ := ZP.zval s5 (FinvPair a b c d f e)

/-- `ev = 1` on both objects. -/
def evPair (_ : Fin 2) : ℤ × ℤ := (2, 0)

/-- `coev 1 = 1`, `coev τ = -1/φ = (1 - √5)/2`. -/
def coevPair (i : Fin 2) : ℤ × ℤ := if i = 0 then (2, 0) else (1, -1)

theorem coevPair_zero : coevPair 0 = ((2 : ℤ), 0) := by
  simp only [coevPair]
  rfl

theorem coevPair_one : coevPair 1 = ((1 : ℤ), -1) := by
  have h : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [coevPair, if_neg h]

/-! ### The pentagon, checked on all `2^9` label tuples in `ℤ[√5]` -/

def pentL (a b c d e i j r x : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (ZP.Zmul 5 (Fpair a b c x e 0) (Fpair a 0 d r x j)) (Fpair b c d j 0 i)
  + ZP.Zmul 5 (ZP.Zmul 5 (Fpair a b c x e 1) (Fpair a 1 d r x j)) (Fpair b c d j 1 i)

def pentR (a b c d e i j r x : Fin 2) : ℤ × ℤ :=
  ZP.Zmul 5 (Fpair e c d r x i) (Fpair a b i r e j)

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

/-! ### The snake equations -/

theorem snakeL_pair : ∀ i : Fin 2,
    ZP.peq (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (Fpair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

theorem snakeR_pair : ∀ i : Fin 2,
    ZP.peq (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (FinvPair i i i i 0 0))
      (ZP.quad ZP.zone) = true := by
  decide

/-- The pair-level snake, for a fixed label. -/
theorem snake_left_aux (i : Fin 2) :
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i) * ZP.zval s5 (Fpair i i i i 0 0) = 1 := by
  have hp := ZP.zval_of_peq (s := s5) (snakeL_pair i)
  have hL : ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
        * ZP.zval s5 (Fpair i i i i 0 0)
      = ZP.zval s5 (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (Fpair i i i i 0 0)) / 4 :=
    ZP.zval_three s5_sq _ _ _
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

theorem snake_right_aux (i : Fin 2) :
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i) * ZP.zval s5 (FinvPair i i i i 0 0) = 1 := by
  have hp := ZP.zval_of_peq (s := s5) (snakeR_pair i)
  have hL : ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
        * ZP.zval s5 (FinvPair i i i i 0 0)
      = ZP.zval s5 (ZP.Zmul 5 (ZP.Zmul 5 (coevPair i) (evPair i)) (FinvPair i i i i 0 0)) / 4 :=
    ZP.zval_three s5_sq _ _ _
  rw [hL, hp, ZP.zval_quad, ZP.zval_zone]
  norm_num

theorem snake_left : ∀ (hn : 0 < 2) (i : Fin 2),
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      * F i (dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro hn i
  fin_cases i
  · show ZP.zval s5 (coevPair 0) * ZP.zval s5 (evPair 0) * ZP.zval s5 (Fpair 0 0 0 0 0 0) = 1
    exact snake_left_aux 0
  · show ZP.zval s5 (coevPair 1) * ZP.zval s5 (evPair 1) * ZP.zval s5 (Fpair 1 1 1 1 0 0) = 1
    exact snake_left_aux 1

theorem snake_right : ∀ (hn : 0 < 2) (i : Fin 2),
    ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      * Finv (dual i) i (dual i) (dual i) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro hn i
  fin_cases i
  · show ZP.zval s5 (coevPair 0) * ZP.zval s5 (evPair 0) * ZP.zval s5 (FinvPair 0 0 0 0 0 0) = 1
    exact snake_right_aux 0
  · show ZP.zval s5 (coevPair 1) * ZP.zval s5 (evPair 1) * ZP.zval s5 (FinvPair 1 1 1 1 0 0) = 1
    exact snake_right_aux 1

/-! ### The system -/

noncomputable def system : FusionSystem 2 ℝ where
  ring := FibonacciRing
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
    have hne : ZP.zval s5 (coevPair i) ≠ 0 := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with h | h
      · rw [h, coevPair_zero]
        simp only [ZP.zval]
        norm_num
      · rw [h, coevPair_one]
        simp only [ZP.zval]
        intro hc
        have hs : s5 * s5 = 5 := s5_sq
        nlinarith [hs]
    exact hne
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

/-! ### `κ = (1, -1/φ)` -/

theorem kappa_val : ∀ i : Fin 2,
    system.kappa i = if i = 0 then 1 else (1 - Real.sqrt 5) / 2 := by
  intro i
  show ZP.zval s5 (coevPair i) * ZP.zval s5 (evPair i)
      = if i = 0 then 1 else (1 - Real.sqrt 5) / 2
  rw [ZP.zval_two (s := s5) (d := 5) s5_sq]
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with h | h
  · rw [h, coevPair_zero, if_pos rfl]
    simp only [evPair, ZP.Zmul, ZP.zval]
    norm_num
  · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    rw [h, coevPair_one, if_neg h10]
    simp only [evPair, ZP.Zmul, ZP.zval, s5]
    ring

theorem kappa_zero : system.kappa 0 = 1 := by
  rw [kappa_val]; simp

theorem kappa_one : system.kappa 1 = (1 - Real.sqrt 5) / 2 := by
  have h : ¬ ((1 : Fin 2) = 0) := by decide
  rw [kappa_val]; simp [h]

/-! ### `ENO823` is false for Yang-Lee

The coevaluation channel `(τ, τ; 1)` carries `J^{1}_{ττ} = 1` as an axiom, so a
pivotal structure with `dim = FPdim` would force
`dim 1 = twistNorm τ τ 1 · (dim τ)²`, i.e. `1 = φ² · φ² = φ⁴`. -/

theorem twisted_norm_one_one_zero :
    twistNorm system 1 1 0 = ((1 + Real.sqrt 5) / 2) ^ 2 := by
  unfold twistNorm
  rw [kappa_zero, kappa_one]
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hJ : system.J 1 1 0 = 1 := rfl
  simp only [hJ, one_mul]
  have h1 : (1 : ℝ) - Real.sqrt 5 ≠ 0 := by
    intro h
    have h2 : Real.sqrt 5 = 1 := by linarith
    rw [h2] at hs
    norm_num at hs
  have hne : (1 - Real.sqrt 5) / 2 * ((1 - Real.sqrt 5) / 2) ≠ 0 :=
    mul_ne_zero (div_ne_zero h1 two_ne_zero) (div_ne_zero h1 two_ne_zero)
  rw [div_eq_iff hne]
  ring_nf
  nlinarith [hs]

theorem not_eno823 : ¬ ENO823 system FibonacciFPData := by
  rintro ⟨P, _hsp, hdim⟩
  have hN : 0 < N 1 1 0 := by decide
  have h0 : dim P 0 = 1 := by
    have h := hdim 0
    simpa [FibonacciFPData, fibFPdim] using h
  have h1 : dim P 1 = (1 + Real.sqrt 5) / 2 := by
    have h := hdim 1
    simpa [FibonacciFPData, fibFPdim] using h
  have heq := dim_eq_twistNorm (S := system) P 1 1 0 hN
  rw [h0, h1, twisted_norm_one_one_zero] at heq
  -- `heq : 1 = ((1+√5)/2)^2 * ((1+√5)/2) * ((1+√5)/2)`, impossible for `√5 ≥ 0`
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [heq, hsq, hs0]

/-- **Yang-Lee is not pseudo-unitary** — ENO §8.4 make exactly this remark
("this property ... fails, for example, for the Yang-Lee category").  Its
categorical global dimension is `1 + 1/φ²` (both dimensions are `±1/φ`), while
`FPdim = 1 + φ²`. -/
theorem not_pseudoUnitary : ¬ IsPseudoUnitary (S := system) FibonacciFPData := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hL : (∑ i : Fin 2, system.kappa i * system.kappa (system.ring.dual i))
      = 1 + (1 - Real.sqrt 5) ^ 2 / 4 := by
    have h0 : system.ring.dual 0 = (0 : Fin 2) := rfl
    have h1 : system.ring.dual 1 = (1 : Fin 2) := rfl
    rw [Fin.sum_univ_two, h0, h1, kappa_zero, kappa_one]
    ring
  have hR : FibonacciFPData.globalDim = 1 + ((1 + Real.sqrt 5) / 2) ^ 2 := by
    unfold FusionRing.FPData.globalDim
    rw [Fin.sum_univ_two]
    simp [FibonacciFPData, fibFPdim]
  have h2 : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) ^ 2 / 4 := by ring
  rw [h2] at hR
  intro h
  unfold IsPseudoUnitary at h
  rw [hL] at h
  have h3 : (1 - Real.sqrt 5) ^ 2 / 4 = (1 + Real.sqrt 5) ^ 2 / 4 := by
    have ht := h.trans hR
    linarith [ht]
  have h4 : (1 - Real.sqrt 5) ^ 2 = (1 + Real.sqrt 5) ^ 2 := by linarith [h3]
  nlinarith [h4, hs]


/-! ### `(M)` holds on Yang–Lee: `κ` is the non-PF character of the Fibonacci ring

The twist is trivial (`J ≡ 1`), so the multiplicity identity

    (M)   Σ_c N a b c · J a b c · κ_c = κ_a κ_b

is exactly the statement that `κ` is a character of the fusion ring.  Yang–Lee's
`κ = (1, -1/φ)` is the other root of `x² = x + 1` (`kappa_one_sq`), hence a
character (`kappa_char`), hence (M) (`dimMult`) — kernel-checked, with the
channel identity discharged by `decide` in the integer pair model `ℤ[√5]`
(`mul_pair`), so no floats and no `norm_num` over the reals.

This makes the hypothesis split of `DimMult.lean` sharp on this very system:

* `dimMult_and_not_pseudoUnitary` — Yang–Lee satisfies (M) and is *not*
  pseudo-unitary;
* `abs_dim_le_fpdim` — from (M) alone one gets ENO 8.21 for its pivotal
  structure `p ≡ 1`: `|dim P i| ≤ FPdim_i`;
* `not_pos_dim_pivotal`, `dim_pivotal_one_ne_fpdim` — but not positivity, and not
  the equality `dim = FPdim` (which is false here: `not_eno823`, since
  `|κ_τ| = 1/φ` while `FPdim τ = φ`).

So (M) is not a weakening of pseudo-unitarity, and it does not make ENO 8.23
true by itself; the pseudo-unitarity equation in
`DimMult.eno823Exact_of_dimMult_pseudoUnitary` is doing independent work.
-/

/-- **`κ` in the integer-pair model `ℤ[√5]`** of `Examples/FibonacciIsing.lean`:
`(2,0)` denotes `1` and `(1,-1)` denotes `(1-√5)/2 = -1/φ`. -/
def kappaPair (i : Fin 2) : ℤ × ℤ := if i = 0 then (2, 0) else (1, -1)

/-- The channel sum of (M) at `(a,b)` in the pair model: `Σ_c N a b c · κ_c`,
componentwise in `ℤ`. -/
def mulPair (a b : Fin 2) : ℤ × ℤ :=
  (N a b 0) • kappaPair 0 + (N a b 1) • kappaPair 1

/-- `zval` commutes with natural multiples (the missing general case of
`ZP.zval_add`/`ZP.zval_dbl`). -/
theorem zval_nsmul (s : ℝ) (n : ℕ) (x : ℤ × ℤ) :
    ZP.zval s (n • x) = (n : ℝ) * ZP.zval s x := by
  induction n with
  | zero => simp [ZP.zval]
  | succ k ih =>
    rw [succ_nsmul, ZP.zval_add, ih]
    push_cast
    ring

/-- The pair model computes `κ`: `κ 0 = (2,0) = 1`, `κ 1 = (1,-1) = -1/φ`. -/
theorem zval_kappaPair (i : Fin 2) : ZP.zval s5 (kappaPair i) = system.kappa i := by
  fin_cases i
  · show ZP.zval s5 (2, 0) = system.kappa 0
    rw [kappa_zero]
    simp only [ZP.zval]
    norm_num
  · show ZP.zval s5 (1, -1) = system.kappa 1
    rw [kappa_one]
    simp only [ZP.zval, s5]
    ring

theorem zval_mulPair (a b : Fin 2) :
    ZP.zval s5 (mulPair a b) = ∑ c : Fin 2, (N a b c : ℝ) * system.kappa c := by
  simp only [mulPair, Fin.sum_univ_two, ZP.zval_add, zval_nsmul, zval_kappaPair]

/-- **The integer certificate for (M)**: the doubled channel sum at `(a,b)` is the
pair product `κ_a · κ_b`, for all four label pairs.  `decide` verifies it in `ℤ`
— the same idiom as the pentagon (`pent_pair`) and the snakes (`snakeL_pair`). -/
theorem mul_pair : ∀ a b : Fin 2,
    ZP.peq (ZP.dbl (mulPair a b)) (ZP.Zmul 5 (kappaPair a) (kappaPair b)) = true := by
  decide

/-- **`κ` is a character of the Fibonacci fusion ring on the non-PF root**:
`Σ_c N a b c · κ_c = κ_a κ_b` with `κ = (1, -1/φ)`, transported from the integer
certificate `mul_pair` through `zval`.  Stated on `system.ring.N`, which is
`FibonacciRing.N` (`N` below). -/
theorem kappa_char : ∀ a b : Fin 2,
    (∑ c : Fin 2, (system.ring.N a b c : ℝ) * system.kappa c)
      = system.kappa a * system.kappa b := by
  intro a b
  have h := ZP.zval_of_peq (s := s5) (mul_pair a b)
  rw [ZP.zval_dbl, ZP.zval_zmul (s := s5) (d := 5) s5_sq, zval_mulPair,
    zval_kappaPair, zval_kappaPair] at h
  show (∑ c : Fin 2, (N a b c : ℝ) * system.kappa c) = system.kappa a * system.kappa b
  linarith

/-- **Yang–Lee satisfies the multiplicity hypothesis (M).**  With `J ≡ 1` this is
`kappa_char`, channelled through the trivial twist. -/
theorem dimMult : DimMultiplicative system :=
  (dimMultiplicative_iff_kappa_char (S := system) (fun _ _ _ => rfl)).mpr kappa_char

/-- `κ_τ = -1/φ` is the *other* root of `x² = x + 1`: the character that is not
the FP-dimension. -/
theorem kappa_one_sq : system.kappa 1 ^ 2 = system.kappa 1 + 1 := by
  rw [kappa_one]
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith

/-- **The sharpness of the pseudo-unitarity hypothesis**: (M) holds on Yang–Lee
and pseudo-unitarity fails, so neither hypothesis implies the other. -/
theorem dimMult_and_not_pseudoUnitary :
    DimMultiplicative system ∧
      ¬ IsPseudoUnitary (S := system) FusionCategory.Examples.FibonacciFPData :=
  ⟨dimMult, not_pseudoUnitary⟩

/-- The pivotal structure `p ≡ 1` of Yang–Lee (available because `J ≡ 1`). -/
noncomputable def pivotal : PivotalStructure system where
  p := fun _ => 1
  p_unit := fun _ => rfl
  p_mon := by
    intro i j kk _
    show (1 : ℝ) = system.J i j kk * 1 * 1
    rw [show system.J i j kk = 1 from rfl]
    ring

/-- Its dimension at `τ` is `κ_τ = -1/φ`. -/
theorem dim_pivotal_one : dim pivotal 1 = (1 - Real.sqrt 5) / 2 := by
  rw [PivotalStructure.dim_eq, kappa_one]
  show (1 : ℝ) * ((1 - Real.sqrt 5) / 2) = (1 - Real.sqrt 5) / 2
  ring

/-- The equality `dim = FPdim` fails at `τ` — the half of ENO 8.23 that
pseudo-unitarity supplies. -/
theorem dim_pivotal_one_ne_fpdim : dim pivotal 1 ≠ FusionCategory.Examples.fibFPdim 1 := by
  rw [dim_pivotal_one]
  simp only [FusionCategory.Examples.fibFPdim]
  have hs : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  nlinarith

/-- So positivity fails too: `dim P τ = -1/φ < 0`. -/
theorem not_pos_dim_pivotal : ¬ (0 < dim pivotal 1) := by
  rw [dim_pivotal_one]
  intro h
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hm : 0 ≤ Real.sqrt 5 * (1 - Real.sqrt 5) := mul_nonneg hs0 (by linarith)
  nlinarith

/-- **The bridge to the character form, on a non-PF instance**: because (M)
holds, the dimension function of *every* pivotal structure of Yang-Lee is a
character of the fusion ring (`DimMult.dimMult_iff_dimEigen`) — here
`(1, -1/φ)`, not the FP-dimension `(1, φ)`. -/
theorem dimEigen_pivotal : DimEigen system (dim pivotal) :=
  dimEigen_of_dimMult dimMult pivotal

/-- **(M) alone does not imply ENO 8.23.**  The pseudo-unitarity hypothesis of
`DimMult.eno823Exact_of_dimMult_pseudoUnitary` cannot be dropped: Yang-Lee
satisfies (M) (`dimMult`) and refutes `ENO823` (`not_eno823`). -/
theorem dimMult_alone_insufficient :
    ¬ (∀ (S : FusionSystem 2 ℝ) (hFP : S.ring.FPData),
        DimMultiplicative S → ENO823 S hFP) := by
  intro h
  exact not_eno823 (h system FusionCategory.Examples.FibonacciFPData dimMult)

/-- **ENO 8.21 from (M) alone, on a system that is not pseudo-unitary.**  The
bound `|dim P i| ≤ FPdim_i` needs no pseudo-unitarity and no `PFUnique`: `(M)`
discharges `DimEigen` at every pivotal structure at once
(`DimMult.abs_dim_le_fpdim_of_dimMult`). -/
theorem abs_dim_le_fpdim : ∀ i : Fin 2, |dim pivotal i| ≤ FibonacciFPData.fpdim i :=
  abs_dim_le_fpdim_of_dimMult (S := system) FusionCategory.Examples.FibonacciFPData
    (by norm_num) dimMult pivotal

end YangLee

/-! ## The pointed `Vec_{Z/2}` witnesses: `(M)` is trivial-twist multiplicativity

`DimMultiplicative` is defined in `DimMult.lean`, which imports `Prop821` and
`ENOSqrt` and so sits *downstream* of `System.lean`.  The two pointed systems at
the end of `System.lean` therefore cannot carry their `(M)`-checks next to their
definitions, and the checks are recorded here, next to the `ℝ`/`ℚ` arithmetic
they are proved with.

Both have the trivial twist `J ≡ 1`, so for them

    (M)   Σ_c N a b c · κ_c = κ_a κ_b

depends only on `(N, κ)` and not on the associator at all: it says that `κ` is a
character of the pointed fusion ring.

* `VecZ2.dimMult` — `κ ≡ 1` and every product has exactly one channel, so the
  channel sum is `1 = κ_a κ_b`.
* `VecZ2Twisted.dimMult` — `κ = (1, -1)`: writing `a, b ∈ {0, 1}` additively in
  `Z/2` the identity is `(-1)^{a+b} = (-1)^a · (-1)^b`.  So (M) holds for
  `Vec^ω_{Z/2}` as well.  Since every object is self-dual, the double dual is the
  identity and `J ≡ 1` is the natural twist here, so this is not a degenerate
  choice: what fails in this system is the *sign* of the dimension of a pivotal
  structure (`Examples/VecZ2Twisted.lean`, `VecZ2Tw.pTriv_dim_one`: `dim P g =
  -1`), not (M).  (M) constrains the twist; positivity of the dimensions is the
  separate, pseudo-unitarity side.
-/

namespace VecZ2

/-- `Vec_{Z/2}` with the trivial cocycle has `κ ≡ 1`. -/
theorem kappa_val : ∀ i : Fin 2, system.kappa i = 1 := by
  intro i
  simp [FusionSystem.kappa, VecZ2.system]

/-- `κ ≡ 1` is a character of the `Vec_{Z/2}` fusion ring. -/
theorem kappa_char : ∀ a b : Fin 2,
    (∑ c : Fin 2, (system.ring.N a b c : ℚ) * system.kappa c)
      = system.kappa a * system.kappa b := by
  intro a b
  show (∑ c : Fin 2, (N a b c : ℚ) * system.kappa c) = system.kappa a * system.kappa b
  rw [Fin.sum_univ_two]
  simp only [kappa_val]
  fin_cases a <;> fin_cases b <;> norm_num [VecZ2.ring, VecZ2.N]

/-- **(M) for `Vec_{Z/2}` (trivial cocycle).** -/
theorem dimMult : DimMultiplicative system :=
  (dimMultiplicative_iff_kappa_char (S := system) (fun _ _ _ => rfl)).mpr kappa_char

end VecZ2

namespace VecZ2Twisted

/-- `Vec^ω_{Z/2}` for the non-trivial cocycle has `κ = (1, -1)`. -/
theorem kappa_val : ∀ i : Fin 2, system.kappa i = if i = 0 then (1 : ℚ) else -1 := by
  intro i
  fin_cases i <;> simp [kappa_unit, kappa_g]

/-- `κ = (1, -1)` is a character of the `Vec_{Z/2}` fusion ring. -/
theorem kappa_char : ∀ a b : Fin 2,
    (∑ c : Fin 2, (system.ring.N a b c : ℚ) * system.kappa c)
      = system.kappa a * system.kappa b := by
  intro a b
  show (∑ c : Fin 2, (VecZ2.N a b c : ℚ) * system.kappa c) = system.kappa a * system.kappa b
  rw [Fin.sum_univ_two]
  simp only [kappa_val]
  fin_cases a <;> fin_cases b <;> norm_num [VecZ2.ring, VecZ2.N]

/-- **(M) for `Vec^ω_{Z/2}` (non-trivial cocycle).** -/
theorem dimMult : DimMultiplicative system :=
  (dimMultiplicative_iff_kappa_char (S := system) (fun _ _ _ => rfl)).mpr kappa_char

end VecZ2Twisted

end FusionCategory

/-! ## Axiom audit (the budget is `[propext, Classical.choice, Quot.sound]`) -/

#print axioms FusionCategory.dimMultiplicative_iff_kappa_char
#print axioms FusionCategory.YangLee.zval_nsmul
#print axioms FusionCategory.YangLee.zval_kappaPair
#print axioms FusionCategory.YangLee.zval_mulPair
#print axioms FusionCategory.YangLee.mul_pair
#print axioms FusionCategory.YangLee.kappa_char
#print axioms FusionCategory.YangLee.dimMult
#print axioms FusionCategory.YangLee.kappa_one_sq
#print axioms FusionCategory.YangLee.dimMult_and_not_pseudoUnitary
#print axioms FusionCategory.YangLee.pivotal
#print axioms FusionCategory.YangLee.dim_pivotal_one
#print axioms FusionCategory.YangLee.dim_pivotal_one_ne_fpdim
#print axioms FusionCategory.YangLee.not_pos_dim_pivotal
#print axioms FusionCategory.YangLee.abs_dim_le_fpdim
#print axioms FusionCategory.YangLee.dimEigen_pivotal
#print axioms FusionCategory.YangLee.dimMult_alone_insufficient
#print axioms FusionCategory.VecZ2.kappa_val
#print axioms FusionCategory.VecZ2.kappa_char
#print axioms FusionCategory.VecZ2.dimMult
#print axioms FusionCategory.VecZ2Twisted.kappa_val
#print axioms FusionCategory.VecZ2Twisted.kappa_char
#print axioms FusionCategory.VecZ2Twisted.dimMult
