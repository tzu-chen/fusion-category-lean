import FusionCategory.Coboundary
import FusionCategory.Examples.Fibonacci
import FusionCategory.Examples.FibonacciIsing

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

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Finset BigOperators

namespace FusionCategory

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

end YangLee

end FusionCategory
