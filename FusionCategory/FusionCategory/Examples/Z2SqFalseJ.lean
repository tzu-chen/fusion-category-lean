import FusionCategory.PseudoUnitary

/-!
# `Vec^ω_{(Z/2)²}` with the trivial twist `J ≡ 1`: the false-`J` witness, kernel-checked

B3a of the first delegation batch (proposal §5.2).  The datum is the pointed
fusion system `Vec^ω_{(Z/2)²}` for the non-trivial 3-cocycle

    ω(a,b,c) = (-1)^{a₁b₂c₁}      (labels `i : Fin 4` read as `(i.val / 2, i.val % 2)`),

with the *trivial* double-dual twist `J ≡ 1` that this repository's
`FusionSystem` carries as data.  The honest twist for this associator is the
coboundary `J^c_{ab} = κ_a κ_b / κ_c`, not `1`; carrying `J ≡ 1` gives a
genuine `FusionSystem` (every field is proved below) which is **pseudo-unitary**
(`Σ_i κ_i κ_{i*} = 4 = Σ_i FPdim_i²`) and yet has no pivotal structure whose
dimensions are the FP-dimensions (`not_eno823`), because the dimension function
of any pivotal structure fails to be multiplicative (`not_mult`), i.e. the
`(M)` law `Σ_c N^c_{ab} J^c_{ab} κ_c = κ_a κ_b` fails (`M_fails`).

So `ENO823`/`ENO823Exact` as stated in `FusionCategory/PseudoUnitary.lean` is
false for this system even though the hypothesis `IsPseudoUnitary` holds — the
`J` of the datum is not the `J` that a rigid structure computes.  This is the
content of the `J_match`/`derivedJ` qualification in the corrected target
(Task 1.5 / 2.3 / 3.3).

Everything is exact arithmetic over `ℝ`: the structure constants are `±1` and
`0`, the cocycle identity and all the `Fin 4` combinatorics are checked by
`decide`, and the pentagon is *not* brute-forced over the `4⁹` label tuples —
it is reduced to the `4⁴` cocycle identity `w_cocycle` by discharging the
support (channel) conditions first (`pentagon_aux`).

Axiom budget: `[propext, Classical.choice, Quot.sound]` (`#print axioms` at the
bottom of the file).
-/

set_option linter.unusedSimpArgs false

namespace FusionCategory
namespace Z2Sq

/-! ## The group law of `(Z/2)²` on `Fin 4`

Label `i : Fin 4` is the pair `(i.val / 2, i.val % 2)`, so `0 = (0,0)`,
`1 = (0,1)`, `2 = (1,0)`, `3 = (1,1)`.  Addition is componentwise mod 2. -/

/-- Addition in `(Z/2)²`, on `Fin 4` by bit pattern. -/
def gadd (a b : Fin 4) : Fin 4 :=
  Fin.ofNat 4 ((a.val % 2 + b.val % 2) % 2 + 2 * ((a.val / 2 + b.val / 2) % 2))

theorem gadd_assoc : ∀ a b c : Fin 4, gadd (gadd a b) c = gadd a (gadd b c) := by
  decide

theorem gadd_comm : ∀ a b : Fin 4, gadd a b = gadd b a := by decide

theorem gadd_zero_left : ∀ b : Fin 4, gadd 0 b = b := by decide

theorem gadd_zero_right : ∀ a : Fin 4, gadd a 0 = a := by decide

theorem gadd_self : ∀ a : Fin 4, gadd a a = 0 := by decide

theorem gadd_eq_zero_iff : ∀ a b : Fin 4, (gadd a b = 0 ↔ b = a) := by decide

theorem gadd_eq_iff : ∀ a b c : Fin 4, (gadd a b = c ↔ b = gadd c a) := by decide

/-- `gadd` at the `⟨0, hn⟩` form of the unit, which is what the `FusionRing`
fields produce syntactically. -/
theorem gadd_zero_left' (hn : 0 < 4) (b : Fin 4) : gadd ⟨0, hn⟩ b = b := gadd_zero_left b

theorem gadd_zero_right' (hn : 0 < 4) (a : Fin 4) : gadd a ⟨0, hn⟩ = a := gadd_zero_right a

/-! ## The cocycle `ω(a,b,c) = (-1)^{a₁b₂c₁}`

Integral form first, so that all the finite checks are `decide` in `ℤ`; the
`ℝ`-valued version is its cast. -/

/-- `ω(a,b,c) = (-1)^{a₁b₂c₁}` as an integer. -/
def wZ (a b c : Fin 4) : ℤ :=
  if a.val / 2 = 1 ∧ b.val % 2 = 1 ∧ c.val / 2 = 1 then -1 else 1

/-- `ω` over `ℝ`. -/
def w (a b c : Fin 4) : ℝ := (wZ a b c : ℝ)

/-- The 3-cocycle identity, on all `4⁴ = 256` label tuples. -/
theorem wZ_cocycle : ∀ a b c d : Fin 4,
    wZ a b c * wZ a (gadd b c) d * wZ b c d = wZ (gadd a b) c d * wZ a b (gadd c d) := by
  decide

theorem wZ_sq : ∀ a b c : Fin 4, wZ a b c * wZ a b c = 1 := by decide

theorem wZ_unit_left : ∀ b c : Fin 4, wZ 0 b c = 1 := by decide

theorem wZ_unit_right : ∀ a b : Fin 4, wZ a b 0 = 1 := by decide

theorem w_cocycle (a b c d : Fin 4) :
    w a b c * w a (gadd b c) d * w b c d = w (gadd a b) c d * w a b (gadd c d) := by
  have h := wZ_cocycle a b c d
  simp only [w]
  exact_mod_cast h

theorem w_sq (a b c : Fin 4) : w a b c * w a b c = 1 := by
  have h := wZ_sq a b c
  simp only [w]
  exact_mod_cast h

theorem w_ne_zero (a b c : Fin 4) : w a b c ≠ 0 := by
  intro h
  have h1 := w_sq a b c
  rw [h] at h1
  norm_num at h1

theorem w_unit_left (b c : Fin 4) : w 0 b c = 1 := by
  have h := wZ_unit_left b c
  simp only [w]
  exact_mod_cast h

theorem w_unit_right (a b : Fin 4) : w a b 0 = 1 := by
  have h := wZ_unit_right a b
  simp only [w]
  exact_mod_cast h

/-! ## The associator of a pointed system

`Fw w a b c d e f` is the six-index associator of the pointed system with
fusion rule `c = a + b` and cocycle `w`: three channel indicators
(`e = a + b`, `d = (a+b) + c`, `f = b + c`) times `w a b c`.  The fourth
support condition of `FusionSystem`, `d = a + f`, is implied by the first
three by associativity, which is why three indicators suffice. -/

/-- The pointed associator for an arbitrary cocycle `w`. -/
def Fw (w : Fin 4 → Fin 4 → Fin 4 → ℝ) (a b c d e f : Fin 4) : ℝ :=
  (if e = gadd a b then (1 : ℝ) else 0) *
  (if d = gadd (gadd a b) c then 1 else 0) *
  (if f = gadd b c then 1 else 0) * w a b c

/-- **The pentagon**, from the cocycle identity alone.

The sum over the channel `k` of `a ⊗ b` collapses to `k = b + c`: every other
term carries the indicator `k = b + c` of its first factor.  What remains is an
identity of indicator products, discharged by the five `by_cases` below (each
false branch is `0 = 0`), leaving exactly `w_cocycle`. -/
theorem pentagon_aux (v : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hv : ∀ a b c d : Fin 4,
      v a b c * v a (gadd b c) d * v b c d = v (gadd a b) c d * v a b (gadd c d))
    (a b c d e i j r x : Fin 4) :
    (∑ k : Fin 4, Fw v a b c x e k * Fw v a k d r x j * Fw v b c d j k i)
      = Fw v e c d r x i * Fw v a b i r e j := by
  rw [Finset.sum_eq_single (gadd b c) (fun k _ hk => by simp [Fw, hk])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Fw, gadd_assoc]
  by_cases h1 : e = gadd a b
  · subst h1
    simp only [gadd_assoc]
    by_cases h2 : x = gadd a (gadd b c)
    · subst h2
      by_cases h3 : r = gadd a (gadd b (gadd c d))
      · subst h3
        by_cases h4 : i = gadd c d
        · subst h4
          by_cases h5 : j = gadd b (gadd c d)
          · subst h5
            simp only [Fw, gadd_assoc, reduceIte, one_mul, mul_one]
            exact hv a b c d
          · simp [Fw, h5]
        · simp [Fw, h4]
      · simp [Fw, gadd_assoc, h3]
    · simp [Fw, h2]
  · simp [Fw, h1]

/-! ## The fusion ring `Vec_{(Z/2)²}` -/

/-- The fusion rule: `N a b c = 1` iff `c = a + b`. -/
def N (a b c : Fin 4) : ℕ := if c = gadd a b then 1 else 0

theorem N_pos_iff {a b c : Fin 4} : 0 < N a b c ↔ c = gadd a b := by
  unfold N; split <;> simp_all

theorem N_eq_one_iff {a b c : Fin 4} : N a b c = 1 ↔ c = gadd a b := by
  unfold N; split <;> simp_all

theorem N_eq_zero_iff {a b c : Fin 4} : N a b c = 0 ↔ c ≠ gadd a b := by
  unfold N; split <;> simp_all

/-- `N` is multiplicative-additive in its first two arguments: the delta
convolution. -/
theorem sum_N_mul (i j k l : Fin 4) :
    (∑ p : Fin 4, N i j p * N p k l) = N (gadd i j) k l := by
  rw [Finset.sum_eq_single (gadd i j)]
  · have h : N i j (gadd i j) = 1 := by simp [N]
    rw [h, one_mul]
  · intro p _ hp
    have h : N i j p = 0 := by simp [N, hp]
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_N_mul_right (i j k l : Fin 4) :
    (∑ q : Fin 4, N j k q * N i q l) = N i (gadd j k) l := by
  rw [Finset.sum_eq_single (gadd j k)]
  · have h : N j k (gadd j k) = 1 := by simp [N]
    rw [h, one_mul]
  · intro p _ hp
    have h : N j k p = 0 := by simp [N, hp]
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The fusion ring of `(Z/2)²`: every object self-dual, `c = a + b`. -/
def ring : FusionRing 4 where
  N := N
  dual := id
  dual_involutive := fun _ => rfl
  dual_zero := fun _ => rfl
  left_unit := by
    intro hn i j
    simp only [N, id]
    rw [gadd_zero_left' hn]
    by_cases h : i = j
    · subst h; simp
    · have h2 : ¬ ((j : Fin 4) = i) := fun hc => h hc.symm
      simp [h, h2]
  right_unit := by
    intro hn i j
    simp only [N]
    rw [gadd_zero_right' hn]
    by_cases h : i = j
    · subst h; simp
    · have h2 : ¬ ((j : Fin 4) = i) := fun hc => h hc.symm
      simp [h, h2]
  dual_coeff := by
    intro hn i j
    have hiff : ((⟨0, hn⟩ : Fin 4) = gadd i j) ↔ (j = i) := by
      have h1 : ((⟨0, hn⟩ : Fin 4) = gadd i j) ↔ (gadd i j = (0 : Fin 4)) := eq_comm
      rw [h1]
      exact gadd_eq_zero_iff i j
    simp only [N, id]
    simp only [hiff]
  associativity := by
    intro i j k l
    rw [sum_N_mul, sum_N_mul_right]
    simp only [N, gadd_assoc]
  dual_symm := by
    intro i j k
    simp only [N, id, gadd_comm]

/-! ## The associator, its support, the pentagon, the unit laws, the inverse -/

/-- The associator of `Vec^ω_{(Z/2)²}`. -/
def F (a b c d e f : Fin 4) : ℝ := Fw w a b c d e f

theorem F_support : ∀ a b c d e f : Fin 4,
    ¬ (0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d) → F a b c d e f = 0 := by
  intro a b c d e f h
  by_cases h1 : e = gadd a b <;> by_cases h2 : d = gadd (gadd a b) c <;>
    by_cases h3 : f = gadd b c <;> simp_all [F, Fw, N, gadd_assoc]

theorem F_pentagon : ∀ a b c d e i j r x : Fin 4,
    (∑ k : Fin 4, F a b c x e k * F a k d r x j * F b c d j k i) =
      F e c d r x i * F a b i r e j :=
  pentagon_aux w w_cocycle

theorem F_unit_left : ∀ (_ : 0 < 4) (b c d f : Fin 4), 0 < N b c f →
    F 0 b c d b f = if d = f then 1 else 0 := by
  intro _ b c d f hbcf
  have hf : f = gadd b c := N_pos_iff.mp hbcf
  subst hf
  simp only [F, Fw, gadd_zero_left, reduceIte, one_mul, mul_one, w_unit_left]

theorem F_unit_right : ∀ (_ : 0 < 4) (a b d e : Fin 4), 0 < N a b e →
    F a b 0 d e b = if d = e then 1 else 0 := by
  intro _ a b d e habe
  have he : e = gadd a b := N_pos_iff.mp habe
  subst he
  simp only [F, Fw, gadd_zero_right, reduceIte, one_mul, mul_one, w_unit_right]

/-- The inverse associator: for `±1`-valued pointed data every block is
`1 × 1`, so the inverse is the same scalar read with the channel arguments
exchanged. -/
def Finv (a b c d f e : Fin 4) : ℝ := Fw w a b c d e f

theorem Finv_support : ∀ a b c d f e : Fin 4,
    ¬ (0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d) → Finv a b c d f e = 0 := by
  intro a b c d f e h
  by_cases h1 : e = gadd a b <;> by_cases h2 : d = gadd (gadd a b) c <;>
    by_cases h3 : f = gadd b c <;> simp_all [Finv, Fw, N, gadd_assoc]

theorem Finv_comp : ∀ a b c d f' f : Fin 4,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    (∑ e : Fin 4, Finv a b c d f' e * F a b c d e f) = if f' = f then 1 else 0 := by
  intro a b c d f' f h1 h2 h3 h4
  have hf' : f' = gadd b c := N_pos_iff.mp h1
  have hf : f = gadd b c := N_pos_iff.mp h3
  have hd : d = gadd (gadd a b) c := by
    have h := N_pos_iff.mp h2
    rw [hf'] at h
    rw [h, gadd_assoc]
  have hff : f' = f := by rw [hf', hf]
  subst hff
  rw [if_pos rfl]
  rw [Finset.sum_eq_single (gadd a b) (fun e _ he => by simp [Finv, F, Fw, he])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Finv, F, Fw, hf, hd, reduceIte, one_mul, mul_one, true_and]
  rw [w_sq]

theorem F_comp_inv : ∀ a b c d e' e : Fin 4,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    (∑ f : Fin 4, Finv a b c d f e' * F a b c d e f) = if e' = e then 1 else 0 := by
  intro a b c d e' e h1 h2 h3 h4
  have he' : e' = gadd a b := N_pos_iff.mp h1
  have he : e = gadd a b := N_pos_iff.mp h3
  have hd : d = gadd (gadd a b) c := by
    have h := N_pos_iff.mp h2
    rw [he'] at h
    exact h
  have hee : e' = e := by rw [he', he]
  subst hee
  rw [if_pos rfl]
  rw [Finset.sum_eq_single (gadd b c) (fun f _ hf => by simp [Finv, F, Fw, hf])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Finv, F, Fw, he', hd, reduceIte, one_mul, mul_one, true_and]
  rw [w_sq]

/-! ## The duality normalisation and the twist `J ≡ 1` -/

/-- Evaluation, normalised to `1`. -/
def ev (_ : Fin 4) : ℝ := 1

/-- Coevaluation: `coev i = ω(i,i,i)`, which is what the left snake forces. -/
def coev (i : Fin 4) : ℝ := w i i i

theorem F_loop (i : Fin 4) : F i i i i 0 0 = w i i i := by
  simp [F, Fw, gadd_self, gadd_zero_left]

theorem F_loop_inv (i : Fin 4) : Finv i i i i 0 0 = w i i i := by
  simp [Finv, Fw, gadd_self, gadd_zero_left]

theorem snake_left : ∀ (_ : 0 < 4) (i : Fin 4),
    coev i * ev i * F i (ring.dual i) i i 0 0 = 1 := by
  intro _ i
  change coev i * ev i * F i i i i 0 0 = 1
  rw [F_loop i]
  show w i i i * 1 * w i i i = 1
  rw [mul_one]
  exact w_sq i i i

theorem snake_right : ∀ (_ : 0 < 4) (i : Fin 4),
    coev i * ev i * Finv (ring.dual i) i (ring.dual i) (ring.dual i) 0 0 = 1 := by
  intro _ i
  change coev i * ev i * Finv i i i i 0 0 = 1
  rw [F_loop_inv i]
  show w i i i * 1 * w i i i = 1
  rw [mul_one]
  exact w_sq i i i

/-! ## The datum -/

/-- **The `(Z/2)²` datum with the trivial twist `J ≡ 1`** as a skeletal
`FusionSystem`: non-trivial cocycle `ω = (-1)^{a₁b₂c₁}`, `ev = 1`,
`coev = ω(i,i,i)`, `J ≡ 1`.  Every field is proved; there is no `sorry`. -/
def system : FusionSystem 4 ℝ where
  ring := ring
  mult_free := by
    intro i j kk
    show N i j kk ≤ 1
    unfold N
    split <;> simp
  F := F
  F_support := F_support
  pentagon := F_pentagon
  F_unit_left := F_unit_left
  F_unit_right := F_unit_right
  Finv := Finv
  Finv_support := Finv_support
  Finv_comp := Finv_comp
  F_comp_inv := F_comp_inv
  ev := ev
  coev := coev
  ev_ne_zero := fun _ => one_ne_zero
  coev_ne_zero := fun i => w_ne_zero i i i
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

/-! ## Its `κ` is `(1,1,1,-1)` -/

theorem kappa_three : system.kappa 3 = -1 := by
  show coev 3 * ev 3 = -1
  simp only [coev, ev, w, wZ]
  norm_num

theorem kappa_zero : system.kappa 0 = 1 := by
  show coev 0 * ev 0 = 1
  simp only [coev, ev, w, wZ]
  norm_num

theorem kappa_one : system.kappa 1 = 1 := by
  show coev 1 * ev 1 = 1
  simp only [coev, ev, w, wZ]
  norm_num

theorem kappa_two : system.kappa 2 = 1 := by
  show coev 2 * ev 2 = 1
  simp only [coev, ev, w, wZ]
  norm_num

theorem kappa_val (i : Fin 4) : system.kappa i = if i = 3 then -1 else 1 := by
  have h : system.kappa i = w i i i := by
    show coev i * ev i = w i i i
    simp [coev, ev]
  rw [h]
  fin_cases i <;> simp [w, wZ]

/-! ## ... so the datum is pseudo-unitary

`FPdim ≡ 1` (every object of `Vec_{(Z/2)²}` has FP-dimension `1`), hence
`Σ_i FPdim_i² = 4`; and `κ_i² = 1` for all `i`, so `Σ_i κ_i κ_{i*} = 4` too:
the pseudo-unitarity hypothesis of ENO 8.23 holds. -/

theorem gadd_swap : ∀ a b : Fin 4, gadd a (gadd b a) = b := by decide

/-- The FP-dimension data of `Vec_{(Z/2)²}`: `FPdim ≡ 1`. -/
def fpData : FusionRing.FPData ring where
  fpdim := fun _ => 1
  pos := fun _ => one_pos
  unit_one := fun _ => rfl
  eigenvector := by
    intro i kk
    show (∑ j : Fin 4, (N i j kk : ℝ) * (1 : ℝ)) = (1 : ℝ) * 1
    rw [Finset.sum_eq_single (gadd kk i)]
    · have h : N i (gadd kk i) kk = 1 := by
        rw [N_eq_one_iff]
        exact (gadd_swap i kk).symm
      rw [h]
      norm_num
    · intro j _ hj
      have h : N i j kk = 0 := by
        rw [N_eq_zero_iff]
        intro hc
        exact hj ((gadd_eq_iff i j kk).mp hc.symm)
      rw [h]
      norm_num
    · intro h
      exact absurd (Finset.mem_univ _) h
  dual_eq := fun _ => rfl

theorem J_apply (i j kk : Fin 4) : system.J i j kk = 1 := rfl

theorem kappa_dual : ∀ i : Fin 4, system.ring.dual i = i := fun _ => rfl

theorem kappa_sq (i : Fin 4) : system.kappa i * system.kappa i = 1 := by
  have h : system.kappa i = w i i i := by
    show coev i * ev i = w i i i
    simp [coev, ev]
  rw [h]
  exact w_sq i i i

/-- **The datum is pseudo-unitary**: `Σ_i κ_i κ_{i*} = 4 = Σ_i FPdim_i²`. -/
theorem isPseudoUnitary : IsPseudoUnitary system fpData := by
  show (∑ i : Fin 4, system.kappa i * system.kappa (system.ring.dual i)) = fpData.globalDim
  have hpt : ∀ i : Fin 4, system.kappa i * system.kappa (system.ring.dual i) = (1 : ℝ) := by
    intro i
    rw [kappa_dual i]
    exact kappa_sq i
  have h4 : (∑ _i : Fin 4, (1 : ℝ)) = 4 := by
    norm_num [Fin.sum_univ_four]
  have hg : fpData.globalDim = 4 := by
    show (∑ i : Fin 4, ((1 : ℝ)) ^ 2) = 4
    norm_num [Fin.sum_univ_four]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), h4, hg]

/-! ## ... but no pivotal structure has `dim = FPdim`

The pivotal structure `p ≡ 1` exists (the twist is trivial) and *is* spherical
(every object is self-dual), but its dimensions are `κ = (1,1,1,-1)`, not the
FP-dimensions.  No pivotal structure at all can have `dim = FPdim = 1`:
`p_mon` on the channel `(2,1;3)` forces `p 3 = p 2 · p 1`, whence
`dim 3 = dim 2 · dim 1` would read `-x = x`, impossible for `x ≠ 0`. -/

/-- `p ≡ 1` is a pivotal structure: the twist is trivial. -/
noncomputable def trivialPivotal : PivotalStructure system where
  p := fun _ => 1
  p_unit := fun _ => rfl
  p_mon := by
    intro i j kk _
    show ((1 : ℝˣ) : ℝ) = system.J i j kk * ((1 : ℝˣ) : ℝ) * ((1 : ℝˣ) : ℝ)
    rw [J_apply]
    norm_num

theorem trivialPivotal_isSpherical : trivialPivotal.IsSpherical :=
  trivialPivotal.spherical_of_selfdual (fun _ => rfl)

theorem trivialPivotal_dim_zero : dim trivialPivotal 0 = 1 := by
  show ((1 : ℝˣ) : ℝ) * system.kappa 0 = 1
  rw [kappa_zero]
  norm_num

theorem trivialPivotal_dim_one : dim trivialPivotal 1 = 1 := by
  show ((1 : ℝˣ) : ℝ) * system.kappa 1 = 1
  rw [kappa_one]
  norm_num

theorem trivialPivotal_dim_two : dim trivialPivotal 2 = 1 := by
  show ((1 : ℝˣ) : ℝ) * system.kappa 2 = 1
  rw [kappa_two]
  norm_num

theorem trivialPivotal_dim_three : dim trivialPivotal 3 = -1 := by
  show ((1 : ℝˣ) : ℝ) * system.kappa 3 = -1
  rw [kappa_three]
  norm_num

/-- The spherical pivotal structure of the datum does *not* have the
FP-dimensions: `dim X_3 = -1` while `FPdim X_3 = 1`. -/
theorem trivialPivotal_not_fpdim : dim trivialPivotal 3 ≠ fpData.fpdim 3 := by
  rw [trivialPivotal_dim_three]
  show (-1 : ℝ) ≠ 1
  norm_num

/-- `(M)` fails: the `J ≡ 1` twist does not satisfy
`Σ_c N^c_{ab} J^c_{ab} κ_c = κ_a κ_b` at `(a,b) = (2,1)` (`κ_3 = -1 ≠ 1 = κ_2 κ_1`). -/
theorem M_fails :
    (∑ kk : Fin 4, (N 2 1 kk : ℝ) * system.J 2 1 kk * system.kappa kk) ≠
      system.kappa 2 * system.kappa 1 := by
  have hsum : (∑ kk : Fin 4, (N 2 1 kk : ℝ) * system.J 2 1 kk * system.kappa kk) = -1 := by
    rw [Finset.sum_eq_single (3 : Fin 4)]
    · have h : N 2 1 3 = 1 := by
        rw [N_eq_one_iff]
        rfl
      rw [h, J_apply, kappa_three]
      norm_num
    · intro kk _ hkk
      have h : N 2 1 kk = 0 := by
        rw [N_eq_zero_iff]
        intro hc
        exact hkk (by rw [hc]; rfl)
      rw [h]
      norm_num
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, kappa_two, kappa_one]
  norm_num

/-! ### Non-degeneracy: the datum is not the trivial one

Guards against a vacuous witness: the fusion rule, the associator and the twist
both see the non-trivial cocycle. -/

theorem fusion_nontrivial : N 2 1 3 = 1 := by
  rw [N_eq_one_iff]
  rfl

/-- The associator is genuinely non-trivial: `F²¹³(3,2) = ω(2,1,3) = -1`. -/
theorem associator_nontrivial : F 2 1 3 0 3 2 = -1 := by
  norm_num [F, Fw, w, wZ, gadd]

/-- ... and `κ_3 = -1`: the duality normalisation is not the trivial one either. -/
theorem kappa_nontrivial : system.kappa 3 = -1 := kappa_three

theorem channel_two_one : 0 < N 2 1 3 := by
  rw [N_pos_iff]
  rfl

theorem N_two_one_three : N 2 1 3 = 1 := by
  rw [N_eq_one_iff]
  rfl

/-- **`J ≡ 1` is not the coboundary `δκ`**: `(K)` fails at the channel `(2,1;3)`,
where `κ_2 κ_1 / κ_3 = -1 ≠ 1 = J 2 1 3`.  This is the precise sense in which the
datum is a *false*-`J` witness: the twist it carries is not the one a rigid
structure on this associator computes. -/
theorem J_ne_coboundary :
    ∃ a b c : Fin 4, 0 < N a b c ∧
      system.J a b c ≠ system.kappa a * system.kappa b / system.kappa c := by
  refine ⟨2, 1, 3, channel_two_one, ?_⟩
  rw [J_apply, kappa_two, kappa_one, kappa_three]
  norm_num

/-- **No pivotal structure has the FP-dimensions**: `dim P i = FPdim i = 1` for
all `i` contradicts monoidality of `p` on the channel `(2,1;3)`. -/
theorem no_pivotal_dim_fpdim (P : PivotalStructure system) :
    ¬ (∀ i : Fin 4, dim P i = (1 : ℝ)) := by
  intro hdim
  have h2 : (P.p 2 : ℝ) = 1 := by
    have h := hdim 2
    rw [PivotalStructure.dim_eq, kappa_two] at h
    simpa using h
  have h1 : (P.p 1 : ℝ) = 1 := by
    have h := hdim 1
    rw [PivotalStructure.dim_eq, kappa_one] at h
    simpa using h
  have h3 : (P.p 3 : ℝ) = -1 := by
    have h := hdim 3
    rw [PivotalStructure.dim_eq, kappa_three] at h
    linarith
  have hpm := P.p_mon 2 1 3 channel_two_one
  rw [h2, h1, h3, J_apply] at hpm
  norm_num at hpm

/-- **The dimension function of every pivotal structure fails to be
multiplicative** — `(M)` at the level of `dim`. -/
theorem not_mult (P : PivotalStructure system) :
    ¬ (∀ i kk : Fin 4,
      (∑ j : Fin 4, (N i j kk : ℝ) * dim P j) = dim P i * dim P kk) := by
  intro hmult
  have h := hmult 2 3
  rw [Finset.sum_eq_single (1 : Fin 4)] at h
  · have hp3 : (P.p 3 : ℝ) = (P.p 2 : ℝ) * (P.p 1 : ℝ) := by
      have hp := P.p_mon 2 1 3 channel_two_one
      rw [J_apply] at hp
      simpa using hp
    have hdim1 : dim P 1 = (P.p 1 : ℝ) := by
      rw [PivotalStructure.dim_eq, kappa_one]; ring
    have hdim2 : dim P 2 = (P.p 2 : ℝ) := by
      rw [PivotalStructure.dim_eq, kappa_two]; ring
    have hdim3 : dim P 3 = -((P.p 2 : ℝ) * (P.p 1 : ℝ)) := by
      show (P.p 3 : ℝ) * system.kappa 3 = -((P.p 2 : ℝ) * (P.p 1 : ℝ))
      rw [kappa_three, hp3]
      ring
    rw [N_two_one_three, hdim1, hdim2, hdim3] at h
    norm_num at h
    have hp1 : (P.p 1 : ℝ) ≠ 0 := P.pVal_ne_zero 1
    have hsq : (0 : ℝ) ≤ (P.p 2 : ℝ) ^ 2 := sq_nonneg _
    have hzero : (P.p 1 : ℝ) * (1 + (P.p 2 : ℝ) ^ 2) = 0 := by nlinarith [h]
    have hpos : (0 : ℝ) < 1 + (P.p 2 : ℝ) ^ 2 := by linarith
    have hlast : (P.p 1 : ℝ) = 0 := by
      rcases mul_eq_zero.mp hzero with h' | h'
      · exact h'
      · linarith
    exact hp1 hlast
  · intro j _ hj
    have h0 : N 2 j 3 = 0 := by
      rw [N_eq_zero_iff]
      intro hc
      exact hj ((gadd_eq_iff 2 j 3).mp hc.symm)
    rw [h0]
    norm_num
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- **`ENO823` is false for this datum**, although `IsPseudoUnitary` holds: no
spherical pivotal structure has the FP-dimensions.  This is the false-`J`
witness: the `J` carried by `system` is not the twist that a rigid structure on
this associator computes (that one is the coboundary `κ_a κ_b / κ_c`, B3b). -/
theorem not_eno823 : ¬ ENO823 system fpData := by
  rintro ⟨P, _hsp, hdim⟩
  exact no_pivotal_dim_fpdim P (fun i => by
    have h := hdim i
    show dim P i = (1 : ℝ)
    rw [h]
    rfl)

/-- **`ENO823Exact` is false for this datum**, with its hypothesis satisfied: the
target needs the `J_match` qualification (Task 1.5). -/
theorem not_eno823Exact : ¬ ENO823Exact system fpData := by
  intro h
  exact not_eno823 (eno823_of_exact (S := system) (hFP := fpData) h isPseudoUnitary)

end Z2Sq
end FusionCategory

#print axioms FusionCategory.Z2Sq.gadd_assoc
#print axioms FusionCategory.Z2Sq.w_cocycle
#print axioms FusionCategory.Z2Sq.pentagon_aux
#print axioms FusionCategory.Z2Sq.ring
#print axioms FusionCategory.Z2Sq.system
#print axioms FusionCategory.Z2Sq.associator_nontrivial
#print axioms FusionCategory.Z2Sq.kappa_val
#print axioms FusionCategory.Z2Sq.fpData
#print axioms FusionCategory.Z2Sq.isPseudoUnitary
#print axioms FusionCategory.Z2Sq.trivialPivotal_isSpherical
#print axioms FusionCategory.Z2Sq.trivialPivotal_dim_three
#print axioms FusionCategory.Z2Sq.J_ne_coboundary
#print axioms FusionCategory.Z2Sq.M_fails
#print axioms FusionCategory.Z2Sq.no_pivotal_dim_fpdim
#print axioms FusionCategory.Z2Sq.not_mult
#print axioms FusionCategory.Z2Sq.not_eno823
#print axioms FusionCategory.Z2Sq.not_eno823Exact
