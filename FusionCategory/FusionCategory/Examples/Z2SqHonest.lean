import FusionCategory.PseudoUnitary
import FusionCategory.DimMult

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
namespace Z2SqH

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

end Z2SqH
end FusionCategory

#print axioms FusionCategory.Z2SqH.gadd_assoc
#print axioms FusionCategory.Z2SqH.w_cocycle
#print axioms FusionCategory.Z2SqH.pentagon_aux
#print axioms FusionCategory.Z2SqH.ring
#print axioms FusionCategory.Z2SqH.system
#print axioms FusionCategory.Z2SqH.associator_nontrivial
#print axioms FusionCategory.Z2SqH.kappa_val
#print axioms FusionCategory.Z2SqH.fpData
#print axioms FusionCategory.Z2SqH.isPseudoUnitary
#print axioms FusionCategory.Z2SqH.trivialPivotal_isSpherical
#print axioms FusionCategory.Z2SqH.trivialPivotal_dim_three
#print axioms FusionCategory.Z2SqH.J_ne_coboundary
#print axioms FusionCategory.Z2SqH.M_fails
#print axioms FusionCategory.Z2SqH.no_pivotal_dim_fpdim
#print axioms FusionCategory.Z2SqH.not_mult
#print axioms FusionCategory.Z2SqH.not_eno823
#print axioms FusionCategory.Z2SqH.not_eno823Exact

/-! # PART 2 (member m2, swarm `smw0aylzp`): the honest twist `J = δ(κ)`

Everything above is m4's datum machinery (`Z2SqH.system`, the `J ≡ 1` witness),
verified and accepted in swarm `smw09611h`; only the namespace was renamed.  It
is *twist-generic*: `ring`, `F`, `Finv`, `ev`, `coev` and `pentagon_aux` never
mention `J`.  This part adds the second witness of the same datum, now with the
twist the rigid structure actually computes, and — more importantly — the
**forcing theorem** that says there is no other choice.

## What is new here

1. `deltaJ S` is the coboundary twist `δ(κ) a b c = κ_a κ_b / κ_c` on the fusion
   channels.  For an **arbitrary** `FusionSystem n ℝ` whose `κ` satisfies
   `κ_0 = 1` and `κ_i κ_{i*} = 1` (both hold here: `κ = (1,1,1,-1)`), the four
   twist laws `J_ne_zero`, `J_unit_left`, `J_unit_right`, `J_dual`,
   `J_coherent` are *theorems* — no case bash, no cocycle input.  `δ(κ)` is
   always a legal twist.
2. `systemH` is `system` with `J := δ(κ)`; only the five `J` fields change.
3. `pivotalH` is the nonconstant pivotal structure `p = κ⁻¹` (`p 3 = -1`,
   `p i = 1` otherwise), with `dim ≡ 1`, hence spherical with `dim = FPdim`.
4. **Forcing** (`J_eq_pivotal_ratio`, `J_eq_deltaJ_of_dim_one`): a pivotal
   structure determines `J` on every channel, and every pivotal structure with
   `dim ≡ 1` forces the carried twist to be `δ(κ)`.  Conversely
   (`J_eq_deltaJ_of_M`) the multiplicativity law `(M)` forces it too.  So the
   `J_match` qualification of Task 1.5(b) is a *consequence* of the corrected
   target on this datum, not extra data — and `(M)` fails for `J ≡ 1` for
   exactly that reason (`M_fails_structural`, a second proof of m4's `M_fails`).

Axiom budget: `[propext, Classical.choice, Quot.sound]`; `#print axioms` at the
bottom.
-/

namespace FusionCategory
namespace Z2SqH

/-! ## Part 2A — the coboundary twist `δ(κ)`: general theory -/

section DeltaTwist

variable {n : ℕ} {S : FusionSystem n ℝ}

/-- The coboundary twist `δ(κ)`: on the channel `(a,b;c)` it is
`κ_a κ_b / κ_c`, off the channels it is `1` (where no field constrains it). -/
noncomputable def deltaJ (S : FusionSystem n ℝ) (a b c : Fin n) : ℝ :=
  if 0 < S.ring.N a b c then S.kappa a * S.kappa b / S.kappa c else 1

theorem deltaJ_of_pos {a b c : Fin n} (h : 0 < S.ring.N a b c) :
    deltaJ S a b c = S.kappa a * S.kappa b / S.kappa c := by
  simp only [deltaJ, if_pos h]

theorem deltaJ_ne_zero {a b c : Fin n} (h : 0 < S.ring.N a b c) :
    deltaJ S a b c ≠ 0 := by
  rw [deltaJ_of_pos (S := S) h]
  exact div_ne_zero (mul_ne_zero (S.kappa_ne_zero a) (S.kappa_ne_zero b))
    (S.kappa_ne_zero c)

/-- `δ(κ)` is normalised on the left: `κ_0 = 1` kills both `κ` factors. -/
theorem deltaJ_unit_left (hn : 0 < n) (j : Fin n) :
    deltaJ S ⟨0, hn⟩ j j = 1 := by
  have hN : 0 < S.ring.N ⟨0, hn⟩ j j := by
    rw [S.ring.left_unit hn j j]; simp
  rw [deltaJ_of_pos (S := S) hN, kappa_unit (S := S) hn, one_mul]
  exact div_self (S.kappa_ne_zero j)

/-- `δ(κ)` is normalised on the right. -/
theorem deltaJ_unit_right (hn : 0 < n) (i : Fin n) :
    deltaJ S i ⟨0, hn⟩ i = 1 := by
  have hN : 0 < S.ring.N i ⟨0, hn⟩ i := by
    rw [S.ring.right_unit hn i i]; simp
  rw [deltaJ_of_pos (S := S) hN, kappa_unit (S := S) hn, mul_one]
  exact div_self (S.kappa_ne_zero i)

/-- `δ(κ)` is normalised on the duality channel, which is where the hypothesis
`κ_i κ_{i*} = 1` enters. -/
theorem deltaJ_dual (hn : 0 < n) (i : Fin n)
    (hκd : ∀ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) = 1) :
    deltaJ S i (S.ring.dual i) ⟨0, hn⟩ = 1 := by
  have hN : 0 < S.ring.N i (S.ring.dual i) ⟨0, hn⟩ :=
    PivotalStructure.dual_channel_pos (S := S) hn i
  rw [deltaJ_of_pos (S := S) hN, kappa_unit (S := S) hn, div_one]
  exact hκd i

/-- `δ(κ)` is coherent: both sides of `J a b e * J e c d = J b c f * J a f d`
telescope to `κ_a κ_b κ_c / κ_d`.  The associator does not enter. -/
theorem deltaJ_coherent {a b c d e f : Fin n}
    (h1 : 0 < S.ring.N a b e) (h2 : 0 < S.ring.N e c d)
    (h3 : 0 < S.ring.N b c f) (h4 : 0 < S.ring.N a f d) :
    deltaJ S a b e * deltaJ S e c d = deltaJ S b c f * deltaJ S a f d := by
  rw [deltaJ_of_pos (S := S) h1, deltaJ_of_pos (S := S) h2, deltaJ_of_pos (S := S) h3, deltaJ_of_pos (S := S) h4]
  have ha := S.kappa_ne_zero a
  have hb := S.kappa_ne_zero b
  have hc := S.kappa_ne_zero c
  have hd := S.kappa_ne_zero d
  have he := S.kappa_ne_zero e
  have hf := S.kappa_ne_zero f
  field_simp

/-- **`(M)` holds for `δ(κ)`** whenever `a ⊗ b` has a single channel in total
multiplicity one: with `Σ_c N a b c = 1`, the `(M)` sum
`Σ_c N^c_{ab} J^c_{ab} κ_c` equals `κ_a κ_b`.  This is the multiplicativity of
the dimension function, which is the hypothesis of the corrected target. -/
theorem deltaJ_M {a b : Fin n}
    (hsum : (∑ c : Fin n, (S.ring.N a b c : ℝ)) = 1) :
    (∑ c : Fin n, (S.ring.N a b c : ℝ) * deltaJ S a b c * S.kappa c) =
      S.kappa a * S.kappa b := by
  have hterm : ∀ c : Fin n, (S.ring.N a b c : ℝ) * deltaJ S a b c * S.kappa c =
      (S.ring.N a b c : ℝ) * (S.kappa a * S.kappa b) := by
    intro c
    by_cases h : 0 < S.ring.N a b c
    · rw [deltaJ_of_pos (S := S) h, mul_assoc, div_mul_cancel₀ _ (S.kappa_ne_zero c)]
    · have h0 : S.ring.N a b c = 0 := by omega
      rw [h0]
      norm_num
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_mul, hsum, one_mul]

/-! ### Forcing: the twist is not free data

`p_mon` reads `p_c = J^c_{ab} p_a p_b` on every channel, so a pivotal structure
*pins down* `J` on every channel where `N > 0`.  Hence:

* `J_eq_pivotal_ratio`: `J a b c = p_c / (p_a p_b)`;
* `J_eq_deltaJ_of_dim_one`: if in addition `dim ≡ 1`, then `p = κ⁻¹` and
  `J = δ(κ)` — the twist carried must be the derived one;
* `J_eq_deltaJ_of_M`: `(M)` on a unique channel forces the same value.

The content for the corrected target (Task 1.5(b)) is criterion 4's `J_match`:
on this datum it is a *theorem* about the datum, not a choice. -/

/-- A pivotal structure determines the twist on every channel. -/
theorem J_eq_pivotal_ratio (P : PivotalStructure S) {i j kk : Fin n}
    (h : 0 < S.ring.N i j kk) :
    S.J i j kk = (P.p kk : ℝ) / ((P.p i : ℝ) * (P.p j : ℝ)) := by
  rw [eq_div_iff (mul_ne_zero (P.p i).ne_zero (P.p j).ne_zero)]
  have hpm := P.p_mon i j kk h
  rw [hpm]
  ring

/-- If a pivotal structure has unit dimensions, its scalars are `κ⁻¹`. -/
theorem p_coe_eq_inv_kappa (P : PivotalStructure S)
    (hdim : ∀ i : Fin n, dim P i = 1) (i : Fin n) :
    (P.p i : ℝ) = (S.kappa i)⁻¹ := by
  have h : (P.p i : ℝ) * S.kappa i = 1 := by
    have h' := hdim i
    rw [PivotalStructure.dim_eq] at h'
    exact h'
  exact eq_inv_of_mul_eq_one_left h

/-- The same, read through `pVal`. -/
theorem pVal_eq_inv_kappa (P : PivotalStructure S)
    (hdim : ∀ i : Fin n, dim P i = 1) (i : Fin n) :
    P.pVal i = (S.kappa i)⁻¹ :=
  p_coe_eq_inv_kappa P hdim i

/-- **The twist is forced.**  Any pivotal structure of unit dimensions forces
the carried twist to be the coboundary `δ(κ)` on every channel. -/
theorem J_eq_deltaJ_of_dim_one (P : PivotalStructure S)
    (hdim : ∀ i : Fin n, dim P i = 1) {a b c : Fin n} (h : 0 < S.ring.N a b c) :
    S.J a b c = deltaJ S a b c := by
  rw [J_eq_pivotal_ratio P h, deltaJ_of_pos (S := S) h,
    p_coe_eq_inv_kappa P hdim a, p_coe_eq_inv_kappa P hdim b,
    p_coe_eq_inv_kappa P hdim c]
  have ha := S.kappa_ne_zero a
  have hb := S.kappa_ne_zero b
  have hc := S.kappa_ne_zero c
  field_simp

/-- **Conversely `(M)` forces the twist**, on a channel that is the only channel
of `a ⊗ b` and is of multiplicity one: the multiplicativity law `(M)` already
determines `J` there. -/
theorem J_eq_delta_of_M (J : Fin n → Fin n → Fin n → ℝ) {a b c₀ : Fin n}
    (hN : S.ring.N a b c₀ = 1)
    (huniq : ∀ c : Fin n, 0 < S.ring.N a b c → c = c₀)
    (hM : (∑ c : Fin n, (S.ring.N a b c : ℝ) * J a b c * S.kappa c) =
      S.kappa a * S.kappa b) :
    J a b c₀ = S.kappa a * S.kappa b / S.kappa c₀ := by
  have hpos : 0 < S.ring.N a b c₀ := by rw [hN]; norm_num
  rw [Finset.sum_eq_single c₀, hN] at hM
  · simp only [Nat.cast_one, one_mul] at hM
    rw [eq_div_iff (S.kappa_ne_zero c₀)]
    exact hM
  · intro c _ hc
    have h0 : S.ring.N a b c = 0 := by
      rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h' | h'
      · exact h'
      · exact absurd (huniq c h') hc
    rw [h0]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A `FusionSystem` whose twist satisfies `(M)` carries the coboundary twist on
every such channel: `J = δ(κ)`. -/
theorem J_eq_deltaJ_of_M {a b c₀ : Fin n}
    (hN : S.ring.N a b c₀ = 1)
    (huniq : ∀ c : Fin n, 0 < S.ring.N a b c → c = c₀)
    (hM : (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c) =
      S.kappa a * S.kappa b) :
    S.J a b c₀ = deltaJ S a b c₀ := by
  rw [J_eq_delta_of_M (S := S) S.J hN huniq hM,
    deltaJ_of_pos (S := S) (by rw [hN]; norm_num)]

end DeltaTwist

/-! ## Part 2B — the honest-twist witness `systemH` -/

/-- The twist `J = δ(κ)` of our datum. -/
noncomputable def Jd : Fin 4 → Fin 4 → Fin 4 → ℝ := deltaJ system

theorem kappa_sq_one (i : Fin 4) :
    system.kappa i * system.kappa (system.ring.dual i) = 1 := by
  rw [kappa_dual i]
  exact kappa_sq i

theorem Jd_ne_zero : ∀ i j kk : Fin 4, 0 < ring.N i j kk → Jd i j kk ≠ 0 :=
  fun _ _ _ h => deltaJ_ne_zero (S := system) h

theorem Jd_unit_left : ∀ (hn : 0 < 4) (j : Fin 4), Jd ⟨0, hn⟩ j j = 1 :=
  fun hn j => deltaJ_unit_left (S := system) hn j

theorem Jd_unit_right : ∀ (hn : 0 < 4) (i : Fin 4), Jd i ⟨0, hn⟩ i = 1 :=
  fun hn i => deltaJ_unit_right (S := system) hn i

theorem Jd_dual : ∀ (hn : 0 < 4) (i : Fin 4), Jd i (ring.dual i) ⟨0, hn⟩ = 1 :=
  fun hn i => deltaJ_dual (S := system) hn i (fun j => kappa_sq_one j)

theorem Jd_coherent : ∀ a b c d e f : Fin 4,
    0 < ring.N a b e → 0 < ring.N e c d → 0 < ring.N b c f → 0 < ring.N a f d →
    Jd a b e * Jd e c d = Jd b c f * Jd a f d :=
  fun _ _ _ _ _ _ h1 h2 h3 h4 => deltaJ_coherent (S := system) h1 h2 h3 h4

/-- **The honest-twist witness**: the same pointed `Vec^ω_{(Z/2)²}` datum as
`system`, with the twist changed to `J = δ(κ)`.  Only the five `J` fields
differ; `ring`, `F`, `Finv`, `ev`, `coev` and the snakes are literally the same
terms. -/
noncomputable def systemH : FusionSystem 4 ℝ where
  ring := ring
  mult_free := system.mult_free
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
  J := Jd
  J_ne_zero := Jd_ne_zero
  J_unit_left := Jd_unit_left
  J_unit_right := Jd_unit_right
  J_dual := Jd_dual
  ev_dual := fun i => rfl
  J_coherent := by
    intro a b c d e f h1 h2 h3 h4
    rw [Jd_coherent a b c d e f h1 h2 h3 h4]

/-- The FP-dimension data of the honest witness: definitionally the same as
`fpData` (`FPdim ≡ 1`), stated for `systemH.ring`.  An `abbrev` so that it
unfolds at reducible transparency, which the `IsPseudoUnitary`/`ENO823` target
statements need (`systemH` is a `def`, so `systemH.ring` is only semireducibly
`ring`). -/
abbrev fpDataH : FusionRing.FPData systemH.ring := fpData

theorem systemH_ring : systemH.ring = ring := rfl
theorem systemH_dual (i : Fin 4) : systemH.ring.dual i = i := rfl
theorem systemH_kappa (i : Fin 4) : systemH.kappa i = system.kappa i := rfl
theorem systemH_J (a b c : Fin 4) : systemH.J a b c = Jd a b c := rfl

/-- `κ` of the honest witness: `(1,1,1,-1)`. -/
theorem kappaH_val (i : Fin 4) : systemH.kappa i = if i = 3 then -1 else 1 :=
  kappa_val i

theorem kappaH_three : systemH.kappa 3 = -1 := kappa_three
theorem kappaH_zero : systemH.kappa 0 = 1 := kappa_zero
theorem kappaH_sq (i : Fin 4) : systemH.kappa i * systemH.kappa i = 1 := kappa_sq i

/-! ### The twist is the derived one (`J_match`) -/

/-- **`J_match`** for the honest witness: on every channel the carried twist is
`κ_a κ_b / κ_c = δ(κ)`.  Holds by construction — stated, as Task 1.5(b)
requires, so that it can be contrasted with `J_ne_coboundary` for `J ≡ 1`. -/
theorem J_match : ∀ a b c : Fin 4, 0 < ring.N a b c →
    systemH.J a b c = systemH.kappa a * systemH.kappa b / systemH.kappa c :=
  fun _ _ _ h => deltaJ_of_pos (S := system) h

/-- The false-`J` witness fails `J_match`: at `(2,1;3)` the carried twist `1`
is not `κ_2 κ_1 / κ_3 = -1`. -/
theorem J_match_fails_false :
    ¬ (∀ a b c : Fin 4, 0 < ring.N a b c →
        system.J a b c = system.kappa a * system.kappa b / system.kappa c) := by
  intro h
  have h1 := h 2 1 3 channel_two_one
  rw [J_apply, kappa_two, kappa_one, kappa_three] at h1
  norm_num at h1

/-! ### The nonconstant pivotal structure `p = 1/κ` -/

/-- `p i = κ_i⁻¹` as a unit. -/
noncomputable def pH (i : Fin 4) : ℝˣ := Units.mk0 ((systemH.kappa i)⁻¹) (inv_ne_zero (systemH.kappa_ne_zero i))

theorem pH_val (i : Fin 4) : (pH i : ℝ) = (systemH.kappa i)⁻¹ := by
  simp [pH]

/-- **The nonconstant pivotal structure** `p = 1/κ`: `p 0 = p 1 = p 2 = 1` and
`p 3 = -1`.  `p_mon` is the identity
`κ_c⁻¹ = (κ_a κ_b / κ_c) κ_a⁻¹ κ_b⁻¹`. -/
noncomputable def pivotalH : PivotalStructure systemH where
  p := pH
  p_unit := by
    intro hn
    apply Units.ext
    rw [pH_val, kappa_unit (S := systemH) hn]
    norm_num
  p_mon := by
    intro i j kk hN
    rw [pH_val, pH_val, pH_val, systemH_J, Jd, deltaJ_of_pos (S := system) hN]
    rw [show system.kappa kk = systemH.kappa kk from rfl,
      show system.kappa i = systemH.kappa i from rfl,
      show system.kappa j = systemH.kappa j from rfl]
    have hi := systemH.kappa_ne_zero i
    have hj := systemH.kappa_ne_zero j
    have hk := systemH.kappa_ne_zero kk
    field_simp

theorem pivotalH_val_one : pivotalH.pVal 1 = 1 := by
  show (pH 1 : ℝ) = 1
  rw [pH_val 1, systemH_kappa 1, kappa_one]
  norm_num

theorem pivotalH_val_three : pivotalH.pVal 3 = -1 := by
  show (pH 3 : ℝ) = -1
  rw [pH_val 3, systemH_kappa 3, kappa_three]
  norm_num

/-- The pivotal structure is genuinely **nonconstant**: `p 0 = 1 ≠ -1 = p 3`.
This is the contrast with the trivial `p ≡ 1` that the false-`J` witness
carries. -/
theorem pivotalH_val_zero : pivotalH.pVal 0 = 1 := by
  show (pH 0 : ℝ) = 1
  rw [pH_val 0, systemH_kappa 0, kappa_zero]
  norm_num

theorem pivotalH_nonconstant : pivotalH.pVal 0 ≠ pivotalH.pVal 3 := by
  rw [pivotalH_val_zero, pivotalH_val_three]
  norm_num

/-! ### Dimensions, sphericity, `dim = FPdim` -/

/-- Every simple has dimension `1` in this pivotal structure. -/
theorem dimH (i : Fin 4) : dim pivotalH i = 1 := by
  rw [PivotalStructure.dim_eq]
  show (pH i : ℝ) * systemH.kappa i = 1
  rw [pH_val i]
  exact inv_mul_cancel₀ (systemH.kappa_ne_zero i)

theorem dimH_pos (i : Fin 4) : 0 < dim pivotalH i := by
  rw [dimH i]; norm_num

/-- `dim p = FPdim p` on the nose (`FPdim ≡ 1` for a pointed system). -/
theorem dimH_eq_fpdim (i : Fin 4) : dim pivotalH i = algebraMap ℝ ℝ (fpDataH.fpdim i) := by
  rw [dimH i]
  show (1 : ℝ) = algebraMap ℝ ℝ 1
  norm_num

/-- **Sphericity**: every object is self-dual, so `dim (i*) = dim i`. -/
theorem sphericalH : pivotalH.IsSpherical :=
  pivotalH.spherical_of_selfdual (fun i => systemH_dual i)

/-- Total multiplicity one: `Σ_c N^c_{ab} = 1` for the pointed fusion rule. -/
theorem sum_N_eq_one (a b : Fin 4) : (∑ c : Fin 4, (N a b c : ℝ)) = 1 := by
  rw [Finset.sum_eq_single (gadd a b)]
  · have h : N a b (gadd a b) = 1 := by simp [N]
    rw [h]; norm_num
  · intro c _ hc
    have h : N a b c = 0 := by rw [N_eq_zero_iff]; exact hc
    rw [h]; norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`(M)` holds for the honest twist**: `Σ_c N^c_{ab} J^c_{ab} κ_c = κ_a κ_b`
on every channel — as it must, since `J = δ(κ)`.  Contrast `M_fails` for
`J ≡ 1` in the same datum. -/
theorem M_holds (a b : Fin 4) :
    (∑ c : Fin 4, (ring.N a b c : ℝ) * systemH.J a b c * systemH.kappa c) =
      systemH.kappa a * systemH.kappa b := by
  have hsum : (∑ c : Fin 4, (ring.N a b c : ℝ)) = 1 := sum_N_eq_one a b
  have h := deltaJ_M (S := system) hsum
  show (∑ c : Fin 4, (ring.N a b c : ℝ) * deltaJ system a b c * system.kappa c) =
    system.kappa a * system.kappa b
  exact h

/-- The channel of `a ⊗ b` is unique in this datum. -/
theorem N_channel_unique {a b c : Fin 4} (h : 0 < N a b c) : c = gadd a b :=
  N_pos_iff.mp h

/-- **`(M)` determines `J` here**: since the channel is unique, multiplicativity
of the dimension *forces* the twist `δ(κ)` — the forcing theorem instantiated at
the datum, so `J_match` is a consequence of `(M)`. -/
theorem M_forces_J_match (J : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hM : ∀ a b : Fin 4,
      (∑ c : Fin 4, (ring.N a b c : ℝ) * J a b c * system.kappa c) =
        system.kappa a * system.kappa b)
    (a b c : Fin 4) (hc : 0 < N a b c) :
    J a b c = system.kappa a * system.kappa b / system.kappa c := by
  have hc' : c = gadd a b := N_pos_iff.mp hc
  subst hc'
  exact J_eq_delta_of_M (S := system) J (a := a) (b := b) (c₀ := gadd a b)
    (by show N a b (gadd a b) = 1; rw [N_eq_one_iff])
    (fun c' h' => N_pos_iff.mp h') (hM a b)

/-- **Structural re-derivation of m4's refutation from the forcing theorem**:
any pivotal structure of the `J ≡ 1` datum with unit dimensions would force
`J = δ(κ)`, which fails at `(2,1;3)`.  This is the same fact as m4's
`no_pivotal_dim_fpdim`, proved without touching `p` directly. -/
theorem no_dim_one_of_false_J (P : PivotalStructure system) :
    ¬ (∀ i : Fin 4, dim P i = 1) := by
  intro hdim
  have h := J_eq_deltaJ_of_dim_one (S := system) (P := P) hdim
    (a := 2) (b := 1) (c := 3) channel_two_one
  rw [J_apply, deltaJ_of_pos (S := system) (a := 2) (b := 1) (c := 3) channel_two_one, kappa_two, kappa_one,
    kappa_three] at h
  norm_num at h

/-! ### Pseudo-unitarity and the positive instance of the corrected target -/

/-- `Σ_i κ_i κ_{i*} = 4`: the hypothesis of ENO 8.23 holds for the honest
witness (the `κ` did not change; only `J` did). -/
theorem isPseudoUnitaryH : IsPseudoUnitary systemH fpDataH := by
  unfold IsPseudoUnitary
  have hpt : ∀ i : Fin 4,
      systemH.kappa i * systemH.kappa (systemH.ring.dual i) = (1 : ℝ) := by
    intro i
    rw [systemH_dual i]
    exact kappaH_sq i
  have h4 : (∑ _i : Fin 4, (1 : ℝ)) = 4 := by norm_num [Fin.sum_univ_four]
  have hg : fpDataH.globalDim = 4 := by
    show (∑ i : Fin 4, ((1 : ℝ)) ^ 2) = 4
    norm_num [Fin.sum_univ_four]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), h4, hg]

/-- **`ENO823` holds for the honest twist**: the spherical pivotal structure
`p = 1/κ` has dimension exactly the FP-dimension `1`. -/
theorem ENO823H : ENO823 systemH fpDataH :=
  ⟨pivotalH, sphericalH, dimH_eq_fpdim⟩

/-- **The positive instance of the corrected target**: `ENO823Exact` holds for
`systemH` — the unique spherical pivotal structure of dimension `FPdim ≡ 1` is
`p = 1/κ`.  Compare m4's `not_eno823Exact` on the same datum with `J ≡ 1`: this
is the whole content of the `J_match` qualification. -/
theorem ENO823ExactH : ENO823Exact systemH fpDataH := by
  intro _
  refine ⟨pivotalH, ⟨sphericalH, dimH_pos, dimH_eq_fpdim⟩, ?_⟩
  intro P' hP'
  apply pivotal_ext (S := systemH)
  intro i
  have h1 : dim P' i = 1 := by
    have := hP'.2.2 i
    rw [this]
    show algebraMap ℝ ℝ 1 = (1 : ℝ)
    norm_num
  rw [h1, dimH i]

/-- The uniqueness clause, stated separately: any spherical pivotal structure
with the FP-dimensions is `p = 1/κ`. -/
theorem pivotalH_unique (P : PivotalStructure systemH) (_hsp : P.IsSpherical)
    (hdim : ∀ i : Fin 4, dim P i = algebraMap ℝ ℝ (fpDataH.fpdim i)) :
    P = pivotalH := by
  apply pivotal_ext (S := systemH)
  intro i
  have h1 : dim P i = 1 := by
    rw [hdim i]
    show algebraMap ℝ ℝ 1 = (1 : ℝ)
    norm_num
  rw [h1, dimH i]

/-! ### Non-degeneracy of the honest witness -/

/-- The twist really is nonconstant: `J 2 1 3 = κ_2 κ_1 / κ_3 = -1 ≠ 1`. -/
theorem Jd_nontrivial : systemH.J 2 1 3 = -1 := by
  rw [J_match 2 1 3 channel_two_one, systemH_kappa 2, systemH_kappa 1,
    systemH_kappa 3, kappa_two, kappa_one, kappa_three]
  norm_num

/-- The pivotal structure really is nonconstant in the same slot. -/
theorem pivotalH_nontrivial : pivotalH.pVal 3 = -1 ∧ pivotalH.pVal 1 = 1 :=
  ⟨pivotalH_val_three, pivotalH_val_one⟩

/-- The associator, the fusion rule and `κ` are untouched: the honest witness
lives on exactly the datum of the false-`J` witness. -/
theorem same_datum_F : systemH.F 2 1 3 0 3 2 = -1 := associator_nontrivial
theorem same_datum_coev (i : Fin 4) : systemH.coev i = system.coev i := rfl
theorem same_datum_F_list : systemH.F = system.F := rfl

end Z2SqH
end FusionCategory

/-! # PART 3 (member m4, swarm `smw7b5fyh`, direction d4): `(M)` at the hypothesis level

Part 1 built the datum `system` with the trivial twist `J ≡ 1` and refuted the
multiplicativity law there (`M_fails`); Part 2 built `systemH`, the same datum
with the honest twist `J = δ(κ) = κ_a κ_b / κ_c`, and proved `M_holds`.  This
part states both results at the level of the *named hypothesis*
`DimMultiplicative` of `FusionCategory/DimMult.lean`, and runs ENO 8.23 end to
end through `eno823Exact_of_dimMult_pseudoUnitary`:

* `dimMultH` — `DimMultiplicative systemH`: (M) for the honest twist;
* `not_dimMult` — `¬ DimMultiplicative system`: (M) for `J ≡ 1`.  With
  `pseudoUnitary_and_not_dimMult` this is the sharpness of the pair
  `(IsPseudoUnitary, DimMultiplicative)`: pseudo-unitarity alone does not give
  ENO 8.23;
* `dimMult_iff_J_match` — on this datum (M) is *equivalent* to the per-channel
  identity `J a b c = κ_a κ_b / κ_c` on every channel, i.e. to the `J_match`
  condition of WP3 Task 3.3 (the channel of `a ⊗ b` is unique).  The general
  engine behind the backward direction is
  `sum_N_mul_J_kappa_of_eq_ratio`/`dimMult_of_J_eq_kappa_ratio`: on any system
  whose channel sums are `1`, a twist that agrees with `δ(κ)` on the channels
  satisfies (M).  Both are stated over an **arbitrary field** `k`, and
  `dimMult_iff_dimEigen_kappa_of_J_eq_one` — `J ≡ 1` on the channels gives
  `DimMultiplicative S ↔ DimEigen S S.kappa` — is the form the other examples
  (Fibonacci, Ising, `VecZ2`, `VecZ2Twisted`, all with `J ≡ 1`) need: their (M)
  is the character identity for `κ`, and `fpdim_char` supplies it once
  `κ = FPdim` is known.  Nothing here is specific to `Vec^ω_{(Z/2)²}` except
  the instances;
* `not_dimEigen_falseJ`, `dimEigen_pivotalH` — the same content on the pivotal
  side through `dimMult_iff_dimEigen`: *no* pivotal structure of the `J ≡ 1`
  datum has a multiplicative dimension function, while `p = 1/κ` of the honest
  datum does (`dim_pivotalH_is_character` is the same statement computed
  directly, and `dimMultH_via_character` re-derives `dimMultH` from it, so the
  bridge and the computation agree);
* `not_trace_identity_falseJ`, `trace_identity_H` — the same on ENO's side
  through `trace_iff_dimMult`: for *every* `SqrtData` of `system` the trace
  identity `d_i d_j = Σ_c T^{ij}_c d_c` fails, and for every `SqrtData` of
  `systemH` it holds.  That is WP3's acceptance test, discharged per instance;
* `eno823ExactH_via_dimMult`, `eno823H_via_dimMult` — ENO 8.23 for `systemH`
  from `(M) + IsPseudoUnitary + pivotalH` through the capstone of
  `DimMult.lean`.  `ENO823ExactH` above proves the same statement directly, by
  hand; the capstone route is the one that scales to the examples.

`system` and `systemH` differ *only* in the five `J` fields: `ring`, `F`,
`Finv`, `ev`, `coev`, the snakes and `κ` are literally the same terms
(`same_datum_except_J`, kernel-checked below).  So `not_dimMult` versus
`dimMultH` is exactly the content of WP3 Task 3.3's `J_match`: on one and the
same `Vec^ω_{(Z/2)²}` datum, `IsPseudoUnitary` holds for both twists
(`isPseudoUnitary`, `isPseudoUnitaryH`), `ENO823` is false for `J ≡ 1`
(`not_eno823`) and true for `J = δ(κ)` (`ENO823ExactH`), and what decides it is
(M) — a property of the carried twist alone, carried here as a hypothesis
because the four twist laws of `FusionSystem` do not pin `J` down.

Axiom budget: `[propext, Classical.choice, Quot.sound]` (`#print axioms` in the
Part 3 audit at the bottom of the file).
-/

namespace FusionCategory
namespace Z2SqH

/-! ## The engine: a twist agreeing with `δ(κ)` on the channels satisfies (M) -/

section Engine

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}

/-- **`δ(κ)` satisfies (M) on pointed data, twist-generically** — over any field
`k`, so it applies to the `ℚ` and `ℂ` copies of the examples as well.  If every
channel sum `Σ_c N^c_{ab}` is `1` (true for pointed fusion rules, e.g.
`sum_N_eq_one` below) and `J` agrees with the coboundary `δ(κ)` on the channels,
then the (M) sum collapses: on a channel the `κ_c` cancels, and off the channels
`N^c_{ab} = 0`.  `deltaJ_M` is the special case `J = deltaJ S`; this form is
what makes the equivalence with `J_match` below possible. -/
theorem sum_N_mul_J_kappa_of_eq_ratio
    (hunit : ∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : k)) = 1)
    (J : Fin n → Fin n → Fin n → k)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      J a b c = S.kappa a * S.kappa b / S.kappa c) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * J a b c * S.kappa c) =
        S.kappa a * S.kappa b := by
  intro a b
  have hterm : ∀ c : Fin n, (S.ring.N a b c : k) * J a b c * S.kappa c
      = (S.ring.N a b c : k) * (S.kappa a * S.kappa b) := by
    intro c
    by_cases h : 0 < S.ring.N a b c
    · rw [hJ a b c h, mul_assoc, div_mul_cancel₀ _ (S.kappa_ne_zero c)]
    · have h0 : S.ring.N a b c = 0 := by omega
      rw [h0]
      simp
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_mul, hunit a b, one_mul]

/-- **The honest twist always satisfies (M)** on pointed data: if the carried
twist is the coboundary `δ(κ)` on every channel then `DimMultiplicative S`.
On pointed data `(M)` is therefore automatic — the content of (M) is entirely in
the *non*-pointed examples (Fibonacci, Ising, Yang–Lee), where a channel sum is
`2`.  `Z2SqH.dimMultH` is the instance, and `dimMult_iff_J_match` below is the
converse at this datum. -/
theorem dimMult_of_J_eq_kappa_ratio
    (hunit : ∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : k)) = 1)
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = S.kappa a * S.kappa b / S.kappa c) :
    DimMultiplicative S :=
  sum_N_mul_J_kappa_of_eq_ratio hunit S.J hJ

/-- **For a trivial twist, (M) is exactly `κ` being a character of the fusion
ring**: `DimMultiplicative S ↔ DimEigen S S.kappa`.  This is the reduction the
examples with `J ≡ 1` need — Fibonacci, Ising and `VecZ2Twisted` all have
`J ≡ 1`, so their (M) is the character identity for `κ`, which is
`fpdim_char` once `κ = FPdim` is known (`kappa_val`).  The forward direction
needs no hypothesis at all beyond the triviality of `J` on the channels; the
backward direction is the same term-by-term collapse as above. -/
theorem dimMult_iff_dimEigen_kappa_of_J_eq_one
    (hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c → S.J a b c = 1) :
    DimMultiplicative S ↔ DimEigen S S.kappa := by
  constructor
  · intro hM a b
    rw [← hM a b]
    exact Finset.sum_congr rfl (fun c _ => by
      by_cases h : 0 < S.ring.N a b c
      · rw [hJ a b c h]; ring
      · have h0 : S.ring.N a b c = 0 := by omega
        rw [h0]; simp)
  · intro hκ a b
    rw [← hκ a b]
    exact Finset.sum_congr rfl (fun c _ => by
      by_cases h : 0 < S.ring.N a b c
      · rw [hJ a b c h]; ring
      · have h0 : S.ring.N a b c = 0 := by omega
        rw [h0]; simp)

end Engine

/-! ## `(M)` on the two twists of `Vec^ω_{(Z/2)²}` -/

/-- **(M) holds for the honest twist `J = δ(κ)`** — `M_holds` read at the level
of the hypothesis `DimMultiplicative` of `DimMult.lean`. -/
theorem dimMultH : DimMultiplicative systemH := by
  intro a b
  exact M_holds a b

/-- The channel form of `dimMultH`, with the fields of `systemH` visible. -/
theorem dimMultH_apply (a b : Fin 4) :
    (∑ c : Fin 4, (systemH.ring.N a b c : ℝ) * systemH.J a b c * systemH.kappa c)
      = systemH.kappa a * systemH.kappa b :=
  dimMultH a b

/-- **(M) fails for the trivial twist `J ≡ 1`**, at the level of
`DimMultiplicative`: `M_fails` intersected with the definition.  Since `system`
supplies every field of `FusionSystem`, (M) is *not* a consequence of the
signature. -/
theorem not_dimMult : ¬ DimMultiplicative system := by
  intro hM
  exact M_fails (hM 2 1)

/-- **`κ = (1,1,1,-1)` is not a character of the fusion ring**: at `(2,1)` the
unique channel is `3` and `κ_3 = -1 ≠ 1 = κ_2 κ_1`.  Through
`dimMult_iff_dimEigen_kappa_of_J_eq_one` this is `M_fails` seen on the pivotal
side, and it is what refutes ENO 8.23 for the false twist. -/
theorem not_dimEigen_kappa : ¬ DimEigen system system.kappa :=
  fun h => not_dimMult
    ((dimMult_iff_dimEigen_kappa_of_J_eq_one (S := system)
      (fun a b c _ => J_apply a b c)).mpr h)

/-- **Pseudo-unitarity alone does not give ENO 8.23**: the `J ≡ 1` witness
satisfies `IsPseudoUnitary` and fails (M).  The companion statement for the
other half of the pair ((M) without `IsPseudoUnitary`) is Yang–Lee's. -/
theorem pseudoUnitary_and_not_dimMult :
    IsPseudoUnitary system fpData ∧ ¬ DimMultiplicative system :=
  ⟨isPseudoUnitary, not_dimMult⟩

/-- **On this datum, (M) *is* `J_match`.**  Since the channel of `a ⊗ b` is
unique (`sum_N_eq_one`), the sum identity `DimMultiplicative` is equivalent to
the per-channel identity `J a b c = κ_a κ_b / κ_c` on every channel: forward is
`M_forces_J_match` (via the forcing theorem `J_eq_delta_of_M`), backward is the
engine `sum_N_mul_J_kappa_of_eq_ratio`.  So the `J_match` qualification of WP3
Task 3.3, at the hypothesis level, is precisely `DimMultiplicative`. -/
theorem dimMult_iff_J_match (J : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∀ a b : Fin 4,
        (∑ c : Fin 4, (ring.N a b c : ℝ) * J a b c * system.kappa c) =
          system.kappa a * system.kappa b) ↔
      (∀ a b c : Fin 4, 0 < ring.N a b c →
        J a b c = system.kappa a * system.kappa b / system.kappa c) := by
  constructor
  · intro hM a b c hc
    exact M_forces_J_match J hM a b c hc
  · intro hJ
    exact sum_N_mul_J_kappa_of_eq_ratio (S := system) (fun a b => sum_N_eq_one a b) J
      (fun a b c hc => hJ a b c hc)

/-! ## The pivotal side: which dimension functions are characters -/

/-- **No pivotal structure of the `J ≡ 1` datum has a multiplicative
dimension.**  Through the bridge `dimMult_iff_dimEigen`: `¬ DimMultiplicative`
discharges `¬ DimEigen` at *every* pivotal structure at once.  This is m4's
`not_mult` re-derived from the hypothesis. -/
theorem not_dimEigen_falseJ (P : PivotalStructure system) :
    ¬ DimEigen system (dim P) :=
  fun h => not_dimMult ((dimMult_iff_dimEigen P).mpr h)

/-- The dimension function of the honest datum's pivotal structure `p = 1/κ` is
a character of the fusion ring. -/
theorem dimEigen_pivotalH : DimEigen systemH (dim pivotalH) :=
  dimEigen_of_dimMult dimMultH pivotalH

/-- The same, computed directly: `dim pivotalH ≡ 1` and `Σ_c N^c_{ab} = 1`.
Agreement with `dimEigen_pivotalH` is the consistency of the bridge with the
explicit dimension function. -/
theorem dim_pivotalH_is_character (a b : Fin 4) :
    (∑ c : Fin 4, (systemH.ring.N a b c : ℝ) * dim pivotalH c)
      = dim pivotalH a * dim pivotalH b := by
  have hsum : (∑ c : Fin 4, (systemH.ring.N a b c : ℝ)) = 1 := sum_N_eq_one a b
  have hterm : ∀ c : Fin 4, (systemH.ring.N a b c : ℝ) * dim pivotalH c
      = (systemH.ring.N a b c : ℝ) := fun c => by rw [dimH c, mul_one]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), hsum, dimH a, dimH b]
  norm_num

/-- A second, independent proof of (M) for the honest twist: through the
character form `dim_pivotalH_is_character` and the bridge
`dimMult_iff_dimEigen`.  It agrees with `dimMultH`, which was read off
`M_holds`; both routes are kernel-checked. -/
theorem dimMultH_via_character : DimMultiplicative systemH :=
  (dimMult_iff_dimEigen pivotalH).mpr dim_pivotalH_is_character

/-! ## ENO's side: the trace identity `d_i d_j = Σ_c T^{ij}_c d_c` -/

/-- **ENO's trace identity fails for every square root of `(−)****` on the
`J ≡ 1` datum.**  `trace_iff_dimMult` identifies the trace identity of a
`SqrtData` with (M), and (M) is false here.  This is WP3's acceptance test
applied to the false twist: no choice of `a` saves it. -/
theorem not_trace_identity_falseJ (A : SqrtData system) :
    ¬ (∀ i j : Fin 4,
      A.d i * A.d j =
        ∑ c : Fin 4, (system.ring.N i j c : ℝ) * A.b i j c * A.d c) :=
  fun h => not_dimMult ((trace_iff_dimMult A).mp h)

/-- ...and it holds for every square root on the honest datum. -/
theorem trace_identity_H (A : SqrtData systemH) :
    ∀ i j : Fin 4,
      A.d i * A.d j =
        ∑ c : Fin 4, (systemH.ring.N i j c : ℝ) * A.b i j c * A.d c :=
  (trace_iff_dimMult A).mpr dimMultH

/-! ## ENO 8.23 for the honest twist, through the `DimMult` capstone -/

/-- **ENO Proposition 8.23 for `systemH`, from `(M) + IsPseudoUnitary`** — the
capstone `eno823Exact_of_dimMult_pseudoUnitary` instantiated at the honest
twist, with the pivotal structure `p = 1/κ` witnessing the antecedent.  `PFUnique`
is not used.  `ENO823ExactH` above is the same statement proved by hand. -/
theorem eno823ExactH_via_dimMult : ENO823Exact systemH fpDataH :=
  eno823Exact_of_dimMult_pseudoUnitary (S := systemH) (n := 4) fpDataH
    (by norm_num) dimMultH isPseudoUnitaryH pivotalH

/-- The bare form, through the bare capstone. -/
theorem eno823H_via_dimMult : ENO823 systemH fpDataH :=
  eno823_of_dimMult_pseudoUnitary (S := systemH) (n := 4) fpDataH
    (by norm_num) dimMultH isPseudoUnitaryH pivotalH

/-! ## The two twists live on one datum -/

/-- **`system` and `systemH` differ only in the five `J` fields.**
Kernel-checked: the fusion ring, the associator and its inverse, `ev`, `coev`
and `κ` are the same terms; the twist is not.  Together with
`pseudoUnitary_and_not_dimMult` and `dimMultH` this is WP3 Task 3.3's `J_match`
statement: same datum, same pseudo-unitarity, opposite (M). -/
theorem same_datum_except_J :
    systemH.ring = system.ring ∧ systemH.F = system.F ∧
      systemH.Finv = system.Finv ∧ systemH.ev = system.ev ∧
      systemH.coev = system.coev ∧
      (∀ i : Fin 4, systemH.kappa i = system.kappa i) ∧
      systemH.J ≠ system.J := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, (fun _ => rfl), ?_⟩
  intro h
  have h2 : systemH.J 2 1 3 = system.J 2 1 3 := by rw [h]
  rw [Jd_nontrivial, J_apply] at h2
  norm_num at h2

end Z2SqH
end FusionCategory

/-! ## Axiom audit (Part 2) -/

#print axioms FusionCategory.Z2SqH.deltaJ_of_pos
#print axioms FusionCategory.Z2SqH.deltaJ_ne_zero
#print axioms FusionCategory.Z2SqH.deltaJ_unit_left
#print axioms FusionCategory.Z2SqH.deltaJ_unit_right
#print axioms FusionCategory.Z2SqH.deltaJ_dual
#print axioms FusionCategory.Z2SqH.deltaJ_coherent
#print axioms FusionCategory.Z2SqH.deltaJ_M
#print axioms FusionCategory.Z2SqH.J_eq_pivotal_ratio
#print axioms FusionCategory.Z2SqH.pVal_eq_inv_kappa
#print axioms FusionCategory.Z2SqH.J_eq_deltaJ_of_dim_one
#print axioms FusionCategory.Z2SqH.J_eq_deltaJ_of_M
#print axioms FusionCategory.Z2SqH.systemH
#print axioms FusionCategory.Z2SqH.J_match
#print axioms FusionCategory.Z2SqH.pivotalH
#print axioms FusionCategory.Z2SqH.pivotalH_nonconstant
#print axioms FusionCategory.Z2SqH.dimH
#print axioms FusionCategory.Z2SqH.sphericalH
#print axioms FusionCategory.Z2SqH.M_holds
#print axioms FusionCategory.Z2SqH.M_forces_J_match
#print axioms FusionCategory.Z2SqH.no_dim_one_of_false_J
#print axioms FusionCategory.Z2SqH.isPseudoUnitaryH
#print axioms FusionCategory.Z2SqH.ENO823H
#print axioms FusionCategory.Z2SqH.ENO823ExactH
#print axioms FusionCategory.Z2SqH.pivotalH_unique
#print axioms FusionCategory.Z2SqH.J_match_fails_false

/-! ## Axiom audit (Part 3, direction d4) -/
#print axioms FusionCategory.Z2SqH.sum_N_mul_J_kappa_of_eq_ratio
#print axioms FusionCategory.Z2SqH.dimMult_of_J_eq_kappa_ratio
#print axioms FusionCategory.Z2SqH.dimMult_iff_dimEigen_kappa_of_J_eq_one
#print axioms FusionCategory.Z2SqH.dimMultH
#print axioms FusionCategory.Z2SqH.dimMultH_apply
#print axioms FusionCategory.Z2SqH.not_dimMult
#print axioms FusionCategory.Z2SqH.pseudoUnitary_and_not_dimMult
#print axioms FusionCategory.Z2SqH.not_dimEigen_kappa
#print axioms FusionCategory.Z2SqH.dimMult_iff_J_match
#print axioms FusionCategory.Z2SqH.not_dimEigen_falseJ
#print axioms FusionCategory.Z2SqH.dimEigen_pivotalH
#print axioms FusionCategory.Z2SqH.dim_pivotalH_is_character
#print axioms FusionCategory.Z2SqH.dimMultH_via_character
#print axioms FusionCategory.Z2SqH.not_trace_identity_falseJ
#print axioms FusionCategory.Z2SqH.trace_identity_H
#print axioms FusionCategory.Z2SqH.eno823ExactH_via_dimMult
#print axioms FusionCategory.Z2SqH.eno823H_via_dimMult
#print axioms FusionCategory.Z2SqH.same_datum_except_J

/-! ## Field-by-field audit of the honest witness

`systemH` is a structure literal with **every** field of HEAD's `FusionSystem`
signature supplied; nothing is inherited by a default or a `sorry` (the structure
has no default values, so this is enforced by the elaborator).  The five `J`
fields are the only ones that differ from m4's `system`, and they are restated
here as `example`s so that the audit is visible in the file rather than only in
the definition; the `#check`s after them print the type of every field of
`systemH`, which is exactly the statement that had to be -- and was -- proved. -/

namespace FusionCategory
namespace Z2SqH

example : ∀ i j kk : Fin 4, 0 < ring.N i j kk → systemH.J i j kk ≠ 0 :=
  systemH.J_ne_zero

example : ∀ (hn : 0 < 4) (j : Fin 4), systemH.J ⟨0, hn⟩ j j = 1 :=
  systemH.J_unit_left

example : ∀ (hn : 0 < 4) (i : Fin 4), systemH.J i ⟨0, hn⟩ i = 1 :=
  systemH.J_unit_right

example : ∀ (hn : 0 < 4) (i : Fin 4), systemH.J i (systemH.ring.dual i) ⟨0, hn⟩ = 1 :=
  systemH.J_dual

example : ∀ a b c d e f : Fin 4,
    0 < systemH.ring.N a b e → 0 < systemH.ring.N e c d →
    0 < systemH.ring.N b c f → 0 < systemH.ring.N a f d →
    systemH.J a b e * systemH.J e c d * systemH.F a b c d e f
      = systemH.J b c f * systemH.J a f d * systemH.F a b c d e f :=
  systemH.J_coherent

#check FusionCategory.Z2SqH.systemH.ring
#check FusionCategory.Z2SqH.systemH.mult_free
#check FusionCategory.Z2SqH.systemH.F
#check FusionCategory.Z2SqH.systemH.F_support
#check FusionCategory.Z2SqH.systemH.pentagon
#check FusionCategory.Z2SqH.systemH.F_unit_left
#check FusionCategory.Z2SqH.systemH.F_unit_right
#check FusionCategory.Z2SqH.systemH.Finv
#check FusionCategory.Z2SqH.systemH.Finv_support
#check FusionCategory.Z2SqH.systemH.Finv_comp
#check FusionCategory.Z2SqH.systemH.F_comp_inv
#check FusionCategory.Z2SqH.systemH.ev
#check FusionCategory.Z2SqH.systemH.coev
#check FusionCategory.Z2SqH.systemH.ev_ne_zero
#check FusionCategory.Z2SqH.systemH.coev_ne_zero
#check FusionCategory.Z2SqH.systemH.snake_left
#check FusionCategory.Z2SqH.systemH.snake_right
#check FusionCategory.Z2SqH.systemH.J
#check FusionCategory.Z2SqH.systemH.J_ne_zero
#check FusionCategory.Z2SqH.systemH.J_unit_left
#check FusionCategory.Z2SqH.systemH.J_unit_right
#check FusionCategory.Z2SqH.systemH.J_dual
#check FusionCategory.Z2SqH.systemH.J_coherent

end Z2SqH
end FusionCategory
