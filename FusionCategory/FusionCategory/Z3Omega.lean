import FusionCategory.System
import FusionCategory.DerivedJPointed
import FusionCategory.DerivedJCoherent
import FusionCategory.DerivedJMate

/-!
# `Vec^ω_{Z/3}`: the first legal datum with `i* ≠ i`

`Examples/Z3Pointed.lean` records as *owed* a witness of `FusionSystem` in which
some simple satisfies `i* ≠ i`, so that the two associator entries that the two
snake equations involve — `F^{i i* i}_i(0,0)` and `F^{i* i i*}_{i*}(0,0)` — are
entries of *different* blocks.  Every inhabitant in the tree has `dual = id`
(`VecZ2`, `VecZ2Twisted`, `Z2SqHonest`, `Z2SqFalseJ`, `Fibonacci`, `Ising`,
`Ostrik k2210`, `YangLee`), so no theorem of the derived-J layer has ever been
instantiated off the self-dual locus.

This file supplies that witness: `Vec^ω_{Z/3}` for the non-trivial `3`-cocycle

  `ω(a,b,c) = ζ^(a * ⌊(b+c)/3⌋)`,   `ζ = 2 ∈ ZMod 7`, `ζ³ = 1`, `ζ ≠ 1`,

which is normalised, satisfies the cocycle identity
`ω(a,b,c)·ω(a,b+c,d)·ω(b,c,d) = ω(a+b,c,d)·ω(a,b,c+d)` (the pentagon of
`System.lean` at this associator: on a pointed ring the F-symbol is `ω` on the
unique channel), and satisfies `ω(i,i*,i)·ω(i*,i,i*) = 1`, which is exactly the
consistency of the two snakes.  The field is `ZMod 7`, where `2` is a primitive
cube root of unity, so every axiom is a *closed* decidable statement and the
whole datum is checked by `decide`/`norm_case` with no analysis.

The two blocks the owed witness is about, for `i = 1 = g` (`i* = 2 = g²`), are

  `F   1 2 1 1 0 0 = ζ`   (`F^{i i* i}_i(0,0)`, the left snake)
  `Finv 2 1 2 2 0 0 = ζ`   (`(F^{i* i i*}_{i*})⁻¹(0,0)`, the right snake)

and `κ g = 1/ω(g,g²,g) = ζ²`, `κ g² = 1/ω(g²,g,g²) = ζ`: unlike every previous
witness, `κ` is not constant, so the duality normalisation is a genuine test.

Consequences recorded at the end: the datum is pointed, so
`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed` applies and gives
`derivedJGen = κ_a κ_b / κ_c` on every channel — the first instantiation of that
theorem on data with `i* ≠ i` — and since `κ` happens to be a character here,
`derivedJGen ≡ 1`, so the fourth law and the pivotal factor hold trivially on
this datum.  That is the *expected* outcome (pointed categories are pivotal);
what is new is that the boundary bookkeeping of `pairScalar`/`derivedJGen`,
which is built out of duals, is now exercised where `i* ≠ i`.

## What is landed (all kernel-checked, axiom budget `[propext, Classical.choice, Quot.sound]`)

* `Z3Omega.system : FusionSystem 3 (ZMod 7)` — all 24 fields; the first inhabitant
  with `dual ≠ id`, so the associator entries of the two snake equations are entries
  of different blocks (`loop_entries`).
* `Z3Omega.dual_ne_id`, `Z3Omega.pointed`.
* `Z3Omega.derivedJGen_eq_kappa` — `derivedJGen = κ_a κ_b / κ_c` on channels, the
  first instantiation of the general pointed theorem off the self-dual locus.
* `Z3Omega.derivedJGen_eq_one` — `κ` is a character here, so the derived twist is
  trivial on every channel; `Z3Omega.exists_pivotalFactor` records the target's
  positive shape `∃ φ, ∀ i, φ i ≠ 0 ∧ derivedJGen = φ_a φ_b / φ_c`.
* `Z3Omega.derivedJGen_coherent` — the retained fourth law for the derived twist.
* `Z3Omega.exists_fixpoint` — the twist is computed, not carried: a legal
  `FusionSystem` on the same ring/`F`/`Finv`/`ev`/`coev` with `J = derivedJGen`.
* `Z3Omega.pairScalar_ne_zero`, `Z3Omega.pivotalFactor_one` — no degenerate pairing
  on this datum, and the pivotal factor is `φ ≡ 1`.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

open FusionCategory

namespace Z3Omega

/-- The field: `ZMod 7`, in which `2` is a primitive cube root of unity. -/
abbrev k : Type := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive cube root of unity in `ZMod 7`. -/
def zeta : k := 2

theorem zeta_sq : zeta * zeta = 4 := by decide
theorem zeta_cube : zeta ^ 3 = 1 := by decide
theorem zeta_ne_zero : zeta ≠ 0 := by decide
theorem zeta_ne_one : zeta ≠ 1 := by decide

/-! ## The fusion ring: `Z/3`, dual = negation -/

/-- Fusion rules of `Vec_{Z/3}`: `N a b c = 1` iff `c = a + b` in `Z/3`. -/
def N (a b c : Fin 3) : ℕ := if a + b = c then 1 else 0

theorem N_pos_iff (a b c : Fin 3) : 0 < N a b c ↔ a + b = c := by
  unfold N; split <;> simp_all

/-- The duality: `i* = -i`.  This is the first witness with `dual ≠ id`. -/
def dual (i : Fin 3) : Fin 3 := -i

theorem dual_one : dual 1 = 2 := by decide
theorem dual_two : dual 2 = 1 := by decide
theorem dual_zero : dual 0 = 0 := by decide

/-- The fusion ring of `Vec_{Z/3}`. -/
def ring : FusionRing 3 where
  N := N
  dual := dual
  dual_involutive := by intro i; simp [dual]
  dual_zero := by intro _; simp [dual]
  left_unit := by
    intro _ i j
    show N 0 i j = if i = j then 1 else 0
    unfold N; simp
  right_unit := by
    intro _ i j
    show N i 0 j = if i = j then 1 else 0
    unfold N; simp
  dual_coeff := by
    intro _ i j
    show N i j 0 = if j = dual i then 1 else 0
    fin_cases i <;> fin_cases j <;> decide
  associativity := by
    intro i j kk l
    fin_cases i <;> fin_cases j <;> fin_cases kk <;> fin_cases l <;> decide
  dual_symm := by
    intro i j kk
    fin_cases i <;> fin_cases j <;> fin_cases kk <;> decide

/-! ## The associator: the non-trivial cyclic cocycle -/

/-- The cocycle `ω(a,b,c) = ζ^(a ⌊(b+c)/3⌋)`, as a value in `ZMod 7`. -/
def om (a b c : Fin 3) : k := zeta ^ (a.val * ((b.val + c.val) / 3))

/-- The associator, supported on the fusion channels of `a b c → d`. -/
def F (a b c d e f : Fin 3) : k :=
  if a + b = e ∧ e + c = d ∧ b + c = f ∧ a + f = d then om a b c else 0

/-! ### The pentagon, by `decide` on all `3^10` label tuples -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem F_pentagon : ∀ a b c d e i j r x : Fin 3,
    (∑ kk : Fin 3, F a b c x e kk * F a kk d r x j * F b c d j kk i) =
      F e c d r x i * F a b i r e j := by
  decide

/-! ### The unit axioms and the inverse laws -/

set_option maxHeartbeats 4000000 in
theorem F_unit_left : ∀ (hn : 0 < 3) (b c d f : Fin 3), 0 < N b c f →
    F ⟨0, hn⟩ b c d b f = if d = f then 1 else 0 := by
  intro hn b c d f h
  show F 0 b c d b f = if d = f then 1 else 0
  fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases f <;>
    simp_all [F, N, om]

set_option maxHeartbeats 4000000 in
theorem F_unit_right : ∀ (hn : 0 < 3) (a b d e : Fin 3), 0 < N a b e →
    F a b ⟨0, hn⟩ d e b = if d = e then 1 else 0 := by
  intro hn a b d e h
  show F a b 0 d e b = if d = e then 1 else 0
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp_all [F, N, om]

theorem F_support : ∀ a b c d e f : Fin 3,
    ¬ (0 < N a b e ∧ 0 < N e c d ∧ 0 < N b c f ∧ 0 < N a f d) → F a b c d e f = 0 := by
  intro a b c d e f h
  unfold F
  exact if_neg (fun hc => h ⟨(N_pos_iff _ _ _).mpr hc.1, (N_pos_iff _ _ _).mpr hc.2.1,
    (N_pos_iff _ _ _).mpr hc.2.2.1, (N_pos_iff _ _ _).mpr hc.2.2.2⟩)

/-! ### The inverse associator, with the inverse cocycle written as a table -/

/-- `ζ⁻¹`, `ζ⁻²`, `1⁻¹` as a table on the exponent of `ω`: the inverse of `ZMod 7`
does not reduce in the kernel, so the inverse cocycle is spelled out. -/
def omInv (a b c : Fin 3) : k :=
  if a.val * ((b.val + c.val) / 3) = 0 then 1
  else if a.val * ((b.val + c.val) / 3) = 1 then 4 else 2

/-- The inverse associator. -/
def Finv (a b c d f e : Fin 3) : k :=
  if b + c = f ∧ a + f = d ∧ a + b = e ∧ e + c = d then omInv a b c else 0

theorem Finv_support : ∀ a b c d f e : Fin 3,
    ¬ (0 < N b c f ∧ 0 < N a f d ∧ 0 < N a b e ∧ 0 < N e c d) → Finv a b c d f e = 0 := by
  intro a b c d f e h
  unfold Finv
  exact if_neg (fun hc => h ⟨(N_pos_iff _ _ _).mpr hc.1, (N_pos_iff _ _ _).mpr hc.2.1,
    (N_pos_iff _ _ _).mpr hc.2.2.1, (N_pos_iff _ _ _).mpr hc.2.2.2⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem Finv_comp : ∀ a b c d f' f : Fin 3,
    0 < N b c f' → 0 < N a f' d → 0 < N b c f → 0 < N a f d →
    (∑ e : Fin 3, Finv a b c d f' e * F a b c d e f) = if f' = f then 1 else 0 := by
  simp only [Fin.sum_univ_three]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem F_comp_inv : ∀ a b c d e' e : Fin 3,
    0 < N a b e' → 0 < N e' c d → 0 < N a b e → 0 < N e c d →
    (∑ f : Fin 3, Finv a b c d f e' * F a b c d e f) = if e' = e then 1 else 0 := by
  simp only [Fin.sum_univ_three]
  decide

/-! ### The duality normalisation: `ev = 1`, `coev = (1, ζ², ζ)` -/

/-- Evaluation: identically `1` (the gauge in which `ev` is dual-invariant). -/
def ev (_ : Fin 3) : k := 1

/-- Coevaluation, as a table: `coev i = 1/ω(i,i*,i)`, the left snake's normalisation. -/
def coev (i : Fin 3) : k := if i = 0 then 1 else if i = 1 then 4 else 2

/-- The duality normalisation `κ i = coev i * ev i`. -/
def kap (i : Fin 3) : k := coev i * ev i

/-- The inverse of `κ`, as a table (`κ = (1, ζ², ζ)`, so `κ⁻¹ = (1, ζ, ζ²)`). -/
def kapInv (i : Fin 3) : k := if i = 0 then 1 else if i = 1 then 2 else 4

theorem kap_zero : kap 0 = 1 := by decide
theorem kap_one : kap 1 = 4 := by decide
theorem kap_two : kap 2 = 2 := by decide

theorem kap_ne_zero (i : Fin 3) : kap i ≠ 0 := by
  fin_cases i <;> decide

theorem kapInv_ne_zero (i : Fin 3) : kapInv i ≠ 0 := by
  fin_cases i <;> decide

theorem kap_mul_kapInv (i : Fin 3) : kap i * kapInv i = 1 := by
  fin_cases i <;> decide

/-- The normalisation is not constant: the first witness in which `κ` is a
genuine test rather than `1`. -/
theorem kap_not_const : kap 1 ≠ kap 2 := by decide

theorem kap_dual_mul (i : Fin 3) : kap i * kap (dual i) = 1 := by
  fin_cases i <;> decide

set_option maxHeartbeats 1000000 in
theorem snake_left : ∀ (hn : 0 < 3) (i : Fin 3),
    coev i * ev i * F i (dual i) i i ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro hn i
  show coev i * ev i * F i (dual i) i i 0 0 = 1
  fin_cases i <;> decide

set_option maxHeartbeats 1000000 in
theorem snake_right : ∀ (hn : 0 < 3) (i : Fin 3),
    coev i * ev i * Finv (dual i) i (dual i) (dual i) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
  intro hn i
  show coev i * ev i * Finv (dual i) i (dual i) (dual i) 0 0 = 1
  fin_cases i <;> decide

theorem ev_dual : ∀ i : Fin 3, ev (dual i) = ev i := by
  intro i; rfl

theorem coev_ne_zero (i : Fin 3) : coev i ≠ 0 := by
  fin_cases i <;> decide

/-! ### The twist: the coboundary `δ(κ)` of the duality normalisation -/

/-- The twist `J a b c = κ a · κ b / κ c`, with `κ c⁻¹` as the table `kapInv`. -/
def J (a b c : Fin 3) : k := kap a * kap b * kapInv c

theorem J_ne_zero : ∀ i j kk : Fin 3, 0 < N i j kk → J i j kk ≠ 0 := by
  intro i j kk _
  exact mul_ne_zero (mul_ne_zero (kap_ne_zero i) (kap_ne_zero j)) (kapInv_ne_zero kk)

theorem J_unit_left : ∀ (hn : 0 < 3) (j : Fin 3), J ⟨0, hn⟩ j j = 1 := by
  intro hn j
  show J 0 j j = 1
  simp only [J, kap_zero, one_mul, kap_mul_kapInv]

theorem J_unit_right : ∀ (hn : 0 < 3) (i : Fin 3), J i ⟨0, hn⟩ i = 1 := by
  intro hn i
  show J i 0 i = 1
  simp only [J, kap_zero, mul_one, kap_mul_kapInv]

theorem J_dual : ∀ (hn : 0 < 3) (i : Fin 3), J i (dual i) ⟨0, hn⟩ = 1 := by
  intro hn i
  show J i (dual i) 0 = 1
  simp only [J, kapInv, if_true, mul_one, kap_dual_mul]

theorem J_coherent : ∀ a b c d e f : Fin 3,
    0 < N a b e → 0 < N e c d → 0 < N b c f → 0 < N a f d →
    J a b e * J e c d * F a b c d e f = J b c f * J a f d * F a b c d e f := by
  intro a b c d e f _ _ _ _
  have he : kapInv e * kap e = 1 := by
    rw [mul_comm]; exact kap_mul_kapInv e
  have hf : kapInv f * kap f = 1 := by
    rw [mul_comm]; exact kap_mul_kapInv f
  have key : J a b e * J e c d = J b c f * J a f d := by
    simp only [J]
    calc kap a * kap b * kapInv e * (kap e * kap c * kapInv d)
        = kap a * kap b * (kapInv e * kap e) * kap c * kapInv d := by ring
      _ = kap a * kap b * kap c * kapInv d := by rw [he]; ring
      _ = kap b * kap c * (kapInv f * kap f) * kap a * kapInv d := by rw [hf]; ring
      _ = kap b * kap c * kapInv f * (kap a * kap f * kapInv d) := by ring
  rw [key]

/-! ## The datum -/

/-- `Vec^ω_{Z/3}` over `ZMod 7`: the first legal `FusionSystem` with `i* ≠ i`. -/
def system : FusionSystem 3 k where
  ring := ring
  mult_free := by
    intro i j kk
    show N i j kk ≤ 1
    unfold N; split <;> simp
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
  ev_ne_zero := by intro i; unfold ev; norm_num
  coev_ne_zero := coev_ne_zero
  snake_left := snake_left
  snake_right := snake_right
  ev_dual := ev_dual
  J := J
  J_ne_zero := J_ne_zero
  J_unit_left := J_unit_left
  J_unit_right := J_unit_right
  J_dual := J_dual
  J_coherent := J_coherent

/-- The fusion rules of the datum are the ring's. -/
theorem system_N (a b c : Fin 3) : system.ring.N a b c = N a b c := rfl
theorem system_dual (i : Fin 3) : system.ring.dual i = dual i := rfl
theorem system_kappa (i : Fin 3) : system.kappa i = kap i := rfl

/-- The system is pointed: every product is simple. -/
theorem pointed : WP2.Pointed system := by
  intro a b
  refine ⟨a + b, ?_, ?_⟩
  · show 0 < system.ring.N a b (a + b)
    rw [system_N, N_pos_iff]
  · intro c hc
    rw [system_N, N_pos_iff] at hc
    exact hc.symm

/-- The ring's dual is *not* the identity: `1* = 2`. -/
theorem dual_ne_id : system.ring.dual ≠ id := by
  intro h
  have h1 : dual 1 = (id : Fin 3 → Fin 3) 1 := by
    rw [← system_dual]; exact congrFun h 1
  rw [dual_one] at h1
  exact absurd h1 (by decide)

/-- On this datum the two snake entries are entries of *different* blocks
(`i = 1`, `i* = 2`), and they agree — `snake_consistency` in general form. -/
theorem loop_entries : F 1 2 1 1 0 0 = zeta ∧ Finv 2 1 2 2 0 0 = zeta := by
  constructor <;> decide

/-! ## The derived twist on the first non-self-dual datum -/

/-- **`derivedJGen` on the first non-self-dual datum**: it is the coboundary of
the duality normalisation.  This is the first instantiation of
`DerivedJPointed.derivedJGen_eq_delta_kappa_of_pointed` off the self-dual locus
(every previous witness has `i* = i`). -/
theorem derivedJGen_eq_kappa {a b c : Fin 3} (h : 0 < system.ring.N a b c) :
    derivedJGen system a b c = system.kappa a * system.kappa b / system.kappa c :=
  derivedJGen_eq_delta_kappa_of_pointed system (by norm_num) pointed h

/-- `κ` is a character on this datum, so the derived twist is trivial. -/
theorem kap_mul (a b : Fin 3) : kap a * kap b = kap (a + b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem derivedJGen_eq_one {a b c : Fin 3} (h : 0 < system.ring.N a b c) :
    derivedJGen system a b c = 1 := by
  have hab : c = a + b := by
    rw [system_N, N_pos_iff] at h
    exact h.symm
  subst hab
  rw [derivedJGen_eq_kappa (by rw [system_N, N_pos_iff]),
    system_kappa, system_kappa, system_kappa, kap_mul]
  exact div_self (kap_ne_zero _)

/-- The derived twist is nonzero on every channel (it is `1`). -/
theorem derivedJGen_ne_zero {i j kk : Fin 3} (h : 0 < system.ring.N i j kk) :
    derivedJGen system i j kk ≠ 0 := by
  rw [derivedJGen_eq_one h]; exact one_ne_zero

/-! ## The fourth law and the fixpoint datum on this instance -/

/-- **The fourth law for the derived twist on the first non-self-dual datum.** -/
theorem derivedJGen_coherent :
    ∀ a b c d e f : Fin 3, 0 < system.ring.N a b e → 0 < system.ring.N e c d →
      0 < system.ring.N b c f → 0 < system.ring.N a f d →
      derivedJGen system a b e * derivedJGen system e c d * system.F a b c d e f
        = derivedJGen system b c f * derivedJGen system a f d * system.F a b c d e f :=
  derivedJGen_coherent_of_pointed' system pointed

/-- **The twist is computed, not carried**, on this instance: the datum with the
carried twist replaced by `derivedJGen` is again a legal `FusionSystem`, with the
same ring, `F`, `Finv`, `ev`, `coev`. -/
theorem exists_fixpoint :
    ∃ S' : FusionSystem 3 k,
      S'.F = system.F ∧ S'.Finv = system.Finv ∧ S'.ev = system.ev
        ∧ S'.coev = system.coev ∧ S'.J = derivedJGen system :=
  exists_fusionSystem_derivedJGen_of_pointed system pointed
    (fun _ _ _ h => derivedJGen_ne_zero h)

/-! ## The pivotal factor, on the first non-self-dual datum -/

/-- The mate pairing is non-degenerate on this datum (`F` and `Finv` are the
cocycle and its inverse there, `ev = 1`). -/
theorem pairScalar_ne_zero : ∀ a b c : Fin 3, 0 < system.ring.N a b c →
    pairScalar system a b c ≠ 0 := by
  intro a b c h
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [system, ring, N, F, Finv, ev, om, omInv, pairScalar, dual, zeta] <;>
    decide

/-- **The pivotal factor of the derived twist** on the first non-self-dual datum:
`φ ≡ 1` works, because the derived twist is trivial there. -/
theorem pivotalFactor_one : PivotalFactor system (fun _ => 1) :=
  pivotalFactor_of_coboundary system (fun _ => one_ne_zero)
    (fun a b c h => pairScalar_ne_zero a b c h)
    (fun a b c h => by rw [derivedJGen_eq_one h]; simp)

/-- The target's negation shape fails here, as it must on pointed data. -/
theorem exists_pivotalFactor :
    ∃ φ : Fin 3 → k, (∀ i, φ i ≠ 0) ∧ ∀ a b c : Fin 3, 0 < system.ring.N a b c →
      derivedJGen system a b c = φ a * φ b / φ c := by
  refine ⟨fun _ => 1, fun _ => one_ne_zero, fun a b c h => ?_⟩
  rw [derivedJGen_eq_one h]; simp

/-! ## Axiom audit -/

#print axioms Z3Omega.dual_ne_id
#print axioms Z3Omega.pointed
#print axioms Z3Omega.loop_entries
#print axioms Z3Omega.derivedJGen_eq_kappa
#print axioms Z3Omega.derivedJGen_eq_one
#print axioms Z3Omega.derivedJGen_coherent
#print axioms Z3Omega.exists_fixpoint
#print axioms Z3Omega.pairScalar_ne_zero
#print axioms Z3Omega.pivotalFactor_one
#print axioms Z3Omega.exists_pivotalFactor
#print axioms Z3Omega.F_pentagon
#print axioms Z3Omega.system

end Z3Omega
