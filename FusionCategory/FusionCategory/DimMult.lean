import FusionCategory.Prop821
import FusionCategory.Coboundary
import FusionCategory.ENOSqrt
import Mathlib.Tactic

/-!
# The multiplicativity fork, carried as a hypothesis: `DimMultiplicative`

The four twist laws of `FusionSystem` do not pin `J`, and the one condition
they miss is the sum identity

    (M)   Σ_c N^c_ab · J^c_ab · κ_c = κ_a κ_b .

It has been identified three times over in this library, each time from a
different direction:

* `Prop821.mult_iff_twist` — for a pivotal structure `P`, multiplicativity of
  `dim P` on the fusion ring is *equivalent* to (M).  The right-hand side has
  no `P` in it, so (M) holds iff the dimension of **every** pivotal structure
  is a character of the fusion ring: all-or-nothing, a property of the system;
* `ENOSqrt.trace_iff` — ENO's trace identity `d_i d_j = Σ_c T^{ij}_c d_c` is
  equivalent to (M) in the `kappaD` normalisation, and `ev_dual` (WP1 Task
  1.4) makes `kappaD = kappa` (`kappaD_eq_kappa` below), so the two sum
  identities are the same statement;
* the derivation programme (WP3 Task 3.6) — for the *derived* twist, (M) is
  the acceptance test: the dimension of a pivotal category is multiplicative,
  so a failure of (M) after the derivation means the derivation is wrong.

(M) is not a theorem of the signature: `Vec^ω_{(Z/2)²}` with the trivial twist
`J ≡ 1` satisfies every field of `FusionSystem` and refutes (M)
(`Examples/Z2SqHonest.lean`, `M_fails`), so adding (M) as a field would destroy
that witness.  It is not a definition either: setting `J := δ(κ)` would make it
true by construction and `eno823_of_pseudoUnitary` applicable to every datum,
which `YangLee.not_eno823` refutes.  This file therefore carries it as an
explicit hypothesis — the fork's second route, in the proposal's own fallback
form ("the theorem is stated with `J` as an explicit hypothesis") — together
with the bridge network around it:

* `DimMultiplicative S` — (M) as a `Prop` on the system;
* `dimMult_iff_dimEigen`, `dimEigen_of_dimMult` — the bridge to the pivotal
  side (field-generic port of `mult_iff_twist`'s two halves);
* `dimMult_of_perChannel` — the per-channel identity (K) implies (M)
  (`twist_sum_of_perChannel` restated);
* `kappaD_eq_kappa`, `trace_iff_dimMult` — the bridge to ENO's side: the trace
  identity of a `SqrtData` *is* `DimMultiplicative S`.

## What follows from it: ENO 8.23 from the scalar hypothesis alone

The analytic half of this file is the WP4 route that the hypothesis opens.
Over `ℝ`, (M) together with the pseudo-unitarity equation (`IsPseudoUnitary`,
one scalar equation with no pivotal structure in it) and a single pivotal
structure (any one) give the whole of ENO 8.23:

* `abs_dim_le_fpdim_of_dimMult` — ENO 8.21 for **every** pivotal structure:
  (M) discharges `DimEigen` system-wide, so no `IsPseudoUnitaryPivotal` is
  needed for the bound;
* `eq_abs_dim_of_dimMult_pseudoUnitary` — the equality case, in the
  dual-paired form `Σ_i dim P i · dim P (i*) = Σ_i FPdim_i²` that
  `IsPseudoUnitary` actually delivers (`dim_mul_dim_dual`): every pivotal
  structure has `|dim P i| = FPdim_i`;
* `abs_twistNorm_of_dimMult_pseudoUnitary`, `twistNorm_sq_of_…` — so the
  normalised twist is pinned **up to sign** on every channel,
  `twistNorm² = (FPdim_c/(FPdim_a·FPdim_b))²`: WP4 Task 4.5(a)'s "only the
  squares of the ratios are determined at this stage";
* `twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary` — and the sign is then
  forced by (M) itself, read as a *sum*: (M) says
  `Σ_c N^c_ab · twistNorm^c_ab = 1`, and comparing with the character identity
  `Σ_c N^c_ab · FPdim_c = FPdim_a · FPdim_b` termwise — each channel
  contributes `± FPdim_c/(FPdim_a·FPdim_b)`, and a single minus sign would
  drop the sum strictly below `FPdim_a · FPdim_b` — forces the plus sign on
  every channel.  That is the per-channel identity (K), the hypothesis of
  `eno823_of_twistNorm` and the converse of
  `twistNorm_eq_fpdim_ratio_of_dim_eq`: ENO 8.23's whole remaining content in
  this signature;
* `eno823Exact_of_dimMult_pseudoUnitary` — the source's exact conclusion:
  a *unique* spherical pivotal structure with positive dimensions equal to
  the FP-dimensions, by `exists_spherical_of_twistNorm` at `d = FPdim` plus
  `pivotal_ext` for uniqueness.

No `PFUnique` is used on this route: it is the 8.21/ℓ² route (compare
`Prop821CEq.eno823_c_of_pseudoUnitaryPivotal` at `ℂ`, which takes `Pos` and
per-`P` multiplicativity as hypotheses; here (M) is a property of the system
and positivity is *derived*).

## What is still open, now cleanly separated

* (M) itself — WP3 Tasks 3.2/3.6: derive `J` from `(F, ev, coev)` in closed
  form and prove (M) for it (`J_match` per instance in the interim);
  `Z2SqH.M_fails` is the witness that the four laws do not give it;
* the pivotal structure in the antecedent — WP4 Tasks 4.1–4.2 (`SqrtData`,
  the quadruple dual): `SqrtData.toPivotal` supplies one once the defect
  vanishes, and ENO's rescaling `a ↦ a · FPdim/d` is what kills the defect;
* the `ℂ` port of the chain (`IsPseudoUnitaryC`), where the sign argument
  becomes an equality case of the triangle inequality;
* the slot-2/slot-3 convention clash, kept on purpose elsewhere: (M) gives
  the *character* (third-slot) form of multiplicativity, while
  `IsPseudoUnitaryPivotal.mult` is the *eigenvector* (second-slot) form that
  `PFUnique` consumes; the two differ by the duality reindexing and coincide
  for `*`-invariant dimension functions.

Axiom budget: `[propext, Classical.choice, Quot.sound]` (checked at the end of
the file).
-/

universe u

namespace FusionCategory

open Finset BigOperators

/-! ## (M) as a hypothesis, and the bridges -/

section Def

variable {n : ℕ} {k : Type u} [Field k] {S : FusionSystem n k}

/-- **(M), the multiplicativity sum identity on the twist**: on every pair of
labels, the channel sum of `J · κ` is the product of the `κ`'s.

By `mult_iff_twist` this is equivalent to the dimension of every pivotal
structure being a character of the fusion ring, and by `trace_iff_dimMult`
below it is equivalent to ENO's trace identity for a `SqrtData`.  It is not
implied by the axioms of `FusionSystem` (`Z2SqH.M_fails`), and it must not be
made true by definition (`YangLee.not_eno823`). -/
def DimMultiplicative (S : FusionSystem n k) : Prop :=
  ∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c)
    = S.kappa a * S.kappa b

theorem dimMultiplicative_iff (S : FusionSystem n k) :
    DimMultiplicative S ↔ ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c)
        = S.kappa a * S.kappa b :=
  Iff.rfl

/-- The channel sum of a pivotal dimension, expanded through `p_mon`: each
channel contributes `J a b c · p a · p b · κ_c`.  Field-generic form of
`Prop821.sum_dim_eq`. -/
theorem sum_dim_eq' (P : PivotalStructure S) (a b : Fin n) :
    (∑ c : Fin n, (S.ring.N a b c : k) * dim P c)
      = P.pVal a * P.pVal b *
        (∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h0 | hpos
  · rw [h0]; simp
  · rw [PivotalStructure.dim_eq]
    rw [show P.pVal c = S.J a b c * P.pVal a * P.pVal b from P.p_mon a b c hpos]
    ring

/-- The right-hand side of multiplicativity, in the same normalisation.
Field-generic form of `Prop821.dim_mul_dim`. -/
theorem dim_mul_dim' (P : PivotalStructure S) (a b : Fin n) :
    dim P a * dim P b = P.pVal a * P.pVal b * (S.kappa a * S.kappa b) := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq]; ring

/-- **(M) is all-or-nothing for pivotal structures.**  `DimMultiplicative S`
holds if and only if the dimension of this pivotal structure is a character of
the fusion ring (the third-slot form, `DimEigen`) — and the right-hand side
carries no `P`, so the same equivalence holds at every `P` at once.
Field-generic form of `Prop821.mult_iff_twist`. -/
theorem dimMult_iff_dimEigen (P : PivotalStructure S) :
    DimMultiplicative S ↔ DimEigen S (dim P) := by
  constructor
  · intro hM a b
    rw [sum_dim_eq' P a b, hM a b, dim_mul_dim' P a b]
  · intro h a b
    have hne : P.pVal a * P.pVal b ≠ 0 :=
      mul_ne_zero (P.pVal_ne_zero a) (P.pVal_ne_zero b)
    have h' := h a b
    rw [sum_dim_eq' P a b, dim_mul_dim' P a b] at h'
    exact mul_left_cancel₀ hne h'

/-- **(M) discharges the `DimEigen` hypothesis for every pivotal structure at
once.** -/
theorem dimEigen_of_dimMult (hM : DimMultiplicative S) (P : PivotalStructure S) :
    DimEigen S (dim P) :=
  (dimMult_iff_dimEigen P).mp hM

/-! ## The ENO side: the trace identity is (M) -/

/-- **The two duality normalisations agree**, in the `ev_dual` gauge slice the
signature carries (WP1 Task 1.4): `kappaD i = coev i · ev (i*) = coev i · ev i`.
Consequently `SqrtData.d`, ENO's `Tr(a_i)`, is `a_i · κ_i` on every datum of
this signature, and `SqrtData.trace_iff`'s right-hand side is literally (M). -/
theorem kappaD_eq_kappa (S : FusionSystem n k) (i : Fin n) :
    S.kappaD i = S.kappa i := by
  unfold FusionSystem.kappaD FusionSystem.kappa
  rw [S.ev_dual i]

/-- **ENO's trace identity is `DimMultiplicative`.**  For a square root `a` of
`g`, the identity `d_i d_j = Σ_c T^{ij}_c d_c` holds for all `i, j` if and only
if the system satisfies (M).  The `a`'s cancel (`SqrtData.trace_iff`); what the
trace identity constrains is `(N, J, κ)`, and after `kappaD_eq_kappa` that is
exactly the hypothesis above.  So WP3's acceptance test, WP4's input and this
file's hypothesis are one condition. -/
theorem trace_iff_dimMult (A : SqrtData S) :
    (∀ i j : Fin n, A.d i * A.d j = ∑ c : Fin n, (S.ring.N i j c : k) * A.b i j c * A.d c)
      ↔ DimMultiplicative S := by
  constructor
  · intro h
    refine (dimMultiplicative_iff S).2 fun a b => ?_
    simpa only [kappaD_eq_kappa] using ((A.trace_iff a b).mp (h a b)).symm
  · intro hM i j
    refine (A.trace_iff i j).mpr ?_
    simpa only [kappaD_eq_kappa] using ((dimMultiplicative_iff S).1 hM i j).symm

end Def

/-! ## ENO 8.23 from `(M) + IsPseudoUnitary + P` -/

section Analytic

variable {n : ℕ} {S : FusionSystem n ℝ}

/-- **The per-channel identity (K) implies (M)**: `twist_sum_of_perChannel`
restated through the hypothesis name. -/
theorem dimMult_of_perChannel (hFP : S.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = hFP.fpdim c * S.kappa a * S.kappa b
        / (S.kappa c * hFP.fpdim a * hFP.fpdim b)) :
    DimMultiplicative S :=
  fun a b => twist_sum_of_perChannel hFP hn hK a b

/-- **The equality case of ENO 8.21 in dual-paired form.**  If `f` is positive
and `σ`-invariant, `d` is termwise bounded by `f`, and the dual-paired sum
`Σ_i d_i · d_{σ i}` equals `Σ_i f_i²`, then `|d_i| = f_i` termwise.

This is the form the pseudo-unitarity equation delivers
(`Σ_i dim P i · dim P (i*) = Σ_i κ_i κ_{i*} = Σ_i FPdim_i²`, by
`dim_mul_dim_dual`), and it needs no `σ`-invariance of `d` — only of `f`.
Compare `Prop821CEq.eq_of_sum_mul`, the `ℂ` version with a positive `r`. -/
theorem eq_abs_of_sum_mul_dual {σ : Fin n → Fin n} {d f : Fin n → ℝ}
    (hf : ∀ i, 0 < f i) (hfσ : ∀ i, f (σ i) = f i)
    (hle : ∀ i, |d i| ≤ f i)
    (hsum : (∑ i : Fin n, d i * d (σ i)) = ∑ i : Fin n, f i * f i) :
    ∀ i, |d i| = f i := by
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ f i * f i - d i * d (σ i) := by
    intro i _
    have h1 : d i * d (σ i) ≤ |d i * d (σ i)| := le_abs_self _
    have h2 : |d i * d (σ i)| = |d i| * |d (σ i)| := abs_mul _ _
    have h3 : |d i| * |d (σ i)| ≤ f i * f i := by
      have h4 := hle (σ i)
      rw [hfσ i] at h4
      calc |d i| * |d (σ i)| ≤ f i * |d (σ i)| :=
            mul_le_mul_of_nonneg_right (hle i) (abs_nonneg _)
        _ ≤ f i * f i := mul_le_mul_of_nonneg_left h4 (le_of_lt (hf i))
    linarith
  have hzero : (∑ i : Fin n, (f i * f i - d i * d (σ i))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    ring
  intro i
  have hterm : f i * f i - d i * d (σ i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
  have hf2 : 0 < f i * f i := mul_pos (hf i) (hf i)
  have hdeq : d i * d (σ i) = f i * f i := by linarith
  have habs : |d i| * |d (σ i)| = f i * f i := by
    rw [← abs_mul, abs_of_nonneg (by linarith), hdeq]
  have hdσ : |d (σ i)| ≤ f i := by
    have h := hle (σ i)
    rw [hfσ i] at h
    exact h
  have hge : f i ≤ |d i| := by
    by_contra hlt
    have hlt' : |d i| < f i := by linarith
    have hstrict : |d i| * |d (σ i)| < f i * f i := by
      calc |d i| * |d (σ i)| ≤ |d i| * f i :=
            mul_le_mul_of_nonneg_left hdσ (abs_nonneg _)
        _ < f i * f i := mul_lt_mul_of_pos_right hlt' (hf i)
    linarith
  exact eq_of_le_of_ge (hle i) hge

/-- **ENO 8.21 for every pivotal structure, from (M).**  The bound needs no
`IsPseudoUnitaryPivotal`: (M) discharges `DimEigen` at every `P` at once. -/
theorem abs_dim_le_fpdim_of_dimMult (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (P : PivotalStructure S) :
    ∀ i, |dim P i| ≤ hFP.fpdim i :=
  abs_le_fpdim_of_mult hFP hn (dim P) (dimEigen_of_dimMult hM P)

/-- **The equality case: pseudo-unitarity turns the bound into termwise
equality, for every pivotal structure.**  `Σ_i |dim P i|²` is not what
`IsPseudoUnitary` gives — the dual-paired sum is (`dim_mul_dim_dual`), and
`eq_abs_of_sum_mul_dual` is the equality case in exactly that form. -/
theorem eq_abs_dim_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) :
    ∀ i, |dim P i| = hFP.fpdim i := by
  have hle : ∀ i, |dim P i| ≤ hFP.fpdim i := abs_dim_le_fpdim_of_dimMult hFP hn hM P
  have hsum : (∑ i : Fin n, dim P i * dim P (S.ring.dual i))
      = ∑ i : Fin n, hFP.fpdim i * hFP.fpdim i := by
    calc (∑ i : Fin n, dim P i * dim P (S.ring.dual i))
        = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) :=
          Finset.sum_congr rfl (fun i _ => dim_mul_dim_dual hn P i)
      _ = hFP.globalDim := hPU
      _ = ∑ i : Fin n, hFP.fpdim i * hFP.fpdim i := by
          unfold FusionRing.FPData.globalDim
          exact Finset.sum_congr rfl (fun i _ => by rw [sq])
  exact eq_abs_of_sum_mul_dual (fun i => hFP.pos i) (fun i => hFP.dual_eq i) hle hsum

/-- **The normalised twist is pinned up to sign** on every channel —
WP4 Task 4.5(a): "only the squares of the ratios are determined at this
stage". -/
theorem abs_twistNorm_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    |twistNorm S a b c| = hFP.fpdim c / (hFP.fpdim a * hFP.fpdim b) := by
  have heq := eq_abs_dim_of_dimMult_pseudoUnitary hFP hn hM hPU P
  have h := dim_eq_twistNorm P a b c hN
  have h2 : |dim P c| = |twistNorm S a b c| * |dim P a| * |dim P b| := by
    have h3 := congrArg abs h
    rwa [abs_mul, abs_mul] at h3
  rw [heq c, heq a, heq b] at h2
  exact (eq_div_iff (mul_ne_zero (ne_of_gt (hFP.pos a)) (ne_of_gt (hFP.pos b)))).mpr
    (by rw [h2]; ring)

/-- The squared form of `abs_twistNorm_of_dimMult_pseudoUnitary`: the
per-channel identity holds for the squares unconditionally, the sign being the
residual freedom. -/
theorem twistNorm_sq_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    twistNorm S a b c ^ 2
      = (hFP.fpdim c / (hFP.fpdim a * hFP.fpdim b)) ^ 2 := by
  rw [← sq_abs (twistNorm S a b c),
    abs_twistNorm_of_dimMult_pseudoUnitary hFP hn hM hPU P a b c hN]

/-- **(M) as a normalised channel sum**: divide (M) by `κ_a κ_b` and the
twist-normalised channel sum of `a ⊗ b` is exactly `1`.  This is the form the
sign argument below consumes. -/
theorem sum_twistNorm_of_dimMult (hM : DimMultiplicative S) (a b : Fin n) :
    (∑ c : Fin n, (S.ring.N a b c : ℝ) * twistNorm S a b c) = 1 := by
  have hκ : S.kappa a * S.kappa b ≠ 0 :=
    mul_ne_zero (S.kappa_ne_zero a) (S.kappa_ne_zero b)
  have hstep : (∑ c : Fin n, (S.ring.N a b c : ℝ) * twistNorm S a b c)
      = (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c)
        / (S.kappa a * S.kappa b) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold twistNorm
    rw [div_eq_mul_inv]
    ring
  rw [hstep, hM a b, div_self hκ]

/-- **The sign is forced: (M) + pseudo-unitarity give the per-channel identity
(K).**  Each channel of `a ⊗ b` contributes `twistNorm · FPdim_a · FPdim_b`,
a real number of modulus `FPdim_c` (the equality case); (M) says the channel
sum of these contributions is `FPdim_a · FPdim_b`, and the character identity
`fpdim_char` says the same sum with every contribution replaced by its modulus
`FPdim_c` is `FPdim_a · FPdim_b`.  Since each contribution is at most its
modulus, the two sums can agree only if every contribution *is* its modulus —
no channel carries a minus sign.

This is the skeleton form of ENO's σ/τ normalisation (WP4 Task 4.5): over `ℝ`
the two-step twist collapses to this one comparison, and what it produces is
exactly the hypothesis of `eno823_of_twistNorm` — the per-channel identity
that `twistNorm_eq_fpdim_ratio_of_dim_eq` shows is *equivalent* to `ENO823`. -/
theorem twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary (hFP : S.ring.FPData)
    (hn : 0 < n) (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    twistNorm S a b c = hFP.fpdim c / (hFP.fpdim a * hFP.fpdim b) := by
  have hsum := sum_twistNorm_of_dimMult hM a b
  have hchar := fpdim_char hFP hn a b
  have hf0 : ∀ i, hFP.fpdim i ≠ 0 := fun i => ne_of_gt (hFP.pos i)
  have hfa : hFP.fpdim a ≠ 0 := hf0 a
  have hfb : hFP.fpdim b ≠ 0 := hf0 b
  have hfab : hFP.fpdim a * hFP.fpdim b ≠ 0 := mul_ne_zero hfa hfb
  -- the rescaled channel sum, by (M), equals `FPdim_a · FPdim_b`
  have key : (∑ c' : Fin n, (S.ring.N a b c' : ℝ)
      * (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b))
      = hFP.fpdim a * hFP.fpdim b := by
    calc (∑ c' : Fin n, (S.ring.N a b c' : ℝ)
          * (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b))
        = hFP.fpdim a * hFP.fpdim b
            * (∑ c' : Fin n, (S.ring.N a b c' : ℝ) * twistNorm S a b c') := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun c' _ => by ring)
      _ = hFP.fpdim a * hFP.fpdim b * 1 := by rw [hsum]
      _ = hFP.fpdim a * hFP.fpdim b := by ring
  -- every channel's contribution is at most its modulus
  have hnn : ∀ c' ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (S.ring.N a b c' : ℝ)
        * (hFP.fpdim c' - (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b)) := by
    intro c' _
    rcases Nat.eq_zero_or_pos (S.ring.N a b c') with h0 | hpos
    · rw [h0]; simp
    · apply mul_nonneg (Nat.cast_nonneg _)
      have habs' := abs_twistNorm_of_dimMult_pseudoUnitary hFP hn hM hPU P a b c' hpos
      have hmag : |twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b|
          = hFP.fpdim c' := by
        rw [abs_mul, abs_mul, abs_of_pos (hFP.pos a), abs_of_pos (hFP.pos b), habs']
        field_simp
      have hle : twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b ≤ hFP.fpdim c' := by
        have h := le_abs_self (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b)
        rwa [hmag] at h
      linarith
  -- so the difference against the character sum is a nonnegative sum of zero
  have hzero : (∑ c' : Fin n, (S.ring.N a b c' : ℝ)
      * (hFP.fpdim c' - (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b))) = 0 := by
    have hsplit : ∀ c' : Fin n,
        (S.ring.N a b c' : ℝ) * (hFP.fpdim c'
          - (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b))
        = (S.ring.N a b c' : ℝ) * hFP.fpdim c'
          - (S.ring.N a b c' : ℝ)
              * (twistNorm S a b c' * hFP.fpdim a * hFP.fpdim b) :=
      fun c' => by ring
    rw [Finset.sum_congr rfl (fun c' _ => hsplit c'), Finset.sum_sub_distrib, hchar, key]
    ring
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero c (Finset.mem_univ c)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) (Nat.ne_of_gt hN)
  · have h' : hFP.fpdim c
        = twistNorm S a b c * hFP.fpdim a * hFP.fpdim b := by linarith
    exact (eq_div_iff hfab).mpr (by rw [h']; ring)

/-- **(K), the per-channel identity on the twist itself** — ENO 8.23's
remaining content, in the form `eno823_of_twist_coboundary` consumes. -/
theorem J_eq_fpdim_ratio_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    S.J a b c = hFP.fpdim c * S.kappa a * S.kappa b
      / (S.kappa c * hFP.fpdim a * hFP.fpdim b) := by
  have h := twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary hFP hn hM hPU P a b c hN
  unfold twistNorm at h
  have hκa := S.kappa_ne_zero a
  have hκb := S.kappa_ne_zero b
  have hκc := S.kappa_ne_zero c
  have hfa := ne_of_gt (hFP.pos a)
  have hfb := ne_of_gt (hFP.pos b)
  have hd : S.kappa c * hFP.fpdim a * hFP.fpdim b ≠ 0 :=
    mul_ne_zero (mul_ne_zero hκc hfa) hfb
  rw [eq_div_iff hd]
  rw [div_eq_div_iff (mul_ne_zero hκa hκb) (mul_ne_zero hfa hfb)] at h
  linear_combination h

/-- **ENO Proposition 8.23, the source's exact statement, from `(M) +
pseudo-unitarity + one pivotal structure`.**  A pseudo-unitary system
satisfying (M) admits a *unique* pivotal structure, spherical, whose
dimensions are positive and equal to the FP-dimensions.

The proof is the (K) identity above plus `exists_spherical_of_twistNorm` at
`d = FPdim`; uniqueness is `pivotal_ext` (a pivotal structure is determined by
its dimension function).  No `PFUnique` is used.  The pivotal structure `P` in
the antecedent is any witness of existence — WP4 Tasks 4.1–4.2 (`SqrtData`,
the quadruple dual) are what supply it in ENO's own proof. -/
theorem eno823Exact_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) : ENO823Exact S hFP := by
  have hf0 : ∀ i, hFP.fpdim i ≠ 0 := fun i => ne_of_gt (hFP.pos i)
  have hJ : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      hFP.fpdim c = twistNorm S a b c * hFP.fpdim a * hFP.fpdim b := by
    intro a b c hN
    have hfa : hFP.fpdim a ≠ 0 := hf0 a
    have hfb : hFP.fpdim b ≠ 0 := hf0 b
    have h := twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary hFP hn hM hPU P a b c hN
    rw [h]
    field_simp
  intro _hPU'
  obtain ⟨P', hsp, hdim⟩ := exists_spherical_of_twistNorm (S := S) hFP.fpdim hf0 hJ hn
    (hFP.unit_one hn) (kappa_unit (S := S) hn) (fun i => hFP.dual_eq i)
  refine ⟨P', ⟨hsp, fun i => by rw [hdim i]; exact hFP.pos i, hdim⟩, ?_⟩
  rintro P'' ⟨_, _, hdim''⟩
  exact pivotal_ext P'' P' (fun i => by rw [hdim'' i, hdim i])

/-- The bare form of the same theorem. -/
theorem eno823_of_dimMult_pseudoUnitary (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitary S hFP)
    (P : PivotalStructure S) : ENO823 S hFP :=
  eno823_of_exact hFP (eno823Exact_of_dimMult_pseudoUnitary hFP hn hM hPU P) hPU

end Analytic

end FusionCategory

/-! ## Axiom audit (the budget is `[propext, Classical.choice, Quot.sound]`) -/

#print axioms FusionCategory.DimMultiplicative
#print axioms FusionCategory.sum_dim_eq'
#print axioms FusionCategory.dim_mul_dim'
#print axioms FusionCategory.dimMult_iff_dimEigen
#print axioms FusionCategory.dimEigen_of_dimMult
#print axioms FusionCategory.kappaD_eq_kappa
#print axioms FusionCategory.trace_iff_dimMult
#print axioms FusionCategory.dimMult_of_perChannel
#print axioms FusionCategory.eq_abs_of_sum_mul_dual
#print axioms FusionCategory.abs_dim_le_fpdim_of_dimMult
#print axioms FusionCategory.eq_abs_dim_of_dimMult_pseudoUnitary
#print axioms FusionCategory.abs_twistNorm_of_dimMult_pseudoUnitary
#print axioms FusionCategory.twistNorm_sq_of_dimMult_pseudoUnitary
#print axioms FusionCategory.sum_twistNorm_of_dimMult
#print axioms FusionCategory.twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary
#print axioms FusionCategory.J_eq_fpdim_ratio_of_dimMult_pseudoUnitary
#print axioms FusionCategory.eno823Exact_of_dimMult_pseudoUnitary
#print axioms FusionCategory.eno823_of_dimMult_pseudoUnitary
