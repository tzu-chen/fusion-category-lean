import FusionCategory.Statements
import FusionCategory.Prop821
import Mathlib.Analysis.Complex.Basic

/-!
# ENO Proposition 8.21 at `ℂ`: the eigenvector bound and its equality case

The `ℝ` originals (`FusionCategory.abs_le_fpdim_of_eigenvector`,
`FusionCategory.eq_abs_of_sum_sq` and their consumers in `Prop821.lean`) are retained.
This file adds the `ℂ` forms of Task 1.1's analytic chain, routed through the norm API,
and the `ℂ` consumers at `dim` level.

**Rendering note (kernel-checked, this pinned Mathlib).**  `Complex.abs` does not exist in
this Mathlib and `|z|` on `ℂ` does not elaborate (there is no `Lattice ℂ`); the `ℂ`
absolute value *is* the norm `‖z‖`.  So the `ℂ` statements below are written with `‖·‖`;
for `ℝ` the translation is `Real.norm_eq_abs`.  (Also note `Statements.lean` imports only
`Mathlib.Data.Complex.Basic`, under which `ℂ` carries no norm instance at all — hence the
`Mathlib.Analysis.Complex.Basic` import here.)

The main theorem is proved once over an arbitrary normed ring `K`
(`norm_le_fpdim_of_eigenvector`), which pulls out both the `ℝ` statement
(`abs_le_fpdim_of_eigenvector_real_norm`, a cross-check that the generalisation loses
nothing) and the `ℂ` statement (`abs_le_fpdim_of_eigenvector_c`).
-/

open Finset BigOperators

namespace FusionCategory

open FusionRing

variable {n : ℕ}

/-! ## The eigenvector bound, over an arbitrary normed ring -/

/-- **ENO Proposition 8.21**, spectral form, over a normed ring: if `d : Fin n → K`
satisfies the eigenvector equation `Σ_j N i j k · d_j = d_i · d_k`, then
`‖d i‖ ≤ fpdim i`.  `K = ℝ` gives `Prop821.abs_le_fpdim_of_eigenvector` back (via
`Real.norm_eq_abs`); `K = ℂ` is the scalar contract's form. -/
theorem norm_le_fpdim_of_eigenvector {K : Type*} [NormedRing K] [NormMulClass K]
    [NormOneClass K] [NormSMulClass ℤ K] {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → K)
    (heig : ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : K) * d j) = d i * d kk) :
    ∀ i, ‖d i‖ ≤ h.fpdim i := by
  intro i
  set S : ℝ := ∑ k : Fin n, h.fpdim k * ‖d k‖ with hSdef
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (norm_nonneg _))
  have hbound : ‖d i‖ * S ≤ h.fpdim i * S := by
    calc ‖d i‖ * S
        = ∑ k : Fin n, h.fpdim k * ‖d i * d k‖ := by
          rw [hSdef, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_mul]
          ring
      _ = ∑ k : Fin n, h.fpdim k * ‖∑ j : Fin n, (R.N i j k : K) * d j‖ := by
          apply Finset.sum_congr rfl
          intro k _
          rw [heig i k]
      _ ≤ ∑ k : Fin n, h.fpdim k * (∑ j : Fin n, (R.N i j k : ℝ) * ‖d j‖) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (h.pos k))
          calc ‖∑ j : Fin n, (R.N i j k : K) * d j‖
              ≤ ∑ j : Fin n, ‖(R.N i j k : K) * d j‖ := norm_sum_le _ _
            _ = ∑ j : Fin n, (R.N i j k : ℝ) * ‖d j‖ := by
                apply Finset.sum_congr rfl
                intro j _
                rw [norm_mul, norm_natCast]
      _ = ∑ k : Fin n, ∑ j : Fin n, h.fpdim k * ((R.N i j k : ℝ) * ‖d j‖) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin n, h.fpdim k * ((R.N i j k : ℝ) * ‖d j‖) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, (∑ k : Fin n, h.fpdim k * (R.N i j k : ℝ)) * ‖d j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ j : Fin n, (h.fpdim i * h.fpdim j) * ‖d j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          have hc : (∑ k : Fin n, h.fpdim k * (R.N i j k : ℝ)) = h.fpdim i * h.fpdim j := by
            rw [← fpdim_char h hn i j]
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [hc]
      _ = h.fpdim i * S := by
          rw [hSdef, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  rcases lt_or_eq_of_le hSnn with hpos | hzero
  · exact le_of_mul_le_mul_right hbound hpos
  · have hS0 : (∑ k : Fin n, h.fpdim k * ‖d k‖) = 0 := by rw [← hSdef]; exact hzero.symm
    have hterm : h.fpdim i * ‖d i‖ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun k => h.fpdim k * ‖d k‖)
        (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (norm_nonneg _))).mp hS0 i
        (Finset.mem_univ i)
    have hdi : ‖d i‖ = 0 := by
      rcases mul_eq_zero.mp hterm with h' | h'
      · exact absurd h' (ne_of_gt (h.pos i))
      · exact h'
    rw [hdi]
    exact le_of_lt (h.pos i)

/-! ## The `ℂ` form required by the scalar contract -/

/-- **ENO Proposition 8.21 at `ℂ`** (Task 1.1's analytic chain): any `d : Fin n → ℂ`
satisfying the eigenvector equation `Σ_j N i j k · d_j = d_i · d_k` is bounded by the
FP-dimensions.

Rendering: `‖d i‖` is the `ℂ` absolute value (`Complex.abs` does not exist in this
Mathlib). -/
theorem abs_le_fpdim_of_eigenvector_c {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → ℂ)
    (heig : ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : ℂ) * d j) = d i * d kk) :
    ∀ i, ‖d i‖ ≤ h.fpdim i :=
  norm_le_fpdim_of_eigenvector (K := ℂ) h hn d heig

/-- The `ℝ` original is the `K = ℝ` instance of the general theorem: cross-check that the
generalisation loses nothing. -/
theorem abs_le_fpdim_of_eigenvector_real_norm {R : FusionRing n} (h : R.FPData)
    (hn : 0 < n) (d : Fin n → ℝ)
    (heig : ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : ℝ) * d j) = d i * d kk) :
    ∀ i, |d i| ≤ h.fpdim i := by
  have := norm_le_fpdim_of_eigenvector (K := ℝ) h hn d heig
  simpa only [Real.norm_eq_abs] using this

/-! ## The equality case -/

/-- The equality case ENO draw from Proposition 8.21, at `ℂ`: if `‖d i‖ ≤ f i` termwise
and the sums of squares agree, then the bounds are equalities.  (`‖d i‖` is `ℝ`-valued and
nonnegative, so the `ℝ` original's `|d i|² = (d i)²` step disappears.) -/
theorem eq_abs_of_sum_sq_c {n : ℕ} {d : Fin n → ℂ} {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hle : ∀ i, ‖d i‖ ≤ f i)
    (hsum : (∑ i : Fin n, ‖d i‖ ^ 2) = ∑ i : Fin n, (f i) ^ 2) :
    ∀ i, ‖d i‖ = f i := by
  have hterm : ∀ i : Fin n, (f i) ^ 2 - ‖d i‖ ^ 2 = 0 := by
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (f i) ^ 2 - ‖d i‖ ^ 2 := by
      intro i _
      nlinarith [hle i, norm_nonneg (d i), hf i]
    have hzero : (∑ i : Fin n, ((f i) ^ 2 - ‖d i‖ ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib, ← hsum]
      ring
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i (Finset.mem_univ i)
  intro i
  have hsq : ‖d i‖ ^ 2 = (f i) ^ 2 := by linarith [hterm i]
  exact (sq_eq_sq₀ (norm_nonneg (d i)) (hf i)).mp hsq

/-! ## Consumers at `dim` level: the pseudo-unitary case of ENO §8.4 -/

/-- `IsPseudoUnitaryPivotal.mult` **is** the eigenvector equation: hence ENO's bound holds
for the dimensions of a pseudo-unitary pivotal structure at `ℂ`, with no further input.
This is the `ℂ` analogue of `abs_dim_le_fpdim_of_pseudoUnitary`. -/
theorem abs_dim_le_fpdim_of_pseudoUnitaryC {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P) : ∀ i, ‖dim P i‖ ≤ hFP.fpdim i :=
  abs_le_fpdim_of_eigenvector_c (R := S.ring) hFP hn (dim P) hU.mult

/-- The equality case at `ℂ` in the shape ENO §8.4 uses it: if in addition the squared
norms agree in total, they agree termwise — `‖V‖² = FPdim(V)²` for every simple.  The `ℂ`
analogue of `eq_abs_of_pseudoUnitary`, with `‖·‖` for `|·|`. -/
theorem eq_abs_of_pseudoUnitaryC {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P)
    (hsum : (∑ i : Fin n, ‖dim P i‖ ^ 2) = ∑ i : Fin n, (hFP.fpdim i) ^ 2) :
    ∀ i, ‖dim P i‖ = hFP.fpdim i :=
  eq_abs_of_sum_sq_c (fun i => le_of_lt (hFP.pos i))
    (abs_dim_le_fpdim_of_pseudoUnitaryC hFP hn P hU) hsum

/-! ## The character form at `ℂ` (the shape multiplicativity delivers) -/

/-- **ENO Proposition 8.21 at `ℂ`**, character form: a `d` invariant under duality and
multiplicative on the fusion ring (`Σ_c N a b c d_c = d_a d_b`) is bounded by the
FP-dimensions.  This is the `ℂ` analogue of `abs_le_fpdim_of_char`. -/
theorem abs_le_fpdim_of_char_c {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → ℂ) (hdual : ∀ i, d (R.dual i) = d i)
    (hchar : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℂ) * d c) = d a * d b) :
    ∀ i, ‖d i‖ ≤ h.fpdim i := by
  refine abs_le_fpdim_of_eigenvector_c h hn d ?_
  intro i kk
  calc (∑ j : Fin n, (R.N i j kk : ℂ) * d j)
      = ∑ j : Fin n, (R.N (R.dual kk) i (R.dual j) : ℂ) * d j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cyclic2 hn i j kk]
    _ = ∑ j : Fin n, (R.N (R.dual kk) i (R.dual j) : ℂ) * d (R.dual j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hdual j]
    _ = ∑ m : Fin n, (R.N (R.dual kk) i m : ℂ) * d m :=
        sum_dual_reindex (M := ℂ) (fun m => (R.N (R.dual kk) i m : ℂ) * d m)
    _ = d (R.dual kk) * d i := hchar (R.dual kk) i
    _ = d i * d kk := by rw [hdual kk, mul_comm]


/-! ## The twist algebra: Task 1.4's "settling `J`" at the scalar contract

Everything from here to the end of the file is the `J`/`κ` layer: the equivalence of
multiplicativity with the twist sum identity (M), the per-channel law (K) ⇒ (M), the
canonical settled twist and its identification with the frozen `J_match`, and — composing
that layer with the analytic chain above — the ENO §8.4 conclusion `κ = FPdim` at `ℂ`.
-/

variable {n : ℕ}

/-! ## The scalar bookkeeping: `algebraMap ℝ k` of a positive real is nonzero -/

/-- A positive real stays nonzero under any field-valued `ℝ`-algebra map.  (`algebraMap` of
a field into a field is injective; this is the `r • 1` form of that.) -/
theorem algebraMap_ne_zero_of_ne_zero {k : Type*} [Field k] [Algebra ℝ k] {r : ℝ}
    (hr : r ≠ 0) : algebraMap ℝ k r ≠ 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  intro h
  rcases (smul_eq_zero.mp h) with h' | h'
  · exact hr h'
  · exact one_ne_zero h'

/-! ## The FP-dimension is a character at any scalar field -/

/-- `fpdim_char` (the FP-dimension is a character, `Σ_c N a b c f_c = f_a f_b`) after
scalar extension to a general `ℝ`-algebra `k`.  At `k = ℂ` this is the form the scalar
contract uses. -/
theorem fpdim_char_algebraMap {k : Type*} [Field k] [Algebra ℝ k] {R : FusionRing n}
    (h : R.FPData) (hn : 0 < n) (a b : Fin n) :
    (∑ c : Fin n, (R.N a b c : k) * algebraMap ℝ k (h.fpdim c)) =
      algebraMap ℝ k (h.fpdim a) * algebraMap ℝ k (h.fpdim b) := by
  calc (∑ c : Fin n, (R.N a b c : k) * algebraMap ℝ k (h.fpdim c))
      = ∑ c : Fin n, algebraMap ℝ k ((R.N a b c : ℝ) * h.fpdim c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [map_mul, map_natCast]
    _ = algebraMap ℝ k (∑ c : Fin n, (R.N a b c : ℝ) * h.fpdim c) :=
        (map_sum (algebraMap ℝ k) _ _).symm
    _ = algebraMap ℝ k (h.fpdim a * h.fpdim b) := by rw [fpdim_char h hn a b]
    _ = algebraMap ℝ k (h.fpdim a) * algebraMap ℝ k (h.fpdim b) := map_mul _ _ _

/-! ## The twist algebra at a general scalar field -/

variable {k : Type u} [Field k] {S : FusionSystem n k}

/-- **The dimension sum in the twist normalisation**: multiplying `dim P c = p_c κ_c` out,
`Σ_c N a b c · dim P c` is `p_a p_b` times the twist sum `Σ_c N a b c · J a b c · κ_c`. -/
theorem sum_dim_eq_general (P : PivotalStructure S) (a b : Fin n) :
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

/-- The right-hand side of multiplicativity in the same normalisation. -/
theorem dim_mul_dim_general (P : PivotalStructure S) (a b : Fin n) :
    dim P a * dim P b = P.pVal a * P.pVal b * (S.kappa a * S.kappa b) := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq]
  ring

/-- **Settling `J` is proving (M).**  For any pivotal structure, multiplicativity of its
dimension function is equivalent to the sum identity
`Σ_c N a b c · J a b c · κ_c = κ_a κ_b` on the twist — an equation in which no pivotal
structure appears. -/
theorem mult_iff_twist_general (P : PivotalStructure S) :
    (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : k) * dim P c) = dim P a * dim P b) ↔
      (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c)
          = S.kappa a * S.kappa b) := by
  have hne : ∀ a b : Fin n, P.pVal a * P.pVal b ≠ 0 :=
    fun a b => mul_ne_zero (P.pVal_ne_zero a) (P.pVal_ne_zero b)
  constructor
  · intro h a b
    have h' := h a b
    rw [sum_dim_eq_general P a b, dim_mul_dim_general P a b] at h'
    exact mul_left_cancel₀ (hne a b) h'
  · intro h a b
    rw [sum_dim_eq_general P a b, dim_mul_dim_general P a b, h a b]

/-- Multiplicativity of the dimension does not depend on the pivotal structure: by
`mult_iff_twist_general` both are equivalent to the same twist identity (M). -/
theorem mult_iff_mult_general (P P' : PivotalStructure S) :
    (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : k) * dim P c) = dim P a * dim P b) ↔
      (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : k) * dim P' c) = dim P' a * dim P' b) :=
  (mult_iff_twist_general P).trans (mult_iff_twist_general P').symm

/-- The dual dimension, in the twist normalisation: `dim (i*) = p_i⁻¹ κ_{i*}`.  This is
`dim_eq` with `pVal_dual`, the form in which the squared norm `dim i · dim (i*)` is
computed. -/
theorem dim_dual_general (P : PivotalStructure S) (hn : 0 < n) (i : Fin n) :
    dim P (S.ring.dual i) = (P.pVal i)⁻¹ * S.kappa (S.ring.dual i) := by
  rw [PivotalStructure.dim_eq, P.pVal_dual hn i]

/-- The squared norm of a simple in a pivotal structure: `dim i · dim (i*) = κ_i κ_{i*}`,
independently of the pivotal structure.  (The general-field form of
`PseudoUnitary.dim_mul_dim_dual`.) -/
theorem dim_mul_dim_dual_general (P : PivotalStructure S) (hn : 0 < n) (i : Fin n) :
    dim P i * dim P (S.ring.dual i) = S.kappa i * S.kappa (S.ring.dual i) := by
  rw [PivotalStructure.dim_eq, dim_dual_general P hn i]
  calc P.pVal i * S.kappa i * ((P.pVal i)⁻¹ * S.kappa (S.ring.dual i))
      = (P.pVal i * (P.pVal i)⁻¹) * (S.kappa i * S.kappa (S.ring.dual i)) := by ring
    _ = S.kappa i * S.kappa (S.ring.dual i) := by
        rw [mul_inv_cancel₀ (P.pVal_ne_zero i), one_mul]

/-! ## The unit normalisation of `κ`, at a general scalar field -/

/-- `κ` at the unit index is `1`: the left snake at `i = 1` with the unit law of `F`.
(The general-field form of `PseudoUnitary.kappa_unit`.) -/
theorem kappa_unit_general (hn : 0 < n) : S.kappa ⟨0, hn⟩ = 1 := by
  have hd : S.ring.dual ⟨0, hn⟩ = ⟨0, hn⟩ := S.ring.dual_zero hn
  have hN : 0 < S.ring.N ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [S.ring.left_unit hn ⟨0, hn⟩ ⟨0, hn⟩]
    simp
  have hunit := S.F_unit_left hn ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ hN
  simp only [if_true] at hunit
  have hsnake := S.snake_left hn ⟨0, hn⟩
  rw [hd, hunit, mul_one] at hsnake
  exact hsnake

/-- The dimension of the unit is `1`, at a general scalar field. -/
theorem dim_unit_general (P : PivotalStructure S) (hn : 0 < n) :
    dim P ⟨0, hn⟩ = 1 := by
  rw [PivotalStructure.dim_eq, P.pVal_unit hn, kappa_unit_general (S := S) hn, mul_one]

/-! ## The per-channel law (K) implies multiplicativity, at a general scalar field -/

variable {k' : Type u} [Field k'] [Algebra ℝ k'] {S' : FusionSystem n k'}

/-- **(K) ⇒ (M)**: the per-channel qualification
`J a b c = f_c κ_a κ_b / (κ_c f_a f_b)` on supported channels implies the twist sum
identity (M).  This is `Prop821.twist_sum_of_perChannel` with the FP-dimensions read
through `algebraMap ℝ k'`. -/
theorem twist_sum_of_perChannel_general (hFP : S'.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S'.ring.N a b c →
      S'.J a b c = algebraMap ℝ k' (hFP.fpdim c) * S'.kappa a * S'.kappa b /
        (S'.kappa c * algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b))) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S'.ring.N a b c : k') * S'.J a b c * S'.kappa c)
        = S'.kappa a * S'.kappa b := by
  intro a b
  have hfa : algebraMap ℝ k' (hFP.fpdim a) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos a))
  have hfb : algebraMap ℝ k' (hFP.fpdim b) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos b))
  calc (∑ c : Fin n, (S'.ring.N a b c : k') * S'.J a b c * S'.kappa c)
      = ∑ c : Fin n, (S'.ring.N a b c : k') *
          (algebraMap ℝ k' (hFP.fpdim c) * S'.kappa a * S'.kappa b /
            (algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b))) := by
        apply Finset.sum_congr rfl
        intro c _
        rcases Nat.eq_zero_or_pos (S'.ring.N a b c) with h0 | hpos
        · rw [h0]; simp
        · rw [hK a b c hpos]
          have hk := S'.kappa_ne_zero c
          field_simp
    _ = (S'.kappa a * S'.kappa b /
          (algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b))) *
          (∑ c : Fin n, (S'.ring.N a b c : k') * algebraMap ℝ k' (hFP.fpdim c)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ = (S'.kappa a * S'.kappa b /
          (algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b))) *
          (algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b)) := by
        rw [fpdim_char_algebraMap hFP hn a b]
    _ = S'.kappa a * S'.kappa b := by
        field_simp

/-- **(K) ⇒ multiplicativity**: with the twist satisfying the per-channel law, the
dimension function of *any* pivotal structure is multiplicative. -/
theorem mult_of_perChannel_general (hFP : S'.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S'.ring.N a b c →
      S'.J a b c = algebraMap ℝ k' (hFP.fpdim c) * S'.kappa a * S'.kappa b /
        (S'.kappa c * algebraMap ℝ k' (hFP.fpdim a) * algebraMap ℝ k' (hFP.fpdim b)))
    (P : PivotalStructure S') :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S'.ring.N a b c : k') * dim P c) = dim P a * dim P b :=
  (mult_iff_twist_general P).mpr (twist_sum_of_perChannel_general hFP hn hK)

/-! ## The canonical "settled" twist and the frozen `J_match` -/

/-- **The settled twist** of a datum with FP-dimensions: the per-channel table
`(a,b,c) ↦ f_c κ_a κ_b / (κ_c f_a f_b)`.  It is the table the per-channel form (K) of
Task 1.4 asks the datum's twist to agree with on supported channels; `(K)` implies the
twist sum identity (M) and hence multiplicativity of every pivotal dimension
(`twist_sum_of_perChannel_general`, `mult_of_perChannel_general` below).  On channels with
`N a b c = 0` it is unconstrained by (K). -/
noncomputable def settledJ {k : Type u} [Field k] [Algebra ℝ k] {n : ℕ}
    (S : FusionSystem n k) (hFP : S.ring.FPData) (a b c : Fin n) : k :=
  algebraMap ℝ k (hFP.fpdim c) * S.kappa a * S.kappa b /
    (S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b))

/-- The frozen `J_match` at the settled twist **is** the per-channel law (K): both are
`∀ a b c, 0 < N a b c → J a b c = settledJ S hFP a b c`. -/
theorem j_match_settledJ_iff {k : Type u} [Field k] [Algebra ℝ k] {S : FusionSystem n k}
    (hFP : S.ring.FPData) :
    J_match S (settledJ S hFP) ↔
      ∀ a b : Fin n, ∀ c : Fin n, 0 < S.ring.N a b c →
        S.J a b c = algebraMap ℝ k (hFP.fpdim c) * S.kappa a * S.kappa b /
          (S.kappa c * algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b)) :=
  Iff.rfl

/-- **`J_match` at the settled twist gives the pseudo-unitarity hypothesis**: if the
carried twist agrees with the settled one on supported channels, then the dimension
function of any pivotal structure is multiplicative — the `mult` field that
`IsPseudoUnitaryPivotal` (and hence the frozen `Cx` conditional form) assumes. -/
theorem mult_of_J_match_settledJ {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (hFP : S.ring.FPData) (hn : 0 < n)
    (h : J_match S (settledJ S hFP)) (P : PivotalStructure S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * dim P c) = dim P a * dim P b :=
  mult_of_perChannel_general hFP hn (fun a b c hN => h a b c hN) P

/-! ## The `ℂ` forms of the scalar contract -/

/-- The twist sum identity at `ℂ`. -/
theorem sum_dim_eq_c {S : FusionSystem n ℂ} (P : PivotalStructure S) (a b : Fin n) :
    (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c)
      = P.pVal a * P.pVal b *
        (∑ c : Fin n, (S.ring.N a b c : ℂ) * S.J a b c * S.kappa c) :=
  sum_dim_eq_general P a b

/-- Multiplicativity in the twist normalisation at `ℂ`. -/
theorem dim_mul_dim_c {S : FusionSystem n ℂ} (P : PivotalStructure S) (a b : Fin n) :
    dim P a * dim P b = P.pVal a * P.pVal b * (S.kappa a * S.kappa b) :=
  dim_mul_dim_general P a b

/-- **Settling `J` at `ℂ`**: multiplicativity `⟺` the sum identity (M). -/
theorem mult_iff_twist_c {S : FusionSystem n ℂ} (P : PivotalStructure S) :
    (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c) = dim P a * dim P b) ↔
      (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : ℂ) * S.J a b c * S.kappa c)
          = S.kappa a * S.kappa b) :=
  mult_iff_twist_general P

/-- (K) ⇒ (M) at `ℂ`. -/
theorem twist_sum_of_perChannel_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = algebraMap ℝ ℂ (hFP.fpdim c) * S.kappa a * S.kappa b /
        (S.kappa c * algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b))) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * S.J a b c * S.kappa c)
        = S.kappa a * S.kappa b :=
  twist_sum_of_perChannel_general hFP hn hK

/-- (K) ⇒ multiplicativity at `ℂ`. -/
theorem mult_of_perChannel_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = algebraMap ℝ ℂ (hFP.fpdim c) * S.kappa a * S.kappa b /
        (S.kappa c * algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b)))
    (P : PivotalStructure S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c) = dim P a * dim P b :=
  mult_of_perChannel_general hFP hn hK P

/-- Multiplicativity is a property of the twist, not of the pivotal structure, at `ℂ`. -/
theorem mult_iff_mult_c {S : FusionSystem n ℂ} (P P' : PivotalStructure S) :
    (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c) = dim P a * dim P b) ↔
      (∀ a b : Fin n,
        (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P' c) = dim P' a * dim P' b) :=
  mult_iff_mult_general P P'

/-- `κ` at the unit is `1` at `ℂ`. -/
theorem kappa_unit_c (hn : 0 < n) {S : FusionSystem n ℂ} : S.kappa ⟨0, hn⟩ = 1 :=
  kappa_unit_general (S := S) hn

/-- The dimension of the unit at `ℂ`. -/
theorem dim_unit_c {S : FusionSystem n ℂ} (P : PivotalStructure S) (hn : 0 < n) :
    dim P ⟨0, hn⟩ = 1 :=
  dim_unit_general P hn

/-- The frozen `J_match` at the settled twist at `ℂ` gives multiplicativity of any pivotal
dimension — the `mult` field of `Cx.IsPseudoUnitaryPivotal`. -/
theorem mult_of_J_match_settledJ_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (h : J_match S (settledJ S hFP)) (P : PivotalStructure S) :
    ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * dim P c) = dim P a * dim P b :=
  mult_of_J_match_settledJ hFP hn h P

/-- **Pseudo-unitarity turns the global sum into the sum of squares at `ℂ`**: if `κ` is
duality-invariant (`κ (i*) = κ i`) and `Pos`-valued, the frozen pseudo-unitarity equation
`Σ_i κ_i κ_{i*} = algebraMap ℝ ℂ (globalDim)` says `Σ_i ‖κ_i‖² = Σ_i f_i²`.  This is the
bookkeeping step between the source's `dim(C) = FPdim(C)` and the equality case of
Proposition 8.21. -/
theorem sum_kappa_sq_eq_of_pseudoUnitaryC {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData)
    (hdual : ∀ i, S.kappa (S.ring.dual i) = S.kappa i)
    (hpos : ∀ i, Pos (S.kappa i)) (hPU : IsPseudoUnitaryC S hFP) :
    (∑ i : Fin n, ‖S.kappa i‖ ^ 2) = ∑ i : Fin n, (hFP.fpdim i) ^ 2 := by
  choose r hr hκ using hpos
  have hsq : ((∑ i : Fin n, (r i) ^ 2 : ℝ) : ℂ) =
      ((∑ i : Fin n, (hFP.fpdim i) ^ 2 : ℝ) : ℂ) := by
    have h1 : ((∑ i : Fin n, (r i) ^ 2 : ℝ) : ℂ) = ∑ i, S.kappa i * S.kappa i := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hκ i, pow_two]
    have h2 : (∑ i, S.kappa i * S.kappa i) = algebraMap ℝ ℂ hFP.globalDim := by
      rw [← hPU]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdual i]
    have h3 : (algebraMap ℝ ℂ) hFP.globalDim = ((∑ i : Fin n, (hFP.fpdim i) ^ 2 : ℝ) : ℂ) := by
      rw [FPData.globalDim.eq_def]
      rfl
    exact h1.trans (h2.trans h3)
  have hnorm : ∀ i, ‖S.kappa i‖ = r i := by
    intro i
    rw [hκ i, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr i)]
  calc (∑ i : Fin n, ‖S.kappa i‖ ^ 2)
      = ∑ i : Fin n, (r i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hnorm i]
    _ = ∑ i : Fin n, (hFP.fpdim i) ^ 2 := Complex.ofReal_injective hsq

/-- **ENO §8.4 at `ℂ` for `κ`**: if `κ` is itself a character of the fusion ring (the
character identity, i.e. multiplicativity of the pivotal dimension for the trivial pivotal
structure `p ≡ 1` — equivalently the twist identity (M) with `J ≡ 1` on supported
channels), `κ` is duality-invariant and `Pos`-valued, and the frozen pseudo-unitarity
equation holds, then `κ` *is* the FP-dimension.  Composes the `ℂ` character form of
Proposition 8.21 (`abs_le_fpdim_of_char_c`) with its equality case
(`eq_abs_of_sum_sq_c`). -/
theorem kappa_eq_fpdim_of_pseudoUnitaryC {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n)
    (hchar : ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * S.kappa c) = S.kappa a * S.kappa b)
    (hdual : ∀ i, S.kappa (S.ring.dual i) = S.kappa i)
    (hpos : ∀ i, Pos (S.kappa i)) (hPU : IsPseudoUnitaryC S hFP) :
    ∀ i : Fin n, S.kappa i = algebraMap ℝ ℂ (hFP.fpdim i) := by
  have hbound : ∀ i, ‖S.kappa i‖ ≤ hFP.fpdim i :=
    abs_le_fpdim_of_char_c (R := S.ring) hFP hn S.kappa hdual hchar
  have hsum := sum_kappa_sq_eq_of_pseudoUnitaryC hFP hdual hpos hPU
  have hfeq : ∀ i, ‖S.kappa i‖ = hFP.fpdim i :=
    eq_abs_of_sum_sq_c (fun i => le_of_lt (hFP.pos i)) hbound hsum
  choose r hr hκ using hpos
  intro i
  have h2 : ‖S.kappa i‖ = r i := by
    rw [hκ i, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr i)]
  calc S.kappa i = algebraMap ℝ ℂ (r i) := hκ i
    _ = algebraMap ℝ ℂ ‖S.kappa i‖ := by rw [h2]
    _ = algebraMap ℝ ℂ (hFP.fpdim i) := by rw [hfeq i]

/-- **ENO §8.4 at `ℂ`, termwise form**: for a pivotal structure whose dimension function is
positive, duality-invariant (spherical) and multiplicative, pseudo-unitarity forces the
categorical dimensions to be the FP-dimensions.  The dual-invariance hypothesis is exactly
sphericity of the dimension function, and pseudo-unitarity enters through
`dim P i · dim P (i*) = κ_i κ_{i*}` (`dim_mul_dim_dual_general`): the chain is

`Σ_i ‖dim P i‖² = Σ_i dim P i · dim P (i*) = Σ_i κ_i κ_{i*} = globalDim = Σ_i f_i²`,

after which Proposition 8.21's bound and its equality case give `‖dim P i‖ = f_i` termwise.
-/
theorem dim_eq_fpdim_of_pseudoUnitaryC {n : ℕ} {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (P : PivotalStructure S)
    (hpos : ∀ i : Fin n, Pos (dim P i))
    (hdual : ∀ i : Fin n, dim P (S.ring.dual i) = dim P i)
    (hmult : ∀ i kk : Fin n,
      (∑ j : Fin n, (S.ring.N i j kk : ℂ) * dim P j) = dim P i * dim P kk)
    (hPU : IsPseudoUnitaryC S hFP) :
    ∀ i : Fin n, dim P i = algebraMap ℝ ℂ (hFP.fpdim i) := by
  have hbound : ∀ i, ‖dim P i‖ ≤ hFP.fpdim i :=
    abs_le_fpdim_of_eigenvector_c (R := S.ring) hFP hn (dim P) hmult
  choose r hr hd using hpos
  have hnorm : ∀ i, ‖dim P i‖ = r i := by
    intro i
    rw [hd i, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr i)]
  have hsum : (∑ i : Fin n, ‖dim P i‖ ^ 2) = ∑ i : Fin n, (hFP.fpdim i) ^ 2 := by
    have hsq : ((∑ i : Fin n, (r i) ^ 2 : ℝ) : ℂ) =
        ((∑ i : Fin n, (hFP.fpdim i) ^ 2 : ℝ) : ℂ) := by
      have h1 : ((∑ i : Fin n, (r i) ^ 2 : ℝ) : ℂ) = ∑ i, dim P i * dim P i := by
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        rw [hd i, pow_two]
      have h2 : (∑ i, dim P i * dim P i) =
          ∑ i, S.kappa i * S.kappa (S.ring.dual i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← dim_mul_dim_dual_general P hn i, hdual i]
      have h3 : (∑ i, S.kappa i * S.kappa (S.ring.dual i)) =
          algebraMap ℝ ℂ hFP.globalDim := hPU
      have h4 : (algebraMap ℝ ℂ) hFP.globalDim =
          ((∑ i : Fin n, (hFP.fpdim i) ^ 2 : ℝ) : ℂ) := by
        rw [FPData.globalDim.eq_def]
        rfl
      exact h1.trans (h2.trans (h3.trans h4))
    calc (∑ i : Fin n, ‖dim P i‖ ^ 2) = ∑ i : Fin n, (r i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hnorm i]
      _ = ∑ i : Fin n, (hFP.fpdim i) ^ 2 := Complex.ofReal_injective hsq
  have hfeq : ∀ i, ‖dim P i‖ = hFP.fpdim i :=
    eq_abs_of_sum_sq_c (fun i => le_of_lt (hFP.pos i)) hbound hsum
  intro i
  have h2 : ‖dim P i‖ = r i := hnorm i
  calc dim P i = algebraMap ℝ ℂ (r i) := hd i
    _ = algebraMap ℝ ℂ ‖dim P i‖ := by rw [h2]
    _ = algebraMap ℝ ℂ (hFP.fpdim i) := by rw [hfeq i]

end FusionCategory
#print axioms FusionCategory.norm_le_fpdim_of_eigenvector
#print axioms FusionCategory.abs_le_fpdim_of_eigenvector_c
#print axioms FusionCategory.abs_le_fpdim_of_eigenvector_real_norm
#print axioms FusionCategory.eq_abs_of_sum_sq_c
#print axioms FusionCategory.abs_dim_le_fpdim_of_pseudoUnitaryC
#print axioms FusionCategory.eq_abs_of_pseudoUnitaryC
#print axioms FusionCategory.abs_le_fpdim_of_char_c
#print axioms FusionCategory.algebraMap_ne_zero_of_ne_zero
#print axioms FusionCategory.fpdim_char_algebraMap
#print axioms FusionCategory.sum_dim_eq_general
#print axioms FusionCategory.dim_mul_dim_general
#print axioms FusionCategory.mult_iff_twist_general
#print axioms FusionCategory.mult_iff_mult_general
#print axioms FusionCategory.dim_dual_general
#print axioms FusionCategory.dim_mul_dim_dual_general
#print axioms FusionCategory.kappa_unit_general
#print axioms FusionCategory.dim_unit_general
#print axioms FusionCategory.twist_sum_of_perChannel_general
#print axioms FusionCategory.mult_of_perChannel_general
#print axioms FusionCategory.settledJ
#print axioms FusionCategory.j_match_settledJ_iff
#print axioms FusionCategory.mult_of_J_match_settledJ
#print axioms FusionCategory.sum_dim_eq_c
#print axioms FusionCategory.dim_mul_dim_c
#print axioms FusionCategory.mult_iff_twist_c
#print axioms FusionCategory.mult_iff_mult_c
#print axioms FusionCategory.kappa_unit_c
#print axioms FusionCategory.dim_unit_c
#print axioms FusionCategory.twist_sum_of_perChannel_c
#print axioms FusionCategory.mult_of_perChannel_c
#print axioms FusionCategory.mult_of_J_match_settledJ_c
#print axioms FusionCategory.sum_kappa_sq_eq_of_pseudoUnitaryC
#print axioms FusionCategory.kappa_eq_fpdim_of_pseudoUnitaryC
#print axioms FusionCategory.dim_eq_fpdim_of_pseudoUnitaryC
