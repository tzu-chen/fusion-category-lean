import FusionCategory.Prop821
import FusionCategory.Statements
import Mathlib.Analysis.Complex.Basic

/-!
# ENO §8.4 at `ℂ`: the ℓ²-equality chain downstream of Proposition 8.21

WP1 / Task 1.1, direction D6.  The `ℝ` chain of `FusionCategory.Prop821` is

* `abs_le_fpdim_of_eigenvector` / `abs_le_fpdim_of_mult` — `|d_i| ≤ FPdim_i` whenever
  `d` is an eigenvector (multiplicative on the fusion ring);
* `eq_abs_of_sum_sq` — with the total `Σ_i |d_i|² = Σ_i FPdim_i²` the bound is termwise
  an equality;
* `eq_abs_of_pseudoUnitary` — the two combined.

This file ports the **downstream** half of that chain to `ℂ` — the half WP3/WP4 consume —
and deliberately *does not* reprove the ℂ eigenvector bound itself (that is the parallel
direction's remit): every theorem here either

* pushes a `ℂ` hypothesis down to `ℝ` (`Complex.ofReal_injective`) and applies the
  existing `ℝ` bound, or
* is purely algebraic over `ℂ` (the character-to-eigenvector reindexing), or
* is the equality case in the *product* form `Σ_i r_i r_{i*} = Σ_i f_i²`, which is the
  form the pseudo-unitarity equation `Σ_i κ_i κ_{i*} = D` actually delivers.

## The modulus at `ℂ` is `‖·‖`, not `Complex.abs`

In this Mathlib (Lean 4.33.1, the pinned one) `Complex.abs` **does not exist**: the
`abs → norm` migration has happened.  The scalar modulus is `‖z‖ : ℝ`, with
`Complex.norm_real : ‖(r : ℂ)‖ = ‖r‖` (then `Real.norm_eq_abs`) and
`Complex.normSq_eq_norm_sq : Complex.normSq z = ‖z‖ ^ 2`.  Every statement below is
therefore written with `‖·‖`; read `‖d i‖` for the source's `|d_i|`.

## What is proved here

* `pos_witness` — `Pos` at every index unwinds to a family of positive real witnesses;
  this is the whole content of the scalar contract as far as analysis is concerned.
* `eigenvector_of_eigenvector_c` — a `ℂ` eigenvector equation for a real-valued function
  is an `ℝ` eigenvector equation (`ofReal` injectivity).
* `eigenvector_of_char_c` — the character ⟹ eigenvector reindexing (`cyclic2` +
  `sum_dual_reindex`) with the scalars in `ℂ`.  Purely algebraic: this is the whole of
  the *structural* content of `abs_le_fpdim_of_char`, separated from the estimate.
* `abs_le_fpdim_of_char_c_ofReal` / `abs_le_fpdim_of_char_c` — the character form at `ℂ`:
  closed for real-valued `d`, and reduced to the (parallel) ℂ eigenvector bound in general.
* `fpdim_char_c` — the `ℂ` character identity `Σ_c N^c_{ab} f_c = f_a f_b`.
* `eq_of_sum_mul` — the equality case in product form.
* `dim_mul_dim_dual_c`, `sum_dim_mul_dim_dual_c` — the categorical global dimension at
  `ℂ` is `Σ_i κ_i κ_{i*}`, whatever the pivotal structure (field-generic port of
  `dim_mul_dim_dual`), hence equals `algebraMap ℝ ℂ hFP.globalDim` under
  `IsPseudoUnitaryC`.
* `eq_norm_of_pseudoUnitary_c` — the ℓ² step: positivity + multiplicativity + the global
  sum identity give `‖d_i‖ = FPdim_i` (the `Complex.abs`-era
  `eq_abs_of_pseudoUnitary` rendered with `‖·‖`; it needs **no** ℂ eigenvector bound).
* `eq_norm_dim_of_pseudoUnitaryC` — the same end to end from the frozen hypothesis
  `IsPseudoUnitaryC S hFP` and a pivotal structure with `Cx.IsPseudoUnitaryPivotal P`,
  i.e. ENO §8.4's `|V|² = FPdim(V)²` in the shape the frozen ℂ statements consume.

Axiom budget: `[propext, Classical.choice, Quot.sound]`; checked at the end of the file.
-/

open Finset BigOperators

namespace FusionCategory

open FusionRing

variable {n : ℕ}

/-! ## 0. The scalar contract: `Pos`, and the modulus of a positive real -/

/-- **Unwinding `Pos`.**  A family of `Pos` complex numbers is a family of positive real
witnesses, cast.  Every ℂ-to-ℝ argument below starts here. -/
theorem pos_witness {d : Fin n → ℂ} (hpos : ∀ i, Pos (d i)) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ ∀ i, d i = ((r i : ℝ) : ℂ) := by
  simp only [Pos] at hpos
  choose r hr using hpos
  exact ⟨r, fun i => (hr i).1, fun i => (hr i).2⟩

/-- The modulus of a positive real, at `ℂ`. -/
theorem norm_ofReal_of_pos {r : ℝ} (h : 0 < r) : ‖((r : ℝ) : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h]

/-! ## 1. Pushing a `ℂ` equation down to `ℝ`

These are the only bridge lemmas needed: `algebraMap ℝ ℂ = Complex.ofReal` is `rfl` in
this Mathlib, so `Complex.ofReal_injective` is the whole passage. -/

/-- A `ℂ` eigenvector equation for a real-valued function is an `ℝ` eigenvector
equation for its real witness. -/
theorem eigenvector_of_eigenvector_c {R : FusionRing n} (r : Fin n → ℝ)
    (h : ∀ i kk : Fin n,
      (∑ j : Fin n, (R.N i j kk : ℂ) * ((r j : ℝ) : ℂ))
        = ((r i : ℝ) : ℂ) * ((r kk : ℝ) : ℂ)) :
    ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : ℝ) * r j) = r i * r kk := by
  intro i kk
  apply Complex.ofReal_injective
  push_cast
  exact h i kk

/-! ## 2. The character form at `ℂ`: the algebraic reindexing, with scalars in `ℂ`

`abs_le_fpdim_of_char` at `ℝ` is two things: an estimate (the eigenvector bound) and a
structural reduction of the character form to the eigenvector form.  Only the second is
reproved here, at `ℂ`, and it is the *only* place where the fusion-ring axioms
(`cyclic2`, duality reindexing) enter. -/

/-- **Character form ⟹ eigenvector form, at `ℂ`.**  `N a b c = N (c*) a (b*)` moves the
character's summation slot to the third slot, duality invariance of `d` puts `d` on the
reindexed label, and the sum reindexes along `*`. -/
theorem eigenvector_of_char_c {R : FusionRing n} (hn : 0 < n) (d : Fin n → ℂ)
    (hdual : ∀ i, d (R.dual i) = d i)
    (hchar : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℂ) * d c) = d a * d b) :
    ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : ℂ) * d j) = d i * d kk := by
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
        sum_dual_reindex (fun m => (R.N (R.dual kk) i m : ℂ) * d m)
    _ = d (R.dual kk) * d i := hchar (R.dual kk) i
    _ = d i * d kk := by rw [hdual kk, mul_comm]

/-- The character bound at `ℂ` for real-valued dimension functions, closed: no
hypothesis cargo, the estimate is pushed down to the retained `ℝ` theorem
`abs_le_fpdim_of_char`.  (The complex-valued character bound is
`Prop821CNorm.abs_le_fpdim_of_char_c`, closed there from the eigenvector bound;
the reindexing it needs is `eigenvector_of_char_c` above.) -/
theorem abs_le_fpdim_of_char_c_ofReal {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (r : Fin n → ℝ) (hdual : ∀ i, r (R.dual i) = r i)
    (hchar : ∀ a b : Fin n,
      (∑ c : Fin n, (R.N a b c : ℂ) * ((r c : ℝ) : ℂ))
        = ((r a : ℝ) : ℂ) * ((r b : ℝ) : ℂ)) :
    ∀ i, ‖((r i : ℝ) : ℂ)‖ ≤ h.fpdim i := by
  have hchar_r : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℝ) * r c) = r a * r b :=
    fun a b => by
      apply Complex.ofReal_injective
      push_cast
      exact hchar a b
  have hbound := abs_le_fpdim_of_char h hn r hdual hchar_r
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound

/-- The FP-dimension is a character at `ℂ` too: `Σ_c N^c_{ab} f_c = f_a f_b`.  The `ℝ`
statement `fpdim_char` cast; WP3 needs the `ℂ` form because the twist lives at `ℂ`. -/
theorem fpdim_char_c {R : FusionRing n} (h : R.FPData) (hn : 0 < n) (a b : Fin n) :
    (∑ c : Fin n, (R.N a b c : ℂ) * ((h.fpdim c : ℝ) : ℂ))
      = ((h.fpdim a : ℝ) : ℂ) * ((h.fpdim b : ℝ) : ℂ) := by
  have h2 := congrArg Complex.ofReal (fpdim_char h hn a b)
  simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] using h2

/-! ## 3. The equality case in product form

`eq_abs_of_sum_sq` at `ℝ` compares `Σ_i |d_i|²` with `Σ_i f_i²`.  At `ℂ` the identity
that pseudo-unitarity *actually* provides is the product form `Σ_i d_i d_{i*} = D`: the
categorical global dimension is `Σ_i κ_i κ_{i*}` (`dim_mul_dim_dual`), not `Σ_i κ_i²`.
The equality case in that form is what is needed, and it is a genuinely different
statement when `d` need not be `*`-invariant. -/

/-- **Equality case, product form.**  If `r` and `f` are positive, `f` is invariant under
`σ`, `r ≤ f` termwise and `Σ_i r_i r_{σ i} = Σ_i f_i²`, then `r = f`. -/
theorem eq_of_sum_mul {σ : Fin n → Fin n} {r f : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hf : ∀ i, 0 < f i) (hfσ : ∀ i, f (σ i) = f i)
    (hle : ∀ i, r i ≤ f i)
    (hsum : (∑ i : Fin n, r i * r (σ i)) = ∑ i : Fin n, f i * f i) :
    ∀ i, r i = f i := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ f i * f i - r i * r (σ i) := by
    intro i _
    have h1 : r i ≤ f i := hle i
    have h2 : r (σ i) ≤ f i := by
      have h := hle (σ i)
      rwa [hfσ i] at h
    have h3 : r i * r (σ i) ≤ f i * f i := by
      calc r i * r (σ i) ≤ f i * r (σ i) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt (hr (σ i)))
        _ ≤ f i * f i := mul_le_mul_of_nonneg_left h2 (le_of_lt (hf i))
    linarith
  have hzero : (∑ i : Fin n, (f i * f i - r i * r (σ i))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    ring
  intro i
  have hterm : f i * f i - r i * r (σ i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i (Finset.mem_univ i)
  by_contra hne
  have hlt : r i < f i := lt_of_le_of_ne (hle i) hne
  have h2 : r (σ i) ≤ f i := by
    have h := hle (σ i)
    rwa [hfσ i] at h
  have hprod : r i * r (σ i) < f i * f i := by
    calc r i * r (σ i) < f i * r (σ i) := mul_lt_mul_of_pos_right hlt (hr (σ i))
      _ ≤ f i * f i := mul_le_mul_of_nonneg_left h2 (le_of_lt (hf i))
  linarith

/-! ## 4. The ℓ² step at `ℂ`

Positivity + multiplicativity + the global sum identity give `‖d_i‖ = FPdim_i`.  This is
the ℂ form of `eq_abs_of_pseudoUnitary` — with the sum identity in the product form, and
with the estimate taken from the *retained* `ℝ` bound, so no ℂ eigenvector bound is
used. -/

/-- **Positivity + multiplicativity give the `ℝ` bound.**  The real witness of a `Pos`
dimension function that is multiplicative on the fusion ring is dominated by the
FP-dimensions — ENO Proposition 8.21 at `ℂ` for positive dimension functions, obtained
from the retained `ℝ` theorem, so no `ℂ` eigenvector bound is used. -/
theorem pos_witness_le_fpdim {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (d : Fin n → ℂ) (hpos : ∀ i, Pos (d i))
    (hmult : ∀ i kk : Fin n, (∑ j : Fin n, (S.ring.N i j kk : ℂ) * d j) = d i * d kk) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ (∀ i, d i = ((r i : ℝ) : ℂ)) ∧
      ∀ i, r i ≤ hFP.fpdim i := by
  obtain ⟨r, hrpos, hrd⟩ := pos_witness hpos
  -- the `ℂ` eigenvector equation is an `ℝ` eigenvector equation
  have hmult_r : ∀ i kk : Fin n,
      (∑ j : Fin n, (S.ring.N i j kk : ℂ) * ((r j : ℝ) : ℂ))
        = ((r i : ℝ) : ℂ) * ((r kk : ℝ) : ℂ) := by
    intro i kk
    simpa only [hrd] using hmult i kk
  have heig : ∀ i kk : Fin n, (∑ j : Fin n, (S.ring.N i j kk : ℝ) * r j) = r i * r kk :=
    eigenvector_of_eigenvector_c r hmult_r
  -- the retained `ℝ` bound, Prop. 8.21
  have hbound : ∀ i : Fin n, |r i| ≤ hFP.fpdim i := abs_le_fpdim_of_eigenvector hFP hn r heig
  refine ⟨r, hrpos, hrd, fun i => ?_⟩
  have h := hbound i
  rwa [abs_of_pos (hrpos i)] at h

/-- **ENO Proposition 8.21 at `ℂ`**, dimension-function form: `‖d_i‖ ≤ FPdim_i`. -/
theorem abs_le_fpdim_of_multiplicative_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (d : Fin n → ℂ) (hpos : ∀ i, Pos (d i))
    (hmult : ∀ i kk : Fin n, (∑ j : Fin n, (S.ring.N i j kk : ℂ) * d j) = d i * d kk) :
    ∀ i, ‖d i‖ ≤ hFP.fpdim i := by
  obtain ⟨r, hrpos, hrd, hrle⟩ := pos_witness_le_fpdim hFP hn d hpos hmult
  intro i
  rw [hrd i, norm_ofReal_of_pos (hrpos i)]
  exact hrle i

/-- **ENO §8.4, the ℓ²-equality step at `ℂ`.**  For `d : Fin n → ℂ` with positive real
values (`Pos`), multiplicative on the fusion ring, and satisfying the global identity
`Σ_i d_i d_{i*} = D`, the moduli are the FP-dimensions. -/
theorem eq_norm_of_pseudoUnitary_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (d : Fin n → ℂ) (hpos : ∀ i, Pos (d i))
    (hmult : ∀ i kk : Fin n, (∑ j : Fin n, (S.ring.N i j kk : ℂ) * d j) = d i * d kk)
    (hsum : (∑ i : Fin n, d i * d (S.ring.dual i)) = algebraMap ℝ ℂ hFP.globalDim) :
    ∀ i, ‖d i‖ = hFP.fpdim i := by
  obtain ⟨r, hrpos, hrd, hrle⟩ := pos_witness_le_fpdim hFP hn d hpos hmult
  -- (3) the global identity, pushed down
  have hsum_c : (∑ i : Fin n, d i * d (S.ring.dual i)) = ((hFP.globalDim : ℝ) : ℂ) := by
    simpa [FusionRing.FPData.globalDim] using hsum
  have hsum_r : (∑ i : Fin n, r i * r (S.ring.dual i))
      = ∑ i : Fin n, hFP.fpdim i * hFP.fpdim i := by
    apply Complex.ofReal_injective
    push_cast
    trans (∑ i : Fin n, d i * d (S.ring.dual i))
    · apply Finset.sum_congr rfl
      intro i _
      rw [hrd i, hrd (S.ring.dual i)]
    · trans ((hFP.globalDim : ℝ) : ℂ)
      · exact hsum_c
      · rw [FusionRing.FPData.globalDim]
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        ring
  -- (4) equality case
  have heq : ∀ i : Fin n, r i = hFP.fpdim i :=
    eq_of_sum_mul (σ := S.ring.dual) hrpos (fun i => hFP.pos i) (fun i => hFP.dual_eq i)
      hrle hsum_r
  intro i
  rw [hrd i, norm_ofReal_of_pos (hrpos i)]
  exact heq i

/-- The same with the global identity in the *square* form: `d` is `*`-invariant, so
`Σ_i d_i² = Σ_i d_i d_{i*}`. -/
theorem eq_norm_of_sq_sum_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (d : Fin n → ℂ) (hpos : ∀ i, Pos (d i)) (hdual : ∀ i, d (S.ring.dual i) = d i)
    (hmult : ∀ i kk : Fin n, (∑ j : Fin n, (S.ring.N i j kk : ℂ) * d j) = d i * d kk)
    (hsum : (∑ i : Fin n, d i * d i) = algebraMap ℝ ℂ hFP.globalDim) :
    ∀ i, ‖d i‖ = hFP.fpdim i := by
  refine eq_norm_of_pseudoUnitary_c hFP hn d hpos hmult ?_
  rw [← hsum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hdual i])

/-! ## 5. Assembling with the frozen `ℂ` hypotheses

`dim_mul_dim_dual` is field-generic (`dim P i * dim P i* = κ_i κ_i*` uses only
`pVal_dual`), so it is ported here at `ℂ`; with it, `IsPseudoUnitaryC` becomes exactly
the global identity consumed above, and the ℓ² step becomes a theorem about the frozen
ℂ pseudo-unitarity predicate. -/

/-- The categorical global dimension at `ℂ` is `Σ_i κ_i κ_{i*}`, independently of the
pivotal structure — the `ℂ` form of `dim_mul_dim_dual`. -/
theorem dim_mul_dim_dual_c {S : FusionSystem n ℂ} (hn : 0 < n) (P : PivotalStructure S)
    (i : Fin n) :
    dim P i * dim P (S.ring.dual i) = S.kappa i * S.kappa (S.ring.dual i) := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq, P.pVal_dual hn i]
  field_simp [P.pVal_ne_zero i]

/-- **`IsPseudoUnitaryC` is the global identity on the pivotal dimensions.** -/
theorem sum_dim_mul_dim_dual_c {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (P : PivotalStructure S) (hPU : IsPseudoUnitaryC S hFP) :
    (∑ i : Fin n, dim P i * dim P (S.ring.dual i)) = algebraMap ℝ ℂ hFP.globalDim := by
  calc (∑ i : Fin n, dim P i * dim P (S.ring.dual i))
      = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) :=
        Finset.sum_congr rfl (fun i _ => dim_mul_dim_dual_c hn P i)
    _ = algebraMap ℝ ℂ hFP.globalDim := hPU

/-- **ENO Proposition 8.21 + §8.4 at `ℂ`.**  A pivotal structure of a pseudo-unitary ℂ
system whose dimension function is `Pos` and multiplicative has dimension moduli equal to
the FP-dimensions.  This is the ℂ shape WP3/WP4 consume: no Perron–Frobenius input and no
ℂ eigenvector bound is used. -/
theorem eq_norm_dim_of_pseudoUnitaryC {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P) :
    ∀ i, ‖dim P i‖ = hFP.fpdim i :=
  eq_norm_of_pseudoUnitary_c hFP hn (dim P) hU.pos hU.mult (sum_dim_mul_dim_dual_c hFP hn P hPU)

/-! ## 6. From moduli to dimensions: the conclusion shape of ENO 8.23 at `ℂ`

`‖d_i‖ = FPdim_i` is the *moduli* statement; the frozen ℂ statements ask for
`dim P i = algebraMap ℝ ℂ (hFP.fpdim i)`.  Under `Pos` the passage is the real witness,
and sphericity is then immediate from `fpdim i* = fpdim i`. -/

/-- A positive real read through `algebraMap ℝ ℂ` (which is `Complex.ofReal`
definitionally) is `Pos`.  (The `(r : ℝ) : ℂ` form is `Duality.pos_ofReal`.) -/
theorem pos_algebraMap {r : ℝ} (h : 0 < r) : Pos (algebraMap ℝ ℂ r) := ⟨r, h, rfl⟩

/-- `Pos` excludes zero. -/
theorem Pos.ne_zero {z : ℂ} (h : Pos z) : z ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := h
  exact fun h0 => (ne_of_gt hr) ((Complex.ofReal_eq_zero).mp h0)

/-- **Modulus to dimension.**  A `Pos` complex number whose modulus is `r` *is* `↑r`. -/
theorem eq_algebraMap_of_pos_of_norm {z : ℂ} {r : ℝ} (hz : Pos z) (h : ‖z‖ = r) :
    z = algebraMap ℝ ℂ r := by
  obtain ⟨r', hr', rfl⟩ := hz
  rw [norm_ofReal_of_pos hr'] at h
  rw [h]
  rfl

/-- Dimension functions: moduli equal to the FP-dimensions are the FP-dimensions. -/
theorem dim_eq_algebraMap_of_norm_eq {S : FusionSystem n ℂ} (P : PivotalStructure S)
    (hFP : S.ring.FPData) (hpos : ∀ i, Pos (dim P i)) (h : ∀ i, ‖dim P i‖ = hFP.fpdim i) :
    ∀ i, dim P i = algebraMap ℝ ℂ (hFP.fpdim i) :=
  fun i => eq_algebraMap_of_pos_of_norm (hpos i) (h i)

/-- **ENO §8.4 at `ℂ`: pseudo-unitarity forces the dimensions to be the FP-dimensions.**
For a pivotal structure of a pseudo-unitary ℂ system whose dimensions are `Pos` and
multiplicative.  No Perron–Frobenius input: this is the Proposition-8.21/ℓ² route. -/
theorem dim_eq_algebraMap_of_pseudoUnitaryC {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P) :
    ∀ i, dim P i = algebraMap ℝ ℂ (hFP.fpdim i) :=
  dim_eq_algebraMap_of_norm_eq P hFP hU.pos (eq_norm_dim_of_pseudoUnitaryC hFP hn hPU P hU)

/-- **Sphericity at `ℂ` from pseudo-unitarity**: `dim P i* = dim P i` follows from the
FP-dimension equality, because `fpdim i* = fpdim i`. -/
theorem isSpherical_of_pseudoUnitaryC {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P) : P.IsSpherical := by
  intro i
  rw [dim_eq_algebraMap_of_pseudoUnitaryC hFP hn hPU P hU (S.ring.dual i),
    dim_eq_algebraMap_of_pseudoUnitaryC hFP hn hPU P hU i, hFP.dual_eq i]

/-- **ENO Proposition 8.23, concluded at `ℂ` from pseudo-unitarity.**  A pivotal structure
with `Pos` and multiplicative dimensions on a pseudo-unitary ℂ system is spherical and
carries the FP-dimensions, i.e. the bare ℂ target `ENO823 S hFP` holds there.  Neither
`J_match`/`derivedJ` nor Perron–Frobenius uniqueness is needed on this route (compare the
frozen `Cx.eno823_of_pseudoUnitary`, which takes `PFUnique` and no `IsPseudoUnitaryC`). -/
theorem eno823_c_of_pseudoUnitaryPivotal {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hU : Cx.IsPseudoUnitaryPivotal P) : ENO823 S hFP :=
  ⟨P, isSpherical_of_pseudoUnitaryC hFP hn hPU P hU,
    dim_eq_algebraMap_of_pseudoUnitaryC hFP hn hPU P hU⟩


end FusionCategory

/-! ## Axiom audit (the budget is `[propext, Classical.choice, Quot.sound]`) -/

#print axioms FusionCategory.pos_witness
#print axioms FusionCategory.norm_ofReal_of_pos
#print axioms FusionCategory.eigenvector_of_eigenvector_c
#print axioms FusionCategory.eigenvector_of_char_c
#print axioms FusionCategory.abs_le_fpdim_of_char_c_ofReal
#print axioms FusionCategory.fpdim_char_c
#print axioms FusionCategory.eq_of_sum_mul
#print axioms FusionCategory.pos_witness_le_fpdim
#print axioms FusionCategory.abs_le_fpdim_of_multiplicative_c
#print axioms FusionCategory.eq_norm_of_pseudoUnitary_c
#print axioms FusionCategory.eq_norm_of_sq_sum_c
#print axioms FusionCategory.dim_mul_dim_dual_c
#print axioms FusionCategory.sum_dim_mul_dim_dual_c
#print axioms FusionCategory.eq_norm_dim_of_pseudoUnitaryC
#print axioms FusionCategory.pos_algebraMap
#print axioms FusionCategory.Pos.ne_zero
#print axioms FusionCategory.eq_algebraMap_of_pos_of_norm
#print axioms FusionCategory.dim_eq_algebraMap_of_norm_eq
#print axioms FusionCategory.dim_eq_algebraMap_of_pseudoUnitaryC
#print axioms FusionCategory.isSpherical_of_pseudoUnitaryC
#print axioms FusionCategory.eno823_c_of_pseudoUnitaryPivotal
