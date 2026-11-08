import FusionCategory.DimMult
import FusionCategory.Prop821CEq
import FusionCategory.Prop821CNorm
import FusionCategory.Statements

/-!
# The `ℂ` port of the sign argument: ENO 8.23 at the scalar contract, from `(M)`

WP4, direction D6.  `DimMult.lean` carries the twist sum identity

    (M)   Σ_c N^c_ab · J^c_ab · κ_c = κ_a κ_b

as a hypothesis on a real system and derives the whole of ENO 8.23 from it together with
pseudo-unitarity and one pivotal structure.  The frozen `Cx` family (`Statements.lean`) is
stated over `ℂ`, and its conditional form (`Cx.eno823_of_pseudoUnitary`, and
`Prop821CEq.eno823_c_of_pseudoUnitaryPivotal` which proves the `Cx` statement for one `P`)
carries `Pos` *and* multiplicativity of a chosen pivotal dimension as hypotheses.  This file
removes both: over `ℂ`, (M) alone already makes every pivotal dimension multiplicative,
pseudo-unitarity turns the bound of ENO 8.21 into a modulus equality, and the residual phase
is killed by the equality case of the triangle inequality.  The output is exactly the
per-channel identity (K) that `Coboundary.eno823_of_twistNorm` consumes, and from it the
exact conclusion of the source at `ℂ`: a *unique* spherical pivotal structure with `Pos`
dimensions equal to the FP-dimensions.

## What the `ℂ` chain does *not* need

* **No `Pos`.**  Over `ℝ` the bound `|dim P i| ≤ FPdim_i` plus the dual-paired equality
  gives `|dim P i| = FPdim_i`; over `ℂ` the same two inputs give `‖dim P i‖ = FPdim_i`
  with `Pos` nowhere in the proof (`norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC`).  The
  dimension of a pivotal structure at `ℂ` is a priori an arbitrary nonzero complex number,
  so this is a genuine gain over `abs_le_fpdim_of_multiplicative_c`, which assumes `Pos`.
* **No sphericity, and no `Cx.IsPseudoUnitaryPivotal`.**  Multiplicativity of `dim P` is
  *derived* from (M) (`DimMult.dimEigen_of_dimMult`), not assumed.
* **No `PFUnique`.**  As on the `ℝ` route.
* **No duality invariance of `dim P`.**  `Prop821CNorm.abs_le_fpdim_of_char_c` needs
  `d (i*) = d i` to reindex the character form into the eigenvector form; the weighted-norm
  argument below (`norm_le_fpdim_of_char`) runs directly on the character form, which is the
  form (M) delivers, and is field-generic.

The one thing the `ℂ` chain shares with the `ℝ` route is the pivotal structure `P` in the
antecedent: it is what the bound and the equality case are about.  Its existence is WP4
Tasks 4.1–4.2 (`SqrtData`), not this file.

## The chain, in order

1. `norm_le_fpdim_of_char` — ENO 8.21 over an arbitrary normed ring `K`, from the *character*
   form: `‖d_i‖ ≤ FPdim_i`.  The `ℂ` instance `abs_le_fpdim_of_mult_c` is the port of
   `Prop821.abs_le_fpdim_of_mult`; the datum form is `abs_dim_le_fpdim_of_dimMultC`.
2. `eq_norm_of_sum_mul_dual` — the equality case *in product form*: a termwise bound plus
   `Σ_i d_i d_{i*} = Σ_i f_i²` forces `‖d_i‖ = f_i`.  The `ℂ` form of
   `DimMult.eq_abs_of_sum_mul_dual`, and the place where `ℂ` differs: `Re (z)` is the
   bridge, not `|z|`.
3. `norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC` — (M) + `IsPseudoUnitaryC` give the moduli,
   for *every* pivotal structure.
4. `sum_twistNorm_of_dimMult_general`, `sum_fpdimRatio_general` — (M) read in the
   `κ`-normalised twist, and the character identity read the same way: both channel sums
   are `1`.
5. `norm_twistNorm_of_dimMult_pseudoUnitaryC` — hence the *modulus* of the normalised twist
   is the FP-dimension ratio on every supported channel: WP4 Task 4.5(a) at `ℂ`, with no
   `Pos` needed.
6. `twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c` — **(K), the deliverable**: the
   phase is `1`.  Write `twistNorm = s_c · f_c/(f_a f_b)`; then `‖s_c‖ = 1` on supported
   channels, (M) says `Σ_c N^c_ab s_c f_c = f_a f_b` while the character identity says the
   same sum with `s_c ≡ 1` is `f_a f_b`, so `Σ_c N^c_ab (1 - s_c) f_c = 0`; the real part of
   every term is `N^c_ab f_c (1 - Re s_c) ≥ 0`, so each is `0`, `Re s_c = 1`, and
   `‖s_c‖ = 1` leaves `s_c = 1`.  This is the `ℂ` rendering of ENO's `σ`/`τ` argument as an
   equality case of the triangle inequality.
7. The exact conclusion at `ℂ`, `eno823ExactC_of_dimMult` — via
   `Coboundary.exists_spherical_of_twistNorm` at `d = FPdim` and `pivotal_ext_c` for
   uniqueness; `eno823C_of_dimMult_pseudoUnitary` is the bare form through
   `Coboundary.eno823_of_twistNorm` (the check that (K) is literally that theorem's
   hypothesis), and `dimMult_of_J_match_settledJ` is the bridge that turns the frozen `Cx`
   family's `J_match`-at-the-derived-twist antecedent into (M) —
   `Prop821CNorm.settledJ` *is* the per-channel law (K).
8. `dim_eq_algebraMap_of_dimMult_pseudoUnitaryC`, `isSpherical_of_dimMult_pseudoUnitaryC`,
   `eno823ExactC_of_derivedJ` — the frozen `Cx` statements recovered as corollaries: the
   `Cx.IsPseudoUnitaryPivotal` hypothesis (`Pos` + `mult`) loses its `mult` field, and the
   `Cx` exact family at a derived twist `derivedJ` holds as soon as `derivedJ` satisfies the
   twisted character identity.

Non-vacuity: on the `ℂ` copies the tree carries (`Transported.FibonacciC`,
`Transported.dimMult_fibonacciC`, `Transported.isPseudoUnitaryC_fibonacci`) the chain
instantiates end to end; with `import FusionCategory.Transport`,

    eno823ExactC_of_dimMult fibonacciFPData (by norm_num) dimMult_fibonacciC
      isPseudoUnitaryC_fibonacci (Transport.mapPivotal (algebraMap ℝ ℂ) FibonacciPivotal)

is the exact conclusion of ENO 8.23 for the Fibonacci system read over `ℂ`.

Axiom budget: `[propext, Classical.choice, Quot.sound]` (checked at the end of the file).
-/

open Finset BigOperators
namespace FusionCategory
open FusionRing

variable {n : ℕ}

/-! ## 0. The bound over a normed ring -/

theorem norm_le_fpdim_of_char {K : Type*} [NormedRing K] [NormMulClass K]
    [NormOneClass K] [NormSMulClass ℤ K] {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → K)
    (hm : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : K) * d c) = d a * d b) :
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
      _ = ∑ k : Fin n, h.fpdim k * ‖∑ j : Fin n, (R.N i k j : K) * d j‖ := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hm i k]
      _ ≤ ∑ k : Fin n, h.fpdim k * (∑ j : Fin n, (R.N i k j : ℝ) * ‖d j‖) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (h.pos k))
          calc ‖∑ j : Fin n, (R.N i k j : K) * d j‖
              ≤ ∑ j : Fin n, ‖(R.N i k j : K) * d j‖ := norm_sum_le _ _
            _ = ∑ j : Fin n, (R.N i k j : ℝ) * ‖d j‖ := by
                apply Finset.sum_congr rfl
                intro j _
                rw [norm_mul, norm_natCast]
      _ = ∑ k : Fin n, ∑ j : Fin n, h.fpdim k * ((R.N i k j : ℝ) * ‖d j‖) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin n, h.fpdim k * ((R.N i k j : ℝ) * ‖d j‖) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, (∑ k : Fin n, h.fpdim k * (R.N i k j : ℝ)) * ‖d j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ j : Fin n, (h.fpdim i * h.fpdim j) * ‖d j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          have hc : (∑ k : Fin n, h.fpdim k * (R.N i k j : ℝ)) = h.fpdim i * h.fpdim j :=
            fpdim_char_mid h hn i j
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

theorem abs_le_fpdim_of_mult_c {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → ℂ)
    (hm : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℂ) * d c) = d a * d b) :
    ∀ i, ‖d i‖ ≤ h.fpdim i :=
  norm_le_fpdim_of_char (K := ℂ) h hn d hm

theorem abs_dim_le_fpdim_of_dimMultC {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (P : PivotalStructure S) :
    ∀ i, ‖dim P i‖ ≤ hFP.fpdim i :=
  abs_le_fpdim_of_mult_c hFP hn (dim P) (dimEigen_of_dimMult hM P)

/-! ## 1. The equality case -/

theorem eq_norm_of_sum_mul_dual {σ : Fin n → Fin n} {d : Fin n → ℂ} {f : Fin n → ℝ}
    (hf : ∀ i, 0 < f i) (hfσ : ∀ i, f (σ i) = f i)
    (hle : ∀ i, ‖d i‖ ≤ f i)
    (hsum : (∑ i : Fin n, d i * d (σ i)) = algebraMap ℝ ℂ (∑ i : Fin n, f i * f i)) :
    ∀ i, ‖d i‖ = f i := by
  have hle_term : ∀ i, (d i * d (σ i)).re ≤ f i * f i := by
    intro i
    have h1 : (d i * d (σ i)).re ≤ ‖d i * d (σ i)‖ := Complex.re_le_norm _
    have h2 : ‖d i * d (σ i)‖ = ‖d i‖ * ‖d (σ i)‖ := norm_mul _ _
    have h3 : ‖d (σ i)‖ ≤ f i := by
      have h := hle (σ i)
      rwa [hfσ i] at h
    have h4 : ‖d i‖ * ‖d (σ i)‖ ≤ f i * f i :=
      mul_le_mul (hle i) h3 (norm_nonneg _) (le_of_lt (hf i))
    linarith
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ f i * f i - (d i * d (σ i)).re :=
    fun i _ => by linarith [hle_term i]
  have hsum_re : (∑ i : Fin n, (d i * d (σ i)).re) = ∑ i : Fin n, f i * f i := by
    have h := congrArg Complex.re hsum
    simpa using h
  have hzero : (∑ i : Fin n, (f i * f i - (d i * d (σ i)).re)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_re]
    ring
  have hre : ∀ i, (d i * d (σ i)).re = f i * f i := by
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
    linarith
  intro i
  have hnorm : ‖d i‖ * ‖d (σ i)‖ = f i * f i := by
    have h1 : (d i * d (σ i)).re ≤ ‖d i * d (σ i)‖ := Complex.re_le_norm _
    have h2 : ‖d i * d (σ i)‖ = ‖d i‖ * ‖d (σ i)‖ := norm_mul _ _
    have h3 : ‖d (σ i)‖ ≤ f i := by
      have h := hle (σ i)
      rwa [hfσ i] at h
    have h4 : ‖d i‖ * ‖d (σ i)‖ ≤ f i * f i :=
      mul_le_mul (hle i) h3 (norm_nonneg _) (le_of_lt (hf i))
    have h5 : f i * f i ≤ ‖d i‖ * ‖d (σ i)‖ := by
      rw [← hre i, ← h2]
      exact h1
    linarith
  by_contra hne
  have hlt : ‖d i‖ < f i := lt_of_le_of_ne (hle i) hne
  have h4 : ‖d (σ i)‖ ≤ f i := by
    have h := hle (σ i)
    rwa [hfσ i] at h
  have hstrict : ‖d i‖ * ‖d (σ i)‖ < f i * f i := by
    calc ‖d i‖ * ‖d (σ i)‖ ≤ ‖d i‖ * f i :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ < f i * f i := by nlinarith [hlt, hf i]
  linarith

theorem norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S)
    (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S) :
    ∀ i, ‖dim P i‖ = hFP.fpdim i := by
  have hle : ∀ i, ‖dim P i‖ ≤ hFP.fpdim i := abs_dim_le_fpdim_of_dimMultC hFP hn hM P
  have hgd : hFP.globalDim = ∑ i : Fin n, hFP.fpdim i * hFP.fpdim i := by
    rw [FusionRing.FPData.globalDim]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : (∑ i : Fin n, dim P i * dim P (S.ring.dual i))
      = algebraMap ℝ ℂ (∑ i : Fin n, hFP.fpdim i * hFP.fpdim i) := by
    calc (∑ i : Fin n, dim P i * dim P (S.ring.dual i))
        = ∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i) :=
          Finset.sum_congr rfl (fun i _ => dim_mul_dim_dual_c hn P i)
      _ = algebraMap ℝ ℂ hFP.globalDim := hPU
      _ = algebraMap ℝ ℂ (∑ i : Fin n, hFP.fpdim i * hFP.fpdim i) := by rw [hgd]
  exact eq_norm_of_sum_mul_dual (fun i => hFP.pos i) (fun i => hFP.dual_eq i) hle hsum

/-! ## 2. The twist algebra -/

theorem sum_twistNorm_of_dimMult_general {k : Type u} [Field k] {S : FusionSystem n k}
    (hM : DimMultiplicative S) (a b : Fin n) :
    (∑ c : Fin n, (S.ring.N a b c : k) * twistNorm S a b c) = 1 := by
  have hκ : S.kappa a * S.kappa b ≠ 0 :=
    mul_ne_zero (S.kappa_ne_zero a) (S.kappa_ne_zero b)
  have hstep : (∑ c : Fin n, (S.ring.N a b c : k) * twistNorm S a b c)
      = (∑ c : Fin n, (S.ring.N a b c : k) * S.J a b c * S.kappa c)
        / (S.kappa a * S.kappa b) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold twistNorm
    rw [div_eq_mul_inv]
    ring
  rw [hstep, hM a b, div_self hκ]

theorem sum_fpdimRatio_general {k : Type u} [Field k] [Algebra ℝ k] {R : FusionRing n}
    (hFP : R.FPData) (hn : 0 < n) (a b : Fin n) :
    (∑ c : Fin n, (R.N a b c : k) * (algebraMap ℝ k (hFP.fpdim c) /
      (algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b)))) = 1 := by
  have ha : algebraMap ℝ k (hFP.fpdim a) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos a))
  have hb : algebraMap ℝ k (hFP.fpdim b) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos b))
  have hD : algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b) ≠ 0 :=
    mul_ne_zero ha hb
  have h1 : (∑ c : Fin n, (R.N a b c : k) * (algebraMap ℝ k (hFP.fpdim c) /
        (algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b))))
      = (∑ c : Fin n, (R.N a b c : k) * algebraMap ℝ k (hFP.fpdim c)) /
        (algebraMap ℝ k (hFP.fpdim a) * algebraMap ℝ k (hFP.fpdim b)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h1, fpdim_char_algebraMap hFP hn a b, div_self hD]

theorem norm_twistNorm_of_dimMult_pseudoUnitaryC {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S)
    (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    ‖twistNorm S a b c‖ = hFP.fpdim c / (hFP.fpdim a * hFP.fpdim b) := by
  have heq := norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC hFP hn hM hPU P
  have h := dim_eq_twistNorm P a b c hN
  have h2 : ‖dim P c‖ = ‖twistNorm S a b c‖ * ‖dim P a‖ * ‖dim P b‖ := by
    rw [h, norm_mul, norm_mul]
  rw [heq c, heq a, heq b] at h2
  exact (eq_div_iff (mul_ne_zero (ne_of_gt (hFP.pos a)) (ne_of_gt (hFP.pos b)))).mpr
    (by rw [h2]; ring)

theorem eq_one_of_re_eq_one_of_norm_eq_one {z : ℂ} (hre : z.re = 1) (hno : ‖z‖ = 1) :
    z = 1 := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hno]
    norm_num
  rw [Complex.normSq_apply] at hsq
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact Complex.ext (by simpa using hre) (by simpa using him)

theorem norm_algebraMap_complex (r : ℝ) : ‖algebraMap ℝ ℂ r‖ = |r| := by
  simp [Complex.norm_real]

/-- **The `ℂ` per-channel identity (K)** — the main deliverable. -/
theorem twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S)
    (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (a b c : Fin n) (hN : 0 < S.ring.N a b c) :
    twistNorm S a b c = algebraMap ℝ ℂ (hFP.fpdim c) /
      (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b)) := by
  have hfa : algebraMap ℝ ℂ (hFP.fpdim a) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos a))
  have hfb : algebraMap ℝ ℂ (hFP.fpdim b) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos b))
  have hDne : algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b) ≠ 0 :=
    mul_ne_zero hfa hfb
  set g : Fin n → ℂ :=
    fun c => algebraMap ℝ ℂ (hFP.fpdim c) /
      (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b)) with hg
  have hgne : ∀ c, g c ≠ 0 := by
    intro c
    rw [hg]
    exact div_ne_zero (algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos c))) hDne
  set s : Fin n → ℂ := fun c => twistNorm S a b c / g c with hs
  have hgs : ∀ c, g c * s c = twistNorm S a b c := by
    intro c
    rw [hs]
    exact mul_div_cancel₀ _ (hgne c)
  have hgnorm : ∀ c, ‖g c‖ = hFP.fpdim c / (hFP.fpdim a * hFP.fpdim b) := by
    intro c
    rw [hg]
    rw [norm_div, norm_mul, norm_algebraMap_complex, norm_algebraMap_complex,
      norm_algebraMap_complex, abs_of_pos (hFP.pos c), abs_of_pos (hFP.pos a),
      abs_of_pos (hFP.pos b)]
  have hsn : ∀ c, 0 < S.ring.N a b c → ‖s c‖ = 1 := by
    intro c hNc
    rw [hs, norm_div, hgnorm c,
      norm_twistNorm_of_dimMult_pseudoUnitaryC hFP hn hM hPU P a b c hNc]
    exact div_self (ne_of_gt (div_pos (hFP.pos c) (mul_pos (hFP.pos a) (hFP.pos b))))
  have hsum1 : (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * twistNorm S a b c') = 1 :=
    sum_twistNorm_of_dimMult_general hM a b
  have hsum2 : (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * g c') = 1 := by
    rw [← sum_fpdimRatio_general (k := ℂ) hFP hn a b]
  have hsum0 : (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * g c' * (s c' - 1)) = 0 := by
    have h : (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * g c' * (s c' - 1))
        = (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * twistNorm S a b c')
          - (∑ c' : Fin n, (S.ring.N a b c' : ℂ) * g c') := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c' _
      have h1 : (S.ring.N a b c' : ℂ) * g c' * (s c' - 1)
          = (S.ring.N a b c' : ℂ) * (g c' * s c') - (S.ring.N a b c' : ℂ) * g c' := by
        ring
      rw [h1, hgs c']
    rw [h, hsum1, hsum2]
    ring
  have hsumD : (∑ c' : Fin n,
      algebraMap ℝ ℂ ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * (s c' - 1)) = 0 := by
    have h := congrArg (fun z : ℂ =>
      z * (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b))) hsum0
    rw [Finset.sum_mul, zero_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro c' _
    have hND : (S.ring.N a b c' : ℂ) * g c' *
        (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b))
        = algebraMap ℝ ℂ ((S.ring.N a b c' : ℝ) * hFP.fpdim c') := by
      rw [hg]
      field_simp
      push_cast
      ring
    calc algebraMap ℝ ℂ ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * (s c' - 1)
        = ((S.ring.N a b c' : ℂ) * g c' *
            (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b))) *
            (s c' - 1) := by rw [← hND]
      _ = ((S.ring.N a b c' : ℂ) * g c' * (s c' - 1)) *
            (algebraMap ℝ ℂ (hFP.fpdim a) * algebraMap ℝ ℂ (hFP.fpdim b)) := by ring
  have hre : (∑ c' : Fin n,
      ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * ((s c').re - 1)) = 0 := by
    have h := congrArg Complex.re hsumD
    simpa [Complex.mul_re] using h
  have hterm : ∀ c' ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * (1 - (s c').re) := by
    intro c' _
    rcases Nat.eq_zero_or_pos (S.ring.N a b c') with h0 | hpos
    · rw [h0]
      simp
    · have hs1 := hsn c' hpos
      have h1 : (s c').re ≤ 1 := by
        have := Complex.re_le_norm (s c')
        rw [hs1] at this
        exact this
      have h2 : (0 : ℝ) ≤ 1 - (s c').re := by linarith
      have h3 : (0 : ℝ) ≤ (S.ring.N a b c' : ℝ) * hFP.fpdim c' :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hFP.pos c'))
      exact mul_nonneg h3 h2
  have hzero : (∑ c' : Fin n,
      ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * (1 - (s c').re)) = 0 := by
    have h : (∑ c' : Fin n, ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * (1 - (s c').re))
        = - (∑ c' : Fin n, ((S.ring.N a b c' : ℝ) * hFP.fpdim c') * ((s c').re - 1)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c' _
      ring
    rw [h, hre]
    ring
  have hre1 : (s c).re = 1 := by
    have hNpos : (0 : ℝ) < (S.ring.N a b c : ℝ) := by exact_mod_cast hN
    have hw : (0 : ℝ) < (S.ring.N a b c : ℝ) * hFP.fpdim c :=
      mul_pos hNpos (hFP.pos c)
    have h := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero c (Finset.mem_univ c)
    have h1 : 1 - (s c).re = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt hw)
    linarith
  have hs1 : s c = 1 := eq_one_of_re_eq_one_of_norm_eq_one hre1 (hsn c hN)
  rw [← hgs c, hs1, mul_one, hg]

/-! ## 3. ENO 8.23 exactly, at `ℂ`, from (M) and pseudo-unitarity

`Coboundary.eno823_of_twistNorm` needs the per-channel identity (K) — which is now
`twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c` — and `exists_spherical_of_twistNorm`
produces the pivotal structure from it.  Uniqueness is `pivotal_ext` at `ℂ`, which is
`DimMult`'s `ℝ` statement with the order swapped for a division by `κ ≠ 0`. -/

theorem pivotal_ext_c {S : FusionSystem n ℂ} (P P' : PivotalStructure S)
    (h : ∀ i, dim P i = dim P' i) : P = P' := by
  obtain ⟨p, pu, pm⟩ := P
  obtain ⟨p', pu', pm'⟩ := P'
  have hp : p = p' := by
    funext i
    apply Units.ext
    have hd := h i
    rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq] at hd
    exact mul_right_cancel₀ (S.kappa_ne_zero i) hd
  subst hp
  rfl

theorem eno823ExactC_of_dimMult {S : FusionSystem n ℂ} (hFP : S.ring.FPData) (hn : 0 < n)
    (hM : DimMultiplicative S) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S) :
    ∃! Q : PivotalStructure S, Q.IsSpherical ∧ (∀ i : Fin n, Pos (dim Q i)) ∧
      (∀ i : Fin n, dim Q i = algebraMap ℝ ℂ (hFP.fpdim i)) := by
  have hf : ∀ i, algebraMap ℝ ℂ (hFP.fpdim i) ≠ 0 :=
    fun i => algebraMap_ne_zero_of_ne_zero (ne_of_gt (hFP.pos i))
  have hK : ∀ a b c : Fin n, 0 < S.ring.N a b c →
      algebraMap ℝ ℂ (hFP.fpdim c)
        = twistNorm S a b c * algebraMap ℝ ℂ (hFP.fpdim a)
          * algebraMap ℝ ℂ (hFP.fpdim b) := by
    intro a b c hNc
    have ha := hf a
    have hb := hf b
    have hc := hf c
    rw [twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c hFP hn hM hPU P a b c hNc]
    field_simp
  have hd0 : algebraMap ℝ ℂ (hFP.fpdim ⟨0, hn⟩) = 1 := by
    rw [hFP.unit_one hn, map_one]
  have hdual : ∀ i : Fin n,
      algebraMap ℝ ℂ (hFP.fpdim (S.ring.dual i)) = algebraMap ℝ ℂ (hFP.fpdim i) :=
    fun i => by rw [hFP.dual_eq i]
  obtain ⟨Q, hsp, hdim⟩ := exists_spherical_of_twistNorm (S := S)
    (fun i => algebraMap ℝ ℂ (hFP.fpdim i)) hf hK hn hd0 (kappa_unit_c hn) hdual
  refine ⟨Q, ⟨hsp, fun i => ?_, hdim⟩, ?_⟩
  · rw [hdim i]
    exact pos_algebraMap (hFP.pos i)
  · intro Q' ⟨_, _, hdim'⟩
    exact pivotal_ext_c Q' Q (fun i => by rw [hdim' i, hdim i])

/-- **The frozen `Cx.IsPseudoUnitaryPivotal`-shaped conclusion, with both of its hypotheses
removed**: under (M) a `Pos`-valued pivotal dimension is automatically multiplicative, and
`‖dim P‖ = FPdim` then identifies it with the FP-dimension.  This recovers
`Prop821CEq.dim_eq_algebraMap_of_pseudoUnitaryC` without its `mult` field. -/
theorem dim_eq_algebraMap_of_dimMult_pseudoUnitaryC {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S)
    (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hpos : ∀ i : Fin n, Pos (dim P i)) :
    ∀ i : Fin n, dim P i = algebraMap ℝ ℂ (hFP.fpdim i) :=
  fun i => eq_algebraMap_of_pos_of_norm (hpos i)
    (norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC hFP hn hM hPU P i)

/-- **Sphericity of a `Pos` pivotal structure, from (M) + pseudo-unitarity** — the
sphericity conjunct of `DimMult.eno823Exact_of_dimMult_pseudoUnitary`, at `ℂ`, without
`Cx.IsPseudoUnitaryPivotal`. -/
theorem isSpherical_of_dimMult_pseudoUnitaryC {S : FusionSystem n ℂ}
    (hFP : S.ring.FPData) (hn : 0 < n) (hM : DimMultiplicative S)
    (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (hpos : ∀ i : Fin n, Pos (dim P i)) : P.IsSpherical := by
  intro i
  rw [dim_eq_algebraMap_of_dimMult_pseudoUnitaryC hFP hn hM hPU P hpos (S.ring.dual i),
    dim_eq_algebraMap_of_dimMult_pseudoUnitaryC hFP hn hM hPU P hpos i, hFP.dual_eq i]

/-- **The bare form at `ℂ`**: (M) + pseudo-unitarity give `ENO823`, through
`Coboundary.eno823_of_twistNorm` — the check that the per-channel identity (K) proved above
is literally that theorem's hypothesis. -/
theorem eno823C_of_dimMult_pseudoUnitary {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hM : DimMultiplicative S) (hPU : IsPseudoUnitaryC S hFP)
    (P : PivotalStructure S) : ENO823 S hFP :=
  eno823_of_twistNorm S hFP hn (kappa_unit_c hn)
    (fun r hr => by simpa using hr)
    (fun a b c hNc => twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c hFP hn hM hPU P a b c hNc)

/-! ## 4. The bridge from the frozen `Cx` family's antecedent

The frozen `ENO823ExactC` assumes `J_match S (derivedJ S)`: the carried twist agrees with a
derived table on supported channels.  The lemmas here turn that antecedent into (M) — either
at a `dJ` that satisfies the twisted character identity itself, or at the settled twist
`Prop821CNorm.settledJ`, whose identity with (K) is `Prop821CNorm.j_match_settledJ_iff`. -/

/-- **(M) from a twist sum identity at any matching table.**  If `dJ` agrees with `S.J` on
supported channels and satisfies the twisted character identity, then (M) holds of `S` — the
unsupported channels contribute `0` on both sides.  This is the interface WP2's `derivedJ`
needs: `J_match S derivedJ` plus one sum identity. -/
theorem dimMult_of_twistSum {k : Type u} [Field k] {S : FusionSystem n k}
    (dJ : Fin n → Fin n → Fin n → k) (hJ : J_match S dJ)
    (hM : ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : k) * dJ a b c * S.kappa c) = S.kappa a * S.kappa b) :
    DimMultiplicative S := by
  intro a b
  rw [← hM a b]
  apply Finset.sum_congr rfl
  intro c _
  rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h0 | hpos
  · rw [h0]
    simp
  · rw [hJ a b c hpos]

/-- **`J_match` at the settled twist gives (M)**, at any field with an `ℝ`-algebra
structure: `Prop821CNorm.settledJ S hFP` *is* the per-channel law (K), and (K) ⇒ (M) is
`Prop821CNorm.twist_sum_of_perChannel_general`. -/
theorem dimMult_of_J_match_settledJ {k : Type u} [Field k] [Algebra ℝ k]
    {S : FusionSystem n k} (hFP : S.ring.FPData) (hn : 0 < n)
    (h : J_match S (settledJ S hFP)) : DimMultiplicative S :=
  twist_sum_of_perChannel_general (k' := k) hFP hn (fun a b c hNc => h a b c hNc)

/-- **The exact conclusion at `ℂ` from the frozen `Cx` family's `J_match` antecedent**: if
the carried twist is the settled one — `J_match S (settledJ S hFP)` — then pseudo-unitarity
alone gives the unique spherical pivotal structure with `Pos` dimensions equal to the
FP-dimensions. -/
theorem eno823ExactC_of_J_match_settledJ {S : FusionSystem n ℂ} (hFP : S.ring.FPData)
    (hn : 0 < n) (hPU : IsPseudoUnitaryC S hFP) (P : PivotalStructure S)
    (h : J_match S (settledJ S hFP)) :
    ∃! Q : PivotalStructure S, Q.IsSpherical ∧ (∀ i : Fin n, Pos (dim Q i)) ∧
      (∀ i : Fin n, dim Q i = algebraMap ℝ ℂ (hFP.fpdim i)) :=
  eno823ExactC_of_dimMult hFP hn (dimMult_of_J_match_settledJ hFP hn h) hPU P

/-- **The frozen `Cx` exact target, from a twist sum identity on the derived table.**
`ENO823ExactC derivedJ S hFP` is `IsPseudoUnitaryC → J_match S (derivedJ S) → ∃! P, ...`; the
`J_match` conjunct plus the twisted character identity on `derivedJ` give (M)
(`dimMult_of_twistSum`), and (M) + pseudo-unitarity is `eno823ExactC_of_dimMult`.  So the
content of the frozen family at a derived twist `derivedJ` is that one sum identity on
`derivedJ` — the same shape `Prop821CNorm.j_match_settledJ_iff` identifies with (K). -/
theorem eno823ExactC_of_derivedJ
    (derivedJ : ∀ {n : ℕ}, FusionSystem n ℂ → Fin n → Fin n → Fin n → ℂ)
    {n : ℕ} (S : FusionSystem n ℂ) (hFP : S.ring.FPData) (hn : 0 < n)
    (P : PivotalStructure S)
    (hM : ∀ a b : Fin n,
      (∑ c : Fin n, (S.ring.N a b c : ℂ) * derivedJ S a b c * S.kappa c)
        = S.kappa a * S.kappa b) :
    ENO823ExactC derivedJ S hFP := by
  intro hPU hJ
  exact eno823ExactC_of_dimMult hFP hn (dimMult_of_twistSum (derivedJ S) hJ hM) hPU P

end FusionCategory
#print axioms FusionCategory.norm_le_fpdim_of_char
#print axioms FusionCategory.abs_le_fpdim_of_mult_c
#print axioms FusionCategory.abs_dim_le_fpdim_of_dimMultC
#print axioms FusionCategory.eq_norm_of_sum_mul_dual
#print axioms FusionCategory.norm_dim_eq_fpdim_of_dimMult_pseudoUnitaryC
#print axioms FusionCategory.sum_twistNorm_of_dimMult_general
#print axioms FusionCategory.sum_fpdimRatio_general
#print axioms FusionCategory.norm_twistNorm_of_dimMult_pseudoUnitaryC
#print axioms FusionCategory.eq_one_of_re_eq_one_of_norm_eq_one
#print axioms FusionCategory.norm_algebraMap_complex
#print axioms FusionCategory.twistNorm_eq_fpdim_ratio_of_dimMult_pseudoUnitary_c
#print axioms FusionCategory.pivotal_ext_c
#print axioms FusionCategory.eno823ExactC_of_dimMult
#print axioms FusionCategory.eno823C_of_dimMult_pseudoUnitary
#print axioms FusionCategory.dimMult_of_twistSum
#print axioms FusionCategory.dimMult_of_J_match_settledJ
#print axioms FusionCategory.dim_eq_algebraMap_of_dimMult_pseudoUnitaryC
#print axioms FusionCategory.isSpherical_of_dimMult_pseudoUnitaryC
#print axioms FusionCategory.eno823ExactC_of_J_match_settledJ
#print axioms FusionCategory.eno823ExactC_of_derivedJ
