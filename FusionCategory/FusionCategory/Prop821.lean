import FusionCategory.PFDim
import FusionCategory.Pivotal
import FusionCategory.PseudoUnitary

/-!
# ENO Proposition 8.21: `|V|² ≤ FPdim(V)²`

This is the analytic input of Prop 8.23.  ENO show that the dimension `d_i` of a
simple object is an eigenvalue of a matrix `T_i` whose entries are dominated by
the fusion coefficients, and then bound the operator norm of `T_i` in the
weighted norm `‖x‖ = Σ_j f_j |x_j|` by `f_i`; hence `|d_i| ≤ f_i`.

Two index conventions of the fusion coefficients meet here, and the repo's
axioms only give the `(0,·,·)` and duality relations, so the passage between
them is proved first:

* `cyclic` — `N i j k* = N j k i*`, from associativity at `l = 1` and
  `dual_coeff` (this is `N^k_{ij} = N^i_{j k*}` for the fusion ring);
* `fpdim_char` — the FP-dimension is a character, `Σ_c N a b c f_c = f_a f_b`;
* `abs_le_fpdim_of_eigenvector` — the spectral bound: any `d` with
  `Σ_j N i j k d_j = d_i d_k` satisfies `|d_i| ≤ f_i`.  Nothing about pivotal
  structures enters, which is the point — the representation-theoretic input
  (that a dimension function satisfies that equation) is a separate matter;
* `abs_le_fpdim_of_char` — the same for a dimension function in character form;
* `eq_abs_of_sum_sq` — the equality case ENO draw from it: `Σ_i |d_i|² = Σ_i f_i²`
  together with `|d_i| ≤ f_i` forces `|d_i| = f_i` termwise.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset BigOperators

namespace FusionCategory

open FusionRing

variable {n : ℕ}

/-- **Cyclic symmetry of the fusion coefficients**, `N^k_{ij} = N^i_{j k*}`:
in the repo's slots, `N i j (k*) = N j k (i*)`.  Associativity at `l = 1`
together with `dual_coeff`. -/
theorem cyclic {R : FusionRing n} (hn : 0 < n) (i j k : Fin n) :
    R.N i j (R.dual k) = R.N j k (R.dual i) := by
  have h := R.associativity i j k ⟨0, hn⟩
  have hl : (∑ p : Fin n, R.N i j p * R.N p k ⟨0, hn⟩) = R.N i j (R.dual k) := by
    rw [Finset.sum_eq_single (R.dual k)]
    · rw [R.dual_coeff hn (R.dual k) k]
      simp [R.dual_involutive k]
    · intro b _ hb
      rw [R.dual_coeff hn b k]
      have hne : k ≠ R.dual b := fun hk => hb (by rw [hk, R.dual_involutive])
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hr : (∑ q : Fin n, R.N j k q * R.N i q ⟨0, hn⟩) = R.N j k (R.dual i) := by
    rw [Finset.sum_eq_single (R.dual i)]
    · rw [R.dual_coeff hn i (R.dual i)]
      simp
    · intro b _ hb
      rw [R.dual_coeff hn i b]
      have hne : b ≠ R.dual i := hb
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hl, hr] at h
  exact h

/-- `N a b c = N b c* a*`: `cyclic` with `k` replaced by `c*`. -/
theorem cyclic1 {R : FusionRing n} (hn : 0 < n) (a b c : Fin n) :
    R.N a b c = R.N b (R.dual c) (R.dual a) := by
  have h := cyclic (R := R) hn a b (R.dual c)
  simpa only [R.dual_involutive] using h

/-- `N a b c = N c* a b*`: `cyclic1` applied twice. -/
theorem cyclic2 {R : FusionRing n} (hn : 0 < n) (a b c : Fin n) :
    R.N a b c = R.N (R.dual c) a (R.dual b) := by
  rw [cyclic1 hn a b c]
  have h := cyclic1 (R := R) hn b (R.dual c) (R.dual a)
  simpa only [R.dual_involutive] using h

/-- Reindexing a sum along the duality. -/
theorem sum_dual_reindex {M : Type} [AddCommMonoid M] {R : FusionRing n} (g : Fin n → M) :
    (∑ c : Fin n, g (R.dual c)) = ∑ m : Fin n, g m :=
  Equiv.sum_comp ⟨R.dual, R.dual, fun x => R.dual_involutive x,
    fun x => R.dual_involutive x⟩ g

/-- The FP-dimension is a character of the fusion ring: `Σ_c N a b c f_c = f_a f_b`.

`FPData.eigenvector` sums the *middle* slot; `cyclic1` moves the sum to the
third slot. -/
theorem fpdim_char {R : FusionRing n} (h : R.FPData) (hn : 0 < n) (a b : Fin n) :
    (∑ c : Fin n, (R.N a b c : ℝ) * h.fpdim c) = h.fpdim a * h.fpdim b := by
  calc (∑ c : Fin n, (R.N a b c : ℝ) * h.fpdim c)
      = ∑ c : Fin n, (R.N b (R.dual c) (R.dual a) : ℝ) * h.fpdim c := by
        apply Finset.sum_congr rfl
        intro c _
        rw [cyclic1 hn a b c]
    _ = ∑ c : Fin n, (R.N b (R.dual c) (R.dual a) : ℝ) * h.fpdim (R.dual c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [h.dual_eq c]
    _ = ∑ m : Fin n, (R.N b m (R.dual a) : ℝ) * h.fpdim m :=
        sum_dual_reindex (fun m => (R.N b m (R.dual a) : ℝ) * h.fpdim m)
    _ = h.fpdim b * h.fpdim (R.dual a) := h.eigenvector b (R.dual a)
    _ = h.fpdim a * h.fpdim b := by rw [h.dual_eq a, mul_comm]

/-- **ENO Proposition 8.21**, spectral form: any `d` satisfying the eigenvector
equation `Σ_j N i j k · d_j = d_i · d_k` is bounded by the FP-dimensions. -/
theorem abs_le_fpdim_of_eigenvector {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → ℝ)
    (heig : ∀ i kk : Fin n, (∑ j : Fin n, (R.N i j kk : ℝ) * d j) = d i * d kk) :
    ∀ i, |d i| ≤ h.fpdim i := by
  intro i
  set S : ℝ := ∑ k : Fin n, h.fpdim k * |d k| with hSdef
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (abs_nonneg _))
  have hbound : |d i| * S ≤ h.fpdim i * S := by
    calc |d i| * S
        = ∑ k : Fin n, h.fpdim k * |d i * d k| := by
          rw [hSdef, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul]
          ring
      _ = ∑ k : Fin n, h.fpdim k * |∑ j : Fin n, (R.N i j k : ℝ) * d j| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [heig i k]
      _ ≤ ∑ k : Fin n, h.fpdim k * (∑ j : Fin n, (R.N i j k : ℝ) * |d j|) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (h.pos k))
          calc |∑ j : Fin n, (R.N i j k : ℝ) * d j|
              ≤ ∑ j : Fin n, |(R.N i j k : ℝ) * d j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j : Fin n, (R.N i j k : ℝ) * |d j| := by
                apply Finset.sum_congr rfl
                intro j _
                rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ = ∑ k : Fin n, ∑ j : Fin n, h.fpdim k * ((R.N i j k : ℝ) * |d j|) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin n, h.fpdim k * ((R.N i j k : ℝ) * |d j|) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, (∑ k : Fin n, h.fpdim k * (R.N i j k : ℝ)) * |d j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ j : Fin n, (h.fpdim i * h.fpdim j) * |d j| := by
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
  · have hS0 : (∑ k : Fin n, h.fpdim k * |d k|) = 0 := by rw [← hSdef]; exact hzero.symm
    have hterm : h.fpdim i * |d i| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun k => h.fpdim k * |d k|)
        (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (abs_nonneg _))).mp hS0 i (Finset.mem_univ i)
    have hdi : |d i| = 0 := by
      rcases mul_eq_zero.mp hterm with h' | h'
      · exact absurd h' (ne_of_gt (h.pos i))
      · exact h'
    rw [hdi]
    exact le_of_lt (h.pos i)

/-- **ENO Proposition 8.21** for a dimension function given in character form. -/
theorem abs_le_fpdim_of_char {R : FusionRing n} (h : R.FPData) (hn : 0 < n) (d : Fin n → ℝ)
    (hdual : ∀ i, d (R.dual i) = d i)
    (hchar : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℝ) * d c) = d a * d b) :
    ∀ i, |d i| ≤ h.fpdim i := by
  refine abs_le_fpdim_of_eigenvector h hn d ?_
  intro i kk
  calc (∑ j : Fin n, (R.N i j kk : ℝ) * d j)
      = ∑ j : Fin n, (R.N (R.dual kk) i (R.dual j) : ℝ) * d j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cyclic2 hn i j kk]
    _ = ∑ j : Fin n, (R.N (R.dual kk) i (R.dual j) : ℝ) * d (R.dual j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hdual j]
    _ = ∑ m : Fin n, (R.N (R.dual kk) i m : ℝ) * d m :=
        sum_dual_reindex (fun m => (R.N (R.dual kk) i m : ℝ) * d m)
    _ = d (R.dual kk) * d i := hchar (R.dual kk) i
    _ = d i * d kk := by rw [hdual kk, mul_comm]

/-- The equality case ENO draw from Proposition 8.21. -/
theorem eq_abs_of_sum_sq {d f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hle : ∀ i, |d i| ≤ f i)
    (hsum : (∑ i : Fin n, (d i) ^ 2) = ∑ i : Fin n, (f i) ^ 2) :
    ∀ i, |d i| = f i := by
  have hterm : ∀ i : Fin n, (f i) ^ 2 - (d i) ^ 2 = 0 := by
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (f i) ^ 2 - (d i) ^ 2 := by
      intro i _
      have h1 : |d i| ^ 2 ≤ (f i) ^ 2 := by
        nlinarith [hle i, abs_nonneg (d i), hf i]
      have h2 : |d i| ^ 2 = (d i) ^ 2 := sq_abs (d i)
      linarith [h1, h2]
    have hzero : (∑ i : Fin n, ((f i) ^ 2 - (d i) ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib, ← hsum]
      ring
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i (Finset.mem_univ i)
  intro i
  have hsq : (d i) ^ 2 = (f i) ^ 2 := by linarith [hterm i]
  have h1 : |d i| ≤ f i := hle i
  have h2 : 0 ≤ f i := hf i
  have h3 : 0 ≤ |d i| := abs_nonneg _
  have h4 : |d i| ^ 2 = (f i) ^ 2 := by rw [sq_abs]; exact hsq
  nlinarith [h4, h1, h2, h3, sq_nonneg (|d i| - f i)]

/-- The FP-dimension is a character in the *third* slot as well,
`Σ_k N i k j · f_k = f_i f_j` — the form in which ENO's `T`-matrix uses it. -/
theorem fpdim_char_mid {R : FusionRing n} (h : R.FPData) (hn : 0 < n) (i j : Fin n) :
    (∑ k : Fin n, h.fpdim k * (R.N i k j : ℝ)) = h.fpdim i * h.fpdim j := by
  calc (∑ k : Fin n, h.fpdim k * (R.N i k j : ℝ))
      = ∑ k : Fin n, h.fpdim k * (R.N (R.dual j) i (R.dual k) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [cyclic2 hn i k j]
    _ = ∑ k : Fin n, h.fpdim (R.dual k) * (R.N (R.dual j) i (R.dual k) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h.dual_eq k, mul_comm]
    _ = ∑ m : Fin n, h.fpdim m * (R.N (R.dual j) i m : ℝ) :=
        sum_dual_reindex (fun m => h.fpdim m * (R.N (R.dual j) i m : ℝ))
    _ = h.fpdim (R.dual j) * h.fpdim i := by
        rw [← fpdim_char h hn (R.dual j) i]
        apply Finset.sum_congr rfl
        intro m _
        ring
    _ = h.fpdim i * h.fpdim j := by rw [h.dual_eq j, mul_comm]

/-- **ENO Proposition 8.21**, in the form ENO's `T`-matrix delivers: a dimension
function that is multiplicative on the fusion ring — `Σ_c N a b c d_c = d_a d_b`,
the character form — is bounded by the FP-dimensions. -/
theorem abs_le_fpdim_of_mult {R : FusionRing n} (h : R.FPData) (hn : 0 < n)
    (d : Fin n → ℝ)
    (hm : ∀ a b : Fin n, (∑ c : Fin n, (R.N a b c : ℝ) * d c) = d a * d b) :
    ∀ i, |d i| ≤ h.fpdim i := by
  intro i
  set S : ℝ := ∑ k : Fin n, h.fpdim k * |d k| with hSdef
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (abs_nonneg _))
  have hbound : |d i| * S ≤ h.fpdim i * S := by
    calc |d i| * S
        = ∑ k : Fin n, h.fpdim k * |d i * d k| := by
          rw [hSdef, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul]
          ring
      _ = ∑ k : Fin n, h.fpdim k * |∑ j : Fin n, (R.N i k j : ℝ) * d j| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hm i k]
      _ ≤ ∑ k : Fin n, h.fpdim k * (∑ j : Fin n, (R.N i k j : ℝ) * |d j|) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (h.pos k))
          calc |∑ j : Fin n, (R.N i k j : ℝ) * d j|
              ≤ ∑ j : Fin n, |(R.N i k j : ℝ) * d j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j : Fin n, (R.N i k j : ℝ) * |d j| := by
                apply Finset.sum_congr rfl
                intro j _
                rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ = ∑ k : Fin n, ∑ j : Fin n, h.fpdim k * ((R.N i k j : ℝ) * |d j|) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin n, h.fpdim k * ((R.N i k j : ℝ) * |d j|) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, (∑ k : Fin n, h.fpdim k * (R.N i k j : ℝ)) * |d j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ j : Fin n, (h.fpdim i * h.fpdim j) * |d j| := by
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
  · have hS0 : (∑ k : Fin n, h.fpdim k * |d k|) = 0 := by rw [← hSdef]; exact hzero.symm
    have hterm : h.fpdim i * |d i| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun k => h.fpdim k * |d k|)
        (fun k _ => mul_nonneg (le_of_lt (h.pos k)) (abs_nonneg _))).mp hS0 i (Finset.mem_univ i)
    have hdi : |d i| = 0 := by
      rcases mul_eq_zero.mp hterm with h' | h'
      · exact absurd h' (ne_of_gt (h.pos i))
      · exact h'
    rw [hdi]
    exact le_of_lt (h.pos i)

/-! ## The `T`-matrix itself (ENO §3.1, pivotal case)

ENO's `T`-matrix is `(T_i)_{kj} = T^{ik}_j = tr(b^{ik}_j)` with `(b^{ik}_j)² = 1`,
and Remark 3.1 records that **in the pivotal case `b^{ik}_j = 1`**, so `T_i` is
the fusion matrix.  Its entries are therefore integers with
`|(T_i)_{kj}| ≤ N^{ik}_j` an equality, and `T_i d = d_i · d` is exactly
multiplicativity of the dimension. -/

/-- ENO's `T`-matrix for a pivotal fusion system: `(T_i)_{kj} = N^{ik}_j`. -/
noncomputable def tMatrix (S : FusionSystem n ℝ) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => (S.ring.N i k j : ℝ)

/-- ENO's domination `|(T_i)_{kj}| ≤ N^{ik}_j` is an equality in the pivotal case,
because the entries *are* the fusion coefficients. -/
theorem abs_tMatrix (S : FusionSystem n ℝ) (i k j : Fin n) :
    |tMatrix S i k j| = (S.ring.N i k j : ℝ) := by
  rw [tMatrix, abs_of_nonneg (Nat.cast_nonneg _)]

/-- `T_i d = d_i · d` for ENO's `T`-matrix is multiplicativity of the dimension,
`d_a d_b = Σ_c N a b c d_c` — the `mult` field of `IsPseudoUnitaryPivotal`. -/
theorem tMatrix_mulVec (S : FusionSystem n ℝ) (d : Fin n → ℝ) (i : Fin n) :
    (tMatrix S i).mulVec d = (d i) • d ↔
      ∀ k : Fin n, (∑ m : Fin n, (S.ring.N i k m : ℝ) * d m) = d i * d k := by
  constructor
  · intro h k
    have := congrFun h k
    simpa [tMatrix, Matrix.mulVec, dotProduct, smul_eq_mul] using this
  · intro h
    funext k
    simpa [tMatrix, Matrix.mulVec, dotProduct, smul_eq_mul] using h k

/-- The input ENO get from the `T`-matrix, stated for a skeletal dimension
function: multiplicative on the fusion ring.  `tMatrix_mulVec` identifies it with
`T_i d = d_i · d`. -/
def DimEigen {n : ℕ} [Field k] (S : FusionSystem n k) (d : Fin n → k) : Prop :=
  ∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : k) * d c) = d a * d b

/-- **ENO Proposition 8.21** for a skeletal fusion system: a dimension function
satisfying ENO's `T`-matrix eigenvector equation is bounded by the
FP-dimensions, `|d_i| ≤ FPdim_i`. -/
theorem abs_dim_le_fpdim {n : ℕ} {S : FusionSystem n ℝ} (hFP : S.ring.FPData)
    (hn : 0 < n) (P : PivotalStructure S) (heig : DimEigen S (dim P)) :
    ∀ i, |dim P i| ≤ hFP.fpdim i :=
  abs_le_fpdim_of_mult hFP hn (dim P) heig

/-- **ENO Proposition 8.21 for pseudo-unitary data**: for a pivotal structure
whose dimension function is positive and multiplicative —
`IsPseudoUnitaryPivotal`, the hypothesis of `eno823_of_pseudoUnitary` — the bound
holds with no further input.  This discharges `DimEigen` from `mult`. -/
theorem abs_dim_le_fpdim_of_pseudoUnitary {n : ℕ} {S : FusionSystem n ℝ}
    (hFP : S.ring.FPData) (hn : 0 < n) (P : PivotalStructure S)
    (hU : IsPseudoUnitaryPivotal P) : ∀ i, |dim P i| ≤ hFP.fpdim i :=
  abs_le_fpdim_of_eigenvector hFP hn (dim P) hU.mult

/-- ENO's consequence: if in addition the squared norms agree in total, they agree
termwise — `|V|² = FPdim(V)²` for every simple. -/
theorem eq_abs_of_pseudoUnitary {n : ℕ} {S : FusionSystem n ℝ}
    (hFP : S.ring.FPData) (hn : 0 < n) (P : PivotalStructure S)
    (hU : IsPseudoUnitaryPivotal P)
    (hsum : (∑ i : Fin n, (dim P i) ^ 2) = ∑ i : Fin n, (hFP.fpdim i) ^ 2) :
    ∀ i, |dim P i| = hFP.fpdim i :=
  eq_abs_of_sum_sq (fun i => le_of_lt (hFP.pos i))
    (abs_dim_le_fpdim_of_pseudoUnitary hFP hn P hU) hsum

/-!
## What "settling `J`" is, exactly: multiplicativity is the sum identity (M) on the twist

`FusionSystem` carries `J` as data under four laws, and those laws do not pin it
(`Vec^ω_{(Z/2)²}` with `J ≡ 1` satisfies them and has non-multiplicative
dimension).  The extra condition is *multiplicativity of the dimension*, and the
two lemmas below show it is literally the sum identity

    (M)   Σ_c N a b c · J a b c · κ_c = κ_a · κ_b

on the twist.  So "settling `J`" = "proving (M)", and (K), the per-channel form,
implies (M) immediately.  Defining `J` to be the coboundary `δ(κ)` would make (M)
true by construction, and is therefore not a settlement: it would make
`eno823_of_pseudoUnitary` apply to every data set, which `YangLee.not_eno823`
refutes.
-/

section SettleJ

variable {n : ℕ} {S : FusionSystem n ℝ}

/-- The multiplicativity sum, expanded through `p_mon`: each channel contributes
`J a b c · p a · p b · κ_c`. -/
theorem sum_dim_eq (P : PivotalStructure S) (a b : Fin n) :
    (∑ c : Fin n, (S.ring.N a b c : ℝ) * dim P c)
      = P.pVal a * P.pVal b *
        (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h0 | hpos
  · rw [h0]; simp
  · rw [PivotalStructure.dim_eq]
    rw [show P.pVal c = S.J a b c * P.pVal a * P.pVal b from P.p_mon a b c hpos]
    ring

/-- The right-hand side of multiplicativity, in the same normalisation. -/
theorem dim_mul_dim (P : PivotalStructure S) (a b : Fin n) :
    dim P a * dim P b = P.pVal a * P.pVal b * (S.kappa a * S.kappa b) := by
  rw [PivotalStructure.dim_eq, PivotalStructure.dim_eq]; ring

/-- **Settling `J` is proving (M).**  For a pivotal structure, multiplicativity of
the dimension is equivalent to the sum identity
`Σ_c N a b c · J a b c · κ_c = κ_a κ_b` on the double-dual twist. -/
theorem mult_iff_twist (P : PivotalStructure S) :
    (∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : ℝ) * dim P c)
        = dim P a * dim P b) ↔
      (∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c)
        = S.kappa a * S.kappa b) := by
  have hne : ∀ a b : Fin n, P.pVal a * P.pVal b ≠ 0 :=
    fun a b => mul_ne_zero (P.pVal_ne_zero a) (P.pVal_ne_zero b)
  constructor
  · intro h a b
    have h' := h a b
    rw [sum_dim_eq P a b, dim_mul_dim P a b] at h'
    exact mul_left_cancel₀ (hne a b) h'
  · intro h a b
    rw [sum_dim_eq P a b, dim_mul_dim P a b, h a b]

/-- The per-channel form (K) implies the sum form (M), hence multiplicativity:
sum (K) against the FP-dimensions and use that these are a character. -/
theorem twist_sum_of_perChannel (hFP : S.ring.FPData) (hn : 0 < n)
    (hK : ∀ a b : Fin n, ∀ c : Fin n, 0 < S.ring.N a b c →
      S.J a b c = hFP.fpdim c * S.kappa a * S.kappa b /
        (S.kappa c * hFP.fpdim a * hFP.fpdim b)) :
    ∀ a b : Fin n, (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c)
      = S.kappa a * S.kappa b := by
  intro a b
  have hfa : hFP.fpdim a ≠ 0 := ne_of_gt (hFP.pos a)
  have hfb : hFP.fpdim b ≠ 0 := ne_of_gt (hFP.pos b)
  calc (∑ c : Fin n, (S.ring.N a b c : ℝ) * S.J a b c * S.kappa c)
      = ∑ c : Fin n, (S.ring.N a b c : ℝ) *
          (hFP.fpdim c * S.kappa a * S.kappa b / (hFP.fpdim a * hFP.fpdim b)) := by
        apply Finset.sum_congr rfl
        intro c _
        rcases Nat.eq_zero_or_pos (S.ring.N a b c) with h0 | hpos
        · rw [h0]; simp
        · rw [hK a b c hpos]
          have hk := S.kappa_ne_zero c
          field_simp
    _ = (S.kappa a * S.kappa b / (hFP.fpdim a * hFP.fpdim b)) *
          (∑ c : Fin n, (S.ring.N a b c : ℝ) * hFP.fpdim c) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ = (S.kappa a * S.kappa b / (hFP.fpdim a * hFP.fpdim b)) *
          (hFP.fpdim a * hFP.fpdim b) := by
        rw [fpdim_char hFP hn a b]
    _ = S.kappa a * S.kappa b := by
        field_simp

end SettleJ

end FusionCategory
