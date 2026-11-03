import FusionCategory.PseudoUnitary
import Mathlib.Tactic

/-!
# `PFUnique` unconditionally: Perron--Frobenius uniqueness of the positive character

`FusionCategory.PFUnique R h` (`PFDim.lean:25`) is the analytic input that every statement of
ENO 8.23 in this repository carries as a hypothesis, and `PFDim.lean` records it as proved only
for the example rings (`n = 2, 3`), with the general case deferred to the Perron--Frobenius
development.

This file proves it for **every** fusion ring carrying `FPData`:

* `fusionRowSum R i j = sum_k N i j k` is the number of constituents of `i (x) j`;
* `fusionRowSum_pos` -- strictly positive for every pair.  The identity behind it is
  associativity for `i (x) (j (x) j*)` against `(i (x) j) (x) j*` at the channel `i`:
  `sum_p N i j p * N p j* i = sum_q N j j* q * N i q i >= N j j* 1 * N i 1 i = 1*1`,
  using only `dual_coeff`, `right_unit` and associativity;
* every positive normalised eigenvector `v` of all the fusion matrices `N^(k)` is a positive
  eigenvector of the strictly positive matrix `M = sum_k N^(k)`;
* `eq_smul_of_pos_eigenvector` -- the elementary Collatz--Wielandt argument: for a strictly
  positive matrix two positive eigenvectors are proportional and have the same eigenvalue
  (minimum of the ratio `x_i / y_i`, then the maximum principle).  No irreducibility
  hypothesis and no Mathlib Perron--Frobenius is needed;
* normalising both at the unit (`v 1 = 1 = FPdim 1`) gives `v = FPdim`.

No `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.unusedVariables false
set_option autoImplicit false

universe u

namespace FusionCategory

open FusionRing

variable {n : Nat}

/-! ## The elementary Perron--Frobenius uniqueness for a strictly positive matrix -/

/-- **Collatz--Wielandt comparison of eigenvalues.**  For a matrix with strictly positive
entries, a positive eigenvector with eigenvalue `mu` forces `mu <= lam` for every other positive
eigenvalue `lam`. -/
theorem eigen_le_of_pos_eigenvector {m : Nat} {M : Fin m -> Fin m -> Real}
    (hM : forall i j, 0 < M i j) {x y : Fin m -> Real} (hx : forall i, 0 < x i)
    (hy : forall i, 0 < y i)
    {lam mu : Real} (hxe : forall i, (Finset.univ.sum fun j => M i j * x j) = lam * x i)
    (hye : forall i, (Finset.univ.sum fun j => M i j * y j) = mu * y i) (hm : 0 < m) :
    mu <= lam := by
  classical
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin m)) (fun j => x j / y j)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  set t : Real := x j0 / y j0 with ht
  have htpos : 0 < t := by
    rw [ht]; exact div_pos (hx j0) (hy j0)
  have hstep : forall i, t * (Finset.univ.sum fun j => M i j * y j)
      <= Finset.univ.sum fun j => M i j * x j := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hle : t <= x j / y j := hj0 j (Finset.mem_univ j)
    have h1 : t * y j <= x j := by
      have h3 := mul_le_mul_of_nonneg_right hle (le_of_lt (hy j))
      rwa [div_mul_cancel₀ (x j) (ne_of_gt (hy j))] at h3
    calc t * (M i j * y j) = M i j * (t * y j) := by ring
      _ <= M i j * x j := mul_le_mul_of_nonneg_left h1 (le_of_lt (hM i j))
  have hmain : t * (mu * y j0) <= lam * x j0 := by
    have h := hstep j0
    rwa [hye j0, hxe j0] at h
  have hxj0 : x j0 = t * y j0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt (hy j0))]
  rw [hxj0] at hmain
  have hpos : 0 < t * y j0 := mul_pos htpos (hy j0)
  have h2 : mu * (t * y j0) <= lam * (t * y j0) := by
    calc mu * (t * y j0) = t * (mu * y j0) := by ring
      _ <= lam * (t * y j0) := hmain
  exact le_of_mul_le_mul_right h2 hpos

/-- **Uniqueness of the positive eigenvector** of a matrix with strictly positive entries:
two positive eigenvectors are proportional, with the proportionality factor fixed at any index.
-/
theorem eq_smul_of_pos_eigenvector {m : Nat} (hm : 0 < m) {M : Fin m -> Fin m -> Real}
    (hM : forall i j, 0 < M i j) {x y : Fin m -> Real} (hx : forall i, 0 < x i)
    (hy : forall i, 0 < y i)
    {lam mu : Real} (hxe : forall i, (Finset.univ.sum fun j => M i j * x j) = lam * x i)
    (hye : forall i, (Finset.univ.sum fun j => M i j * y j) = mu * y i) :
    forall i, x i = (x ⟨0, hm⟩ / y ⟨0, hm⟩) * y i := by
  classical
  have hmu_le : mu <= lam := eigen_le_of_pos_eigenvector hM hx hy hxe hye hm
  have hlam_le : lam <= mu := eigen_le_of_pos_eigenvector hM hy hx hye hxe hm
  have hlam : lam = mu := le_antisymm hlam_le hmu_le
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin m)) (fun j => x j / y j)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  set t : Real := x j0 / y j0 with ht
  have htpos : 0 < t := by
    rw [ht]; exact div_pos (hx j0) (hy j0)
  have hge : forall i, t * y i <= x i := by
    intro i
    have hle : t <= x i / y i := hj0 i (Finset.mem_univ i)
    have h3 := mul_le_mul_of_nonneg_right hle (le_of_lt (hy i))
    rwa [div_mul_cancel₀ (x i) (ne_of_gt (hy i))] at h3
  have hz : forall i, 0 <= x i - t * y i := fun i => by linarith [hge i]
  have hzj0 : x j0 - t * y j0 = 0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt (hy j0)), sub_self]
  have hze : forall i, (Finset.univ.sum fun j => M i j * (x j - t * y j))
      = lam * (x i - t * y i) := by
    intro i
    have h1 : (Finset.univ.sum fun j => M i j * (x j - t * y j))
        = (Finset.univ.sum fun j => M i j * x j)
          - t * (Finset.univ.sum fun j => M i j * y j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, hxe i, hye i, hlam]
    ring
  have hzero : forall k, x k - t * y k = 0 := by
    intro k
    have h1 : (Finset.univ.sum fun j => M j0 j * (x j - t * y j)) = 0 := by
      rw [hze j0, hzj0, mul_zero]
    have h2 : M j0 k * (x k - t * y k)
        <= Finset.univ.sum fun j => M j0 j * (x j - t * y j) :=
      Finset.single_le_sum (f := fun j => M j0 j * (x j - t * y j))
        (fun j _ => mul_nonneg (le_of_lt (hM j0 j)) (hz j)) (Finset.mem_univ k)
    have h4 : M j0 k * (x k - t * y k) = 0 := by
      have h3 : 0 <= M j0 k * (x k - t * y k) :=
        mul_nonneg (le_of_lt (hM j0 k)) (hz k)
      linarith
    exact (mul_eq_zero.mp h4).resolve_left (ne_of_gt (hM j0 k))
  have ht_eq : t = x ⟨0, hm⟩ / y ⟨0, hm⟩ := by
    have h0 : x ⟨0, hm⟩ = t * y ⟨0, hm⟩ := by linarith [hzero ⟨0, hm⟩]
    rw [h0, mul_div_cancel_right₀ t (ne_of_gt (hy _))]
  intro i
  rw [← ht_eq]
  linarith [hzero i]

/-! ## The row-sum matrix of a fusion ring is strictly positive -/

/-- `M i j = sum_k N i j k`: the total multiplicity of `i (x) j` (the sum of the entries in
the `(i,j)` row of all the fusion matrices at once).  Its positive eigenvectors are the
*simultaneous* positive eigenvectors of every `N^(k)`. -/
noncomputable def fusionRowSum (R : FusionRing n) (i j : Fin n) : Real :=
  Finset.univ.sum fun k => (R.N i j k : Real)

theorem fusionRowSum_apply (R : FusionRing n) (i j : Fin n) :
    fusionRowSum R i j = Finset.univ.sum fun k => (R.N i j k : Real) := rfl

/-- **Every product of two simples is nonzero**: `sum_k N i j k > 0`.

Associativity at `(i, j, j*, i)`, where both unit channels are computable:
`sum_p N i j p * N p j* i = sum_q N j j* q * N i q i >= 1 * 1`.  So not all the `N i j p`
vanish.  This is the connectedness input Perron--Frobenius needs, with no irreducibility
hypothesis. -/
theorem fusionRowSum_pos (R : FusionRing n) (hn : 0 < n) (i j : Fin n) :
    0 < fusionRowSum R i j := by
  classical
  have hkey : (Finset.univ.sum fun p => R.N i j p * R.N p (R.dual j) i)
      = Finset.univ.sum fun q => R.N j (R.dual j) q * R.N i q i :=
    R.associativity i j (R.dual j) i
  have hterm1 : R.N j (R.dual j) ⟨0, hn⟩ = 1 := by
    have h := R.dual_coeff hn j (R.dual j)
    simpa using h
  have hterm2 : R.N i ⟨0, hn⟩ i = 1 := by
    have h := R.right_unit hn i i
    simpa using h
  have hrhs : 0 < Finset.univ.sum fun q => R.N j (R.dual j) q * R.N i q i := by
    have hle : R.N j (R.dual j) ⟨0, hn⟩ * R.N i ⟨0, hn⟩ i
        <= Finset.univ.sum fun q => R.N j (R.dual j) q * R.N i q i :=
      Finset.single_le_sum (f := fun q => R.N j (R.dual j) q * R.N i q i)
        (fun q _ => Nat.zero_le _) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    rw [hterm1, hterm2] at hle
    omega
  have hlhs : 0 < Finset.univ.sum fun p => R.N i j p * R.N p (R.dual j) i := hkey ▸ hrhs
  have hne : (Finset.univ.sum fun p => R.N i j p) ≠ 0 := by
    intro hzero
    have hall : forall p : Fin n, R.N i j p = 0 := by
      intro p
      have hle : R.N i j p <= Finset.univ.sum fun q => R.N i j q :=
        Finset.single_le_sum (f := fun q => R.N i j q) (fun q _ => Nat.zero_le _)
          (Finset.mem_univ p)
      omega
    have hz : (Finset.univ.sum fun p => R.N i j p * R.N p (R.dual j) i) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [hall p, Nat.zero_mul]
    rw [hz] at hlhs
    exact lt_irrefl 0 hlhs
  have hpos : 0 < Finset.univ.sum fun p => R.N i j p := Nat.pos_of_ne_zero hne
  rw [fusionRowSum_apply]
  exact_mod_cast hpos

/-! ## The eigenrelation for the row-sum matrix -/

theorem fusionRowSum_pos' (R : FusionRing n) (hn : 0 < n) :
    forall i j, 0 < fusionRowSum R i j := fun i j => fusionRowSum_pos R hn i j

/-- A positive eigenvector of every fusion matrix `N^(k)`, with eigenvalues `v k`, is a positive
eigenvector of the row-sum matrix, with eigenvalue `sum k, v k`. -/
theorem sum_eigenrelation {R : FusionRing n} {v : Fin n -> Real}
    (heig : forall (i : Fin n) (k : Fin n),
      (Finset.univ.sum fun j => (R.N i j k : Real) * v j) = v i * v k) (i : Fin n) :
    (Finset.univ.sum fun j => fusionRowSum R i j * v j)
      = (Finset.univ.sum fun k => v k) * v i := by
  classical
  calc (Finset.univ.sum fun j => fusionRowSum R i j * v j)
      = Finset.univ.sum fun j => Finset.univ.sum fun k => (R.N i j k : Real) * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fusionRowSum_apply, Finset.sum_mul]
    _ = Finset.univ.sum fun k => Finset.univ.sum fun j => (R.N i j k : Real) * v j :=
        Finset.sum_comm
    _ = Finset.univ.sum fun k => v i * v k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [heig i k]
    _ = v i * Finset.univ.sum fun k => v k := by rw [Finset.mul_sum]
    _ = (Finset.univ.sum fun k => v k) * v i := by rw [mul_comm]

/-! ## `PFUnique`, unconditionally -/

/-- **Perron--Frobenius uniqueness of the FP-dimension, for every fusion ring.**

`PFUnique R h` is a hypothesis of every ENO 8.23 statement in the repository; here it is
discharged with no hypothesis beyond the fusion-ring axioms and `FPData`. -/
theorem pfUnique_unconditional (R : FusionRing n) (h : R.FPData) : PFUnique R h := by
  intro v hv hv0 heig
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    funext i
    exact i.elim0
  · have hveig := sum_eigenrelation (R := R) (v := v) heig
    have hfeig := sum_eigenrelation (R := R) (v := h.fpdim) h.eigenvector
    have hprop := eq_smul_of_pos_eigenvector hn (fusionRowSum_pos' R hn) hv h.pos hveig hfeig
    funext i
    rw [hprop i, hv0 hn, h.unit_one hn]
    norm_num
/-- **The positive eigenvector without normalisation**: any positive eigenvector of all the
fusion matrices is the FP-dimension scaled by its value at the unit.  This is the form that does
not need `v 1 = 1` (and so applies to dimension functions whose unit value is not yet known). -/
theorem pos_eigenvector_eq_smul_fpdim (R : FusionRing n) (h : R.FPData) (hn : 0 < n)
    {v : Fin n -> Real} (hv : forall i, 0 < v i)
    (heig : forall (i : Fin n) (k : Fin n),
      (Finset.univ.sum fun j => (R.N i j k : Real) * v j) = v i * v k) :
    forall i, v i = v ⟨0, hn⟩ * h.fpdim i := by
  have hveig := sum_eigenrelation (R := R) (v := v) heig
  have hfeig := sum_eigenrelation (R := R) (v := h.fpdim) h.eigenvector
  have hprop := eq_smul_of_pos_eigenvector hn (fusionRowSum_pos' R hn) hv h.pos hveig hfeig
  intro i
  rw [hprop i, h.unit_one hn, div_one]

/-- **`FPData` is a property of the ring, not extra data**: two FP-dimension data on the same
fusion ring have the same FP-dimension function. -/
theorem fpdim_unique {R : FusionRing n} (h1 h2 : R.FPData) : h1.fpdim = h2.fpdim := by
  funext i
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact i.elim0
  · exact (congrFun (pfUnique_unconditional R h1 h2.fpdim (fun i => h2.pos i)
      (fun hn' => h2.unit_one hn') h2.eigenvector) i).symm

/-- **The form consumers use.**  The fusion ring of a *system* is scalar-independent, so every
`PFUnique` hypothesis appearing in the ENO 8.23 statements -- at `Real` or at `Complex` -- is
discharged by `pfUnique_unconditional`. -/
theorem pfUnique_system {n : Nat} {k : Type u} [Field k] (S : FusionSystem n k)
    (hFP : S.ring.FPData) : PFUnique S.ring hFP :=
  pfUnique_unconditional S.ring hFP



/-! ## The point of it: ENO 8.23 without the `PFUnique` hypothesis -/

/-- **ENO 8.23 (Real form) with the Perron--Frobenius hypothesis removed.**  A pseudo-unitary
pivotal structure is spherical with the FP-dimensions -- unconditionally. -/
theorem eno823_of_pseudoUnitary_noPF {n : Nat} {S : FusionSystem n Real} (hn : 0 < n)
    (hFP : S.ring.FPData) (P : PivotalStructure S) (hU : IsPseudoUnitaryPivotal P) :
    ENO823 S hFP :=
  eno823_of_pseudoUnitary hn hFP (pfUnique_unconditional S.ring hFP) P hU

#print axioms FusionCategory.eigen_le_of_pos_eigenvector
#print axioms FusionCategory.eq_smul_of_pos_eigenvector
#print axioms FusionCategory.fusionRowSum_pos
#print axioms FusionCategory.sum_eigenrelation
#print axioms FusionCategory.pfUnique_unconditional
#print axioms FusionCategory.pos_eigenvector_eq_smul_fpdim
#print axioms FusionCategory.fpdim_unique
#print axioms FusionCategory.pfUnique_system
#print axioms FusionCategory.eno823_of_pseudoUnitary_noPF

end FusionCategory
