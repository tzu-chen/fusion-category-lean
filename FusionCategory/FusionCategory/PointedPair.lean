import FusionCategory.DerivedJMate
import FusionCategory.DerivedJPointed

/-!
# The mate pairing never degenerates on pointed data

The third refutation shape of this round is a datum on which `PivotalFactor` holds
but the mate pairing degenerates — `pairScalar S a b c = 0` on a *supported*
channel — so that `PairCocycle` fails although the datum is pivotal.  This file
rules that shape out for the whole pointed class:

* `Finv_ne_zero_of_pointed`: on pointed data the inverse associator is nonzero on
  every supported boundary block (from `Finv_comp`: the sum has one nonzero term
  and equals `1`, so it cannot have a vanishing factor);
* `pairScalar_ne_zero_of_pointed`: hence `pairScalar` is nonzero on channels.

Consequences (`pairCocycle_of_pointed`, `exists_coboundary_of_pointed`): the
F-free fourth law `PairCocycle` and the target's positive shape both hold on
*every* pointed datum with no nonvanishing side condition at all, and with no
hypothesis on the dual involution (so this covers the non-self-dual labels that
no inhabitant in the tree had before `FusionCategory.Z3Omega`).  A
degenerate-pairing refutation — a supported channel with `pairScalar = 0` — must
therefore come from non-pointed data.

Not claimed here: the same for non-pointed data.  There the boundary `F`-entry is
free (`DerivedJBlockMatrix.boundary_F_ne_zero` is unconditional) but the
`Finv (x* x y y z 1)`-entry at composite `d = y ≠ 1` is not, and
`Finv_ne_zero_of_pointed` above is where pointedness enters.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

variable {n : ℕ} {k : Type u} [Field k]

/-- On pointed data the inverse associator does not vanish on a supported
boundary block: `Finv_comp` writes `1` as a sum with a single surviving term
`Finv a b c d f e · F a b c d e f`, and that `F`-entry is nonzero
(`F_ne_zero_of_pointed`). -/
theorem Finv_ne_zero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c d f e : Fin n}
    (hbcf : 0 < S.ring.N b c f) (hafd : 0 < S.ring.N a f d)
    (habe : 0 < S.ring.N a b e) (hecd : 0 < S.ring.N e c d) :
    S.Finv a b c d f e ≠ 0 := by
  have huniq : ∀ e' : Fin n, 0 < S.ring.N a b e' → e' = e :=
    fun e' he' => pointed_unique S hP he' habe
  have hsum : (∑ e' : Fin n, S.Finv a b c d f e' * S.F a b c d e' f) = 1 := by
    have h := S.Finv_comp a b c d f f hbcf hafd hbcf hafd
    simpa using h
  have hsingle : (∑ e' : Fin n, S.Finv a b c d f e' * S.F a b c d e' f)
      = S.Finv a b c d f e * S.F a b c d e f := by
    refine Finset.sum_eq_single e ?_ ?_
    · intro e' _ hne
      by_cases h : 0 < S.ring.N a b e'
      · exact absurd (huniq e' h) hne
      · have hzero : S.F a b c d e' f = 0 :=
          S.F_support a b c d e' f (fun hc => h hc.1)
        rw [hzero, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ e) hmem
  have hF : S.F a b c d e f ≠ 0 := F_ne_zero_of_pointed S hP habe hecd hbcf hafd
  intro hzero
  rw [hzero, zero_mul] at hsingle
  rw [hsingle] at hsum
  exact one_ne_zero hsum.symm

/-- **The mate pairing is non-degenerate on pointed data.**  Both boundary
entries of `pairScalar` are nonzero on a supported channel, and so is `ev`. -/
theorem pairScalar_ne_zero_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) {a b c : Fin n} (hN : 0 < S.ring.N a b c) :
    pairScalar S a b c ≠ 0 := by
  have hsymm : 0 < S.ring.N (S.ring.dual b) (S.ring.dual a) (S.ring.dual c) :=
    N_dual_symm S hN
  have hacb : 0 < S.ring.N (S.ring.dual a) c b :=
    N_dual_shift' S hn hP (N_dual_shift S hn hP hN)
  have hF : S.F (S.ring.dual b) (S.ring.dual a) c ⟨0, hn⟩ (S.ring.dual c) b ≠ 0 :=
    F_ne_zero_of_pointed S hP hsymm (pos_dual_coeff' (S := S) hn c) hacb
      (pos_dual_coeff' (S := S) hn b)
  have hFi : S.Finv (S.ring.dual a) a b b c ⟨0, hn⟩ ≠ 0 :=
    Finv_ne_zero_of_pointed S hn hP hN hacb (pos_dual_coeff' (S := S) hn a)
      (pos_left_unit (S := S) hn b)
  rw [pairScalar_def, dif_pos hn]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hF hFi) (S.ev_ne_zero a)) (S.ev_ne_zero b)

/-- Consequently the mate-pairing route to the fourth law needs no nonvanishing
side condition on pointed data. -/
theorem pairCocycle_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) : PairCocycle S :=
  (pairCocycle_iff_crossCocycle S
    (fun a b c h => pairScalar_ne_zero_of_pointed S hn hP h)).mpr
    (crossCocycle_of_pivotalFactor S
      (pivotalFactor_of_coboundary S (fun i => S.kappa_ne_zero i)
        (fun a b c h => pairScalar_ne_zero_of_pointed S hn hP h)
        (fun a b c h => derivedJGen_eq_delta_kappa_of_pointed S hn hP h)))

/-- **The target's positive shape, unconditionally on pointed data**: there is a
nowhere-vanishing `φ` with `derivedJGen = φ_a φ_b / φ_c` on every channel — and
the whole F-retained fourth law follows (`DerivedJCoherent`). -/
theorem exists_coboundary_of_pointed (S : FusionSystem n k) (hn : 0 < n)
    (hP : WP2.Pointed S) :
    ∃ φ : Fin n → k, (∀ i, φ i ≠ 0) ∧
      ∀ a b c : Fin n, 0 < S.ring.N a b c → derivedJGen S a b c = φ a * φ b / φ c :=
  ⟨S.kappa, fun i => S.kappa_ne_zero i,
    fun a b c h => derivedJGen_eq_delta_kappa_of_pointed S hn hP h⟩

#print axioms FusionCategory.Finv_ne_zero_of_pointed
#print axioms FusionCategory.pairScalar_ne_zero_of_pointed
#print axioms FusionCategory.pairCocycle_of_pointed
#print axioms FusionCategory.exists_coboundary_of_pointed

end FusionCategory
