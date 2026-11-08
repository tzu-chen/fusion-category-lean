import FusionCategory.DerivedJCoherent

/-!
# d2 — the boundary-collapse layer for the `omegaCoeff` cocycle

`DerivedJCoherent.derivedJGen_coherent_iff_omegaCoeff_cocycle` reduces the fourth twist law
on tuples with the four `OmegaNe` brackets nonzero to the associator-only identity

  `Ω(a,b;e)·Ω(e,c;d) = Ω(b,c;f)·Ω(a,f;d)`,   `Ω = FusionMat.omegaCoeff`.

This file builds the layer that identity has to be proved from, and isolates exactly what is
still missing.  Nothing here is pointed: every statement is about arbitrary `FusionSystem`
data.

## §1 — Frobenius reciprocity on arbitrary data

`DerivedJPointed.N_shift` derived `N a b c > 0 → N c b* a > 0` on *pointed* data, where the
channel sums collapse.  The same conclusion on arbitrary data comes from a single
associativity instance with a **unit in the last slot**, which collapses both sides: at
`(a, b, c*, 1)` the two sums become `N a b c` and `N b c* a*`.  So `frobenius_N` is an
equality of the individual structure constants, and both of the shifts the collapse lemmas
need are immediate (`frobenius_N_pos`, `frobenius_N'_pos`); nothing about unique channels
enters.

## §2 — the boundary pattern

Every entry of `Ω` is a boundary entry: each `F`-entry has the composite slot `d` equal to the
unit, each `Finv`-entry has the channel slot `e` equal to the unit.  In those two slots a
unit determines the neighbouring labels by `dual_coeff` (`F_boundary_fst/_snd`,
`Finv_boundary_fst/_snd`) — again with no uniqueness of fusion channels.

## §3 — the two pentagon instances whose `k`-sum collapses on arbitrary data

This is the heart of the file.  The pointed proof (`DerivedJPointed.pentagon_P1`–`P3`)
collapsed the pentagon's `k`-sum by *pointedness*.  Two of the three instances do not need
it: the collapse is forced by `dual_coeff` from a **unit slot inside the pentagon**, and both
instances are valid on arbitrary data.

* `pentagon_composite_unit` — the pentagon at `(x, y, z*, z)` with composite `1`: the
  second term carries `N x k 1 > 0`, so `k = x*` and the sum is one term.
* `pentagon_channel_unit` — the pentagon at `(y, y*, x*, z)` with `j = 1`: the third term
  carries `N k z 1 > 0`, so `k = z*`.

Eliminating the common factor `F y z* z y x* 1` (by multiplying, not by cancelling: the
factor may vanish) gives `boundary_chain`:

  `loop z · (Y · G_y) = loop y · (X · A₃)`.

The third pointed instance (`pentagon_P1`) has **no** collapse on arbitrary data: on the
Fibonacci ring the `k`-sum keeps two terms (`1/φ + 1/φ² = 1`), and its sum-free consequence
`A₃ = loop x · G_x` is false there.  That is exactly the residual — see §4.

## §4 — where the residual is, precisely

`Ω(x,y;z)` is a ratio of two *unit-composite* entries (`F x y z* 1 z x*`,
`F y* x* z 1 z* y`) against two entries of **inverse blocks** (`Finv y y* x* x* z* 1`,
`Finv x* x y y z 1`).  Under the reciprocal hypothesis (which holds when those blocks are
`1 × 1`, in particular on pointed data, and is false in general) `Ω` becomes the Finv-free
ratio `X·G_x/(Y·G_y)`, and `boundary_chain` turns that into the three-entry closed form

  `Ω(x,y;z) = loop z · G_x / (loop y · A₃)`   (`omegaCoeff_eq_closed`, cross-multiplied).

So the whole remaining obligation is an argument controlling those two *inverse*-block
entries (a block-matrix statement) plus the `P1` relation `A₃ = loop x · G_x`.  The file
proves nothing that assumes either.

## §5 — a usable reduction

`omegaCoeff_cocycle_of_coboundary`: if `Ω` is presented as a coboundary `g x · g y / g z` of
a nowhere-vanishing `g` on supported channels, the cocycle identity holds by cancellation;
`derivedJGen_coherent_of_omegaCoboundary` carries that through
`derivedJGen_coherent_iff_omegaCoeff_cocycle` to the `F`-retained fourth law for
`derivedJGen` on the `OmegaNe` tuples.  (Numerically `Ω` is a coboundary on all seven data
sets of the census — but it is *not* always the coboundary of `κ`: on
`Vec^ω_{(Z/2)²} × Fibonacci` it is a coboundary of a `±1` character while `κ` is not.  So
this reduction is a sufficient, not a necessary, route.)

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace FusionCategory

open CategoryTheory

variable {n : ℕ} {k : Type u} [Field k]

/-! ## §1 — Frobenius reciprocity on arbitrary data -/

/-- **Frobenius reciprocity, arbitrary data**: `a ⊗ b ∋ c` iff `b ⊗ c* ∋ a*`.

The associativity at `(a, b, c*, 1)` has a unit in the last slot, so *both* sums collapse to
a single structure constant. -/
theorem frobenius_N (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    S.ring.N a b c = S.ring.N b (S.ring.dual c) (S.ring.dual a) := by
  have hassoc := S.ring.associativity a b (S.ring.dual c) ⟨0, hn⟩
  have hL : (∑ p : Fin n, (S.ring.N a b p : ℕ) * S.ring.N p (S.ring.dual c) ⟨0, hn⟩)
      = S.ring.N a b c := by
    have hzero : ∀ p ∈ (Finset.univ : Finset (Fin n)), p ≠ c →
        (S.ring.N a b p : ℕ) * S.ring.N p (S.ring.dual c) ⟨0, hn⟩ = 0 := by
      intro p _ hp
      have h1 : S.ring.N p (S.ring.dual c) ⟨0, hn⟩ = 0 := by
        rw [S.ring.dual_coeff hn p (S.ring.dual c)]
        exact if_neg (fun hcon => hp (S.ring.dual_injective hcon).symm)
      rw [h1, Nat.mul_zero]
    rw [Finset.sum_eq_single c hzero (fun h => absurd (Finset.mem_univ c) h)]
    have h1 : S.ring.N c (S.ring.dual c) ⟨0, hn⟩ = 1 := by
      rw [S.ring.dual_coeff hn c (S.ring.dual c)]
      simp
    rw [h1, Nat.mul_one]
  have hR : (∑ q : Fin n, (S.ring.N b (S.ring.dual c) q : ℕ) * S.ring.N a q ⟨0, hn⟩)
      = S.ring.N b (S.ring.dual c) (S.ring.dual a) := by
    have hzero : ∀ q ∈ (Finset.univ : Finset (Fin n)), q ≠ S.ring.dual a →
        (S.ring.N b (S.ring.dual c) q : ℕ) * S.ring.N a q ⟨0, hn⟩ = 0 := by
      intro q _ hq
      have h1 : S.ring.N a q ⟨0, hn⟩ = 0 := by
        rw [S.ring.dual_coeff hn a q]
        exact if_neg hq
      rw [h1, Nat.mul_zero]
    rw [Finset.sum_eq_single (S.ring.dual a) hzero (fun h => absurd (Finset.mem_univ _) h)]
    have h1 : S.ring.N a (S.ring.dual a) ⟨0, hn⟩ = 1 := by
      rw [S.ring.dual_coeff hn a (S.ring.dual a)]
      simp
    rw [h1, Nat.mul_one]
  rw [hL, hR] at hassoc
  exact hassoc

/-- **`a ⊗ b ∋ c` implies `b ⊗ c* ∋ a*`** on arbitrary data. -/
theorem frobenius_N_pos (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (h : 0 < S.ring.N a b c) :
    0 < S.ring.N b (S.ring.dual c) (S.ring.dual a) := by
  rw [← frobenius_N S hn a b c]
  exact h

/-- **The other Frobenius form**: `N a b c = N a* c b`. -/
theorem frobenius_N' (S : FusionSystem n k) (hn : 0 < n) (a b c : Fin n) :
    S.ring.N a b c = S.ring.N (S.ring.dual a) c b := by
  rw [frobenius_N S hn a b c, frobenius_N S hn b (S.ring.dual c) (S.ring.dual a)]
  rw [S.ring.dual_symm]
  simp [FusionRing.dual_dual]

/-- **`a ⊗ b ∋ c` implies `a* ⊗ c ∋ b`** on arbitrary data. -/
theorem frobenius_N'_pos (S : FusionSystem n k) (hn : 0 < n) {a b c : Fin n}
    (h : 0 < S.ring.N a b c) :
    0 < S.ring.N (S.ring.dual a) c b := by
  rw [← frobenius_N' S hn a b c]
  exact h

/-! ## §2 — the boundary pattern of `F` and `Finv` -/

/-- **`F` at a unit composite**: the channel of `a ⊗ b` is `c*`. -/
theorem F_boundary_fst (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : S.F x y z ⟨0, hn⟩ e f ≠ 0) : e = S.ring.dual z := by
  by_contra hne
  refine h (S.F_support x y z ⟨0, hn⟩ e f ?_)
  rintro ⟨-, h2, -, -⟩
  rw [S.ring.dual_coeff hn e z] at h2
  by_cases hze : z = S.ring.dual e
  · exact hne (by rw [hze, FusionRing.dual_dual])
  · rw [if_neg hze] at h2
    exact absurd h2 (lt_irrefl 0)

/-- **`F` at a unit composite**: the channel of `b ⊗ c` is `a*`. -/
theorem F_boundary_snd (S : FusionSystem n k) (hn : 0 < n) {x y z e f : Fin n}
    (h : S.F x y z ⟨0, hn⟩ e f ≠ 0) : f = S.ring.dual x := by
  by_contra hne
  refine h (S.F_support x y z ⟨0, hn⟩ e f ?_)
  rintro ⟨-, -, -, h4⟩
  rw [S.ring.dual_coeff hn x f] at h4
  by_cases hfx : f = S.ring.dual x
  · exact hne hfx
  · rw [if_neg hfx] at h4
    exact absurd h4 (lt_irrefl 0)

/-- **`Finv` at a unit channel `e = 1`**: the second factor is `a*`. -/
theorem Finv_boundary_fst (S : FusionSystem n k) (hn : 0 < n) {x y z d f : Fin n}
    (h : S.Finv x y z d f ⟨0, hn⟩ ≠ 0) : y = S.ring.dual x := by
  by_contra hne
  refine h (S.Finv_support x y z d f ⟨0, hn⟩ ?_)
  rintro ⟨-, -, h3, -⟩
  rw [S.ring.dual_coeff hn x y] at h3
  by_cases hyx : y = S.ring.dual x
  · exact hne hyx
  · rw [if_neg hyx] at h3
    exact absurd h3 (lt_irrefl 0)

/-- **`Finv` at a unit channel `e = 1`**: the third factor equals the composite. -/
theorem Finv_boundary_snd (S : FusionSystem n k) (hn : 0 < n) {x y z d f : Fin n}
    (h : S.Finv x y z d f ⟨0, hn⟩ ≠ 0) : z = d := by
  by_contra hne
  refine h (S.Finv_support x y z d f ⟨0, hn⟩ ?_)
  rintro ⟨-, -, -, h4⟩
  rw [S.ring.left_unit hn z d] at h4
  by_cases hzd : z = d
  · exact hne hzd
  · rw [if_neg hzd] at h4
    exact absurd h4 (lt_irrefl 0)

/-! ## §3 — the two pentagon instances that collapse on arbitrary data -/

/-- **The pentagon at `(x, y, z*, z)` with intermediate composite `1`.**  The `k`-sum
collapses to `k = x*` because the middle term carries `N x k 1 > 0`; no uniqueness of fusion
channels is used.  The unit entry on the right is `F x y 1 z z y = 1` (`F_unit_right`). -/
theorem pentagon_composite_unit (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hxy : 0 < S.ring.N x y z) :
    S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
        S.F x (S.ring.dual x) z z ⟨0, hn⟩ y *
        S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩
      = S.F z (S.ring.dual z) z z ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hp := S.pentagon x y (S.ring.dual z) z z ⟨0, hn⟩ y z ⟨0, hn⟩
  have hcol : (∑ kk : Fin n, S.F x y (S.ring.dual z) ⟨0, hn⟩ z kk *
        S.F x kk z z ⟨0, hn⟩ y * S.F y (S.ring.dual z) z y kk ⟨0, hn⟩)
      = S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
        S.F x (S.ring.dual x) z z ⟨0, hn⟩ y *
        S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩ := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun kk : Fin n => S.F x y (S.ring.dual z) ⟨0, hn⟩ z kk *
        S.F x kk z z ⟨0, hn⟩ y * S.F y (S.ring.dual z) z y kk ⟨0, hn⟩)
      (a := (S.ring.dual x : Fin n)) ?_ ?_
    · intro kk _ hk
      have hz : S.F x kk z z ⟨0, hn⟩ y = 0 := by
        refine S.F_support x kk z z ⟨0, hn⟩ y ?_
        rintro ⟨h1, -, -, -⟩
        rw [S.ring.dual_coeff hn x kk] at h1
        by_cases hkx : kk = S.ring.dual x
        · exact absurd hkx hk
        · rw [if_neg hkx] at h1
          exact absurd h1 (lt_irrefl 0)
      simp [hz]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcol] at hp
  have hR : S.F x y ⟨0, hn⟩ z z y = 1 := by
    have h := S.F_unit_right hn x y z z hxy
    simpa using h
  rw [hR, mul_one] at hp
  exact hp

/-- **The pentagon at `(y, y*, x*, z)` with `j = 1`.**  The `k`-sum collapses to `k = z*`
because the third term carries `N k z 1 > 0`.  The unit entry is `F 1 x* z y x* y = 1`
(`F_unit_left`), whose hypothesis `0 < N x* z y` is `frobenius_N'_pos`. -/
theorem pentagon_channel_unit (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hxy : 0 < S.ring.N x y z) :
    S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z) *
        S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩ *
        S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y
      = S.F y (S.ring.dual y) y y ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hp := S.pentagon y (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ y ⟨0, hn⟩ y
    (S.ring.dual x)
  have hcol : (∑ kk : Fin n, S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
        ⟨0, hn⟩ kk * S.F y kk z y (S.ring.dual x) ⟨0, hn⟩ *
        S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ kk y)
      = S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z) *
        S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩ *
        S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y := by
    refine Finset.sum_eq_single (s := Finset.univ)
      (f := fun kk : Fin n => S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x)
        ⟨0, hn⟩ kk * S.F y kk z y (S.ring.dual x) ⟨0, hn⟩ *
        S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ kk y)
      (a := (S.ring.dual z : Fin n)) ?_ ?_
    · intro kk _ hk
      have hz : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ kk y = 0 := by
        refine S.F_support (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ kk y ?_
        rintro ⟨-, h2, -, -⟩
        rw [S.ring.dual_coeff hn kk z] at h2
        by_cases hzk : z = S.ring.dual kk
        · exact hk (by rw [hzk, FusionRing.dual_dual])
        · rw [if_neg hzk] at h2
          exact absurd h2 (lt_irrefl 0)
      simp [hz]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcol] at hp
  have hL : S.F ⟨0, hn⟩ (S.ring.dual x) z y (S.ring.dual x) y = 1 := by
    have h := S.F_unit_left hn (S.ring.dual x) z y y (frobenius_N'_pos S hn hxy)
    simpa using h
  rw [hL, one_mul] at hp
  exact hp

/-- **The elimination chain**: the two collapsible pentagon instances share the factor
`F y z* z y x* 1`, and eliminating it — by multiplying, so no nonvanishing hypothesis is
needed — gives

  `loop z · (Y · G_y) = loop y · (X · A₃)`

with `X = F x y z* 1 z x*`, `A₃ = F x x* z z 1 y`, `Y = F y* x* z 1 z* y`,
`G_y = F y y* x* x* 1 z*` and `loop x = F x x* x x 1 1`. -/
theorem boundary_chain (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hxy : 0 < S.ring.N x y z) :
    S.F z (S.ring.dual z) z z ⟨0, hn⟩ ⟨0, hn⟩ *
        (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
          S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z))
      = S.F y (S.ring.dual y) y y ⟨0, hn⟩ ⟨0, hn⟩ *
        (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
          S.F x (S.ring.dual x) z z ⟨0, hn⟩ y) := by
  have h2 := pentagon_composite_unit S hn hxy
  have h3 := pentagon_channel_unit S hn hxy
  calc S.F z (S.ring.dual z) z z ⟨0, hn⟩ ⟨0, hn⟩ *
        (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
          S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z))
      = (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
            S.F x (S.ring.dual x) z z ⟨0, hn⟩ y *
            S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩) *
          (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
            S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
              (S.ring.dual z)) := by rw [h2]
    _ = (S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
            (S.ring.dual z) *
          S.F y (S.ring.dual z) z y (S.ring.dual x) ⟨0, hn⟩ *
          S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y) *
          (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
            S.F x (S.ring.dual x) z z ⟨0, hn⟩ y) := by ring
    _ = S.F y (S.ring.dual y) y y ⟨0, hn⟩ ⟨0, hn⟩ *
        (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
          S.F x (S.ring.dual x) z z ⟨0, hn⟩ y) := by rw [h3]

/-! ## §4 — the `omegaCoeff` bookkeeping -/

/-- The two inversely-read block entries of `omegaCoeff` are the reciprocals of the two
block entries that occur in `boundary_chain`.  When the blocks `F^{y y* x*}_{x*}` and
`F^{x* x y}_y` are `1 × 1` — in particular on pointed data — this holds by
`finv_mul_F_of_unique`; in general it is exactly the block-matrix input that is missing. -/
theorem omegaCoeff_eq_of_block_inv (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (h1 : S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z)
        ⟨0, hn⟩ = (S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
          (S.ring.dual z))⁻¹)
    (h2 : S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ =
        (S.F (S.ring.dual x) x y y ⟨0, hn⟩ z)⁻¹) :
    FusionMat.omegaCoeff S x y z =
      (S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) *
          S.F (S.ring.dual x) x y y ⟨0, hn⟩ z) /
        (S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
          S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z)) := by
  rw [FusionMat.omegaCoeff_def, dif_pos hn, h1, h2]
  by_cases hGx : S.F (S.ring.dual x) x y y ⟨0, hn⟩ z = 0
  · simp [hGx]
  by_cases hGy : S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
      (S.ring.dual z) = 0
  · simp [hGy]
  · field_simp
    try ring

/-- **The algebraic core of the closed form**: a pure field identity, no fusion data.  If
`Y`, `Gy` do not vanish and `lz · (Y · Gy) = ly · (X · A₃)` then
`(X·Gx)/(Y·Gy) · (ly·A₃) = lz·Gx` — the content of `boundary_chain` read as the closed form
of `Ω`. -/
theorem boundary_closed_key {K : Type*} [Field K] (X Gx Y Gy A3 lz ly : K)
    (hden : Y * Gy ≠ 0) (hchain : lz * (Y * Gy) = ly * (X * A3)) :
    (X * Gx) / (Y * Gy) * (ly * A3) = lz * Gx := by
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  calc X * Gx * (ly * A3) = Gx * (ly * (X * A3)) := by ring
    _ = Gx * (lz * (Y * Gy)) := by rw [hchain]
    _ = lz * Gx * (Y * Gy) := by ring


/-- **The three-entry closed form of `omegaCoeff`** under the same reciprocal hypotheses and
the `OmegaNe` nonvanishing: cross-multiplied against `boundary_chain`, the four-entry
definition collapses to

  `Ω(x,y;z) · (loop y · A₃) = loop z · G_x`,

i.e. `Ω(x,y;z) = loop z · G_x / (loop y · A₃)`.  The interposition `A₃ = loop x · G_x` (the
pointed `pentagon_P1`) would then make this `δ(κ)`; that relation is *false* on
multiplicity-free non-pointed data, so it is not used. -/
theorem omegaCoeff_eq_closed (S : FusionSystem n k) (hn : 0 < n) {x y z : Fin n}
    (hN : 0 < S.ring.N x y z)
    (hne : OmegaNe S hn x y z)
    (h1 : S.Finv y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) (S.ring.dual z)
        ⟨0, hn⟩ = (S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
          (S.ring.dual z))⁻¹)
    (h2 : S.Finv (S.ring.dual x) x y y z ⟨0, hn⟩ =
        (S.F (S.ring.dual x) x y y ⟨0, hn⟩ z)⁻¹) :
    FusionMat.omegaCoeff S x y z *
        (S.F y (S.ring.dual y) y y ⟨0, hn⟩ ⟨0, hn⟩ *
          S.F x (S.ring.dual x) z z ⟨0, hn⟩ y)
      = S.F z (S.ring.dual z) z z ⟨0, hn⟩ ⟨0, hn⟩ *
        S.F (S.ring.dual x) x y y ⟨0, hn⟩ z := by
  have hX : S.F x y (S.ring.dual z) ⟨0, hn⟩ z (S.ring.dual x) ≠ 0 := by
    intro h0
    obtain ⟨-, hcon⟩ := hne
    exact hcon (by rw [h0, zero_mul])
  have hGx : S.F (S.ring.dual x) x y y ⟨0, hn⟩ z ≠ 0 := by
    intro h0
    obtain ⟨hcon, -⟩ := hne
    rw [h2, h0, inv_zero, mul_zero] at hcon
    exact hcon rfl
  have hY : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y ≠ 0 := by
    intro h0
    obtain ⟨hcon, -⟩ := hne
    exact hcon (by rw [h0, zero_mul])
  have hGy : S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩
      (S.ring.dual z) ≠ 0 := by
    intro h0
    obtain ⟨-, hcon⟩ := hne
    rw [h1, h0, inv_zero, mul_zero] at hcon
    exact hcon rfl
  have hden : S.F (S.ring.dual y) (S.ring.dual x) z ⟨0, hn⟩ (S.ring.dual z) y *
      S.F y (S.ring.dual y) (S.ring.dual x) (S.ring.dual x) ⟨0, hn⟩ (S.ring.dual z) ≠ 0 :=
    mul_ne_zero hY hGy
  rw [omegaCoeff_eq_of_block_inv S hn h1 h2]
  exact boundary_closed_key _ _ _ _ _ _ _ hden (boundary_chain S hn hN)

/-! ## §5 — a sufficient reduction: a coboundary presentation of `omegaCoeff` -/

/-- **A coboundary presentation of `omegaCoeff` gives the cocycle identity.**  Nothing about
associators enters: both sides become `g a · g b · g c / g d`. -/
theorem omegaCoeff_cocycle_of_coboundary (S : FusionSystem n k) (hn : 0 < n)
    (g : Fin n → k) (hg : ∀ i, g i ≠ 0)
    (hOm : ∀ x y z : Fin n, 0 < S.ring.N x y z → FusionMat.omegaCoeff S x y z = g x * g y / g z) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      FusionMat.omegaCoeff S a b e * FusionMat.omegaCoeff S e c d
        = FusionMat.omegaCoeff S b c f * FusionMat.omegaCoeff S a f d := by
  intro a b c d e f h1 h2 h3 h4
  rw [hOm a b e h1, hOm e c d h2, hOm b c f h3, hOm a f d h4]
  have ha : g a ≠ 0 := hg a
  have hb : g b ≠ 0 := hg b
  have hc : g c ≠ 0 := hg c
  have he : g e ≠ 0 := hg e
  have hf : g f ≠ 0 := hg f
  have hd : g d ≠ 0 := hg d
  field_simp
  try ring

/-- **The `F`-free fourth law for `derivedJGen` from a coboundary presentation of
`omegaCoeff`**, on the tuples where the four `OmegaNe` brackets are nonzero. -/
theorem derivedJGen_qualified_of_omegaCoboundary (S : FusionSystem n k) (hn : 0 < n)
    (g : Fin n → k) (hg : ∀ i, g i ≠ 0)
    (hOm : ∀ x y z : Fin n, 0 < S.ring.N x y z → FusionMat.omegaCoeff S x y z = g x * g y / g z) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d = derivedJGen S b c f * derivedJGen S a f d := by
  intro a b c d e f h1 h2 h3 h4 hA hB hC hD
  exact (derivedJGen_coherent_iff_omegaCoeff_cocycle S hn).mpr
    (fun a b c d e f h1 h2 h3 h4 _ _ _ _ =>
      omegaCoeff_cocycle_of_coboundary S hn g hg hOm a b c d e f h1 h2 h3 h4)
    a b c d e f h1 h2 h3 h4 hA hB hC hD

/-- **The `F`-retained fourth law for `derivedJGen` from a coboundary presentation of
`omegaCoeff`** — the exact shape `FusionSystem.J_coherent` asks for, on `OmegaNe` tuples. -/
theorem derivedJGen_coherent_of_omegaCoboundary (S : FusionSystem n k) (hn : 0 < n)
    (g : Fin n → k) (hg : ∀ i, g i ≠ 0)
    (hOm : ∀ x y z : Fin n, 0 < S.ring.N x y z → FusionMat.omegaCoeff S x y z = g x * g y / g z) :
    ∀ a b c d e f : Fin n, 0 < S.ring.N a b e → 0 < S.ring.N e c d →
      0 < S.ring.N b c f → 0 < S.ring.N a f d →
      OmegaNe S hn a b e → OmegaNe S hn e c d → OmegaNe S hn b c f → OmegaNe S hn a f d →
      derivedJGen S a b e * derivedJGen S e c d * S.F a b c d e f
        = derivedJGen S b c f * derivedJGen S a f d * S.F a b c d e f := by
  intro a b c d e f h1 h2 h3 h4 hA hB hC hD
  have h := derivedJGen_qualified_of_omegaCoboundary S hn g hg hOm a b c d e f h1 h2 h3 h4
    hA hB hC hD
  rw [h]

end FusionCategory

/-! ## Axiom audit -/

#print axioms FusionCategory.frobenius_N
#print axioms FusionCategory.frobenius_N_pos
#print axioms FusionCategory.frobenius_N'
#print axioms FusionCategory.frobenius_N'_pos
#print axioms FusionCategory.F_boundary_fst
#print axioms FusionCategory.F_boundary_snd
#print axioms FusionCategory.Finv_boundary_fst
#print axioms FusionCategory.Finv_boundary_snd
#print axioms FusionCategory.pentagon_composite_unit
#print axioms FusionCategory.pentagon_channel_unit
#print axioms FusionCategory.boundary_chain
#print axioms FusionCategory.boundary_closed_key
#print axioms FusionCategory.omegaCoeff_eq_of_block_inv
#print axioms FusionCategory.omegaCoeff_eq_closed
#print axioms FusionCategory.omegaCoeff_cocycle_of_coboundary
#print axioms FusionCategory.derivedJGen_qualified_of_omegaCoboundary
#print axioms FusionCategory.derivedJGen_coherent_of_omegaCoboundary
