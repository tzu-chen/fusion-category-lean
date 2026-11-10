import FusionCategory.DerivedJScalar
import FusionCategory.Examples.FibonacciIsing
import FusionCategory.Examples.YangLee
import FusionCategory.Examples.Z2SqHonest

/-!
# WP3: Bartlett's Theorem 4.17, channel by channel, in the kernel

`docs/bartlett_check.py` (WP3 Task 3.5) compares the tree's derived twist
`derivedJGen` with Bartlett's closed form (*Fusion categories via string
diagrams*, arXiv:1502.02882, Thm 4.17 and Thm 5.4) index by index, in exact
arithmetic, on the data sets of `PLAN.md` "WP3 round 1".  That comparison has
been a *script* result: the Lean tree carried the twist, the comparison scalar
and their laws, but not the equality with Bartlett's index.  This file moves
that comparison into the kernel.

## The statement

Bartlett's apex associator and its monodromy are

  `apexAssoc S i j l = S.F i j l 0 l* i*`,
  `apexMonodromy S i j l = apexAssoc S j l i * apexAssoc S l i j * apexAssoc S i j l`,

and the two `F`/`Finv` products read by `DerivedJScalar.comparisonScalar` are,
at the channel `(a,b;c)`, `hD = F b* a* c 0 c* b · Finv a* a b b c 0` and its
dual twin `hN = F a b c* 0 c a* · Finv b b* a* a* c* 0`.  The two identities
proved here are

  (F)  `hN * apexMonodromy S c* a b = hD`   (division-free, `F`/`Finv` only),
  (E)  `derivedJGen S a b c * apexMonodromy S c* a b = 1`,

which are the script's identities (F) and (E).  `derivedJGen_eq_raw` and
`derivedJGen_mul_apexMonodromy` do the passage (F) => (E) once, generically,
on a self-dual datum with `ev ≡ 1`: there the derived twist *is* `hN / hD`, so
(E) is (F) divided by `hD ≠ 0`.  In the tree's normalisation `J` sits where
`1/T` sits in Bartlett's Thm 4.17 (`p_mon` against his Thm 5.4), so (E) is the
form the dictionary predicts.

## What is proved

`bartlett` at every supported channel of each of the six data sets the script
compares — `VecZ2` (4 channels), `VecZ2Twisted` (4), `Z2SqH.systemH` (16),
`YangLee` (5), `Fibonacci` (5), `Ising` (10): 44 channels, the script's whole
census.  Each one is fed by a division-free `bartlettF`, which in turn is the
integer-pair identity `bartlettF_pair` (in `ℤ[√d]`, `d = 5` for
Fibonacci/Yang-Lee, `2` for Ising, `1` for the pointed data) or
`bartlettF_int` (`ℤ`) settled by `decide`; `bartlettD_ne_zero` supplies the
non-vanishing the division needs, by the norm form `p² - d q²` on supported
channels.

## What is NOT proved here

* No general theorem.  (F) is *not* derived for arbitrary data: that is the
  block-matrix composition of `F`-blocks that `PLAN.md` "WP3 round 1" records
  as still owed.  It is proved data set by data set, which is what the script
  does, and no more.
* The script's identity (D) (`J · T = δ(σ)`, with Bartlett's indicator `p` and
  the dimension normalisation `σ`) is not restated: on these six data
  `σ = p ∈ {±1}` and `δ(σ) = 1`, so (D) agrees with (E) there, but the
  indicators are not computed in Lean here.
* Bartlett's published Yang-Lee numbers (`p(τ) = -1`, `S_τττ = 1`,
  `T^τ_ττ = -1`, `d_τ = (√5-1)/2`) remain a script read-off, and the control
  datum `Vec^ω_{Z/4}` (`i* ≠ i`, not in the tree) remains script-only.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace FusionCategory

universe u

variable {n : ℕ} {k : Type u} [Field k]

/-- Bartlett's apex associator `S_ijk = F i j k 0 k* i*` (multiplicity-free). -/
def apexAssoc (S : FusionSystem n k) (h0 : 0 < n) (i j l : Fin n) : k :=
  S.F i j l ⟨0, h0⟩ (S.ring.dual l) (S.ring.dual i)

/-- Bartlett's apex associator monodromy `A_ijk = S_jki * S_kij * S_ijk`. -/
def apexMonodromy (S : FusionSystem n k) (h0 : 0 < n) (i j l : Fin n) : k :=
  apexAssoc S h0 j l i * apexAssoc S h0 l i j * apexAssoc S h0 i j l

theorem apexMonodromy_eq (S : FusionSystem n k) (h0 : 0 < n)
    (hdual : ∀ i, S.ring.dual i = i) (i j l : Fin n) :
    apexMonodromy S h0 i j l =
      S.F j l i ⟨0, h0⟩ i j * S.F l i j ⟨0, h0⟩ j l * S.F i j l ⟨0, h0⟩ l i := by
  simp only [apexMonodromy, apexAssoc, hdual]

/-- The derived twist as the ratio of the two `F`/`Finv` channel products, on a
self-dual datum with `ev ≡ 1`. -/
theorem derivedJGen_eq_raw (S : FusionSystem n k) (h0 : 0 < n)
    (hdual : ∀ i, S.ring.dual i = i) (hev : ∀ i, S.ev i = 1) (a b c : Fin n) :
    derivedJGen S a b c =
      (S.F a b c ⟨0, h0⟩ c a * S.Finv b b a a c ⟨0, h0⟩) /
        (S.F b a c ⟨0, h0⟩ c b * S.Finv a a b b c ⟨0, h0⟩) := by
  unfold derivedJGen comparisonScalar
  rw [dif_pos h0, dif_pos h0]
  simp only [hdual, hev, mul_one]
  field_simp

/-- **Bartlett's Theorem 4.17 at one channel, in the tree's normalisation**: the
derived twist is the reciprocal of the apex associator monodromy. -/
theorem derivedJGen_mul_apexMonodromy (S : FusionSystem n k) (h0 : 0 < n)
    (hdual : ∀ i, S.ring.dual i = i) (hev : ∀ i, S.ev i = 1) (a b c : Fin n)
    (hne : S.F b a c ⟨0, h0⟩ c b * S.Finv a a b b c ⟨0, h0⟩ ≠ 0)
    (hF : (S.F a b c ⟨0, h0⟩ c a * S.Finv b b a a c ⟨0, h0⟩) *
        (S.F a b c ⟨0, h0⟩ c a * S.F b c a ⟨0, h0⟩ a b * S.F c a b ⟨0, h0⟩ b c)
      = S.F b a c ⟨0, h0⟩ c b * S.Finv a a b b c ⟨0, h0⟩) :
    derivedJGen S a b c * apexMonodromy S h0 (S.ring.dual c) a b = 1 := by
  rw [derivedJGen_eq_raw S h0 hdual hev a b c, apexMonodromy_eq S h0 hdual, hdual c,
    div_mul_eq_mul_div, hF, div_self hne]

namespace BartlettPair

/-- `8 • x`. -/
def e8 (x : ℤ × ℤ) : ℤ × ℤ := (8 * x.1, 8 * x.2)

theorem zval_e8 {s : ℝ} (x : ℤ × ℤ) : ZP.zval s (e8 x) = 8 * ZP.zval s x := by
  simp only [e8, ZP.zval]
  push_cast
  ring

end BartlettPair

open BartlettPair in
/-- Pair-level transfer: an identity of the seven `ℤ[√d]` pairs that reads
`8 (D1 D2) = (N1 N2)(A1 A2 A3)` in the pair ring gives the corresponding
identity of real numbers. -/
theorem bartlett_transfer {d : ℤ} {s : ℝ} (hs : s * s = (d : ℝ))
    (D1 D2 N1 N2 A1 A2 A3 : ℤ × ℤ)
    (h : ZP.peq (e8 (ZP.Zmul d D1 D2))
      (ZP.Zmul d (ZP.Zmul d N1 N2) (ZP.Zmul d (ZP.Zmul d A1 A2) A3)) = true) :
    (ZP.zval s N1 * ZP.zval s N2) * (ZP.zval s A1 * ZP.zval s A2 * ZP.zval s A3)
      = ZP.zval s D1 * ZP.zval s D2 := by
  have hz := ZP.zval_of_peq (s := s) h
  rw [zval_e8] at hz
  simp only [ZP.zval_zmul hs] at hz
  nlinarith [hz]

/-- The real-side `F`/`Finv` product against its pair form. -/
theorem zval_mul_eq {s : ℝ} {d : ℤ} (hs : s * s = (d : ℝ)) (x y : ℤ × ℤ) :
    ZP.zval s x * ZP.zval s y = ZP.zval s (ZP.Zmul d x y) / 2 := by
  rw [ZP.zval_zmul hs]
  ring

end FusionCategory

/-! ## Fibonacci -/

namespace FusionCategory.Fibonacci

open FusionCategory.BartlettPair

variable (h0 : 0 < 2)

theorem bartlettF_pair : ∀ a b c : Fin 2,
    ZP.peq (e8 (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)))
      (ZP.Zmul 5
        (ZP.Zmul 5 (Fpair a b c 0 c a) (FinvPair b b a a c 0))
        (ZP.Zmul 5
          (ZP.Zmul 5 (Fpair a b c 0 c a) (Fpair b c a 0 a b))
          (Fpair c a b 0 b c))) = true := by
  decide

theorem bartlettF (a b c : Fin 2) :
    (F a b c ⟨0, h0⟩ c a * Finv b b a a c ⟨0, h0⟩) *
        (F a b c ⟨0, h0⟩ c a * F b c a ⟨0, h0⟩ a b * F c a b ⟨0, h0⟩ b c)
      = F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ :=
  FusionCategory.bartlett_transfer (d := 5) (s := s5) s5_sq _ _ _ _ _ _ _
    (bartlettF_pair a b c)

theorem bartlettD_pair_norm_ne : ∀ a b c : Fin 2, 0 < N a b c →
    (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).1 ^ 2 ≠
      5 * (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).2 ^ 2 := by
  decide

theorem bartlettD_ne_zero (a b c : Fin 2) (h : 0 < N a b c) :
    F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  have hz : F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ =
      ZP.zval s5 (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)) / 2 :=
    FusionCategory.zval_mul_eq s5_sq _ _
  rw [hz]
  exact div_ne_zero
    (ZP.zval_ne_zero_of_norm_ne s5_sq (bartlettD_pair_norm_ne a b c h)) two_ne_zero

/-- **Bartlett's Theorem 4.17 for `Fibonacci`**, channel by channel: our derived
twist is the reciprocal of his apex associator monodromy. -/
theorem bartlett (a b c : Fin 2) (h : 0 < N a b c) :
    derivedJGen system a b c * FusionCategory.apexMonodromy system h0 c a b = 1 := by
  have hd : ∀ i : Fin 2, system.ring.dual i = i := fun i => by fin_cases i <;> decide
  have hev : ∀ i : Fin 2, system.ev i = 1 := fun i => evPair_zval i
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy system h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.Fibonacci


/-! ## Ising -/

namespace FusionCategory.Ising

open FusionCategory.BartlettPair

variable (h0 : 0 < 3)

theorem bartlettF_pair : ∀ a b c : Fin 3,
    ZP.peq (e8 (ZP.Zmul 2 (Fpair b a c 0 c b) (FinvPair a a b b c 0)))
      (ZP.Zmul 2
        (ZP.Zmul 2 (Fpair a b c 0 c a) (FinvPair b b a a c 0))
        (ZP.Zmul 2
          (ZP.Zmul 2 (Fpair a b c 0 c a) (Fpair b c a 0 a b))
          (Fpair c a b 0 b c))) = true := by
  decide

theorem bartlettF (a b c : Fin 3) :
    (F a b c ⟨0, h0⟩ c a * Finv b b a a c ⟨0, h0⟩) *
        (F a b c ⟨0, h0⟩ c a * F b c a ⟨0, h0⟩ a b * F c a b ⟨0, h0⟩ b c)
      = F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ :=
  FusionCategory.bartlett_transfer (d := 2) (s := s2) s2_sq _ _ _ _ _ _ _
    (bartlettF_pair a b c)

theorem bartlettD_pair_norm_ne : ∀ a b c : Fin 3, 0 < N a b c →
    (ZP.Zmul 2 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).1 ^ 2 ≠
      2 * (ZP.Zmul 2 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).2 ^ 2 := by
  decide

theorem bartlettD_ne_zero (a b c : Fin 3) (h : 0 < N a b c) :
    F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  have hz : F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ =
      ZP.zval s2 (ZP.Zmul 2 (Fpair b a c 0 c b) (FinvPair a a b b c 0)) / 2 :=
    FusionCategory.zval_mul_eq s2_sq _ _
  rw [hz]
  exact div_ne_zero
    (ZP.zval_ne_zero_of_norm_ne s2_sq (bartlettD_pair_norm_ne a b c h)) two_ne_zero

/-- **Bartlett's Theorem 4.17 for `Ising`**, channel by channel: our derived
twist is the reciprocal of his apex associator monodromy. -/
theorem bartlett (a b c : Fin 3) (h : 0 < N a b c) :
    derivedJGen system a b c * FusionCategory.apexMonodromy system h0 c a b = 1 := by
  have hd : ∀ i : Fin 3, system.ring.dual i = i := fun i => by fin_cases i <;> decide
  have hev : ∀ i : Fin 3, system.ev i = 1 := fun i => evPair_zval i
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy system h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.Ising


/-! ## Yang-Lee -/

namespace FusionCategory.YangLee

open FusionCategory.BartlettPair

variable (h0 : 0 < 2)

theorem evPair_zval_yang (i : Fin 2) : ZP.zval s5 (YangLee.evPair i) = 1 := by
  simp only [YangLee.evPair, ZP.zval]
  norm_num

theorem bartlettF_pair : ∀ a b c : Fin 2,
    ZP.peq (e8 (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)))
      (ZP.Zmul 5
        (ZP.Zmul 5 (Fpair a b c 0 c a) (FinvPair b b a a c 0))
        (ZP.Zmul 5
          (ZP.Zmul 5 (Fpair a b c 0 c a) (Fpair b c a 0 a b))
          (Fpair c a b 0 b c))) = true := by
  decide

theorem bartlettF (a b c : Fin 2) :
    (F a b c ⟨0, h0⟩ c a * Finv b b a a c ⟨0, h0⟩) *
        (F a b c ⟨0, h0⟩ c a * F b c a ⟨0, h0⟩ a b * F c a b ⟨0, h0⟩ b c)
      = F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ :=
  FusionCategory.bartlett_transfer (d := 5) (s := s5) s5_sq _ _ _ _ _ _ _
    (bartlettF_pair a b c)

theorem bartlettD_pair_norm_ne : ∀ a b c : Fin 2, 0 < N a b c →
    (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).1 ^ 2 ≠
      5 * (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)).2 ^ 2 := by
  decide

theorem bartlettD_ne_zero (a b c : Fin 2) (h : 0 < N a b c) :
    F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  have hz : F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ =
      ZP.zval s5 (ZP.Zmul 5 (Fpair b a c 0 c b) (FinvPair a a b b c 0)) / 2 :=
    FusionCategory.zval_mul_eq s5_sq _ _
  rw [hz]
  exact div_ne_zero
    (ZP.zval_ne_zero_of_norm_ne s5_sq (bartlettD_pair_norm_ne a b c h)) two_ne_zero

/-- **Bartlett's Theorem 4.17 for `Yang-Lee`**, channel by channel: our derived
twist is the reciprocal of his apex associator monodromy. -/
theorem bartlett (a b c : Fin 2) (h : 0 < N a b c) :
    derivedJGen system a b c * FusionCategory.apexMonodromy system h0 c a b = 1 := by
  have hd : ∀ i : Fin 2, system.ring.dual i = i := fun i => by fin_cases i <;> decide
  have hev : ∀ i : Fin 2, system.ev i = 1 := fun i => evPair_zval_yang i
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy system h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.YangLee

/-! ## `Vec_{Z/2}` -/

namespace FusionCategory.VecZ2

variable (h0 : 0 < 2)

theorem bartlettF (a b c : Fin 2) :
    (system.F a b c ⟨0, h0⟩ c a * system.Finv b b a a c ⟨0, h0⟩) *
        (system.F a b c ⟨0, h0⟩ c a * system.F b c a ⟨0, h0⟩ a b *
          system.F c a b ⟨0, h0⟩ b c)
      = system.F b a c ⟨0, h0⟩ c b * system.Finv a a b b c ⟨0, h0⟩ := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [system, F, ring, N] <;> norm_num

theorem bartlettD_ne_zero (a b c : Fin 2) (h : 0 < N a b c) :
    system.F b a c ⟨0, h0⟩ c b * system.Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [system, F, ring, N] at * <;> norm_num at *

theorem bartlett (a b c : Fin 2) (h : 0 < N a b c) :
    derivedJGen system a b c * FusionCategory.apexMonodromy system h0 c a b = 1 := by
  have hd : ∀ i : Fin 2, system.ring.dual i = i := fun i => by fin_cases i <;> rfl
  have hev : ∀ i : Fin 2, system.ev i = 1 := fun _ => rfl
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy system h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.VecZ2


/-! ## `Vec^ω_{Z/2}` (the non-trivial cocycle) -/

namespace FusionCategory.VecZ2Twisted

variable (h0 : 0 < 2)

theorem bartlettF (a b c : Fin 2) :
    (system.F a b c ⟨0, h0⟩ c a * system.Finv b b a a c ⟨0, h0⟩) *
        (system.F a b c ⟨0, h0⟩ c a * system.F b c a ⟨0, h0⟩ a b *
          system.F c a b ⟨0, h0⟩ b c)
      = system.F b a c ⟨0, h0⟩ c b * system.Finv a a b b c ⟨0, h0⟩ := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [system, F, VecZ2.ring, VecZ2.N] <;> norm_num

theorem bartlettD_ne_zero (a b c : Fin 2) (h : 0 < VecZ2.N a b c) :
    system.F b a c ⟨0, h0⟩ c b * system.Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [system, F, VecZ2.ring, VecZ2.N] at * <;> norm_num at *

theorem bartlett (a b c : Fin 2) (h : 0 < VecZ2.N a b c) :
    derivedJGen system a b c * FusionCategory.apexMonodromy system h0 c a b = 1 := by
  have hd : ∀ i : Fin 2, system.ring.dual i = i := fun i => by fin_cases i <;> rfl
  have hev : ∀ i : Fin 2, system.ev i = 1 := fun _ => rfl
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy system h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.VecZ2Twisted


/-! ## `Vec^ω_{(Z/2)²}` (Z2SqH) -/

namespace FusionCategory.Z2SqH

variable (h0 : 0 < 4)

/-- The associator of the pointed datum as an integer, mirroring `Fw`. -/
def Fint (a b c d e f : Fin 4) : ℤ :=
  (if e = gadd a b then 1 else 0) * (if d = gadd (gadd a b) c then 1 else 0) *
    (if f = gadd b c then 1 else 0) * wZ a b c

/-- The inverse associator as an integer. -/
def Finvint (a b c d f e : Fin 4) : ℤ := Fint a b c d e f

theorem F_eq_Fint (a b c d e f : Fin 4) : F a b c d e f = (Fint a b c d e f : ℝ) := by
  simp only [F, Fw, Fint, w]
  push_cast
  ring

theorem Finv_eq_Finvint (a b c d f e : Fin 4) : Finv a b c d f e = (Finvint a b c d f e : ℝ) := by
  simp only [Finv, Finvint, Fw, Fint, w]
  push_cast
  ring

theorem bartlettF_int : ∀ a b c : Fin 4,
    (Fint a b c 0 c a * Finvint b b a a c 0) *
        (Fint a b c 0 c a * Fint b c a 0 a b * Fint c a b 0 b c)
      = Fint b a c 0 c b * Finvint a a b b c 0 := by
  decide

theorem bartlettF (a b c : Fin 4) :
    (F a b c ⟨0, h0⟩ c a * Finv b b a a c ⟨0, h0⟩) *
        (F a b c ⟨0, h0⟩ c a * F b c a ⟨0, h0⟩ a b * F c a b ⟨0, h0⟩ b c)
      = F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ := by
  simp only [F_eq_Fint, Finv_eq_Finvint]
  push_cast
  exact_mod_cast bartlettF_int a b c

theorem bartlettD_int : ∀ a b c : Fin 4, 0 < N a b c →
    Fint b a c 0 c b * Finvint a a b b c 0 ≠ 0 := by
  decide

theorem bartlettD_ne_zero (a b c : Fin 4) (h : 0 < N a b c) :
    F b a c ⟨0, h0⟩ c b * Finv a a b b c ⟨0, h0⟩ ≠ 0 := by
  simp only [F_eq_Fint, Finv_eq_Finvint]
  push_cast
  intro h0'
  have hZ := bartlettD_int a b c h
  apply hZ
  exact_mod_cast h0'

theorem bartlett (a b c : Fin 4) (h : 0 < N a b c) :
    derivedJGen systemH a b c * FusionCategory.apexMonodromy systemH h0 c a b = 1 := by
  have hd : ∀ i : Fin 4, systemH.ring.dual i = i := fun i => rfl
  have hev : ∀ i : Fin 4, systemH.ev i = 1 := fun _ => rfl
  have hmain := FusionCategory.derivedJGen_mul_apexMonodromy systemH h0 hd hev a b c
    (bartlettD_ne_zero h0 a b c h) (bartlettF h0 a b c)
  simpa only [hd c] using hmain

end FusionCategory.Z2SqH
