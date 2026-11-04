/-
WP2 round 3, member m8, direction D8 (the adversarial audit).

# The battery's data bridge

`battery.py` re-implements the canonical scaffold's definitions
(`Recon.lean`'s `blockDiag`, `ReconTensor`'s `tensorHom`/`TensorIdx`,
`ReconAssoc`'s `assocEntry`/`assocInvEntry`, `ReconRigid`'s `ev`/`coev`/unitors,
`ReconSnake`'s snake composites) and runs the frozen statements on numeric data.
A numeric check is only as good as the numbers: hand-transcribing the `F`-tables
of five fusion systems invites silent error, and a typo would read as a defect
of the derivation.

This file removes the hand transcription.  It

* dumps, by `#eval`, the *computable* definition of each datum's data
  (`N`, `dual`, `F`, `Finv`, `ev`, `coev`, and the `ℚ(√d)` pair encodings used by
  the `ℝ`-valued instances), and
* states, as kernel-checked `example`s, that the dumped function *is* the field
  of the `FusionSystem` (`rfl`, because the instances are defined from the pair
  functions by `ZP.zval`),

so the Python tables are the Lean data, not a copy of it.

Run: `LEAN_PATH=... lean Bridge.lean > bridge.out`; `battery.py` parses
`bridge.out` and refuses to run if a table it uses is not in it.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/
import FusionCategory.Examples.FibonacciIsing
import FusionCategory.Examples.YangLee
import FusionCategory.Examples.Z2SqHonest
import FusionCategory.Examples.VecZ2Twisted
import FusionCategory.System

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FusionBattery

open FusionCategory

/-! ## Dumpers (one per arity/shape; nothing clever) -/

def dumpN (m : ℕ) (tag : String) (f : Fin m → Fin m → Fin m → ℕ) : IO Unit := do
  for a in List.finRange m do
    for b in List.finRange m do
      for c in List.finRange m do
        IO.println s!"{tag} {a.val} {b.val} {c.val} {f a b c}"

def dumpQ6 (m : ℕ) (tag : String) (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → ℚ) :
    IO Unit := do
  for a in List.finRange m do
    for b in List.finRange m do
      for c in List.finRange m do
        for d in List.finRange m do
          for e in List.finRange m do
            for g in List.finRange m do
              IO.println s!"{tag} {a.val} {b.val} {c.val} {d.val} {e.val} {g.val} {f a b c d e g}"

def dumpQ1 (m : ℕ) (tag : String) (f : Fin m → ℚ) : IO Unit := do
  for a in List.finRange m do
    IO.println s!"{tag} {a.val} {f a}"

def dumpFin1 (m : ℕ) (tag : String) (f : Fin m → Fin m) : IO Unit := do
  for a in List.finRange m do
    IO.println s!"{tag} {a.val} {(f a).val}"

def dumpFin2 (m : ℕ) (tag : String) (f : Fin m → Fin m → Fin m) : IO Unit := do
  for a in List.finRange m do
    for b in List.finRange m do
      IO.println s!"{tag} {a.val} {b.val} {(f a b).val}"

def dumpZ3 (m : ℕ) (tag : String) (f : Fin m → Fin m → Fin m → ℤ) : IO Unit := do
  for a in List.finRange m do
    for b in List.finRange m do
      for c in List.finRange m do
        IO.println s!"{tag} {a.val} {b.val} {c.val} {f a b c}"

def dumpP1 (m : ℕ) (tag : String) (f : Fin m → ℤ × ℤ) : IO Unit := do
  for a in List.finRange m do
    IO.println s!"{tag} {a.val} {(f a).1} {(f a).2}"

def dumpP6 (m : ℕ) (tag : String)
    (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → ℤ × ℤ) : IO Unit := do
  for a in List.finRange m do
    for b in List.finRange m do
      for c in List.finRange m do
        for d in List.finRange m do
          for e in List.finRange m do
            for g in List.finRange m do
              IO.println s!"{tag} {a.val} {b.val} {c.val} {d.val} {e.val} {g.val} \
                {(f a b c d e g).1} {(f a b c d e g).2}"

/-! ## `Vec_{Z/2}`: the trivial and the non-trivial cocycle (`ℚ`-valued, computable) -/

#eval dumpN 2 "VECZ2.N" VecZ2.system.ring.N
#eval dumpFin1 2 "VECZ2.dual" VecZ2.system.ring.dual
#eval dumpQ6 2 "VECZ2.F" VecZ2.system.F
#eval dumpQ6 2 "VECZ2.Finv" VecZ2.system.Finv
#eval dumpQ1 2 "VECZ2.ev" VecZ2.system.ev
#eval dumpQ1 2 "VECZ2.coev" VecZ2.system.coev

#eval dumpN 2 "VECZ2T.N" VecZ2Twisted.system.ring.N
#eval dumpFin1 2 "VECZ2T.dual" VecZ2Twisted.system.ring.dual
#eval dumpQ6 2 "VECZ2T.F" VecZ2Twisted.system.F
#eval dumpQ6 2 "VECZ2T.Finv" VecZ2Twisted.system.Finv
#eval dumpQ1 2 "VECZ2T.ev" VecZ2Twisted.system.ev
#eval dumpQ1 2 "VECZ2T.coev" VecZ2Twisted.system.coev

/-! ## Fibonacci, Ising, Yang–Lee: the `ℚ(√d)` pair encodings (`ℝ`-valued systems)

The instances are defined as `F := fun a b c d e f => ZP.zval s5 (Fpair a b c d e f)`
(and the analogous `coev`), so the pair functions below *are* the data; the
`example`s record the identification as `rfl`. -/

#eval dumpN 2 "FIB.N" Fibonacci.N
#eval dumpFin1 2 "FIB.dual" Fibonacci.dual
#eval dumpP6 2 "FIB.F" Fibonacci.Fpair
#eval dumpP6 2 "FIB.Finv" Fibonacci.FinvPair
#eval dumpP1 2 "FIB.ev" Fibonacci.evPair
#eval dumpP1 2 "FIB.coev" Fibonacci.coevPair

#eval dumpN 3 "ISING.N" Ising.N
#eval dumpFin1 3 "ISING.dual" Ising.dual
#eval dumpP6 3 "ISING.F" Ising.Fpair
#eval dumpP6 3 "ISING.Finv" Ising.FinvPair
#eval dumpP1 3 "ISING.ev" Ising.evPair
#eval dumpP1 3 "ISING.coev" Ising.coevPair

#eval dumpN 2 "YL.N" YangLee.N
#eval dumpFin1 2 "YL.dual" YangLee.dual
#eval dumpP6 2 "YL.F" YangLee.Fpair
#eval dumpP6 2 "YL.Finv" YangLee.FinvPair
#eval dumpP1 2 "YL.ev" YangLee.evPair
#eval dumpP1 2 "YL.coev" YangLee.coevPair

/-! ## `(Z/2)²` with the honest cocycle `ω(a,b,c) = (-1)^{a₁b₂c₁}`: `ℤ`/`Fin` tables

`F` is `ℝ`-valued, so it is not `#eval`-able; but it is `Fw w` with
`w = (wZ : ℝ)`, so `wZ` and `gadd` determine it exactly. -/

#eval dumpN 4 "Z2SQ.N" Z2SqH.system.ring.N
#eval dumpFin1 4 "Z2SQ.dual" Z2SqH.system.ring.dual
#eval dumpFin2 4 "Z2SQ.gadd" Z2SqH.gadd
#eval dumpZ3 4 "Z2SQ.wZ" Z2SqH.wZ

/-! ## The identifications (kernel-checked, `rfl`) -/

noncomputable section Ident
open FusionCategory.ZP

theorem fib_ring_N : ∀ a b c : Fin 2, Fibonacci.system.ring.N a b c = Fibonacci.N a b c :=
  fun _ _ _ => rfl
theorem fib_ring_dual : ∀ a : Fin 2, Fibonacci.system.ring.dual a = Fibonacci.dual a := fun _ => rfl
theorem ising_ring_N : ∀ a b c : Fin 3, Ising.system.ring.N a b c = Ising.N a b c := fun _ _ _ => rfl
theorem ising_ring_dual : ∀ a : Fin 3, Ising.system.ring.dual a = Ising.dual a := fun _ => rfl
theorem yl_ring_N : ∀ a b c : Fin 2, YangLee.system.ring.N a b c = YangLee.N a b c := fun _ _ _ => rfl
theorem yl_ring_dual : ∀ a : Fin 2, YangLee.system.ring.dual a = YangLee.dual a := fun _ => rfl

theorem fib_F : Fibonacci.system.F
    = fun a b c d e f => zval Fibonacci.s5 (Fibonacci.Fpair a b c d e f) := rfl
theorem fib_Finv : Fibonacci.system.Finv
    = fun a b c d f e => zval Fibonacci.s5 (Fibonacci.FinvPair a b c d f e) := rfl
example (i : Fin 2) : Fibonacci.system.ev i = zval Fibonacci.s5 (Fibonacci.evPair i) := rfl
example (i : Fin 2) : Fibonacci.system.coev i = zval Fibonacci.s5 (Fibonacci.coevPair i) := rfl

theorem ising_F : Ising.system.F
    = fun a b c d e f => zval Ising.s2 (Ising.Fpair a b c d e f) := rfl
theorem ising_Finv : Ising.system.Finv
    = fun a b c d f e => zval Ising.s2 (Ising.FinvPair a b c d f e) := rfl
example (i : Fin 3) : Ising.system.ev i = zval Ising.s2 (Ising.evPair i) := rfl
example (i : Fin 3) : Ising.system.coev i = zval Ising.s2 (Ising.coevPair i) := rfl

theorem yl_F : YangLee.system.F
    = fun a b c d e f => zval YangLee.s5 (YangLee.Fpair a b c d e f) := rfl
theorem yl_Finv : YangLee.system.Finv
    = fun a b c d f e => zval YangLee.s5 (YangLee.FinvPair a b c d f e) := rfl
example (i : Fin 2) : YangLee.system.ev i = zval YangLee.s5 (YangLee.evPair i) := rfl
example (i : Fin 2) : YangLee.system.coev i = zval YangLee.s5 (YangLee.coevPair i) := rfl

theorem z2sq_F : Z2SqH.system.F
    = fun a b c d e f => Z2SqH.Fw Z2SqH.w a b c d e f := rfl
theorem z2sq_Finv : Z2SqH.system.Finv
    = fun a b c d f e => Z2SqH.Fw Z2SqH.w a b c d e f := rfl
example (i : Fin 4) : Z2SqH.system.coev i = Z2SqH.w i i i := rfl
example (i : Fin 4) : Z2SqH.system.ev i = 1 := rfl

end Ident

#print axioms FusionBattery.dumpN
#print axioms FusionBattery.dumpP6
#print axioms FusionBattery.fib_ring_N
#print axioms FusionBattery.fib_ring_dual
#print axioms FusionBattery.fib_F
#print axioms FusionBattery.fib_Finv
#print axioms FusionBattery.ising_ring_N
#print axioms FusionBattery.ising_ring_dual
#print axioms FusionBattery.ising_F
#print axioms FusionBattery.ising_Finv
#print axioms FusionBattery.yl_ring_N
#print axioms FusionBattery.yl_ring_dual
#print axioms FusionBattery.yl_F
#print axioms FusionBattery.yl_Finv
#print axioms FusionBattery.z2sq_F
#print axioms FusionBattery.z2sq_Finv


end FusionBattery
