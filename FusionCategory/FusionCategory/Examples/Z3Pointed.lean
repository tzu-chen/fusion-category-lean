import FusionCategory.System

/-!
# `Vec^ω_{Z/3}`: the witness with `i* ≠ i` is still owed

`System.lean` carries two witnesses: `Vec_{Z/2}` with the trivial cocycle
(`F ≡ 1`, `κ ≡ 1`) and with the non-trivial one (`F = −1` on the all-`g` block,
`κ g = −1`).  Both have `i* = i` for every simple, so neither can see the
difference between the two associator entries `F^{i i* i}_i(0,0)` and
`F^{i* i i*}_{i*}(0,0)` that the two snake equations involve — the difference
that the correction in `a8d6178` and the matrix-inverse correction of
`snake_right` are about.  A witness with `i* ≠ i` is owed, and this file records
what blocks it.

The obvious candidate is `Vec^ω_{Z/3}` for the non-trivial 3-cocycle, which is a
genuine fusion category and needs a cube root of unity:
`ω(a,b,c) = ζ^(a·⌊(b+c)/3⌋)` is a normalised cocycle (checked by hand and in
Python on all 81 quadruples), nontrivial (`ω(g,g²,g) = ζ`), and it satisfies the
cocycle identity that makes the two snakes consistent,
`ω(i,i*,i)·ω(i*,i,i*) = 1`, which forces `κ g = ω(g²,g,g²) = ζ²` and
`κ g² = ω(g,g²,g) = ζ`.

Two routes were tried and neither is finished:

* over `ℂ`, the identity `ζ² + ζ + 1 = 0` has to be fed to the arithmetic by
  hand, and neither `norm_num` nor `nlinarith` applies (`ℂ` is not ordered);
* over `ZMod 7`, where `ζ = 2` is a primitive cube root and every axiom is a
  *closed decidable* statement, the pentagon and the unit laws go through by
  `decide`, but `ZMod.decidableEq` gets stuck on the sums that the two inverse
  laws need (`Finv_comp`, `F_comp_inv`): the redex is
  `(↑(∑ e, ...)).beq ↑(if ...)`, and `decide` reports that it failed to reduce
  the instance rather than reducing to `true`.

The route that will work is the one `Examples/FibonacciIsing.lean` uses for
`ℚ(√5)` and `ℚ(√2)`: encode `ℚ(ζ) = ℚ(√−3)` as integer pairs `(p,q)` meaning
`p + qζ` with `ζ² = −1 − ζ`, prove that the map to `ℂ` (or to any field with a
primitive cube root of unity) is additive and multiplicative, and let `decide`
check every associator identity in `ℤ`.  The `zval`/`Zmul`/`peq` layer of that
file ports verbatim, with `zval` landing in `ℂ` instead of `ℝ`.

## Status of the multiplicity hypothesis (M) here

This file contains no `FusionSystem` inhabitant, so `DimMultiplicative`
(`DimMult.lean`) is not even *stateable* for `Vec^ω_{Z/3}`: there is no `system`
to apply it to (and `DimMult.lean` is downstream of `System.lean`, so the
hypothesis cannot be stated at the point where the witness would be built
either).  Once the datum exists, (M) is a check on it like any other, and for a
pointed category with `J ≡ 1` it reduces to multiplicativity of `κ`,
`Σ_c N a b c · κ_c = κ_a κ_b` — the form in which (M) is verified for
`Vec_{Z/2}` and `Vec^ω_{Z/2}` in `Examples/YangLee.lean` (`VecZ2.dimMult`,
`VecZ2Twisted.dimMult`); for the non-trivial `Z/3` cocycle the twist `J` is not
trivial and (M) would be a genuine additional test of the datum.

Axiom budget for whatever replaces this note: `[propext, Classical.choice,
Quot.sound]`, no `sorry`.
-/
