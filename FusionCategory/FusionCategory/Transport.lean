import FusionCategory.Statements
import FusionCategory.Examples.YangLee

/-!
# D8 — scalar transport of skeletal fusion systems, and the `ℂ` instance battery

One file, two layers, because a Lean file outside the package cannot be `import`ed as a
module (imports resolve in `LEAN_PATH`, and the package's build directory is not mine to
write): §1 is `Transport.mapSystem`, §2 is the battery.

## §1 — `mapSystem`

`mapSystem f S` pushes a `FusionSystem` over `k` forward along a ring homomorphism
`f : k →+* K` between fields.  The fusion ring and multiplicity-freeness carry no scalars and
are kept unchanged; every scalar field — the associator `F` and its inverse `Finv`, the
duality data `ev`, `coev` and the twist `J` — is mapped through `f`.

Because `k` and `K` are fields, `f` is injective (`RingHom.injective`, via
`DivisionRing.isSimpleRing`), so the nonzero side conditions `ev_ne_zero`, `coev_ne_zero`,
`J_ne_zero` transport too — the only place injectivity is used.  Every axiom is discharged
uniformly: apply `congrArg f` to the source axiom and push `f` through `∑`, `*`, `0`, `1` and
the `if d = f then 1 else 0` normalisations.

## §2 — the `ℂ` instance battery

`VecZ2R`, `FibonacciC`, `IsingC`, `YangLeeC` are the scalar copies of the landed examples, and
the battery proves `IsPseudoUnitaryC` for the `ℂ` Fibonacci and Ising copies and its
refutation for the `ℂ` Yang–Lee copy.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

/-!
# D8 — scalar transport of skeletal fusion systems

`mapSystem f S` pushes a `FusionSystem` over `k` forward along a ring homomorphism
`f : k →+* K` between fields.  The fusion ring and multiplicity-freeness carry no scalars and
are kept unchanged; every scalar field — the associator `F` and its inverse `Finv`, the
duality data `ev`, `coev` and the twist `J` — is mapped through `f`.

This is the base of the `ℂ` instance battery: `Fibonacci`, `Ising`, Yang–Lee and
`Vec_{Z/2}` are all built over `ℝ` (resp. `ℚ`), and the `ℂ` copies the analytic chain
consumes are their images under `algebraMap ℝ ℂ` (resp. `algebraMap ℚ ℝ`).

Because `k` and `K` are fields, `f` is injective (`RingHom.injective`, via
`DivisionRing.isSimpleRing`), so the nonzero side conditions `ev_ne_zero`, `coev_ne_zero`,
`J_ne_zero` transport as well — that is the only place injectivity is used.

The axioms are discharged uniformly: apply `congrArg f` to the source axiom and push `f`
through `∑`, `*`, `0`, `1` and the `if d = f then 1 else 0` normalisations.

Axiom budget: `[propext, Classical.choice, Quot.sound]`.
-/

universe u

namespace FusionCategory

namespace Transport

variable {n : ℕ} {k K : Type u} [Field k] [Field K]

/-- **Scalar extension** of a skeletal fusion system along a ring homomorphism
`f : k →+* K` between fields. -/
def mapSystem (f : k →+* K) (S : FusionSystem n k) : FusionSystem n K where
  ring := S.ring
  mult_free := S.mult_free
  F := fun a b c d e g => f (S.F a b c d e g)
  F_support := by
    intro a b c d e g h
    rw [S.F_support a b c d e g h, map_zero]
  pentagon := by
    intro a b c d e i j r x
    have h := congrArg f (S.pentagon a b c d e i j r x)
    simpa only [map_sum, map_mul] using h
  F_unit_left := by
    intro hn b c d g hN
    have h := congrArg f (S.F_unit_left hn b c d g hN)
    simpa only [apply_ite ⇑f, map_one, map_zero] using h
  F_unit_right := by
    intro hn a b d e hN
    have h := congrArg f (S.F_unit_right hn a b d e hN)
    simpa only [apply_ite ⇑f, map_one, map_zero] using h
  Finv := fun a b c d g e => f (S.Finv a b c d g e)
  Finv_support := by
    intro a b c d g e h
    rw [S.Finv_support a b c d g e h, map_zero]
  Finv_comp := by
    intro a b c d f' g h1 h2 h3 h4
    have h := congrArg f (S.Finv_comp a b c d f' g h1 h2 h3 h4)
    simpa only [map_sum, map_mul, apply_ite ⇑f, map_one, map_zero] using h
  F_comp_inv := by
    intro a b c d e' e h1 h2 h3 h4
    have h := congrArg f (S.F_comp_inv a b c d e' e h1 h2 h3 h4)
    simpa only [map_sum, map_mul, apply_ite ⇑f, map_one, map_zero] using h
  ev := fun i => f (S.ev i)
  coev := fun i => f (S.coev i)
  ev_ne_zero := fun i => (map_ne_zero f).mpr (S.ev_ne_zero i)
  coev_ne_zero := fun i => (map_ne_zero f).mpr (S.coev_ne_zero i)
  snake_left := by
    intro hn i
    have h := congrArg f (S.snake_left hn i)
    simpa only [map_mul, map_one] using h
  snake_right := by
    intro hn i
    have h := congrArg f (S.snake_right hn i)
    simpa only [map_mul, map_one] using h
  ev_dual := fun i => congrArg f (S.ev_dual i)
  J := fun i j kk => f (S.J i j kk)
  J_ne_zero := fun i j kk hN => (map_ne_zero f).mpr (S.J_ne_zero i j kk hN)
  J_unit_left := by
    intro hn j
    exact congrArg f (S.J_unit_left hn j) |>.trans (map_one f)
  J_unit_right := by
    intro hn i
    exact congrArg f (S.J_unit_right hn i) |>.trans (map_one f)
  J_dual := by
    intro hn i
    exact congrArg f (S.J_dual hn i) |>.trans (map_one f)
  J_coherent := by
    intro a b c d e g h1 h2 h3 h4
    have h := congrArg f (S.J_coherent a b c d e g h1 h2 h3 h4)
    simpa only [map_mul] using h

/-! ## Projection lemmas

Every field of `mapSystem f S` reduces definitionally, which is what makes `kappa` and the
pseudo-unitarity transport below one-liners. -/

@[simp] theorem mapSystem_ring (f : k →+* K) (S : FusionSystem n k) :
    (mapSystem f S).ring = S.ring := rfl

@[simp] theorem mapSystem_F (f : k →+* K) (S : FusionSystem n k) (a b c d e g : Fin n) :
    (mapSystem f S).F a b c d e g = f (S.F a b c d e g) := rfl

@[simp] theorem mapSystem_ev (f : k →+* K) (S : FusionSystem n k) (i : Fin n) :
    (mapSystem f S).ev i = f (S.ev i) := rfl

@[simp] theorem mapSystem_coev (f : k →+* K) (S : FusionSystem n k) (i : Fin n) :
    (mapSystem f S).coev i = f (S.coev i) := rfl

@[simp] theorem mapSystem_J (f : k →+* K) (S : FusionSystem n k) (i j kk : Fin n) :
    (mapSystem f S).J i j kk = f (S.J i j kk) := rfl

/-- **The κ sanity law**: the duality normalisation transports, `κ_i ↦ f (κ_i)`.  Both
inputs (`coev`, `ev`) are multiplicative data, so this is `map_mul` and nothing else. -/
@[simp] theorem mapSystem_kappa (f : k →+* K) (S : FusionSystem n k) (i : Fin n) :
    (mapSystem f S).kappa i = f (S.kappa i) := by
  rw [FusionSystem.kappa, FusionSystem.kappa, mapSystem_coev, mapSystem_ev, ← map_mul]

/-- The global-dimension equation of the `κ`'s transports: the ℂ-side sum is the image of
the `k`-side sum.  This is what turns `IsPseudoUnitary` into `IsPseudoUnitaryC`. -/
theorem sum_kappa_map (f : k →+* K) (S : FusionSystem n k) :
    (∑ i : Fin n,
        (mapSystem f S).kappa i * (mapSystem f S).kappa ((mapSystem f S).ring.dual i))
      = f (∑ i : Fin n, S.kappa i * S.kappa (S.ring.dual i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mapSystem_kappa, mapSystem_kappa, mapSystem_ring, ← map_mul]

/-! ## Transport of the signature's normalisations

The `ev_dual` gauge, the triangle law and the retained-`F` coherence form are equations over
the scalar field, so they transport along any ring hom: this is the check that the corrected
signature of B1–B4 is stable under scalar extension. -/

theorem mapSystem_EvDual {m : ℕ} {k K : Type u} [Field k] [Field K] (f : k →+* K)
    {S : FusionSystem m k} (h : EvDual S) : EvDual (mapSystem f S) :=
  fun i => congrArg f (h i)

theorem mapSystem_TriangleLaw {m : ℕ} {k K : Type u} [Field k] [Field K] (f : k →+* K)
    {S : FusionSystem m k} (h : TriangleLaw S) : TriangleLaw (mapSystem f S) := by
  intro hn a c d hN
  have hh := congrArg f (h hn a c d hN)
  simpa only [mapSystem_F, map_one] using hh

theorem mapSystem_retained {m : ℕ} {k K : Type u} [Field k] [Field K] (f : k →+* K)
    {S : FusionSystem m k} (h : J_coherent_retained S) :
    J_coherent_retained (mapSystem f S) := by
  intro a b c d e g h1 h2 h3 h4
  have hh := congrArg f (h a b c d e g h1 h2 h3 h4)
  simpa only [mapSystem_J, mapSystem_F, map_mul] using hh

theorem mapSystem_qualified {m : ℕ} {k K : Type u} [Field k] [Field K] (f : k →+* K)
    {S : FusionSystem m k} (h : J_coherent_qualified S) :
    J_coherent_qualified (mapSystem f S) := by
  intro a b c d e g h1 h2 h3 h4 hF
  have hF' : S.F a b c d e g ≠ 0 := fun hz => hF (by simp [hz])
  simpa only [mapSystem_J, map_mul] using congrArg f (h a b c d e g h1 h2 h3 h4 hF')

end Transport

namespace Transport

/-- **Pseudo-unitarity transports from `ℝ` to `ℂ`**: the global-dimension equation
`Σ_i κ_i κ_{i*} = FPdim(C)` is an equation between real numbers read in `ℂ`, and both sides
are images of the `ℝ` sides under `algebraMap ℝ ℂ`. -/
theorem isPseudoUnitaryC_of_algebraMap {n : ℕ} {S : FusionSystem n ℝ} (hFP : S.ring.FPData)
    (h : IsPseudoUnitary S hFP) :
    IsPseudoUnitaryC (mapSystem (algebraMap ℝ ℂ) S) hFP := by
  unfold IsPseudoUnitaryC IsPseudoUnitary at *
  rw [sum_kappa_map, h]
  rfl

/-- The same for an arbitrary characterisation of `κ` by the `FP`-dimensions: if `κ` *is*
the FP-dimension, pseudo-unitarity is immediate (`hFP.dual_eq` kills the dual and `sq`
absorbs the product). -/
theorem isPseudoUnitary_of_kappa_eq_fpdim {n : ℕ} {S : FusionSystem n ℝ}
    (hFP : S.ring.FPData) (hκ : ∀ i : Fin n, S.kappa i = hFP.fpdim i) :
    IsPseudoUnitary S hFP := by
  unfold IsPseudoUnitary FusionRing.FPData.globalDim
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hκ i, hκ (S.ring.dual i), hFP.dual_eq i, sq]

end Transport

namespace Transport

variable {n : ℕ} {k K : Type u} [Field k] [Field K]

/-! ## Transport of pivotal structures

A pivotal structure is a family of nonzero scalars, so it pushes forward along any ring hom;
monoidality is the same equation read in `K`.  Consequently `dim` transports, sphericity
transports, and so does `ENO823`. -/

/-- Push a pivotal structure along `f : k →+* K`: the scalars are the images of the `p i`. -/
def mapPivotal (f : k →+* K) {S : FusionSystem n k} (P : PivotalStructure S) :
    PivotalStructure (mapSystem f S) where
  p := fun i => Units.map f.toMonoidHom (P.p i)
  p_unit := by
    intro hn
    apply Units.ext
    show f (P.pVal ⟨0, hn⟩) = 1
    rw [P.pVal_unit hn, map_one]
  p_mon := by
    intro i j kk hN
    show f (P.pVal kk) = f (S.J i j kk) * f (P.pVal i) * f (P.pVal j)
    rw [← map_mul, ← map_mul]
    exact congrArg f (P.p_mon i j kk hN)

/-- The dimension function of the pushed-forward pivotal structure is the image of the
original one. -/
theorem mapPivotal_dim (f : k →+* K) {S : FusionSystem n k} (P : PivotalStructure S)
    (i : Fin n) : dim (mapPivotal f P) i = f (dim P i) := by
  show f (P.pVal i) * (mapSystem f S).kappa i = f (P.pVal i * S.kappa i)
  rw [mapSystem_kappa, map_mul]

/-- Sphericity transports. -/
theorem mapPivotal_isSpherical (f : k →+* K) {S : FusionSystem n k} (P : PivotalStructure S)
    (h : P.IsSpherical) : (mapPivotal f P).IsSpherical := by
  intro i
  show dim (mapPivotal f P) (S.ring.dual i) = dim (mapPivotal f P) i
  rw [mapPivotal_dim, mapPivotal_dim, h i]

/-- **`ENO823` transports from `ℝ` to `ℂ`**: a spherical pivotal structure whose dimensions
are the `FP`-dimensions gives one over `ℂ` with dimensions the images of those. -/
theorem eno823_of_algebraMap {n : ℕ} {S : FusionSystem n ℝ} (hFP : S.ring.FPData)
    (h : ENO823 S hFP) : ENO823 (mapSystem (algebraMap ℝ ℂ) S) hFP := by
  obtain ⟨P, hsp, hdim⟩ := h
  refine ⟨mapPivotal (algebraMap ℝ ℂ) P, mapPivotal_isSpherical _ P hsp, fun i => ?_⟩
  rw [mapPivotal_dim, hdim i]
  simp

end Transport

namespace Transported

/-! ## The scalar copies -/

/-- `Vec_{Z/2}` with the trivial cocycle, over `ℝ`. -/
noncomputable abbrev VecZ2R : FusionSystem 2 ℝ :=
  Transport.mapSystem (algebraMap ℚ ℝ) VecZ2.system

/-- The Fibonacci system over `ℂ`. -/
noncomputable abbrev FibonacciC : FusionSystem 2 ℂ :=
  Transport.mapSystem (algebraMap ℝ ℂ) FibonacciSystem

/-- The Ising system over `ℂ`. -/
noncomputable abbrev IsingC : FusionSystem 3 ℂ :=
  Transport.mapSystem (algebraMap ℝ ℂ) IsingSystem

/-- The Yang–Lee system over `ℂ`. -/
noncomputable abbrev YangLeeC : FusionSystem 2 ℂ :=
  Transport.mapSystem (algebraMap ℝ ℂ) YangLee.system

/-! ## `FPData` for the rings the systems carry

`FPdimFibonacci` and `FPdimIsing` are the Perron–Frobenius dimensions of the systems'
own fusion rings; every field but `eigenvector` is a case split, and the eigenvector
equation at `(τ, τ)` is `1 + φ = φ²`, resp. `1 + 1 = (√2)²`. -/

/-- The Fibonacci system carries the Fibonacci ring, definitionally. -/
@[simp] theorem fibonacciSystem_ring : FibonacciSystem.ring = Fibonacci.ring := rfl

/-- The Fibonacci ring's structure constants, definitionally. -/
@[simp] theorem fibonacci_ring_N (a b c : Fin 2) :
    Fibonacci.ring.N a b c = Fibonacci.N a b c := rfl

theorem fibonacciFPData_dual (i : Fin 2) :
    FPdimFibonacci (Fibonacci.ring.dual i) = FPdimFibonacci i := by
  fin_cases i <;> rfl

/-- The Perron–Frobenius data of the Fibonacci system: `FPdim = 1, φ`. -/
noncomputable def fibonacciFPData : FibonacciSystem.ring.FPData where
  fpdim := FPdimFibonacci
  pos := by
    intro i
    fin_cases i <;> simp [FPdimFibonacci] <;> linarith [Real.sqrt_nonneg 5]
  unit_one := by
    intro hn
    simp [FPdimFibonacci]
  eigenvector := by
    intro i kk
    fin_cases i <;> fin_cases kk <;>
      simp [Fibonacci.N, FPdimFibonacci, Fin.sum_univ_two]
    all_goals nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  dual_eq := fibonacciFPData_dual

/-- The Ising system carries the Ising ring, definitionally. -/
@[simp] theorem isingSystem_ring : IsingSystem.ring = Ising.ring := rfl

/-- The Ising ring's structure constants, definitionally. -/
@[simp] theorem ising_ring_N (a b c : Fin 3) :
    Ising.ring.N a b c = Ising.N a b c := rfl

theorem isingFPData_dual (i : Fin 3) :
    FPdimIsing (Ising.ring.dual i) = FPdimIsing i := by
  fin_cases i <;> rfl

/-- The Perron–Frobenius data of the Ising system: `FPdim = 1, √2, 1`. -/
noncomputable def isingFPData : IsingSystem.ring.FPData where
  fpdim := FPdimIsing
  pos := by
    intro i
    fin_cases i <;> simp [FPdimIsing]
  unit_one := by
    intro hn
    simp [FPdimIsing]
  eigenvector := by
    intro i kk
    fin_cases i <;> fin_cases kk <;>
      simp [Ising.N, FPdimIsing, Fin.sum_univ_three]
    all_goals norm_num
  dual_eq := isingFPData_dual

/-! ## The battery: pseudo-unitarity over `ℝ` and over `ℂ` -/

/-- Fibonacci is pseudo-unitary over `ℝ`: `κ` is the FP-dimension. -/
theorem isPseudoUnitary_fibonacci : IsPseudoUnitary FibonacciSystem fibonacciFPData :=
  Transport.isPseudoUnitary_of_kappa_eq_fpdim fibonacciFPData fun i => by
    rw [FibonacciSystem_kappa]
    rfl

/-- Ising is pseudo-unitary over `ℝ`. -/
theorem isPseudoUnitary_ising : IsPseudoUnitary IsingSystem isingFPData :=
  Transport.isPseudoUnitary_of_kappa_eq_fpdim isingFPData fun i => by
    rw [IsingSystem_kappa]
    rfl

/-- **The `ℂ` Fibonacci copy is pseudo-unitary.** -/
theorem isPseudoUnitaryC_fibonacci : IsPseudoUnitaryC FibonacciC fibonacciFPData :=
  Transport.isPseudoUnitaryC_of_algebraMap fibonacciFPData isPseudoUnitary_fibonacci

/-- **The `ℂ` Ising copy is pseudo-unitary.** -/
theorem isPseudoUnitaryC_ising : IsPseudoUnitaryC IsingC isingFPData :=
  Transport.isPseudoUnitaryC_of_algebraMap isingFPData isPseudoUnitary_ising

/-- **The `ℂ` Yang–Lee copy is *not* pseudo-unitary**: its categorical global dimension is
`1 + 1/φ²` while the Perron–Frobenius one is `1 + φ²`.  The refutation transports from
`YangLee.not_pseudoUnitary` because `algebraMap ℝ ℂ` is injective. -/
theorem not_isPseudoUnitaryC_yangLee :
    ¬ IsPseudoUnitaryC YangLeeC Examples.FibonacciFPData := by
  intro h
  apply YangLee.not_pseudoUnitary
  unfold IsPseudoUnitaryC at h
  unfold IsPseudoUnitary
  rw [Transport.sum_kappa_map] at h
  exact Complex.ofReal_injective h

/-- The transported `κ` law at the `ℂ` copies, recorded as the sanity check that the
`ℝ`-valued `κ`'s are the images of one another. -/
theorem kappa_fibonacciC (i : Fin 2) : FibonacciC.kappa i = (FibonacciSystem.kappa i : ℂ) :=
  Transport.mapSystem_kappa (algebraMap ℝ ℂ) FibonacciSystem i

/-- `κ` of the `ℝ` copy of `Vec_{Z/2}` is `1` at both labels: the `ℚ → ℝ` transport does
nothing to the duality normalisation. -/
theorem kappa_VecZ2R (i : Fin 2) : VecZ2R.kappa i = 1 := by
  rw [Transport.mapSystem_kappa]
  simp [FusionSystem.kappa, VecZ2.system]

/-! ## `ENO823` at the `ℂ` copies

The conclusions of the conditional theorem, instantiated at the two pseudo-unitary copies:
the transported pivotal structure `p ≡ 1` is spherical with the `FP`-dimensions, read in `ℂ`.
This is the non-vacuity witness for the `ℂ` statements, and it comes from the landed `ℝ`
facts by `eno823_of_algebraMap` — no analytic input beyond `ℝ` is used. -/

/-- The ℝ Fibonacci system satisfies `ENO823` for its trivial pivotal structure. -/
theorem eno823_fibonacci : ENO823 FibonacciSystem fibonacciFPData :=
  ⟨FibonacciPivotal, FibonacciSystem_spherical, fun i => FibonacciSystem_dim i⟩

/-- The ℝ Ising system satisfies `ENO823`. -/
theorem eno823_ising : ENO823 IsingSystem isingFPData :=
  ⟨IsingPivotal, IsingSystem_spherical, fun i => IsingSystem_dim i⟩

/-- **`ENO823` holds for the `ℂ` Fibonacci copy.** -/
theorem eno823_fibonacciC : ENO823 FibonacciC fibonacciFPData :=
  Transport.eno823_of_algebraMap fibonacciFPData eno823_fibonacci

/-- **`ENO823` holds for the `ℂ` Ising copy.** -/
theorem eno823_isingC : ENO823 IsingC isingFPData :=
  Transport.eno823_of_algebraMap isingFPData eno823_ising

end Transported

end FusionCategory

#print axioms FusionCategory.Transport.mapSystem
#print axioms FusionCategory.Transport.mapSystem_kappa
#print axioms FusionCategory.Transport.sum_kappa_map
#print axioms FusionCategory.Transport.mapSystem_EvDual
#print axioms FusionCategory.Transport.mapSystem_TriangleLaw
#print axioms FusionCategory.Transport.mapSystem_retained
#print axioms FusionCategory.Transport.mapSystem_qualified
#print axioms FusionCategory.Transport.isPseudoUnitaryC_of_algebraMap
#print axioms FusionCategory.Transport.isPseudoUnitary_of_kappa_eq_fpdim
#print axioms FusionCategory.Transported.fibonacciFPData_dual
#print axioms FusionCategory.Transported.isingFPData_dual
#print axioms FusionCategory.Transported.fibonacciFPData
#print axioms FusionCategory.Transported.isingFPData
#print axioms FusionCategory.Transported.isPseudoUnitary_fibonacci
#print axioms FusionCategory.Transported.isPseudoUnitary_ising
#print axioms FusionCategory.Transported.isPseudoUnitaryC_fibonacci
#print axioms FusionCategory.Transported.isPseudoUnitaryC_ising
#print axioms FusionCategory.Transported.not_isPseudoUnitaryC_yangLee
#print axioms FusionCategory.Transport.mapPivotal
#print axioms FusionCategory.Transport.mapPivotal_dim
#print axioms FusionCategory.Transport.mapPivotal_isSpherical
#print axioms FusionCategory.Transport.eno823_of_algebraMap
#print axioms FusionCategory.Transported.kappa_fibonacciC
#print axioms FusionCategory.Transported.kappa_VecZ2R
#print axioms FusionCategory.Transported.eno823_fibonacci
#print axioms FusionCategory.Transported.eno823_ising
#print axioms FusionCategory.Transported.eno823_fibonacciC
#print axioms FusionCategory.Transported.eno823_isingC
