module

public import HaagerupIzumi.Analytic.GammaIdentities
public import HaagerupIzumi.Analytic.ResidueAlgebra
public import Mathlib.Topology.Algebra.Module.Cardinality
import all Mathlib.Data.Complex.Basic

/-!
# A concrete corrected contour for the four-gamma kernel

The starting line lies strictly to the left of both right-pole families and
avoids all left poles. Only finitely many left poles have crossed it. The
normalized corrected integral is consequently an explicit total definition;
its analytic characterizations require the convergence and no-pinch conditions.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation

namespace HaagerupIzumi.GammaK4Contour

/-- Poles of `gamma(c + z)`. -/
def leftFamily (a b : ℝ) (c : ℂ) : Set ℂ := {z | c + z ∈ poleLattice a b}

/-- Poles of `gamma(c - z)`. -/
def rightFamily (a b : ℝ) (c : ℂ) : Set ℂ := {z | c - z ∈ poleLattice a b}

lemma leftFamily_mem_iff (a b : ℝ) (c z : ℂ) :
    z ∈ leftFamily a b c ↔ ∃ m n : ℕ, z = -c - (m : ℂ) * a - (n : ℂ) * b := by
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by linear_combination h⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by ring⟩

lemma rightFamily_mem_iff (a b : ℝ) (c z : ℂ) :
    z ∈ rightFamily a b c ↔ ∃ m n : ℕ, z = c + (m : ℂ) * a + (n : ℂ) * b := by
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by linear_combination -h⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by ring⟩

lemma leftFamily_countable (a b : ℝ) (c : ℂ) : (leftFamily a b c).Countable := by
  apply ((poleLattice_countable a b).image (fun p : ℂ => p - c)).mono
  intro z hz
  exact ⟨c + z, hz, by ring⟩

lemma rightFamily_countable (a b : ℝ) (c : ℂ) : (rightFamily a b c).Countable := by
  apply ((poleLattice_countable a b).image (fun p : ℂ => c - p)).mono
  intro z hz
  exact ⟨c - z, hz, by ring⟩

lemma poleLattice_re_nonpos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {p : ℂ} (hp : p ∈ poleLattice a b) : p.re ≤ 0 := by
  obtain ⟨m, n, rfl⟩ := hp
  simp only [neg_re, add_re, mul_re, natCast_re, ofReal_re, natCast_im,
    ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (add_nonneg (mul_nonneg (Nat.cast_nonneg m) ha.le)
    (mul_nonneg (Nat.cast_nonneg n) hb.le))

lemma poleLattice_norm_eq_neg_re {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {p : ℂ} (hp : p ∈ poleLattice a b) : ‖p‖ = -p.re := by
  have him : p.im = 0 := by obtain ⟨m, n, rfl⟩ := hp; simp
  have heq : p = (p.re : ℂ) := by apply Complex.ext <;> simp [him]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (poleLattice_re_nonpos ha hb hp)]
  simp

lemma poleLattice_re_tail_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (B : ℝ) :
    {p ∈ poleLattice a b | B < p.re}.Finite := by
  apply (poleLattice_inter_finite ha hb (-B)).subset
  intro p hp
  refine ⟨hp.1, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, poleLattice_norm_eq_neg_re ha hb hp.1]
  linarith [hp.2]

lemma leftFamily_crossed_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c : ℂ) (σ : ℝ) : {z ∈ leftFamily a b c | σ < z.re}.Finite := by
  apply ((poleLattice_re_tail_finite ha hb (c.re + σ)).image (fun p : ℂ => p - c)).subset
  intro z hz
  refine ⟨c + z, ⟨hz.1, ?_⟩, by ring⟩
  simp only [add_re]
  linarith [hz.2]

lemma rightFamily_crossed_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c : ℂ) (σ : ℝ) : {z ∈ rightFamily a b c | z.re < σ}.Finite := by
  apply ((poleLattice_re_tail_finite ha hb (c.re - σ)).image (fun p : ℂ => c - p)).subset
  intro z hz
  refine ⟨c - z, ⟨hz.1, ?_⟩, by ring⟩
  simp only [sub_re]
  linarith [hz.2]

lemma rightFamily_re_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {c z : ℂ} (hz : z ∈ rightFamily a b c) : c.re ≤ z.re := by
  have h := poleLattice_re_nonpos ha hb hz
  simp only [sub_re] at h
  linarith

/-- The two families crossed on the left of a separating contour. -/
def leftPoles (a b : ℝ) (r s x : ℂ) : Set ℂ :=
  leftFamily a b (k4U a b r s) ∪ leftFamily a b (k4V a b r s + x)

/-- The two families crossed on the right of a separating contour. -/
def rightPoles (a b : ℝ) (r s x : ℂ) : Set ℂ :=
  rightFamily a b (k4U a b r s) ∪ rightFamily a b (k4V a b r s - x)

lemma leftPoles_countable (a b : ℝ) (r s x : ℂ) : (leftPoles a b r s x).Countable :=
  (leftFamily_countable a b _).union (leftFamily_countable a b _)

lemma rightPoles_countable (a b : ℝ) (r s x : ℂ) : (rightPoles a b r s x).Countable :=
  (rightFamily_countable a b _).union (rightFamily_countable a b _)

lemma leftPoles_crossed_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (r s x : ℂ) (σ : ℝ) : {z ∈ leftPoles a b r s x | σ < z.re}.Finite := by
  apply ((leftFamily_crossed_finite ha hb (k4U a b r s) σ).union
    (leftFamily_crossed_finite ha hb (k4V a b r s + x) σ)).subset
  rintro z ⟨hz | hz, hσ⟩
  · exact Or.inl ⟨hz, hσ⟩
  · exact Or.inr ⟨hz, hσ⟩

lemma rightPoles_crossed_finite {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (r s x : ℂ) (σ : ℝ) : {z ∈ rightPoles a b r s x | z.re < σ}.Finite := by
  apply ((rightFamily_crossed_finite ha hb (k4U a b r s) σ).union
    (rightFamily_crossed_finite ha hb (k4V a b r s - x) σ)).subset
  rintro z ⟨hz | hz, hσ⟩
  · exact Or.inl ⟨hz, hσ⟩
  · exact Or.inr ⟨hz, hσ⟩

lemma exists_startLine (a b : ℝ) (r s x : ℂ) :
    ∃ σ : ℝ, σ < min (k4U a b r s).re (k4V a b r s - x).re ∧
      ∀ z ∈ leftPoles a b r s x, z.re ≠ σ := by
  have hd := ((leftPoles_countable a b r s x).image Complex.re).dense_compl ℝ
  obtain ⟨σ, hσ, hlt⟩ := hd.exists_lt (min (k4U a b r s).re (k4V a b r s - x).re)
  refine ⟨σ, hlt, ?_⟩
  intro z hz heq
  exact hσ ⟨z, hz, heq⟩

/-- A fixed choice of initial vertical line. It has no right crossed poles. -/
def startLine (a b : ℝ) (r s x : ℂ) : ℝ := (exists_startLine a b r s x).choose

lemma startLine_spec (a b : ℝ) (r s x : ℂ) :
    startLine a b r s x < min (k4U a b r s).re (k4V a b r s - x).re ∧
      ∀ z ∈ leftPoles a b r s x, z.re ≠ startLine a b r s x :=
  (exists_startLine a b r s x).choose_spec

/-- A vertical line misses all four candidate pole families. -/
def AvoidsPoles (a b : ℝ) (r s x : ℂ) (σ : ℝ) : Prop :=
  ∀ z ∈ leftPoles a b r s x ∪ rightPoles a b r s x, z.re ≠ σ

lemma startLine_avoidsPoles {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r s x : ℂ) :
    AvoidsPoles a b r s x (startLine a b r s x) := by
  intro z hz
  rcases hz with hz | hz
  · exact (startLine_spec a b r s x).2 z hz
  · have hσ := (startLine_spec a b r s x).1
    rcases hz with hz | hz
    · have hz' := rightFamily_re_ge ha hb hz
      have hσ' := lt_of_lt_of_le hσ (min_le_left _ _)
      linarith
    · have hz' := rightFamily_re_ge ha hb hz
      have hσ' := lt_of_lt_of_le hσ (min_le_right _ _)
      linarith

/-- Finite sets deduplicate coincident poles of the same orientation. Their
multiplicity is retained by the generalized residue of the full kernel. -/
def crossedLeft (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x : ℂ) (σ : ℝ) : Finset ℂ :=
  (leftPoles_crossed_finite (lt_of_lt_of_le hb hba) hb r s x σ).toFinset

def crossedRight (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x : ℂ) (σ : ℝ) : Finset ℂ :=
  (rightPoles_crossed_finite (lt_of_lt_of_le hb hba) hb r s x σ).toFinset

@[simp] lemma mem_crossedLeft (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) (z : ℂ) :
    z ∈ crossedLeft a b hb hba r s x σ ↔ z ∈ leftPoles a b r s x ∧ σ < z.re := by
  simp [crossedLeft]

@[simp] lemma mem_crossedRight (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (r s x : ℂ) (σ : ℝ) (z : ℂ) :
    z ∈ crossedRight a b hb hba r s x σ ↔ z ∈ rightPoles a b r s x ∧ z.re < σ := by
  simp [crossedRight]

lemma crossedRight_startLine (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x : ℂ) :
    crossedRight a b hb hba r s x (startLine a b r s x) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hzlt⟩ := (mem_crossedRight a b hb hba r s x _ z).mp hz
  have hσ := (startLine_spec a b r s x).1
  rcases hz with hz | hz
  · have hz' := rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
    have hσ' := lt_of_lt_of_le hσ (min_le_left _ _)
    linarith
  · have hz' := rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
    have hσ' := lt_of_lt_of_le hσ (min_le_right _ _)
    linarith

/-- The four-gamma integrand uses the constructed gamma function. -/
def kernel (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y : ℂ) : ℂ → ℂ :=
  k4Integrand (gamma a b hb hba) a b r s x y

/-- The corrected four-gamma contour, normalized as in Section 7.2. -/
def K4 (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y : ℂ) : ℂ :=
  CorrectedContour.value (kernel a b hb hba r s x y) (startLine a b r s x)
    (crossedLeft a b hb hba r s x (startLine a b r s x)) ∅ /
      (I * (Real.sqrt (a * b) : ℂ))

lemma K4_startLine (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (r s x y : ℂ) :
    CorrectedContour.value (kernel a b hb hba r s x y) (startLine a b r s x)
      (crossedLeft a b hb hba r s x (startLine a b r s x)) ∅ =
        I * (Real.sqrt (a * b) : ℂ) * K4 a b hb hba r s x y := by
  have hs : (Real.sqrt (a * b) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hb hba) hb)).ne'
  unfold K4
  field_simp

lemma poleLattice_add {a b : ℝ} {u v : ℂ} (hu : u ∈ poleLattice a b)
    (hv : v ∈ poleLattice a b) : u + v ∈ poleLattice a b := by
  obtain ⟨m, n, rfl⟩ := hu
  obtain ⟨p, q, rfl⟩ := hv
  refine ⟨m + p, n + q, ?_⟩
  push_cast
  ring

lemma families_disjoint {a b : ℝ} {c d : ℂ} (hcd : c + d ∉ poleLattice a b) :
    Disjoint (leftFamily a b c) (rightFamily a b d) := by
  rw [Set.disjoint_left]
  intro z hz hd
  apply hcd
  convert poleLattice_add hz hd using 1 <;> ring

lemma poleLattice_eq_poleSet (a b : ℝ) : poleLattice a b = poleSet a b := rfl

lemma noPinch_disjoint {a b : ℝ} {r s x : ℂ} (h : K4NoPinch a b r s x) :
    Disjoint (leftPoles a b r s x) (rightPoles a b r s x) := by
  rcases h with ⟨hUU, hVV, hUVm, hUVp⟩
  have h₁ : Disjoint (leftFamily a b (k4U a b r s)) (rightFamily a b (k4U a b r s)) :=
    families_disjoint (by rw [poleLattice_eq_poleSet]; simpa only [two_mul] using hUU)
  have h₂ : Disjoint (leftFamily a b (k4U a b r s))
      (rightFamily a b (k4V a b r s - x)) :=
    families_disjoint (by rw [poleLattice_eq_poleSet]; simpa only [add_sub_assoc] using hUVm)
  have h₃ : Disjoint (leftFamily a b (k4V a b r s + x))
      (rightFamily a b (k4U a b r s)) :=
    families_disjoint (by rw [poleLattice_eq_poleSet]; convert hUVp using 1 <;> ring)
  have h₄ : Disjoint (leftFamily a b (k4V a b r s + x))
      (rightFamily a b (k4V a b r s - x)) :=
    families_disjoint (by rw [poleLattice_eq_poleSet]; convert hVV using 1 <;> ring)
  exact (h₁.union_right h₂).union_left (h₃.union_right h₄)

end HaagerupIzumi.GammaK4Contour
