module

public import HaagerupIzumi.Analytic.GammaTwoCenter
public import HaagerupIzumi.Analytic.GammaK4Contour
public import HaagerupIzumi.Analytic.ContourLinearity
import all Mathlib.Data.Complex.Basic

/-!
# The corrected two-gamma Fourier contour

The negative and positive gamma arguments provide one pole family of each
orientation. A fixed initial line lies left of the right family, and its
finite crossed left residues define the continued transform.
-/

@[expose] public section
noncomputable section

open Complex Set Filter Topology MeasureTheory
open HaagerupIzumi.GammaContinuation
open HaagerupIzumi.GammaK4Contour (leftFamily rightFamily)

namespace HaagerupIzumi.GammaTwoFourier

def AvoidsPoles (a b : ℝ) (f h : ℂ) (σ : ℝ) : Prop :=
  ∀ z ∈ leftFamily a b f ∪ rightFamily a b h, z.re ≠ σ

lemma exists_startLine (a b : ℝ) (f h : ℂ) :
    ∃ σ : ℝ, σ < h.re ∧ ∀ z ∈ leftFamily a b f, z.re ≠ σ := by
  have hd := ((GammaK4Contour.leftFamily_countable a b f).image Complex.re).dense_compl ℝ
  obtain ⟨σ, hσ, hlt⟩ := hd.exists_lt h.re
  refine ⟨σ, hlt, ?_⟩
  intro z hz heq
  exact hσ ⟨z, hz, heq⟩

def startLine (a b : ℝ) (f h : ℂ) : ℝ := (exists_startLine a b f h).choose

lemma startLine_spec (a b : ℝ) (f h : ℂ) :
    startLine a b f h < h.re ∧ ∀ z ∈ leftFamily a b f, z.re ≠ startLine a b f h :=
  (exists_startLine a b f h).choose_spec

lemma startLine_avoidsPoles (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h : ℂ) :
    AvoidsPoles a b f h (startLine a b f h) := by
  intro z hz
  rcases hz with hz | hz
  · exact (startLine_spec a b f h).2 z hz
  · have hz' := GammaK4Contour.rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
    have hσ := (startLine_spec a b f h).1
    linarith

def crossedLeft (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f : ℂ) (σ : ℝ) : Finset ℂ :=
  (GammaK4Contour.leftFamily_crossed_finite (lt_of_lt_of_le hb hba) hb f σ).toFinset

def crossedRight (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (h : ℂ) (σ : ℝ) : Finset ℂ :=
  (GammaK4Contour.rightFamily_crossed_finite (lt_of_lt_of_le hb hba) hb h σ).toFinset

@[simp] lemma mem_crossedLeft (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f : ℂ) (σ : ℝ) (z : ℂ) :
    z ∈ crossedLeft a b hb hba f σ ↔ z ∈ leftFamily a b f ∧ σ < z.re := by
  simp [crossedLeft]

@[simp] lemma mem_crossedRight (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (h : ℂ) (σ : ℝ) (z : ℂ) :
    z ∈ crossedRight a b hb hba h σ ↔ z ∈ rightFamily a b h ∧ z.re < σ := by
  simp [crossedRight]

lemma crossedRight_startLine (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h : ℂ) :
    crossedRight a b hb hba h (startLine a b f h) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hzlt⟩ := (mem_crossedRight a b hb hba h _ z).mp hz
  have hσ := (startLine_spec a b f h).1
  have hz' := GammaK4Contour.rightFamily_re_ge (lt_of_lt_of_le hb hba) hb hz
  linarith

/-- The real-parameter Fourier normalization: dividing the corrected complex
line integral by `I` recovers the ordinary `dt` integral on the imaginary axis. -/
def correctedTransform (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) : ℂ :=
  CorrectedContour.value (kernel a b hb hba f h y) (startLine a b f h)
    (crossedLeft a b hb hba f (startLine a b f h)) ∅ / I

lemma correctedTransform_startLine (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h y : ℂ) :
    CorrectedContour.value (kernel a b hb hba f h y) (startLine a b f h)
      (crossedLeft a b hb hba f (startLine a b f h)) ∅ =
        I * correctedTransform a b hb hba f h y := by
  unfold correctedTransform
  field_simp

lemma kernel_differentiableAt_of_not_poles (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h y z : ℂ) (hz : z ∉ leftFamily a b f ∪ rightFamily a b h) :
    DifferentiableAt ℂ (kernel a b hb hba f h y) z := by
  have hg₁ := gamma_differentiableAt_add a b hb hba f z (fun h => hz (Or.inl h))
  have hg₂ := gamma_differentiableAt_sub a b hb hba h z (fun h => hz (Or.inr h))
  have he : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (2 * Real.pi * y * w / ((a : ℂ) * b))) z := by fun_prop
  exact (he.mul hg₁).mul hg₂

lemma kernel_exists_hasResidueGen (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y z : ℂ) :
    ∃ ρ, HasResidueGen (kernel a b hb hba f h y) z ρ := by
  obtain ⟨ρ, hρ⟩ := exists_hasResidueGen_mul (gamma_atMostSimple_add a b hb hba hirr f z)
    (gamma_atMostSimple_sub a b hb hba hirr h z)
  have he : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (2 * Real.pi * y * w / ((a : ℂ) * b))) z := by fun_prop
  obtain ⟨ρ', hρ'⟩ := hρ.mul_differentiableAt he
  refine ⟨ρ', ?_⟩
  have hk : kernel a b hb hba f h y = fun w =>
      (gamma a b hb hba (f + w) * gamma a b hb hba (h - w)) *
        Complex.exp (2 * Real.pi * y * w / ((a : ℂ) * b)) := by
    funext w
    unfold kernel
    ring
  rw [hk]
  exact hρ'

lemma kernel_hasResidueGen_residueValue (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hirr : Irrational (a / b)) (f h y z : ℂ) :
    HasResidueGen (kernel a b hb hba f h y) z
      (residueValue (kernel a b hb hba f h y) z) :=
  hasResidueGen_residueValue (kernel_exists_hasResidueGen a b hb hba hirr f h y z)

lemma kernel_residueValue_eq_zero (a b : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (f h y z : ℂ) (hz : z ∉ leftFamily a b f ∪ rightFamily a b h) :
    residueValue (kernel a b hb hba f h y) z = 0 :=
  residueValue_of_continuousAt (kernel_differentiableAt_of_not_poles a b hb hba f h y z hz).continuousAt

lemma eventually_not_mem_families (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (f h p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ leftFamily a b f ∪ rightFamily a b h := by
  have hL := (tendsto_punctured_of_injective (continuous_const_add f) (add_right_injective f) p).eventually
    (eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb (f + p))
  have hR := (tendsto_punctured_of_injective (continuous_const.sub continuous_id) sub_right_injective p).eventually
    (eventually_not_mem_poleLattice (lt_of_lt_of_le hb hba) hb (h - p))
  filter_upwards [hL, hR] with z hzL hzR
  exact fun hz => hz.elim hzL hzR

end HaagerupIzumi.GammaTwoFourier
