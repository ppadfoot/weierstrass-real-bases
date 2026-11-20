module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A uniform circle angle is outside four short critical pieces except on a set of mass
at most 4δ. On each remaining cosine branch the inverse image of an interval has length
controlled by its width divided by δ. Angles are measured in turns. -/

@[expose] public noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace Weierstrass

abbrev circleUniform : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle

def turnRep (z : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 z : ℝ)

def harmonicCos (z : AddCircle (1 : ℝ)) : ℝ := Real.cos (2 * Real.pi * turnRep z)

def regularTurns (δ : ℝ) : Set ℝ := Icc δ (1 / 2 - δ) ∪ Icc (1 / 2 + δ) (1 - δ)

def regularPhase (δ : ℝ) : Set (AddCircle (1 : ℝ)) := turnRep ⁻¹' regularTurns δ

theorem measurable_turnRep : Measurable turnRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

theorem measurable_harmonicCos : Measurable harmonicCos :=
  Real.continuous_cos.measurable.comp (measurable_const.mul measurable_turnRep)

theorem measurableSet_regularPhase (δ : ℝ) : MeasurableSet (regularPhase δ) :=
  measurable_turnRep (measurableSet_Icc.union measurableSet_Icc)

private theorem turn_distribution (s : Set ℝ) (hs : MeasurableSet s) :
    circleUniform (turnRep ⁻¹' s) = volume (s ∩ Ioc 0 1) := by
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = circleUniform := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol, AddCircle.add_projection_respects_measure 1 0 (measurable_turnRep hs)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, zero_add]
  refine ⟨fun ⟨hx, h01⟩ ↦ ⟨?_,h01⟩, fun ⟨hx,h01⟩ ↦ ⟨?_,h01⟩⟩ <;>
    have hx' : x ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using h01
  · simpa [turnRep, AddCircle.equivIoc_coe_eq hx'] using hx
  · simpa [turnRep, AddCircle.equivIoc_coe_eq hx'] using hx

/-- Total mass discarded around the two extrema of the cosine. -/
theorem harmonic_bad_mass (δ : ℝ) (hδ : 0 ≤ δ) :
    circleUniform (regularPhase δ)ᶜ ≤ ENNReal.ofReal (4 * δ) := by
  change circleUniform (turnRep ⁻¹' (regularTurns δ)ᶜ) ≤ _
  rw [turn_distribution (regularTurns δ)ᶜ (measurableSet_Icc.union measurableSet_Icc).compl]
  let A := Icc 0 δ
  let B := Icc (1 / 2 - δ) (1 / 2 + δ)
  let C := Icc (1 - δ) 1
  have hsub : (regularTurns δ)ᶜ ∩ Ioc 0 1 ⊆ (A ∪ B) ∪ C := by
    intro x hx
    simp only [regularTurns, mem_inter_iff, mem_compl_iff, mem_union, mem_Icc, mem_Ioc] at hx
    change ((0 ≤ x ∧ x ≤ δ) ∨ (1 / 2 - δ ≤ x ∧ x ≤ 1 / 2 + δ)) ∨ 1 - δ ≤ x ∧ x ≤ 1
    grind
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  dsimp [A,B,C]
  rw [Real.volume_Icc, Real.volume_Icc, Real.volume_Icc]
  rw [show 1 / 2 + δ - (1 / 2 - δ) = 2 * δ by ring, show 1 - (1 - δ) = δ by ring, sub_zero,
    ← ENNReal.ofReal_add hδ (by positivity), ← ENNReal.ofReal_add (by positivity) hδ]
  exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem sine_lower (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (Real.pi * t) := by
  simpa only [show Real.pi / 2 * (2 * t) = Real.pi * t by ring] using
    Real.le_sin_mul (show 0 ≤ 2 * t by positivity) (show 2 * t ≤ 1 by linarith)

private theorem cosine_branch {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hx : x ∈ Icc δ (1 / 2 - δ)) (hy : y ∈ Icc δ (1 / 2 - δ)) :
    16 * δ * |x - y| ≤ |Real.cos (2 * Real.pi * x) - Real.cos (2 * Real.pi * y)| := by
  rcases hx with ⟨hx,hx'⟩; rcases hy with ⟨hy,hy'⟩
  have hsum : 4 * δ ≤ |Real.sin (Real.pi * (x + y))| := by
    rcases le_total (x+y) (1/2) with h | h
    · exact (show 4 * δ ≤ 2 * (x+y) by linarith).trans
        ((sine_lower _ (by linarith) h).trans (le_abs_self _))
    · rw [← Real.sin_pi_sub, show Real.pi - Real.pi * (x+y) = Real.pi * (1 - (x+y)) by ring]
      exact (show 4 * δ ≤ 2 * (1 - (x+y)) by linarith).trans
        ((sine_lower _ (by linarith) (by linarith)).trans (le_abs_self _))
  have hdiff : 2 * |x-y| ≤ |Real.sin (Real.pi * (x-y))| := by
    have ha : |x-y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h := Real.mul_abs_le_abs_sin (x := Real.pi * (x-y)) (by
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [mul_le_mul_of_nonneg_left ha Real.pi_pos.le])
    rwa [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_pos.ne'] at h
  rw [Real.cos_sub_cos, show (2 * Real.pi * x + 2 * Real.pi * y) / 2 = Real.pi * (x+y) by ring,
    show (2 * Real.pi * x - 2 * Real.pi * y) / 2 = Real.pi * (x-y) by ring, abs_mul, abs_mul]
  norm_num
  nlinarith [mul_le_mul hsum hdiff (by positivity) (abs_nonneg _)]

private theorem cosine_mirror (x : ℝ) : Real.cos (2 * Real.pi * (1 - x)) = Real.cos (2 * Real.pi * x) := by
  rw [show 2 * Real.pi * (1-x) = 2 * Real.pi - 2 * Real.pi * x by ring, Real.cos_two_pi_sub]

/-- Away from the critical arcs, a band of radius r has mass at most r/(4δ), uniformly in its center. -/
theorem harmonic_good_band {δ : ℝ} (hδ : 0 < δ) (y r : ℝ) (hr : 0 ≤ r) :
    circleUniform {z | z ∈ regularPhase δ ∧ |harmonicCos z - y| ≤ r} ≤
      ENNReal.ofReal (r / (4 * δ)) := by
  let band : Set ℝ := {x | |Real.cos (2 * Real.pi * x) - y| ≤ r}
  have hm : MeasurableSet band := by dsimp [band]; measurability
  change circleUniform (turnRep ⁻¹' (regularTurns δ ∩ band)) ≤ _
  rw [turn_distribution (regularTurns δ ∩ band) ((measurableSet_Icc.union measurableSet_Icc).inter hm)]
  have hclose {x x' : ℝ} (hx : x ∈ band) (hx' : x' ∈ band) :
      |Real.cos (2 * Real.pi * x) - Real.cos (2 * Real.pi * x')| ≤ 2 * r := by
    change |Real.cos (2*Real.pi*x) - y| ≤ r at hx
    change |Real.cos (2*Real.pi*x') - y| ≤ r at hx'
    rw [abs_le] at hx hx' ⊢; constructor <;> linarith
  have hdiam {D : Set ℝ} (h : ∀ x ∈ D, ∀ x' ∈ D,
      16 * δ * |x-x'| ≤ |Real.cos (2 * Real.pi * x) - Real.cos (2 * Real.pi * x')|) :
      volume (D ∩ band) ≤ ENNReal.ofReal (r / (8 * δ)) := by
    apply (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
    intro x hx x' hx'
    rw [Real.dist_eq, le_div_iff₀ (by positivity)]
    linarith [h x hx.1 x' hx'.1, hclose hx.2 hx'.2]
  have hpos := hdiam (D := Icc δ (1/2-δ)) (fun _ hx _ hx' ↦ cosine_branch hδ.le hx hx')
  have hneg := hdiam (D := Icc (1/2+δ) (1-δ)) (by
    rintro x ⟨hx,hx'⟩ x' ⟨hy,hy'⟩
    have h := cosine_branch (x := 1-x) (y := 1-x') hδ.le ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
    rw [cosine_mirror, cosine_mirror, show (1-x) - (1-x') = -(x-x') by ring, abs_neg] at h
    exact h)
  refine (measure_mono inter_subset_left).trans ?_
  rw [regularTurns, union_inter_distrib_right]
  refine (measure_union_le _ _).trans ((add_le_add hpos hneg).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by field_simp; linarith)

end Weierstrass
