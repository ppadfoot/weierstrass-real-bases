module

public import Weierstrass.Transcendental
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.UrysohnsLemma

/-! Finite-dimensional Fourier separation of cosets of the compact physical phase group. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal
namespace Weierstrass

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {d : Type*} [Fintype d]

private def projectedMean (μ : Measure G) [IsFiniteMeasure μ] (p : C(G, UnitAddTorus d)) :
    C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp ((ContinuousMap.toLp 1 μ ℂ).comp (ContinuousMap.compCLM ℂ ℂ p))

omit [AddCommGroup G] [IsTopologicalAddGroup G] [Fintype d] in
private theorem projectedMean_apply (μ : Measure G) [IsFiniteMeasure μ] (p : C(G, UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) : projectedMean μ p f = ∫ g, f (p g) ∂μ := by
  rw [projectedMean, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 1) (f.comp p))

private theorem mFourier_add_point (n : d → ℤ) (z w : UnitAddTorus d) :
    UnitAddTorus.mFourier n (z + w) = UnitAddTorus.mFourier n z * UnitAddTorus.mFourier n w := by
  simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
    Finset.prod_mul_distrib]

/-- A point belongs to a compact subgroup image in a finite torus whenever each
integer character nontrivial at the point is nontrivial somewhere in the image. -/
theorem mem_torus_image_of_characters (μ : Measure G) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] (p : G →+ UnitAddTorus d) (hp : Continuous p)
    (y : UnitAddTorus d) (hn : ∀ n : d → ℤ, UnitAddTorus.mFourier n y ≠ 1 →
      ∃ g : G, UnitAddTorus.mFourier n (p g) ≠ 1) : y ∈ range p := by
  classical
  let p₀ : C(G, UnitAddTorus d) := ⟨p, hp⟩
  let p₁ : C(G, UnitAddTorus d) := ⟨fun g ↦ y + p g, continuous_const.add hp⟩
  let D := projectedMean μ p₁ - projectedMean μ p₀
  have hD (n : d → ℤ) : D (UnitAddTorus.mFourier n) = 0 := by
    change projectedMean μ p₁ _ - projectedMean μ p₀ _ = 0
    rw [projectedMean_apply, projectedMean_apply]
    by_cases hny : UnitAddTorus.mFourier n y = 1
    · change (∫ g, UnitAddTorus.mFourier n (y + p g) ∂μ) -
          (∫ g, UnitAddTorus.mFourier n (p g) ∂μ) = 0
      simp only [mFourier_add_point, hny, one_mul, sub_self]
    obtain ⟨g₀, hg₀⟩ := hn n hny
    let v := ∫ g, UnitAddTorus.mFourier n (p g) ∂μ
    have heq : UnitAddTorus.mFourier n (p g₀) * v = v := by
      have h := integral_add_left_eq_self (μ := μ) (fun g ↦ UnitAddTorus.mFourier n (p g)) g₀
      simpa only [map_add, mFourier_add_point, integral_const_mul, v] using h
    have hv : v = 0 := by
      by_contra hzero
      exact hg₀ ((mul_right_cancel₀ hzero) (heq.trans (one_mul v).symm))
    change (∫ g, UnitAddTorus.mFourier n (y + p g) ∂μ) - v = 0
    simp only [mFourier_add_point, integral_const_mul, ← show (∫ g, UnitAddTorus.mFourier n (p g) ∂μ) = v from rfl]
    change UnitAddTorus.mFourier n y * v - v = 0
    simp [hv]
  have hspan : Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d))) ≤ LinearMap.ker D :=
    Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hD n)
  have hker := Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
  rw [UnitAddTorus.span_mFourier_closure_eq_top] at hker
  by_contra hy
  have hclosed : IsClosed (range p) := (isCompact_range hp).isClosed
  have hclosed' : IsClosed (range p₁) := (isCompact_range p₁.continuous).isClosed
  have hdis : Disjoint (range p) (range p₁) := by
    apply disjoint_left.mpr
    rintro _ ⟨a, rfl⟩ ⟨b, h⟩
    apply hy
    refine ⟨a-b, ?_⟩
    change y + p b = p a at h
    rw [map_sub, ← h, add_sub_cancel_right]
  obtain ⟨f, hf₀, hf₁, _⟩ := exists_continuous_zero_one_of_isClosed hclosed hclosed' hdis
  let F : C(UnitAddTorus d, ℂ) := ⟨fun z ↦ f z, Complex.continuous_ofReal.comp f.continuous⟩
  have hF : D F = 0 := hker (show F ∈ (⊤ : Submodule ℂ _) from trivial)
  change projectedMean μ p₁ F - projectedMean μ p₀ F = 0 at hF
  rw [projectedMean_apply, projectedMean_apply] at hF
  have hF₁ (g : G) : F (p₁ g) = 1 := by
    change ((f (p₁ g) : ℝ) : ℂ) = 1
    rw [hf₁ (mem_range_self g)]
    norm_num
  have hF₀ (g : G) : F (p₀ g) = 0 := by
    change ((f (p g) : ℝ) : ℂ) = 0
    rw [hf₀ (mem_range_self g)]
    norm_num
  simp [hF₁, hF₀] at hF

/-- A compact additive group mapping to a finite torus surjects if every nonzero
integer character is nonconstant on its image. -/
theorem surjective_torus_of_characters (μ : Measure G) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] (p : G →+ UnitAddTorus d) (hp : Continuous p)
    (hn : ∀ n : d → ℤ, n ≠ 0 → ∃ g : G, UnitAddTorus.mFourier n (p g) ≠ 1) :
    Function.Surjective p := by
  intro y
  apply mem_torus_image_of_characters μ p hp y
  intro n hny
  apply hn n
  rintro rfl
  exact hny (by simp [UnitAddTorus.mFourier_zero])

private theorem prod_toCircle {ι : Type*} (t : Finset ι) (w : ι → AddCircle (1 : ℝ)) :
    (∏ i ∈ t, (AddCircle.toCircle (w i) : ℂ)) = (AddCircle.toCircle (∑ i ∈ t, w i) : ℂ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [ha, ih, AddCircle.toCircle_add]

/-- The multiplicative Fourier character is the circle image of the additive angle. -/
theorem mFourier_eq_sum_toCircle (n : d → ℤ) (z : UnitAddTorus d) :
    UnitAddTorus.mFourier n z = (AddCircle.toCircle (∑ i, n i • z i) : ℂ) := by
  change (∏ i, (AddCircle.toCircle (n i • z i) : ℂ)) = _
  exact prod_toCircle Finset.univ _

/-- Every finite projection of the orbit closure is the full coordinate torus. -/
theorem finite_phase_projection_surjective {b : ℝ} (hb : b ≠ 0) (ht : Transcendental ℤ b)
    (S : Finset ℤ) : Function.Surjective
      (fun z : phaseGroup b ↦ fun i : S ↦ z.val i) := by
  classical
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar; infer_instance
  let p : phaseGroup b →+ UnitAddTorus S :=
    { toFun := fun z i ↦ z.val i, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hp : Continuous p := continuous_pi (fun i ↦ (continuous_apply (i : ℤ)).comp continuous_subtype_val)
  apply surjective_torus_of_characters (phaseHaar b) p hp
  intro n hn
  let c (i : ℤ) : ℤ := if h : i ∈ S then n ⟨i, h⟩ else 0
  obtain ⟨i, hi⟩ : ∃ i : S, n i ≠ 0 := by simpa [funext_iff] using hn
  have hc : ∃ j ∈ S, c j ≠ 0 := ⟨i, i.property, by simpa [c, i.property] using hi⟩
  let z : AddCircle (1 : ℝ) := ↑(1 / 2 : ℝ)
  have hz : z ≠ 0 := by
    apply mt (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (show (1 / 2 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num)).mp
    norm_num
  obtain ⟨x, hx⟩ := character_phaseOrbit_surjective hb ht S c hc z
  change torusCharacter S c (phaseOrbit b x) = z at hx
  let w : phaseGroup b := ⟨phaseOrbit b x, (phaseOrbit b).range.le_topologicalClosure ⟨x, rfl⟩⟩
  refine ⟨w, ?_⟩
  have hsum : (∑ j : S, n j • (p w j)) = torusCharacter S c (phaseOrbit b x) := by
    rw [torusCharacter, ← Finset.sum_attach S]
    change (∑ j : S, n j • ((phaseOrbit b x) j)) = _
    apply Finset.sum_congr rfl
    intro j _
    simp [c, j.property]
  have hv : UnitAddTorus.mFourier n (p w) = (AddCircle.toCircle z : ℂ) := by
    change (∏ j : S, (AddCircle.toCircle (n j • p w j) : ℂ)) = _
    rw [prod_toCircle, hsum]
    exact congrArg (fun t : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle t : ℂ)) hx
  rw [hv]
  intro he
  apply hz
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  simpa using he

/-- At a transcendental base the bilateral phase group is the entire countable product torus. -/
theorem phaseGroup_eq_top_of_transcendental {b : ℝ} (hb : b ≠ 0) (ht : Transcendental ℤ b) :
    phaseGroup b = ⊤ := by
  classical
  apply top_unique
  intro z _
  by_contra hz
  have hclosed : IsClosed (phaseGroup b : Set PhaseTorus) := (phaseOrbit b).range.isClosed_topologicalClosure
  obtain ⟨S, u, hu, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl z hz
  obtain ⟨w, hw⟩ := finite_phase_projection_surjective hb ht S (fun i : S ↦ z i)
  apply (hsub (a := w.val) ?_) w.property
  intro i hi
  have hi' := congrFun hw ⟨i, hi⟩
  change w.val i = z i at hi'
  rw [hi']
  exact (hu i hi).2

local instance phaseGroupBorelMeasurableSpace (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

/-- In every translated phase group, any finite set of coordinates has the product of
normalized uniform circle laws. This gives joint independence, including for three consecutive modes. -/
theorem finite_phase_product_law {b : ℝ} (hb : b ≠ 0) (ht : Transcendental ℤ b)
    (S : Finset ℤ) (ω : PhaseTorus) :
    Measure.map (fun z : phaseGroup b ↦ fun i : S ↦ ω i + z.val i) (phaseHaar b) =
      Measure.pi (fun _ : S ↦ (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))) := by
  classical
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar; infer_instance
  let p : phaseGroup b →+ UnitAddTorus S :=
    { toFun := fun z i ↦ z.val i, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hp : Continuous p := continuous_pi (fun i ↦ (continuous_apply (i : ℤ)).comp continuous_subtype_val)
  let _ : IsProbabilityMeasure ((phaseHaar b).map p) := Measure.isProbabilityMeasure_map hp.measurable.aemeasurable
  let _ : Measure.IsAddLeftInvariant ((phaseHaar b).map p) :=
    isAddLeftInvariant_map p.toAddHom hp.measurable (finite_phase_projection_surjective hb ht S)
  let ν := Measure.pi (fun _ : S ↦ (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))
  have hmap : (phaseHaar b).map p = ν := by
    have htop (η : Measure (UnitAddTorus S)) [IsProbabilityMeasure η] [Measure.IsAddLeftInvariant η] :
        Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts (UnitAddTorus S)) = η :=
      (Measure.addHaarMeasure_eq_iff _ _).mpr (by simp)
    exact (htop _).symm.trans (htop ν)
  let t : UnitAddTorus S := fun i ↦ ω i
  change (phaseHaar b).map ((t + ·) ∘ p) = ν
  rw [← Measure.map_map (measurable_const_add t) hp.measurable, hmap, map_add_left_eq_self]

end Weierstrass
