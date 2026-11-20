module

public import Weierstrass.StripRetention
public import Weierstrass.StripCenters
public import Weierstrass.RetainedLimit

/-! # Comparison of physical retained heights with normalized strip projections -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Weierstrass.StripProof

theorem measurable_collision (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (i k d : ℝ) : Measurable (fun θ => collision μ ν i k θ d) := by
  let A : Set (ℝ × (Plane × Plane)) := {v | |project i v.1 v.2.1-project k v.1 v.2.2| ≤ d}
  have mA : MeasurableSet A := by unfold A project; apply measurableSet_le _ measurable_const; fun_prop
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν := μ.prod ν) mA)

private theorem integrable_collision (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (i k d : ℝ) (σ : Measure ℝ) [IsFiniteMeasure σ] : Integrable (fun θ => collision μ ν i k θ d) σ :=
  (integrable_const ((μ.prod ν).real univ)).mono' (measurable_collision _ _ _ _ _).aestronglyMeasurable
    (ae_of_all _ fun θ => by rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ collision μ ν i k θ d from measureReal_nonneg)]; exact measureReal_mono (subset_univ _))

/-- Comparing the actual retained-height self-collision to two independent input points
tested in every pair of physical strips, with one common direction. -/
theorem collision_decomposition (κ : Measure ℝ) [IsFiniteMeasure κ] (Q : Set ℝ)
    {Y F : ℝ → ℝ} (mY : Measurable Y) (mF : Measurable F) {Δ d R E θ : ℝ}
    (hΔ : 0 < Δ) (hR : R+2*E ≤ Δ*d)
    (model : ∀ x ∈ Q, |F x - (Y x+Δ*θ*x)| ≤ E) (I : Finset ℤ)
    (hcover : ∀ x ∈ Q, ∃ i ∈ I, x ∈ heightStrip Y Δ i) :
    Weierstrass.collision ((κ.restrict Q).map F) R ≤
      ∑ i ∈ I, ∑ k ∈ I, collision (stripLaw κ Q Y Δ i) (stripLaw κ Q Y Δ k) i k θ d := by
  let C := {v : ℝ × ℝ | |v.1-v.2| ≤ R}
  have mC : MeasurableSet C := measurableSet_le
    (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)) measurable_const
  let approx (i k : ℤ) : Set (Plane × Plane) := {p | |project i θ p.1 - project k θ p.2| ≤ d}
  have mA (i k : ℤ) : MeasurableSet (approx i k) := by
    unfold approx project; apply measurableSet_le _ measurable_const; fun_prop
  let raw (i k : ℤ) := (Prod.map (stripPoint Y Δ i) (stripPoint Y Δ k) ⁻¹' approx i k) ∩
    ((Q ∩ heightStrip Y Δ i) ×ˢ (Q ∩ heightStrip Y Δ k))
  have rawid (i k : ℤ) : collision (stripLaw κ Q Y Δ i) (stripLaw κ Q Y Δ k) i k θ d =
      (κ.prod κ).real (raw i k) := by
    unfold collision stripLaw raw
    rw [Measure.map_prod_map _ _ (measurable_stripPoint mY _ _) (measurable_stripPoint mY _ _),
      map_measureReal_apply ((measurable_stripPoint mY _ _).prodMap (measurable_stripPoint mY _ _)) (mA i k),
      Measure.prod_restrict,measureReal_restrict_apply ((mA i k).preimage
      ((measurable_stripPoint mY _ _).prodMap (measurable_stripPoint mY _ _)))]
  change (((κ.restrict Q).map F).prod ((κ.restrict Q).map F)).real C ≤ _
  rw [Measure.map_prod_map _ _ mF mF,map_measureReal_apply (mF.prodMap mF) mC,
    Measure.prod_restrict,measureReal_restrict_apply (mC.preimage (mF.prodMap mF))]
  simp_rw [rawid]
  have inc : (Prod.map F F ⁻¹' C ∩ (Q ×ˢ Q)) ⊆ ⋃ i ∈ I, ⋃ k ∈ I, raw i k := by
    rintro ⟨x,y⟩ ⟨hxy,hx,hy⟩
    obtain ⟨i,hi,hs⟩ := hcover x hx
    obtain ⟨k,hk,ht⟩ := hcover y hy
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,?_⟩⟩⟩⟩
    refine ⟨?_,⟨hx,hs⟩,hy,ht⟩
    have ah := abs_le.mp (model x hx)
    have bh := abs_le.mp (model y hy)
    change |F x-F y| ≤ R at hxy
    have ch := abs_le.mp hxy
    have eqn (j : ℤ) (t : ℝ) : project j θ (stripPoint Y Δ j t) = (Y t+Δ*θ*t)/Δ := by
      dsimp [project,stripPoint]; field_simp; ring
    change |project i θ (stripPoint Y Δ i x)-project k θ (stripPoint Y Δ k y)| ≤ d
    rw [eqn,eqn,← sub_div,abs_div,abs_of_pos hΔ,div_le_iff₀ hΔ]
    exact abs_le.mpr ⟨by nlinarith only [ah.1,ah.2,bh.1,bh.2,ch.1,ch.2,hR],
      by nlinarith only [ah.1,ah.2,bh.1,bh.2,ch.1,ch.2,hR]⟩
  apply (measureReal_mono (μ := κ.prod κ) inc (measure_ne_top _ _)).trans
  apply (measureReal_biUnion_finset_le I _).trans
  exact Finset.sum_le_sum fun i _ => measureReal_biUnion_finset_le _ _

/-- Fubini for the same retained stable parameter in both physical ordinates. -/
theorem stable_mean_comparison (κ η : Measure ℝ) [IsFiniteMeasure κ] [IsFiniteMeasure η]
    (Q U : Set ℝ) {Y : ℝ → ℝ} (mY : Measurable Y) (F : ℝ → ℝ → ℝ)
    (mF : ∀ h, Measurable (F h)) {ϑ : ℝ → ℝ} (mθ : Measurable ϑ)
    {Δ d R E : ℝ} (hΔ : 0 < Δ) (hR : R+2*E ≤ Δ*d)
    (model : ∀ h ∈ U, ∀ x ∈ Q, |F h x-(Y x+Δ*ϑ h*x)| ≤ E) (I : Finset ℤ)
    (hcover : ∀ x ∈ Q, ∃ i ∈ I, x ∈ heightStrip Y Δ i) (mU : MeasurableSet U) :
    ∫ h in U, Weierstrass.collision ((κ.restrict Q).map (F h)) R ∂η ≤
      ∑ i ∈ I, ∑ k ∈ I, ∫ θ, collision (stripLaw κ Q Y Δ i) (stripLaw κ Q Y Δ k) i k θ d
        ∂(η.restrict U).map ϑ := by
  let G (i k : ℤ) (θ : ℝ) := collision (stripLaw κ Q Y Δ i) (stripLaw κ Q Y Δ k) i k θ d
  have hi (i k : ℤ) : Integrable (fun h => G i k (ϑ h)) (η.restrict U) :=
    (integrable_collision _ _ _ _ _ ((η.restrict U).map ϑ)).comp_measurable mθ
  have eqn (i k : ℤ) : ∫ θ, G i k θ ∂(η.restrict U).map ϑ = ∫ h in U, G i k (ϑ h) ∂η :=
    integral_map mθ.aemeasurable (measurable_collision _ _ _ _ _).aestronglyMeasurable
  change _ ≤ ∑ i ∈ I, ∑ k ∈ I, ∫ θ, G i k θ ∂(η.restrict U).map ϑ
  simp_rw [eqn]
  have inner (i : ℤ) : (∑ k ∈ I, ∫ h in U, G i k (ϑ h) ∂η) = ∫ h in U, ∑ k ∈ I, G i k (ϑ h) ∂η :=
    (integral_finsetSum I (fun k _ => hi i k)).symm
  simp_rw [inner]
  rw [← integral_finsetSum I (fun i _ => integrable_finsetSum I (fun k _ => hi i k))]
  apply integral_mono_of_nonneg (ae_of_all _ fun _ => measureReal_nonneg)
    (integrable_finsetSum I (fun i _ => integrable_finsetSum I (fun k _ => hi i k)))
  filter_upwards [ae_restrict_mem mU] with h hh
  exact collision_decomposition κ Q mY (mF h) hΔ hR (model h hh) I hcover

end Weierstrass.StripProof
