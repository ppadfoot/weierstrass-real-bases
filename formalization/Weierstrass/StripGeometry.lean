module

public import Weierstrass.StripComparison
public import Weierstrass.SeedSampling

/-! # Finite physical strip cover, bounded directions and normalized physical sampling -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Weierstrass.StripProof
open CriticalRay

theorem measurable_time_slice {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (F : X → Y → Z) (hf : Measurable (fun v : X × Y => F v.1 v.2)) (x : X) : Measurable (F x) :=
  hf.comp (measurable_prodMk_left (x := x))

theorem measurable_ray_time (b g : ℝ) (p : RayParameters) (z : PhaseTorus) :
    Measurable (circleRay b g p.1 p.2 z) :=
  measurable_time_slice (circleRay b g p.1 p.2) (measurable_circleRay b g p.1 p.2) z

theorem measurable_direction_time (b g ρ : ℝ) (p : RayParameters) (e : ℤ → ℝ) (z : PhaseTorus) (m : ℕ) :
    Measurable (direction b g ρ p.1 p.2 e z m) :=
  measurable_time_slice (fun z => direction b g ρ p.1 p.2 e z m) (measurable_direction b g ρ p.1 p.2 e m) z

def physicalLaw (T : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1+2*T)⁻¹) • volume.restrict (RaySeed.sampleInterval T)

theorem physicalLaw_probability {T : ℝ} (hT : 0 < T) : IsProbabilityMeasure (physicalLaw T) := by
  constructor
  have hm : 0 < 1+2*T := by linarith
  simp only [physicalLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,
    RaySeed.sampleInterval,Real.volume_Icc]
  rw [show 1+T- -T = 1+2*T by ring,← ENNReal.ofReal_mul (inv_pos.mpr hm).le,inv_mul_cancel₀ hm.ne',
    ENNReal.ofReal_one]

theorem physicalLaw_le {T : ℝ} (hT : 0 < T) : physicalLaw T ≤ volume.restrict (RaySeed.sampleInterval T) := by
  intro S
  rw [physicalLaw,Measure.smul_apply,smul_eq_mul]
  exact mul_le_of_le_one_left' (by simpa using (inv_le_one_of_one_le₀ (by linarith : 1 ≤ 1+2*T)))

theorem physicalLaw_supported (T : ℝ) : ∀ᵐ x ∂physicalLaw T, x ∈ RaySeed.sampleInterval T :=
  Measure.ae_smul_measure (ae_restrict_mem (μ := volume) measurableSet_Icc) _

theorem physical_full_mass {T : ℝ} (hT : 0 < T) (F : ℝ → ℝ) (S : Set ℝ) :
    RaySeed.sampledLaw F T S = ENNReal.ofReal (1+2*T)*((physicalLaw T).map F) S := by
  have hm : 0 < 1+2*T := by linarith
  rw [physicalLaw,Measure.map_smul,Measure.smul_apply,smul_eq_mul,← mul_assoc,
    ← ENNReal.ofReal_mul hm.le,mul_inv_cancel₀ hm.ne',ENNReal.ofReal_one,one_mul]
  rfl

theorem sample_radius {T x : ℝ} (_hT : 0 < T) (hx : x ∈ RaySeed.sampleInterval T) :
    |x| ≤ 1+T := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩

/-- Zeroth-mesh ordinate test for each physical strip, with the entire physical interval. -/
theorem centered_height_mass {b g T : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hT : 0 < T) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1)
    (z : PhaseTorus) {x : ℝ} (hx : x ∈ RaySeed.sampleInterval T) (Δ : ℝ) :
    physicalLaw T {y | |circleRay b g p.1 p.2 z y-circleRay b g p.1 p.2 z x| ≤ Δ} ≤
      rayOccupation b g (shiftedParameters p 0) (physicalEnvironment b p.2 z 0 x) (1+2*T) 1 Δ := by
  apply (physicalLaw_le hT _).trans
  rw [Measure.restrict_apply' (show MeasurableSet (RaySeed.sampleInterval T) from measurableSet_Icc)]
  let S : Set ℝ := {u | u ∈ Icc (-(1+2*T)) (1+2*T) ∧ |circleRay b g (shiftedParameters p 0).1
    (shiftedParameters p 0).2 (physicalEnvironment b p.2 z 0 x) u| ≤ 1*Δ}
  change volume _ ≤ volume S
  rw [← measure_preimage_add_right volume (-x) S]
  apply measure_mono
  rintro y ⟨hy,hI⟩
  have H := circleRay_recenter_scale hb hg hg1 hbg hc hd z (0:ℤ) x (y-x)
  simp only [neg_zero,zpow_zero,one_mul,show x+(y-x)=y by ring] at H
  change |circleRay b g p.1 p.2 z y-circleRay b g p.1 p.2 z x| ≤ Δ at hy
  rw [H] at hy
  change y + -x ∈ Icc (-(1+2*T)) (1+2*T) ∧ _
  rw [← sub_eq_add_neg]
  refine ⟨⟨by linarith [hx.1,hx.2,hI.1,hI.2],by linarith [hx.1,hx.2,hI.1,hI.2]⟩,?_⟩
  change |circleRay b g (fun j => p.1 (j+0)) (fun j => p.2 (j+0)) (fun j => z (j+0)+↑(b^(j+0)*p.2 (j+0)*x)) (y + -x)| ≤ 1*Δ
  simpa only [Int.add_zero,← sub_eq_add_neg,one_mul] using hy

theorem finite_height_cover {Y : ℝ → ℝ} {Q : Set ℝ} {Δ M : ℝ} (hΔ : 0 < Δ)
    (hb : ∀ x ∈ Q, |Y x| ≤ M) : ∃ I : Finset ℤ, ∀ x ∈ Q, ∃ i ∈ I, x ∈ heightStrip Y Δ i := by
  refine ⟨Finset.Icc ⌊(-M)/Δ⌋ ⌊M/Δ⌋,?_⟩
  intro x hx
  obtain ⟨hl,hu⟩ := abs_le.mp (hb x hx)
  refine ⟨⌊Y x/Δ⌋,Finset.mem_Icc.mpr ⟨Int.floor_mono (by gcongr),Int.floor_mono (by gcongr)⟩,?_,?_⟩
  · exact (le_div_iff₀ hΔ).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hΔ).mp (Int.lt_floor_add_one _)

theorem physical_support (κ : Measure ℝ) [IsFiniteMeasure κ] {Q : Set ℝ} (mQ : MeasurableSet Q)
    {Y : ℝ → ℝ} (mY : Measurable Y) {Δ S : ℝ} (hΔ : 0 < Δ) (hS : 1 ≤ S)
    (bound : ∀ x ∈ Q, |x| ≤ S) (i : ℤ) : ∀ᵐ p ∂stripLaw κ Q Y Δ i, p ∈ box 0 S := by
  unfold stripLaw
  apply (ae_map_iff (measurable_stripPoint mY _ _).aemeasurable (measurable_box _ _)).mpr
  filter_upwards [ae_restrict_mem (mQ.inter (measurableSet_Ico.preimage mY))] with x hx
  have xx := abs_le.mp (bound x hx.1)
  have lo : (i:ℝ)*Δ ≤ Y x := hx.2.1
  have hi : Y x < ((i:ℝ)+1)*Δ := hx.2.2
  change x ∈ Icc ((0:ℝ)-S) (0+S) ∧ (Y x-i*Δ)/Δ ∈ Icc (0-S) (0+S)
  simp only [zero_sub,zero_add]
  exact ⟨xx,(neg_nonpos.mpr (zero_le_one.trans hS)).trans (div_nonneg (sub_nonneg.mpr lo) hΔ.le),
    (div_le_iff₀ hΔ).mpr (by nlinarith [mul_le_mul_of_nonneg_right hS hΔ.le])⟩

theorem equal_rate_direction_bound {b g : ℝ} (hb : 1 < b) (_hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (he : ∀ j, |e j| ≤ 1) (z : PhaseTorus) (m : ℕ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    |direction b g b⁻¹ c d e z m u| ≤ τ*rayBound b (b*g)⁻¹ 1 + dualError b g b⁻¹ := by
  have bp := zero_lt_one.trans hb
  have gp := inv_pos.mpr (zero_lt_one.trans hbg)
  have dual : 1 < (b⁻¹)⁻¹*(b*g)⁻¹ := by
    rw [inv_inv,←div_eq_mul_inv,lt_div_iff₀ (zero_lt_one.trans hbg)]
    nlinarith [mul_lt_mul_of_pos_left hg1 bp]
  have rle : b⁻¹/(b*g)⁻¹ ≤ 1 := by
    rw [div_le_one gp]; exact (inv_le_inv₀ bp (zero_lt_one.trans hbg)).mpr (by nlinarith [mul_lt_mul_of_pos_left hg1 bp])
  have Epos : 0 ≤ dualError b g b⁻¹ := by
    unfold dualError; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ dual).le))
  have hu' : |u| ≤ 1 := by simpa [abs_of_nonneg hu.1] using hu.2
  have H := direction_recenter hbg (inv_pos.mpr bp) dual hc hd he z m 0 u
  have tr0 : transverseOrbit b⁻¹ e 0 = 0 := by funext j; simp [transverseOrbit]
  have z0 : direction b g b⁻¹ c d e z m 0 = 0 := by simp [direction,tr0]
  rw [z0,sub_zero,sub_zero] at H
  have ray := circleRay_uniform_bound (b := b) (g := (b*g)⁻¹) bp gp (inv_lt_one_of_one_lt₀ hbg)
    (by simpa using dual) (fun j => dualWeight_bound hc hd (j+(m:ℤ))) (fun j => he (-(j+m)))
    (reversedEnvironment (z+transverseOrbit b⁻¹ e (b⁻¹^m*0)) m) hu'
  rw [inv_inv] at H
  let v := circleRay b (b*g)⁻¹ (reversedParameters c d e m).1 (reversedParameters c d e m).2
    (reversedEnvironment (z+transverseOrbit b⁻¹ e (b⁻¹^m*0)) m) u
  change |v| ≤ rayBound b (b*g)⁻¹ 1 at ray
  change |direction b g b⁻¹ c d e z m u - τ*v| ≤ _ at H
  have hp : (b⁻¹/(b*g)⁻¹)^m ≤ 1 := pow_le_one₀ (div_nonneg (inv_nonneg.mpr bp.le) gp.le) rle
  have heq : dualError b g b⁻¹*(b⁻¹/(b*g)⁻¹)^m*|u| ≤ dualError b g b⁻¹ :=
    (mul_le_of_le_one_right (mul_nonneg Epos (pow_nonneg (div_nonneg (inv_nonneg.mpr bp.le) gp.le) m)) hu').trans
      (mul_le_of_le_one_right Epos hp)
  have vbound : |τ*v| ≤ τ*rayBound b (b*g)⁻¹ 1 := by rw [abs_mul,abs_of_pos (show 0 < τ by dsimp [τ]; positivity)]; gcongr
  have final := (abs_sub_le (direction b g b⁻¹ c d e z m u) (τ*v) 0).trans
    (add_le_add (H.trans heq) (show |τ*v-0| ≤ τ*rayBound b (b*g)⁻¹ 1 by simpa only [sub_zero] using vbound))
  rw [sub_zero,add_comm] at final
  exact final

end Weierstrass.StripProof
