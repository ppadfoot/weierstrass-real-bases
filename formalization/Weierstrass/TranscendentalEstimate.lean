module

public import Weierstrass.HarmonicScale
public import Weierstrass.HaarHarmonics
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Uniform small-ball and occupation estimates for the unweighted bilateral
cosine increment at a transcendental base. The number of good frequencies can
be chosen before taking the scale to zero. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Weierstrass

local instance transcendentalGroupBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

private theorem band_exponent {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (ht : Transcendental ℤ b) {h A : ℝ} (hh : h < 1) (hA : 0 < A) :
    ∃ k D E : ℝ, h < k ∧ 0 ≤ D ∧ 0 ≤ E ∧ ∀ u : ℝ, u ≠ 0 → ∀ r : ℝ, 0 < r →
    ∀ ω : PhaseTorus,
      phaseHaar b {z : phaseGroup b | |circleIncrement b l (ω+z.val) u| ≤ A*r} ≤
        ENNReal.ofReal (r ^ k * (D+E*|u|^(-alpha b l))) := by
  classical
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hh)
  let p : ℝ := 1/((m:ℝ)+1)
  let k := 1-p
  have hpm : p*(m:ℝ) = k := by dsimp [k,p]; field_simp; ring
  obtain ⟨C,hC,hscale⟩ := exists_active_harmonics hb hl hl' m
  refine ⟨k,4^m,(m:ℝ)*A/(4*C),by dsimp [k,p]; linarith,by positivity,by positivity,?_⟩
  intro u hu r hr ω
  obtain ⟨j₀,hj₀⟩ := hscale u hu
  let S := Finset.Ioc (j₀-(m:ℤ)) j₀
  have nS : S.card = m := by simp [S,Int.card_Ioc]
  let a := C * |u| ^ alpha b l
  have hapos : 0 < a := mul_pos hC (Real.rpow_pos_of_pos (abs_pos.mpr hu) _)
  have active (j : ℤ) (hj : j ∈ S) : a ≤ |2*l^j*Real.sin (Real.pi*(b^j*u))| := by
    obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp hj
    let d := (j₀-j).toNat
    have hd : d ≤ m := by dsimp [d]; omega
    have hj : j₀-(d:ℤ) = j := by dsimp [d]; omega
    simpa only [hj] using hj₀ d hd
  have hband := circleIncrement_band_of_active_coordinates hb hl hl' ht S hapos
    (Real.rpow_pos_of_pos hr p) (mul_nonneg hA.le hr.le) active ω 0
  simp only [sub_zero,nS] at hband
  apply hband.trans
  have hdpos : 0 ≤ 4*r^p := by positivity
  have hbandpos : 0 ≤ ((A*r)/a)/(4*r^p) := by positivity
  rw [← ENNReal.ofReal_pow hdpos, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m), ← ENNReal.ofReal_add (pow_nonneg hdpos m) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow, ← Real.rpow_mul_natCast hr.le, hpm,
    Real.rpow_neg (abs_nonneg u)]
  have hk : r^k = r/(r^p) := by rw [show k=1-p by rfl, Real.rpow_sub hr, Real.rpow_one]
  have hs : |u|^alpha b l ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hu) _).ne'
  have hpr : r^p ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  dsimp [a]
  rw [hk]
  apply le_of_eq
  field_simp

private theorem time_weight_integrable {α T : ℝ} (hα : α < 1) (hT : 0 < T) :
    IntegrableOn (fun u : ℝ ↦ |u|^(-α)) (Icc (-T) T) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -T ≤ T)).mp
  apply intervalIntegrable_of_even (by simp)
  intro x hx
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).mpr
  exact ((intervalIntegral.integrableOn_Ioo_rpow_iff hx).mpr (by linarith : -1 < -α)).congr_fun
    (fun t ht ↦ by simp [abs_of_pos ht.1]) measurableSet_Ioo

/-- Assertion (2.2) at exponent one, for all transcendental real bases,
every allowed amplitude and uniformly over all deterministic phase offsets. -/
theorem anchoredEstimate_transcendental {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (ht : Transcendental ℤ b) : AnchoredEstimate b l 1 := by
  apply anchored_of_first_moment
  intro h _ hh T A hT hA
  obtain ⟨k,D,E,hk,hD,hE,hband⟩ := band_exponent hb hl hl' ht hh hA
  let μ := volume.restrict (Icc (-T) T)
  let weight (u : ℝ) := D+E*|u|^(-alpha b l)
  have integrable : Integrable weight μ := by
    have hi := time_weight_integrable (alpha_mem_Ioo hb hl hl').2 hT
    exact (integrable_const D).add (hi.const_mul E)
  have hnon (u : ℝ) : 0 ≤ weight u := add_nonneg hD (mul_nonneg hE (Real.rpow_nonneg (abs_nonneg u) _))
  let C := ∫ u, weight u ∂μ
  have hC : 0 ≤ C := integral_nonneg hnon
  refine ⟨k,C,hk,hC,?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  intro ω
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let V := {p : phaseGroup b × ℝ | |circleIncrement b l (ω+p.1.val) p.2| ≤ A*r}
  have mV : MeasurableSet V := by
    have hcoord : Continuous (fun p : phaseGroup b × ℝ ↦ ω + p.1.val) :=
      continuous_const.add (continuous_subtype_val.comp continuous_fst)
    have hp : Measurable (fun p : phaseGroup b × ℝ ↦ (ω+p.1.val,p.2)) :=
      hcoord.measurable.prodMk measurable_snd
    have hi : Measurable (fun p : phaseGroup b × ℝ ↦ circleIncrement b l (ω+p.1.val) p.2) := by
      change Measurable ((fun pt : PhaseTorus × ℝ ↦ circleIncrement b l pt.1 pt.2) ∘
        (fun p : phaseGroup b × ℝ ↦ (ω+p.1.val,p.2)))
      exact (measurable_circleIncrement b l).comp hp
    exact measurableSet_le (continuous_abs.measurable.comp hi) measurable_const
  have hsec (z : phaseGroup b) : μ (Prod.mk z ⁻¹' V) = occupation b l T A r (ω+z.val) := by
    rw [Measure.restrict_apply (measurable_prodMk_left mV)]
    unfold occupation
    congr 1
    ext u
    exact and_comm
  calc
    _ = (phaseHaar b).prod μ V := by rw [Measure.prod_apply mV]; simp_rw [hsec]
    _ = ∫⁻ u, phaseHaar b ((fun z ↦ (z,u)) ⁻¹' V) ∂μ := Measure.prod_apply_symm mV
    _ ≤ ∫⁻ u, ENNReal.ofReal (r^k*weight u) ∂μ := by
      apply lintegral_mono_ae
      have hzero : ∀ᵐ u ∂μ, u ≠ 0 := ae_restrict_of_ae (ae_iff.mpr (by simp))
      filter_upwards [hzero] with u hu
      exact hband u hu r hr' ω
    _ = ENNReal.ofReal (C*r^k) := by
      have hpos := Real.rpow_pos_of_pos hr' k
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable.const_mul (r^k))
        (.of_forall (fun u ↦ mul_nonneg hpos.le (hnon u))),integral_const_mul,mul_comm]
      
end Weierstrass
