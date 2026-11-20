module

public import Weierstrass.HaarHarmonics
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Continuous test functions for the deterministic graph comparison in Appendix A.
Truncating the negative log at q log(1/λ) keeps the entropy cutoff finite everywhere. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace Weierstrass

private theorem continuous_harmonicCos : Continuous harmonicCos := by
  apply (isQuotientMap_quotient_mk' (s := QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1:ℝ)))).continuous_iff.mpr
  change Continuous (fun t : ℝ ↦ harmonicCos (t : AddCircle (1:ℝ)))
  simp_rw [harmonicCos_coe]
  fun_prop

private def cropTime (u : ℝ) := max (-1) (min u 1)

private theorem continuous_cropped_increment {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1) :
    Continuous (fun p : PhaseTorus × ℝ ↦ circleIncrement b l p.1 (cropTime p.2)) := by
  let τ (p : PhaseTorus × ℝ) := cropTime p.2
  let Z (p : PhaseTorus × ℝ) (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (p.1 j)
  let F (j : ℤ) (p : PhaseTorus × ℝ) := incrementTerm b l (Z p) (τ p) j
  have hτ : Continuous τ := by dsimp [τ,cropTime]; fun_prop
  have ht (p : PhaseTorus × ℝ) : |τ p| ≤ 1 := by simp [τ,cropTime,abs_le]
  have hb₀ := zero_lt_one.trans hb
  have hl₀ := (inv_pos.mpr hb₀).trans hl
  have hbl := (inv_lt_iff_one_lt_mul₀' hb₀).mp hl
  have cterm (j : ℤ) : Continuous (F j) := by
    have e (p : PhaseTorus × ℝ) : F j p = l^j *
        (harmonicCos (p.1 j + ↑(b^j*τ p)) - harmonicCos (p.1 j)) := by
      have he : ((Z p j) : AddCircle (1:ℝ)) = p.1 j := AddCircle.coe_equivIco
      rw [← he, ← AddCircle.coe_add,harmonicCos_coe,harmonicCos_coe]
      rfl
    rw [funext e]
    have hj := (continuous_apply j).comp (continuous_fst (X:=PhaseTorus) (Y:=ℝ))
    have hq : Continuous (fun p : PhaseTorus × ℝ ↦ (↑(b^j*τ p) : AddCircle (1:ℝ))) :=
      continuous_quotient_mk'.comp (continuous_const.mul hτ)
    exact continuous_const.mul ((continuous_harmonicCos.comp (hj.add hq)).sub
      (continuous_harmonicCos.comp hj))
  let major (j : ℤ) := if 0 ≤ j then 2*l^j else 2*Real.pi*(b*l)^j
  have hmajor : Summable major := by
    apply Summable.of_nat_of_neg_add_one
    · simpa [major] using (summable_geometric_of_lt_one hl₀.le hl').mul_left 2
    · have hh := (summable_geometric_of_lt_one (inv_pos.mpr (mul_pos hb₀ hl₀)).le
        (inv_lt_one_of_one_lt₀ hbl)).mul_left (2*Real.pi*(b*l)⁻¹)
      convert! hh using 1
      funext n
      dsimp only [major]
      rw [if_neg (by omega), show -(↑n+1 : ℤ) = -((n+1:ℕ):ℤ) by omega,
        zpow_neg,zpow_natCast,← inv_pow,pow_succ]
      ring
  have bound (j : ℤ) (p : PhaseTorus × ℝ) : ‖F j p‖ ≤ major j := by
    by_cases hj : 0 ≤ j
    · simpa [F,major,hj] using incrementTerm_bound b l hl₀ (Z p) (τ p) j
    · calc
        _ ≤ (2*Real.pi*|τ p|) * (b*l)^j := incrementTerm_lipschitz b l hb₀ hl₀ (Z p) (τ p) j
        _ ≤ (2*Real.pi*1)*(b*l)^j := by gcongr; exact ht p
        _ = major j := by simp [major,hj]
  exact continuous_tsum cterm hmajor bound

def softBand (v : ℝ) := max 0 (min 1 (4-|v|))

def graphCutoff (b l : ℝ) (q : ℕ) (z : PhaseTorus) :=
  2 * ∫ u in Icc (-1:ℝ) 1, softBand (circleIncrement b l z u / l^q)

def graphEntropy (b l : ℝ) (q : ℕ) (z : PhaseTorus) :=
  -Real.log (min 1 (max (l^q) (graphCutoff b l q z)))

theorem continuous_graphCutoff {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (q : ℕ) : Continuous (graphCutoff b l q) := by
  let f (z : PhaseTorus) (u : ℝ) := softBand (circleIncrement b l z (cropTime u)/l^q)
  have hsoft : Continuous softBand := by unfold softBand; fun_prop
  have hf : Continuous f.uncurry := hsoft.comp ((continuous_cropped_increment hb hl hl').div_const _)
  have hint := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc (a := (-1:ℝ)) (b:=1))
  apply ((continuous_const (y := (2:ℝ))).mul hint).congr
  intro z
  change 2*(∫ y in Icc (-1:ℝ) 1, f z y) = 2*_
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  simp [f,cropTime,min_eq_left hu.2,max_eq_right hu.1]

theorem continuous_graphEntropy {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (q : ℕ) : Continuous (graphEntropy b l q) := by
  have hpos := pow_pos ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl) q
  unfold graphEntropy
  exact ((continuous_const.min (continuous_const.max (continuous_graphCutoff hb hl hl' q))).log
    (fun z ↦ (lt_min zero_lt_one (hpos.trans_le (le_max_left _ _))).ne')).neg

/-- The continuous cutoff bounds the hard times at radius 3r from above
and is bounded by the hard times at 4r. -/
theorem graphCutoff_sandwich {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l)
    (q : ℕ) (z : PhaseTorus) :
    2*(occupation b l 1 3 (l^q) z).toReal ≤ graphCutoff b l q z ∧
    graphCutoff b l q z ≤ 2*(occupation b l 1 4 (l^q) z).toReal := by
  let μ := volume.restrict (Icc (-1:ℝ) 1)
  have hq := pow_pos ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl) q
  let v (u : ℝ) := circleIncrement b l z u/l^q
  have mV : Measurable v := by
    have e := (measurable_circleIncrement b l).comp (measurable_prodMk_left (x:=z))
    exact e.div_const _
  let S (K : ℝ) := {u | |v u| ≤ K}
  have mS (K : ℝ) : MeasurableSet (S K) :=
    measurableSet_le (continuous_abs.measurable.comp mV) measurable_const
  have identity (K : ℝ) : (∫ u, (S K).indicator (fun _ ↦ (1:ℝ)) u ∂μ) =
      (occupation b l 1 K (l^q) z).toReal := by
    change (∫ u, (S K).indicator (1 : ℝ → ℝ) u ∂μ) = _
    rw [integral_indicator_one (mS K),measureReal_def]
    change (volume.restrict (Icc (-1:ℝ) 1) (S K)).toReal = _
    rw [Measure.restrict_apply (mS K)]
    unfold occupation
    apply congrArg ENNReal.toReal
    apply congrArg (fun U : Set ℝ ↦ volume U)
    ext u
    change ((|circleIncrement b l z u/l^q| ≤ K) ∧ _) ↔ (_ ∧ _)
    rw [abs_div,abs_of_pos hq,div_le_iff₀ hq]
    exact and_comm
  have msoft : Measurable (fun u ↦ softBand (v u)) := by
    unfold softBand
    fun_prop
  have hsoft : Integrable (fun u ↦ softBand (v u)) μ := by
    let _ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    refine Integrable.of_bound msoft.aestronglyMeasurable 1 (.of_forall ?_)
    intro u
    rw [Real.norm_eq_abs,softBand,abs_of_nonneg (le_max_left 0 _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hInd (K : ℝ) : Integrable ((S K).indicator (fun _ : ℝ ↦ (1:ℝ))) μ := by
    let _ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    exact (integrable_const _).indicator (mS K)
  rw [← identity 3, ← identity 4]
  unfold graphCutoff
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply integral_mono (hInd 3) hsoft
    intro u
    by_cases h : u ∈ S 3
    · have hx : |v u| ≤ 3 := h
      simp [h,softBand,min_eq_left (show (1:ℝ) ≤ 4-|v u| by linarith)]
    · simp [h,softBand]
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply integral_mono hsoft (hInd 4)
    intro u
    by_cases h : u ∈ S 4
    · simp [h,softBand]
    · have hx : 4 < |v u| := lt_of_not_ge h
      simp [h,softBand, max_eq_left ((min_le_right _ _).trans (by linarith : 4-|v u| ≤ 0))]

local instance entropyGroupBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

/-- The uniform coset lower bound in (G1), with its finite-scale probability loss.
The factor ε can be taken arbitrarily small after choosing the exponent h. -/
theorem anchored_entropy_floor {b l s : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (hs : s ≤ 1) (H : AnchoredEstimate b l s) {h ε : ℝ} (hh : 0 < h) (hh' : h < s)
    (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ ω : PhaseTorus,
      (1-ε)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2) ≤
      ∫ z : phaseGroup b, graphEntropy b l q (ω+z.val) ∂phaseHaar b := by
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  have hl₀ := (inv_pos.mpr (zero_lt_one.trans hb)).trans hl
  have trend : Tendsto (fun q : ℕ ↦ l^q) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hl₀.le hl',
      .of_forall (fun q ↦ pow_pos hl₀ q)⟩
  have anchor := (H h hh hh' 1 4 one_pos (by norm_num)).comp trend
  have high := anchor.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hε))
  filter_upwards [high] with q hq
  intro ω
  let μ := phaseHaar b
  let r := l^q
  have hr : 0 < r := pow_pos hl₀ q
  have hr₁ : r ≤ 1 := pow_le_one₀ hl₀.le hl'.le
  let B := {z : phaseGroup b | ENNReal.ofReal (r^h) < occupation b l 1 4 r (ω+z.val)}
  have mtrans : Measurable (fun z : phaseGroup b ↦ ω+z.val) :=
    (continuous_const.add continuous_subtype_val).measurable
  have mB : MeasurableSet B := measurableSet_lt measurable_const
    ((measurable_occupation b l 1 4 r).comp mtrans)
  have hbprob : μ B ≤ ENNReal.ofReal ε := (le_iSup (fun v : PhaseTorus ↦
    μ {z : phaseGroup b | ENNReal.ofReal (r^h) < occupation b l 1 4 r (v+z.val)}) ω).trans hq.le
  have mass : 1-ε ≤ μ.real Bᶜ := by
    rw [measureReal_compl mB,probReal_univ]
    exact sub_le_sub_left (ENNReal.toReal_le_of_le_ofReal hε.le hbprob) 1
  let f (z : phaseGroup b) := graphEntropy b l q (ω+z.val)
  let v := max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2)
  have fcont : Continuous f := (continuous_graphEntropy hb hl hl' q).comp
    (continuous_const.add continuous_subtype_val)
  have fpos (z : phaseGroup b) : 0 ≤ f z := by
    exact neg_nonneg.mpr (Real.log_nonpos (le_min zero_le_one (hr.le.trans (le_max_left _ _)))
      (min_le_left _ _))
  have lower (z : phaseGroup b) (hz : z ∈ Bᶜ) : v ≤ f z := by
    apply max_le (fpos z)
    have hbnd : occupation b l 1 4 r (ω+z.val) ≤ ENNReal.ofReal (r^h) := le_of_not_gt hz
    have hp := Real.rpow_pos_of_pos hr h
    have hC := (graphCutoff_sandwich hb hl q (ω+z.val)).2
    have hupper : min 1 (max r (graphCutoff b l q (ω+z.val))) ≤ 2*(r^h) := by
      apply (min_le_right _ _).trans
      apply max_le
      · have ha : r^(1:ℝ) ≤ r^h := Real.rpow_le_rpow_of_exponent_ge hr hr₁ (hh'.le.trans hs)
        rw [Real.rpow_one] at ha
        linarith
      · exact hC.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hp.le hbnd) (by norm_num))
    have hlog := Real.log_le_log (lt_min zero_lt_one (hr.trans_le (le_max_left _ _))) hupper
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne',Real.log_rpow hr] at hlog
    change _ ≤ -Real.log (min 1 (max r (graphCutoff b l q (ω+z.val))))
    dsimp only [r] at hlog ⊢
    rw [Real.log_pow] at hlog
    linarith only [hlog]
  have intf : Integrable f μ := fcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ μ.real Bᶜ * v := mul_le_mul_of_nonneg_right mass (le_max_left _ _)
    _ = ∫ z, Bᶜ.indicator (fun _ : phaseGroup b ↦ v) z ∂μ := by
      rw [integral_indicator_const _ mB.compl,smul_eq_mul]
    _ ≤ ∫ z, f z ∂μ := by
      apply integral_mono ((integrable_const v).indicator mB.compl) intf
      intro z
      by_cases hz : z ∈ Bᶜ
      · simpa only [indicator_of_mem hz] using lower z hz
      · simpa only [indicator_of_notMem hz] using fpos z

end Weierstrass
