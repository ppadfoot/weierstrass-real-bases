module

public import Weierstrass.BranchLoss

/-! The supremum-over-phases integral appearing after Theorem B.1, including
nonpositive test exponents. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Branch
open scoped ENNReal NNReal Topology
namespace Weierstrass.Predecessor

theorem slopeHeavy_eq_conditional_integral {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (g : ℝ)
    (η : ℕ → ℝ) (R τ : ℝ) :
    slopeHeavy hp d a g η R τ = ∫⁻ w : Fin d → UnitAddCircle, let ν := baseSlopeLaw hp d a (centralLift w) η g
      ν {y | ENNReal.ofReal τ < ν (Icc (y-R) (y+R))} := by
  let Ω := Fin d → UnitAddCircle
  let F (w : Ω) (x : ℝ) := codedSlope d (fun i ↦ (a i:ℝ)) p g (centralLift w) η (uniformCode p hp x)
  let E := {v : Ω × ℝ | ENNReal.ofReal τ < ballMass (baseSlopeLaw hp d a (centralLift v.1) η g) v.2 R}
  have mE : MeasurableSet E := measurableSet_lt measurable_const (measurable_ballMass_family hp d a g _
    (fun _ ↦ η) _ R (fun i ↦ (measurable_centralLift _ i).comp measurable_fst) (fun _ ↦ measurable_const) measurable_snd)
  have mF : Measurable (Function.uncurry F) := measurable_coded_sample hp d a _ (fun i ↦ (measurable_centralLift _ i).comp measurable_fst)
    _ measurable_snd η g
  change (volume.prod unitLaw) ((fun v : Ω × ℝ ↦ (v.1,F v.1 v.2)) ⁻¹' E) = _
  have mm : MeasurableSet ((fun v : Ω × ℝ ↦ (v.1,F v.1 v.2)) ⁻¹' E) := (measurable_fst.prodMk mF) mE
  rw [Measure.prod_apply mm]
  apply lintegral_congr;intro w
  change _ = (unitLaw.map (F w)) (Prod.mk w ⁻¹' E)
  rw [Measure.map_apply mF.of_uncurry_left (measurable_prodMk_left mE)];rfl

theorem conditional_slope_uniform_limit {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hγ' : γ<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (j : ℕ) {h A : ℝ}
    (hs : h<slopeExponent p (γ*c^j)) (hA : 0<A) :
    let g := γ*c^j
    Tendsto (fun r : ℝ ↦ ⨆ η : ℕ → ℝ, ∫⁻ w : Fin (d+1) → UnitAddCircle,
      let ν := baseSlopeLaw (by omega : 0<p) (d+1) a (centralLift w) η g
      ν {y | ENNReal.ofReal (r^h) < ν (Icc (y-A*r) (y+A*r))})
      (𝓝[>] 0) (𝓝 0) := by
  intro g
  have hp' : 0<p := by omega
  by_cases hp0 : 0<h
  · apply ENNReal.tendsto_nhds_zero.mpr
    intro δ dpos
    obtain ⟨u,hu,huδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp dpos
    have pos : 0<(u:ℝ) := by exact_mod_cast (show (0:ℝ≥0)<u by exact_mod_cast hu)
    filter_upwards [(slopeInformation_all hp a ha hc hc' hγ hγ' hbc hpoly j) h hp0 hs A hA u pos] with r small
    apply iSup_le;intro η
    rw [←slopeHeavy_eq_conditional_integral]
    exact (small η).trans (by simpa only [ENNReal.ofReal_coe_nnreal] using huδ.le)
  · apply (tendsto_const_nhds (x:=(0:ℝ≥0∞))).congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (rp : 0<r) r1
    apply Eq.symm;apply le_antisymm _ bot_le;apply iSup_le;intro η
    have th : (1:ℝ≥0∞)≤ENNReal.ofReal (r^h) := by
      rw [←ENNReal.ofReal_one];exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow_of_pos_of_le_one_of_nonpos rp r1.le (le_of_not_gt hp0))
    apply le_trans (lintegral_mono (g:=fun _ ↦ (0:ℝ≥0∞)) _) (by simp)
    intro w
    let ν := baseSlopeLaw hp' (d+1) a (centralLift w) η g
    have e : {y : ℝ | ENNReal.ofReal (r^h)<ν (Icc (y-A*r) (y+A*r))}=∅ := eq_empty_iff_forall_notMem.mpr (fun y upper ↦
      (not_lt_of_ge (((measure_mono (subset_univ _)).trans_eq (baseSlopeLaw_univ hp' (d+1) a (centralLift w) η g)).trans th)) upper)
    change ν _ ≤ 0
    rw [e,measure_empty]

end Weierstrass.Predecessor
