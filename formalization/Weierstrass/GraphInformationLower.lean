module

public import Weierstrass.GraphComparison

/-! Appendix A.1 at every information exponent, including the graph comparison
at a subcritical amount of conditional information. -/
@[expose] public noncomputable section
open Filter Set MeasureTheory
open scoped ENNReal Topology
namespace Weierstrass

private theorem standard_graph_subset {b g v : ℝ} (hb : 1<b) (hg : b⁻¹<g) (hg1 : g<1)
    (hv : 0<v) (hv1 : v≤1) (H : AnchoredEstimate b g v) (ψ : ℕ → ℝ)
    {J : Set ℝ} (mJ : MeasurableSet J) (hJ : J ⊆ Ico 0 1) (pos : volume J ≠ 0) :
    ENNReal.ofReal (1+v*(1-alpha b g)) ≤ dimH (graph b g ψ J) := by
  let φ (j : ℤ) := ψ j.toNat
  obtain ⟨T,C,win⟩ := GraphInformation.square_mass_window_bound hb hg hg1 φ
  let F := graphMap b g ψ
  let μ := GraphWindow.standardLaw.map F
  let o : ℂ := ⟨0,T⟩
  have gp := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hg).le
  have emb : MeasurableEmbedding F := (continuous_graphMap gp hg1 b ψ).measurableEmbedding
    (fun _ _ h ↦ congrArg Complex.re h)
  let : IsProbabilityMeasure GraphWindow.standardLaw := ⟨by simp [GraphWindow.standardLaw,Real.volume_Ico]⟩
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map emb.measurable.aemeasurable
  have hcell (s : ℝ) (hs : s < 1+v*(1-alpha b g)) : ∀ᵐ z ∂μ, ∀ᶠ k : ℕ in atTop,
      μ {y | GraphInformation.squareLabel k o y = GraphInformation.squareLabel k o z} ≤ ENNReal.ofReal (((1/2:ℝ)^s)^k) := by
    change ∀ᵐ z ∂GraphWindow.standardLaw.map F, _
    rw [emb.ae_map_iff]
    filter_upwards [GraphWindow.cell_decay_at_information hb hg hg1 hv hv1 H φ T C win hs] with x hx
    filter_upwards [hx] with k h
    let Q := {y | GraphInformation.squareLabel k o y = GraphInformation.squareLabel k o (F x)}
    have mQ : MeasurableSet Q := (GraphInformation.measurable_squareLabel k o) (measurableSet_singleton _)
    change (GraphWindow.standardLaw.map F) Q ≤ _
    rw [Measure.map_apply emb.measurable mQ]
    change GraphWindow.standardLaw {y | (GraphInformation.dyadicLabel k 0 y,GraphInformation.dyadicLabel k T (series b g ψ y)) = (GraphInformation.dyadicLabel k 0 x,GraphInformation.dyadicLabel k T (series b g ψ x))} ≤ _
    simpa only [φ,Int.toNat_natCast,GraphWindow.cellMass] using h
  have positive : μ (graph b g ψ J) ≠ 0 := by
    have h := Measure.le_map_apply_image (μ:=GraphWindow.standardLaw) emb.measurable.aemeasurable J
    have sz : GraphWindow.standardLaw J = volume J := by
      rw [GraphWindow.standardLaw,Measure.restrict_apply mJ,inter_eq_self_of_subset_left hJ]
    rw [sz] at h
    exact fun zero ↦ pos (bot_unique (h.trans zero.le))
  apply le_dimH_of_lower_ball_law (μ:=μ) _ positive
  intro s hs sU
  obtain ⟨u,su,uU⟩ := exists_between sU
  obtain ⟨t,ut,tU⟩ := exists_between uU
  have L := GraphInformation.lower_local_of_dyadic_square_mass μ o (hs.trans_lt su) ut (hcell t tU)
  filter_upwards [L] with x hx
  filter_upwards [hx,Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with r lr hr
  by_cases hzero : (μ (Metric.ball x r)).toReal=0
  · rw [hzero];exact Real.rpow_nonneg hr.1.le _
  · apply (Real.log_le_log_iff (ENNReal.toReal_nonneg.lt_of_ne' hzero) (Real.rpow_pos_of_pos hr.1 _)).mp
    rw [Real.log_rpow hr.1];exact ((lt_div_iff_of_neg (Real.log_neg hr.1 hr.2)).mp (su.trans_le lr)).le

/-- Proposition A.1, for every `0 < v ≤ 1` and every nonempty open part of
an arbitrary input set. The input need not be bounded or connected. -/
theorem graph_lower_of_anchored_information {b g v : ℝ} (hb : 1<b) (hg : b⁻¹<g) (hg1 : g<1)
    (hv : 0<v) (hv1 : v≤1) (H : AnchoredEstimate b g v) (ψ : ℕ → ℝ)
    {I : Set ℝ} (hi : (interior I).Nonempty) :
    ENNReal.ofReal (1+v*(1-alpha b g)) ≤ dimH (graph b g ψ I) := by
  obtain ⟨x,hx⟩ := hi
  let u := x-1/2
  let J := (fun y : ℝ ↦ u+y) ⁻¹' interior I ∩ Ioo 0 1
  have op : IsOpen J := (isOpen_interior.preimage (continuous_const.add continuous_id)).inter isOpen_Ioo
  have nj : J.Nonempty := ⟨1/2,by change u+1/2 ∈ interior I ∧ _;dsimp only [u];rw [sub_add_cancel];exact ⟨hx,by norm_num⟩⟩
  let φ := fun j : ℕ ↦ ψ j+b^j*u
  have h := standard_graph_subset hb hg hg1 hv hv1 H φ op.measurableSet (fun y hy ↦ ⟨hy.2.1.le,hy.2.2⟩) (op.measure_pos volume nj).ne'
  have sub : (fun z : ℂ ↦ (u:ℂ)+z) '' graph b g φ J ⊆ graph b g ψ I := by
    rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
    refine ⟨u+y,interior_subset hy.1,?_⟩
    apply Complex.ext
    · rfl
    · simp [graphMap,φ,series_translate b g ψ u y]
  have tr := (isometry_add_left (u:ℂ)).dimH_image (graph b g φ J)
  exact h.trans (tr ▸ dimH_mono sub)

end Weierstrass
