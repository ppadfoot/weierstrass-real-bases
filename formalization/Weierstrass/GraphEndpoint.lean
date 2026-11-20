module

public import Weierstrass.WindowLimit
public import Weierstrass.GraphProof
public import Weierstrass.GraphMeasureUpper

/-! Euclidean graph and measure conclusions at one fixed pair of parameters. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass

private theorem standard_graphMeasure (b l : ℝ) (phase : ℕ → ℝ) :
    graphMeasure b l phase (Icc 0 1) = GraphWindow.standardLaw.map (graphMap b l phase) := by
  simp [graphMeasure,GraphWindow.standardLaw,Measure.restrict_congr_set (μ:=volume)
    (Ico_ae_eq_Icc (a:=(0:ℝ)) (b:=1))]

/-- Exact dimensionality on the standard unit interval from the anchored
estimate and the physical, finite-window mass inequality. -/
theorem exactDimension_of_window {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (H : AnchoredEstimate b l 1) (φ : ℤ → ℝ) (T C : ℝ)
    (G : GraphWindow.WindowMassBound b l φ T C) :
    ExactDimensional (graphMeasure b l (fun j : ℕ ↦ φ j) (Icc 0 1)) (2-alpha b l) := by
  let phase (j : ℕ) := φ j
  let F := graphMap b l phase
  let μ := graphMeasure b l phase (Icc 0 1)
  let o : ℂ := ⟨0,T⟩
  let d := 2-alpha b l
  have hl₀ := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le
  have hi : (interior (Icc (0:ℝ) 1)).Nonempty := by rw [interior_Icc]; exact nonempty_Ioo.mpr zero_lt_one
  have hbd := (isCompact_Icc (a:=(0:ℝ)) (b:=1)).isBounded
  let _ : IsProbabilityMeasure μ := graphMeasure_probability hl₀ hl' b phase hi hbd
  have emb : MeasurableEmbedding F :=
    (continuous_graphMap hl₀ hl' b phase).measurableEmbedding (fun _ _ e ↦ congrArg Complex.re e)
  have hp : μ = GraphWindow.standardLaw.map F := standard_graphMeasure b l phase
  have hcell (s : ℝ) (hs : s < d) : ∀ᵐ z ∂μ, ∀ᶠ K : ℕ in atTop,
      μ {y | GraphInformation.squareLabel K o y = GraphInformation.squareLabel K o z} ≤
        ENNReal.ofReal (((1/2:ℝ)^s)^K) := by
    rw [hp,emb.ae_map_iff]
    filter_upwards [GraphWindow.cell_decay_of_window_mass hb hl hl' H φ T C G hs] with x hx
    filter_upwards [hx] with K hK
    let Q := {y | GraphInformation.squareLabel K o y = GraphInformation.squareLabel K o (F x)}
    have mQ : MeasurableSet Q :=
      (GraphInformation.measurable_squareLabel K o) (measurableSet_singleton _)
    change GraphWindow.standardLaw.map F Q ≤ _
    rw [Measure.map_apply emb.measurable mQ]
    exact hK
  have lower (r : ℚ) : ∀ᵐ z ∂μ, (0 < (r:ℝ) ∧ (r:ℝ) < d) → ∀ᶠ t : ℝ in 𝓝[>] 0,
      (r:ℝ) ≤ Real.log (μ (Metric.ball z t)).toReal/Real.log t := by
    by_cases hr : 0 < (r:ℝ) ∧ (r:ℝ) < d
    · obtain ⟨s,hr',hs⟩ := exists_between hr.2
      exact (GraphInformation.lower_local_of_dyadic_square_mass μ o hr.1 hr' (hcell s hs)).mono
        fun _ h _ ↦ h
    · exact .of_forall fun _ h ↦ (hr h).elim
  have dpos : 0 < d := by
    have e := (alpha_mem_Ioo hb hl hl').2
    dsimp [d]; linarith
  filter_upwards [ae_all_iff.mpr lower, ae_upper_local_dimension_graphMeasure hb hl hl' phase hi hbd]
    with z hlo hup
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,hr,hr'⟩ := exists_rat_btwn (max_lt ha dpos)
    exact (hlo r ⟨(le_max_right _ _).trans_lt hr,hr'⟩).mono
      (fun _ hh ↦ ((le_max_left _ _).trans_lt hr).trans_le hh)
  · intro c hc
    obtain ⟨w,hw,hw'⟩ := exists_between hc
    exact (hup w hw).mono (fun _ h ↦ h.trans_lt hw')

/-- The full interval and Hausdorff conclusions, for a fixed base and
amplitude, follow from exact dimensionality on the unit interval for all phases. -/
theorem fixedParameters_of_exact_unit {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (unit : ∀ phase : ℕ → ℝ, ExactDimensional (graphMeasure b l phase (Icc 0 1)) (2-alpha b l))
    (phase : ℕ → ℝ) (I : Set ℝ) (hI : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l)) := by
  have hl₀ := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le
  have each (J : Set ℝ) (hJ : J.OrdConnected) (hO : (interior J).Nonempty) (hd : Bornology.IsBounded J) :
      ExactDimensional (graphMeasure b l phase J) (2-alpha b l) := by
    apply exactDimension_of_unit_intervals hl₀ hl' phase _ hJ hO hd
    intro u
    rw [graphMeasure_unit_translate hl₀ hl' phase]
    exact exactDimension_translate _ (unit _) _
  refine ⟨le_antisymm (graph_dim_le_formula hb hl hl' phase I) ?_, each I hI hi⟩
  obtain ⟨x,hx⟩ := hi
  obtain ⟨a,z,_,nh,sub⟩ := exists_Icc_mem_subset_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  have hi' : (interior (Icc a z)).Nonempty := ⟨x,mem_interior_iff_mem_nhds.mpr nh⟩
  have bounded := (isCompact_Icc (a:=a) (b:=z)).isBounded
  let _ := graphMeasure_probability hl₀ hl' b phase hi' bounded
  have mass := graphMeasure_self (b:=b) hl₀ hl' phase hi' bounded
  exact ((each _ ordConnected_Icc hi' bounded).le_dimH_of_positive_mass (mass ▸ one_ne_zero)).trans
    (dimH_mono (image_mono sub))

end Weierstrass
