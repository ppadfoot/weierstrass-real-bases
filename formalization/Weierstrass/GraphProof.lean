module

public import Weierstrass.DimensionFromMeasure
public import Weierstrass.GraphInformation
public import Weierstrass.WindowBound
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Localizing graph measures to physical intervals

A graph ball projects into a physical interval of the same radius. At an
interior point of a parameter set its small-ball mass therefore depends on
that set only through the factor used to normalize Lebesgue measure.
-/

public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Weierstrass

private theorem physical_ball_subset {b lam : ℝ} (phase : ℕ → ℝ) (x r : ℝ) :
    graphMap b lam phase ⁻¹' ball (graphMap b lam phase x) r ⊆ ball x r := by
  intro y hy
  change dist (graphMap b lam phase y) (graphMap b lam phase x) < r at hy
  rw [dist_eq_norm] at hy
  change |y-x| < r
  exact (Complex.abs_re_le_norm (graphMap b lam phase y - graphMap b lam phase x)).trans_lt hy

/-- At an interior point, the only local effect of restriction is normalization. -/
theorem graphMeasure_ball_interior {b lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) {I : Set ℝ} {x : ℝ} (hx : x ∈ interior I) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, graphMeasure b lam phase I (ball (graphMap b lam phase x) r) =
      (volume I)⁻¹ * volume (graphMap b lam phase ⁻¹' ball (graphMap b lam phase x) r) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hm := (continuous_graphMap hl h1 b phase).measurable
  have hs := (physical_ball_subset phase x r (b := b) (lam := lam)).trans
    ((ball_subset_ball hr.2.le).trans hsub)
  rw [graphMeasure, Measure.map_apply hm isOpen_ball.measurableSet, Measure.smul_apply,
    Measure.restrict_apply (hm isOpen_ball.measurableSet), smul_eq_mul, inter_eq_left.mpr hs]

private theorem exact_rate_on_interior {b lam d : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) {I J : Set ℝ} {x : ℝ}
    (hxI : x ∈ interior I) (hxJ : x ∈ interior J)
    (hI : Bornology.IsBounded I) (hJ : volume J = 1)
    (h : Tendsto (fun r : ℝ ↦ Real.log
      ((graphMeasure b lam phase J) (ball (graphMap b lam phase x) r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r : ℝ ↦ Real.log
      ((graphMeasure b lam phase I) (ball (graphMap b lam phase x) r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 d) := by
  let c := ((volume I)⁻¹).toReal
  have hc : 0 < c := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr (hI.measure_lt_top (μ := volume)).ne)
    (ENNReal.inv_ne_top.mpr (Measure.measure_pos_of_nonempty_interior volume ⟨x,hxI⟩).ne')
  have shift : Tendsto (fun r : ℝ ↦ Real.log c / Real.log r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  apply (show Tendsto _ _ (𝓝 d) from (zero_add d) ▸ shift.add h).congr'
  filter_upwards [graphMeasure_ball_interior hl h1 phase hxI,
    graphMeasure_ball_interior hl h1 phase hxJ, self_mem_nhdsWithin] with r hrI hrJ hr
  let U := graphMap b lam phase ⁻¹' ball (graphMap b lam phase x) r
  have hu0 : 0 < volume U := (isOpen_ball.preimage (continuous_graphMap hl h1 b phase)).measure_pos
    volume ⟨x, mem_ball_self hr⟩
  have hu1 : volume U ≠ ∞ := ((measure_mono (physical_ball_subset phase x r)).trans_lt
    (measure_ball_lt_top (μ := volume))).ne
  have hreal := ENNReal.toReal_pos hu0.ne' hu1
  rw [hrI, hrJ, hJ, inv_one, one_mul, ENNReal.toReal_mul, Real.log_mul hc.ne' hreal.ne', add_div]

private theorem graphMap_embedding {b lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) : MeasurableEmbedding (graphMap b lam phase) :=
  (continuous_graphMap hl h1 b phase).measurableEmbedding (fun _ _ h ↦ congrArg Complex.re h)

/-- Rational translates of the unit interval suffice for exact dimensionality
on every bounded interval, independent of endpoint conventions. -/
theorem exactDimension_of_unit_intervals {b lam d : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) (units : ∀ u : ℚ,
      ExactDimensional (graphMeasure b lam phase (Icc (u:ℝ) (u+1))) d)
    {I : Set ℝ} (hc : I.OrdConnected) (hi : (interior I).Nonempty)
    (hbd : Bornology.IsBounded I) : ExactDimensional (graphMeasure b lam phase I) d := by
  let J (u : ℚ) := Icc (u:ℝ) (u+1)
  have volJ (u : ℚ) : volume (J u) = 1 := by
    simp [J, Real.volume_Icc]
  let rate (S : Set ℝ) (x : ℝ) := Tendsto (fun r : ℝ ↦ Real.log
    ((graphMeasure b lam phase S) (ball (graphMap b lam phase x) r)).toReal / Real.log r)
    (𝓝[>] 0) (𝓝 d)
  have emb := graphMap_embedding (b := b) hl h1 phase
  have each (u : ℚ) : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ J u → rate (J u) x := by
    have h := emb.ae_map_iff.mp (units u)
    change ∀ᵐ x ∂(volume (J u))⁻¹ • volume.restrict (J u), rate (J u) x at h
    rw [volJ, inv_one, one_smul] at h
    exact (ae_restrict_iff' measurableSet_Icc).mp h
  have allUnits := ae_all_iff.mpr each
  apply emb.ae_map_iff.mpr
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' hc.measurableSet).mpr
  filter_upwards [allUnits, volume.ae_ne (sInf I), volume.ae_ne (sSup I)] with x hx hBot hTop
  intro hxI
  have endpoints := subset_Icc_csInf_csSup hbd.bddBelow hbd.bddAbove hxI
  have openSub := (show IsConnected I from ⟨hi.mono interior_subset, hc.isPreconnected⟩).Ioo_csInf_csSup_subset
    hbd.bddBelow hbd.bddAbove
  have insideI : x ∈ interior I := (interior_maximal openSub isOpen_Ioo)
    ⟨lt_of_le_of_ne endpoints.1 hBot.symm, lt_of_le_of_ne endpoints.2 hTop⟩
  obtain ⟨u, hu, ux⟩ := exists_rat_btwn (show x-1 < x by linarith)
  have insideJ : x ∈ interior (J u) := by
    change x ∈ interior (Icc (u:ℝ) (u+1))
    rw [interior_Icc]
    exact ⟨ux, by linarith⟩
  exact exact_rate_on_interior hl h1 phase insideI insideJ hbd (volJ u)
    (hx u (interior_subset insideJ))

/-- The universal theorem is equivalent to its graph-measure clause on just
the countable family of unit intervals with rational left endpoints. -/
theorem mainStatement_iff_exactDimensionOnUnitIntervals : MainStatement ↔
    ∀ b lam : ℝ, 1 < b → b⁻¹ < lam → lam < 1 → ∀ (phase : ℕ → ℝ) (u : ℚ),
      ExactDimensional (graphMeasure b lam phase (Icc (u:ℝ) (u+1))) (2-alpha b lam) := by
  rw [mainStatement_iff_exactDimensionOnBoundedIntervals]
  constructor
  · intro h b lam hb hl h1 phase u
    apply h b lam hb hl h1 phase _ ordConnected_Icc _ isCompact_Icc.isBounded
    rw [interior_Icc]
    exact nonempty_Ioo.mpr (by linarith)
  · intro h b lam hb hl h1 phase I hc hi hbd
    exact exactDimension_of_unit_intervals
      ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le h1 phase (h b lam hb hl h1 phase) hc hi hbd

/-- Translating a physical input adds a prescribed amount to each phase. -/
theorem series_translate (b lam : ℝ) (phase : ℕ → ℝ) (u x : ℝ) :
    series b lam phase (u+x) = series b lam (fun j ↦ phase j + b^j*u) x := by
  apply tsum_congr
  intro j
  unfold term
  congr 3
  ring

/-- The graph on a translated unit interval is the horizontal translate of
the graph for the shifted phases on the standard unit interval, including its measure. -/
theorem graphMeasure_unit_translate {b lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) (u : ℝ) :
    graphMeasure b lam phase (Icc u (u+1)) =
      (graphMeasure b lam (fun j ↦ phase j + b^j*u) (Icc 0 1)).map (fun z : ℂ ↦ (u:ℂ)+z) := by
  have pre : (fun x : ℝ ↦ u+x) ⁻¹' Icc u (u+1) = Icc 0 1 := by
    ext x
    change (u ≤ u+x ∧ u+x ≤ u+1) ↔ (0 ≤ x ∧ x ≤ 1)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have push : (volume.restrict (Icc 0 1)).map (fun x : ℝ ↦ u+x) =
      volume.restrict (Icc u (u+1)) := by
    have hh := Measure.restrict_map (μ := volume) (measurable_const_add u)
      (s := Icc u (u+1)) measurableSet_Icc
    simpa only [pre, map_add_left_eq_self] using hh.symm
  have path : graphMap b lam phase ∘ (fun x : ℝ ↦ u+x) =
      (fun z : ℂ ↦ (u:ℂ)+z) ∘ graphMap b lam (fun j ↦ phase j + b^j*u) := by
    funext x
    apply Complex.ext
    · rfl
    · simp [graphMap, series_translate b lam phase u x]
  simp only [graphMeasure, Real.volume_Icc, add_sub_cancel_left, sub_zero, ENNReal.ofReal_one,
    inv_one, one_smul]
  rw [← push, Measure.map_map (continuous_graphMap hl h1 b phase).measurable (measurable_const_add u),
    Measure.map_map (measurable_const_add (u:ℂ)) (continuous_graphMap hl h1 b _).measurable, path]

theorem exactDimension_translate (μ : Measure ℂ) {d : ℝ} (h : ExactDimensional μ d)
    (u : ℂ) : ExactDimensional (μ.map (fun z : ℂ ↦ u+z)) d := by
  let tr := fun z : ℂ ↦ u+z
  have iso : Isometry tr := Isometry.of_dist_eq (fun x y ↦ dist_add_left _ _ _)
  apply (iso.continuous.measurableEmbedding iso.injective).ae_map_iff.mpr
  filter_upwards [h] with z hz
  apply hz.congr
  intro r
  rw [Measure.map_apply (measurable_const_add u) isOpen_ball.measurableSet, iso.preimage_ball]

/-- With the phases quantified universally, a single fixed unit interval
suffices for the whole graph and graph-measure theorem. -/
theorem mainStatement_iff_exactDimensionOnStandardUnitInterval : MainStatement ↔
    ∀ b lam : ℝ, 1 < b → b⁻¹ < lam → lam < 1 → ∀ phase : ℕ → ℝ,
      ExactDimensional (graphMeasure b lam phase (Icc 0 1)) (2-alpha b lam) := by
  rw [mainStatement_iff_exactDimensionOnUnitIntervals]
  constructor
  · intro h b lam hb hl h1 phase
    simpa using h b lam hb hl h1 phase 0
  · intro h b lam hb hl h1 phase u
    have hl₀ := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le
    rw [graphMeasure_unit_translate hl₀ h1 phase]
    exact exactDimension_translate _ (h b lam hb hl h1 _) _

namespace GraphInformation

private theorem unit_fiber (k : ℕ) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    let R := ((2:ℝ)^k)⁻¹
    let a := (dyadicLabel k 0 x : ℝ)*R
    {y | dyadicLabel k 0 y = dyadicLabel k 0 x} = Ico a (a+R) ∧ Ico a (a+R) ⊆ Ico 0 1 := by
  let R := ((2:ℝ)^k)⁻¹
  let a := (dyadicLabel k 0 x : ℝ)*R
  have P := pow_pos (by norm_num : (0:ℝ)<2) k
  have fiber : {y | dyadicLabel k 0 y = dyadicLabel k 0 x} = Ico a (a+R) := by
    ext y
    rw [mem_ofPred_eq,dyadicLabel,Int.floor_eq_iff,sub_zero]
    dsimp [a,R]
    constructor
    · rintro ⟨l,r⟩
      constructor
      · calc
          _ ≤ (2^k*y)*(2^k)⁻¹ := mul_le_mul_of_nonneg_right l (inv_pos.mpr P).le
          _ = y := by field_simp
      · have := mul_lt_mul_of_pos_right r (inv_pos.mpr P)
        have cancel : (2^k*y)*(2^k)⁻¹ = y := by field_simp
        rw [cancel] at this
        linarith
    · rintro ⟨l,r⟩
      constructor
      · rw [mul_comm (2^k:ℝ) y]
        apply (div_le_iff₀ P).mp
        simpa [div_eq_mul_inv, mul_comm] using l
      · have hh := mul_lt_mul_of_pos_right r P
        field_simp at hh
        linarith
  have sub : Ico a (a+R) ⊆ Ico 0 1 := by
    intro y hy
    have hsame : dyadicLabel k 0 y = dyadicLabel k 0 x := (Set.ext_iff.mp fiber y).mpr hy
    have h0 : dyadicLabel 0 0 y = dyadicLabel 0 0 x := by
      rw [← dyadicLabel_parent (Nat.zero_le k) 0 y, ← dyadicLabel_parent (Nat.zero_le k) 0 x, hsame]
    have hfloor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
    simpa only [dyadicLabel,pow_zero,sub_zero,one_mul,hfloor,Int.floor_eq_zero_iff] using h0
  exact ⟨fiber,sub⟩

private theorem unit_horizontal_mass (k : ℕ) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    (volume.restrict (Ico (0:ℝ) 1)) {y | dyadicLabel k 0 y = dyadicLabel k 0 x} =
      ENNReal.ofReal ((2:ℝ)^k)⁻¹ := by
  obtain ⟨fiber,sub⟩ := unit_fiber k x hx
  rw [fiber,Measure.restrict_apply' measurableSet_Ico,inter_eq_left.mpr sub,Real.volume_Ico,add_sub_cancel_left]

/-- The conditional probabilities in the moving-partition estimate can be
computed by measuring ordinary subsets of the realized physical dyadic cell. -/
private theorem verticalMass_on_unit (Y : ℝ → ℝ) (k j : ℕ) (T x : ℝ)
    (hx : x ∈ Ico (0:ℝ) 1) :
    let R := ((2:ℝ)^k)⁻¹
    let a := (dyadicLabel k 0 x : ℝ)*R
    verticalMass (volume.restrict (Ico (0:ℝ) 1)) id Y 0 T k j x =
      volume {y | y ∈ Ico a (a+R) ∧ dyadicLabel j T (Y y) = dyadicLabel j T (Y x)} /
        ENNReal.ofReal R := by
  let R := ((2:ℝ)^k)⁻¹
  let a := (dyadicLabel k 0 x : ℝ)*R
  obtain ⟨fiber,sub⟩ := unit_fiber k x hx
  unfold verticalMass conditionalLabelLaw
  dsimp only [id_eq]
  have eq : {y | dyadicLabel k 0 y = dyadicLabel k 0 x ∧ dyadicLabel j T (Y y) = dyadicLabel j T (Y x)} =
      {y | y ∈ Ico a (a+R) ∧ dyadicLabel j T (Y y) = dyadicLabel j T (Y x)} := by
    ext y
    exact and_congr (Set.ext_iff.mp fiber y) Iff.rfl
  rw [eq,fiber,Measure.restrict_apply' measurableSet_Ico, Measure.restrict_apply' measurableSet_Ico,
    inter_eq_left.mpr (fun y hy ↦ sub hy.1), inter_eq_left.mpr sub, Real.volume_Ico]
  simp only [add_sub_cancel_left]
  rfl

private theorem cell_coords (k : ℕ) (o x : ℝ) :
    x ∈ Ico (o+(dyadicLabel k o x:ℝ)*((2:ℝ)^k)⁻¹)
      (o+(dyadicLabel k o x:ℝ)*((2:ℝ)^k)⁻¹+((2:ℝ)^k)⁻¹) := by
  have h := Int.floor_eq_iff.mp (rfl : ⌊(2:ℝ)^k*(x-o)⌋ = dyadicLabel k o x)
  have hP := pow_pos (by norm_num : (0:ℝ)<2) k
  have l := mul_le_mul_of_nonneg_right h.1 (inv_pos.mpr hP).le
  have r := mul_lt_mul_of_pos_right h.2 (inv_pos.mpr hP)
  have e : (2^k*(x-o))*(2^k)⁻¹ = x-o := by field_simp
  rw [e] at l r
  unfold dyadicLabel
  exact ⟨by linarith, by linarith⟩

/-- (G2) for the realized vertical label of the actual one-sided series.
A single scale threshold works for all phases, base points and vertical origins. -/
theorem fine_verticalMass_entropy {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (q : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ (phase : ℤ → ℝ) (k j : ℕ) (x T : ℝ),
      x ∈ Ico (0:ℝ) 1 → (b^n)⁻¹/2 ≤ ((2:ℝ)^k)⁻¹ → ((2:ℝ)^k)⁻¹ ≤ (b^n)⁻¹ →
      ((2:ℝ)^j)⁻¹ ≤ 2*lam^(n+q) →
      verticalMass (volume.restrict (Ico (0:ℝ) 1)) id (series b lam (fun j : ℕ ↦ phase j))
        0 T k j x ≤ ENNReal.ofReal (Real.exp (-graphEntropy b lam q (fun i ↦ ↑(environment b phase n x i)))) := by
  filter_upwards [fine_cell_occupation hb hl h1 q] with n hn
  intro phase k j x T hx low high J
  let W := series b lam (fun j : ℕ ↦ phase j)
  let R := ((2:ℝ)^k)⁻¹
  let a := (dyadicLabel k 0 x : ℝ)*R
  let S := ((2:ℝ)^j)⁻¹
  let v := T+(dyadicLabel j T (W x):ℝ)*S
  let z : PhaseTorus := fun i ↦ ↑(environment b phase n x i)
  have hx' : x ∈ Ico a (a+R) := by simpa only [zero_add,a,R] using cell_coords k 0 x
  have hv : W x ∈ Ico v (v+S) := cell_coords j T (W x)
  have h := hn phase x a R v S low high J (Ico_subset_Icc_self hx') (Ico_subset_Icc_self hv)
  let E := {y : ℝ | y ∈ Ico a (a+R) ∧ dyadicLabel j T (W y) = dyadicLabel j T (W x)}
  have eb : E ⊆ {y | y ∈ Icc a (a+R) ∧ W y ∈ Icc v (v+S)} := by
    rintro y ⟨hy,hlbl⟩
    have hy' := cell_coords j T (W y)
    rw [hlbl] at hy'
    exact ⟨Ico_subset_Icc_self hy,Ico_subset_Icc_self hy'⟩
  rw [verticalMass_on_unit _ _ _ _ _ hx]
  let V := volume E / ENNReal.ofReal R
  have b1 : V ≤ 1 := by
    have rpos : 0 < R := by dsimp [R]; positivity
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr rpos).ne' ENNReal.ofReal_ne_top).mpr
    calc
      volume E ≤ volume (Ico a (a+R)) := measure_mono (fun _ hy ↦ hy.1)
      _ = _ := by rw [Real.volume_Ico,add_sub_cancel_left,one_mul]
  have bcut : V ≤ 2*occupation b lam 1 3 (lam^q) z := (mul_le_mul_of_nonneg_right (measure_mono eb) (zero_le (α := ℝ≥0∞))).trans h
  have hoc : occupation b lam 1 3 (lam^q) z ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := volume (Icc (-1:ℝ) 1))
    · simp
    · exact measure_mono (fun _ hx ↦ hx.1)
  have c := (graphCutoff_sandwich hb hl q z).1
  have hl0 := (inv_pos.mpr (zero_lt_one.trans hb)).trans hl
  change V ≤ ENNReal.ofReal (Real.exp (-(-Real.log (min 1 (max (lam^q) (graphCutoff b lam q z))))))
  rw [neg_neg, Real.exp_log (lt_min zero_lt_one ((pow_pos hl0 q).trans_le (le_max_left _ _))),
    ENNReal.ofReal_min, ENNReal.ofReal_one]
  apply le_min b1
  calc
    V ≤ 2*occupation b lam 1 3 (lam^q) z := bcut
    _ = ENNReal.ofReal (2*(occupation b lam 1 3 (lam^q) z).toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_toReal hoc]; norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal (c.trans (le_max_right _ _))

/-- The normalized coarse dyadic probability (G3) in the same
conditional-law notation as the true fine-label estimate. -/
theorem coarse_verticalMass {b lam C α : ℝ} (hC : 1 ≤ C) (hα : 0 < α)
    (phase : ℕ → ℝ) (hold : ∀ y z, |y-z| ≤ 1 →
      |series b lam phase y-series b lam phase z| ≤ C*|y-z|^α)
    (k j : ℕ) (x T : ℝ) (hx : x ∈ Ico (0:ℝ) 1) (scale : (((2:ℝ)^k)⁻¹)^α ≤ ((2:ℝ)^j)⁻¹)
    (hn : (↑((2:ℝ)^j*(series b lam phase x-T)) : UnitAddCircle) ≠ 0) :
    ENNReal.ofReal ((‖(↑((2:ℝ)^j*(series b lam phase x-T)) : UnitAddCircle)‖/C)^α⁻¹) ≤
      verticalMass (volume.restrict (Ico (0:ℝ) 1)) id (series b lam phase) 0 T k j x := by
  let W := series b lam phase
  let R := ((2:ℝ)^k)⁻¹
  let a := (dyadicLabel k 0 x : ℝ)*R
  have hx' : x ∈ Icc a (a+R) := Ico_subset_Icc_self (by simpa only [zero_add,a,R] using cell_coords k 0 x)
  have R1 : R ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have equiv (y : ℝ) : (W y-T)/((2:ℝ)^j)⁻¹ = 2^j*(W y-T) := by simp [div_eq_mul_inv,mul_comm]
  have h := coarse_dyadic_conditional_mass hold hC hα (show 0<R by dsimp [R]; positivity) R1 scale hx'
    (by rw [equiv]; exact hn)
  rw [verticalMass_on_unit _ _ _ _ _ hx]
  dsimp only [W] at equiv
  simpa only [equiv,dyadicLabel,a,R] using h

/-- The actual target square in the graph lift has the moving-window
entropy loss of Appendix A. The boundary constant is chosen before q. -/
theorem square_mass_window_bound {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (phase : ℤ → ℝ) : ∃ T C, GraphWindow.WindowMassBound b lam phase T C := by
  let W := series b lam (fun j : ℕ ↦ phase j)
  let μ := (volume : Measure ℝ).restrict (Ico 0 1)
  let a := GraphWindow.verticalRate lam
  let d := GraphWindow.horizontalRate b
  let α := alpha b lam
  have hl₀ := (inv_pos.mpr (zero_lt_one.trans hb)).trans hl
  have ⟨ha,had⟩ := GraphWindow.rates_admissible hb hl h1
  have hα := (alpha_mem_Ioo hb hl h1).1
  let _ : IsProbabilityMeasure μ := ⟨by simp [μ,Real.volume_Ico]⟩
  have hmW : Measurable W := (continuous_series hl₀.le h1 b _).measurable
  obtain ⟨C₀,hC₀,hW⟩ := holder_estimate hb hl h1
  let C := max 1 C₀
  have hC : 1 ≤ C := le_max_left _ _
  have hold (y z : ℝ) (hyz : |y-z| ≤ 1) : |W y-W z| ≤ C*|y-z|^α :=
    (hW _ y z hyz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  obtain ⟨T,hT⟩ := exists_vertical_origin μ W hmW
  refine ⟨T,C,?_⟩
  unfold GraphWindow.WindowMassBound
  let n (q K i : ℕ) := q*(GraphWindow.left q d K + i)
  let k (q K i : ℕ) := ⌈d*(n q K i:ℝ)⌉₊
  let j (q K i : ℕ) := ⌊a*(n q K i:ℝ)⌋₊
  let m (q K : ℕ) := GraphWindow.right q a K-GraphWindow.left q d K
  let e₀ (v : ℕ) : ℝ := 1/(v+1:ℝ)
  let Mass K x := μ {y | (dyadicLabel K 0 y, dyadicLabel K T (W y)) =
                           (dyadicLabel K 0 x, dyadicLabel K T (W x))}
  let G q x (i : ℕ) := graphEntropy b lam q (fun s ↦ ↑(environment b phase (q*i) x s))
  let B x l := ‖(↑((2:ℝ)^l*(W x-T)) : UnitAddCircle)‖
  have last {q : ℕ} (hq : 0 < q) : ∀ᶠ K : ℕ in atTop, j q K (m q K) ≤ K := by
    filter_upwards [(GraphWindow.endpoint_limits hq ha had).2.2.1] with K hK
    exact GraphWindow.vertical_depth hq ha (Nat.add_sub_of_le hK.le ▸ le_rfl)
  have supply (q v : ℕ) : ∀ᵐ x ∂μ, 0 < q → ∀ᶠ K : ℕ in atTop, Mass K x ≤
      μ {y | dyadicLabel K 0 y = dyadicLabel K 0 x} * ENNReal.ofReal (Real.exp (e₀ v))^K *
        ∏ i ∈ Finset.range (m q K), verticalMass μ id W 0 T (k q K i) (j q K (i+1)) x /
          verticalMass μ id W 0 T (k q K i) (j q K i) x := by
    by_cases hq : 0 < q
    · have hm := ae_moving_square_product μ id W measurable_id hmW 0 T (k q) (j q) (m q)
        (fun K i ↦ GraphWindow.horizontal_depth hq (ha.trans had) (Nat.le_add_right _ _))
        (fun K i ↦ Nat.ceil_mono (by dsimp only [n]; gcongr <;> first | exact (ha.trans had).le | omega))
        (fun K i ↦ Nat.floor_mono (by dsimp only [n]; gcongr; omega)) (last hq)
        (t := ENNReal.ofReal (Real.exp (e₀ v))) (by
          rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.one_lt_exp_iff]
          dsimp [e₀]; positivity) ENNReal.ofReal_ne_top
      exact hm.mono (fun _ h _ ↦ h)
    · exact .of_forall (fun _ h ↦ (hq h).elim)
  filter_upwards [hT, ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico,
    ae_all_iff.mpr (fun q ↦ ae_all_iff.mpr (supply q))] with x hboundary hx hmass
  obtain ⟨hnz,D,hD⟩ := hboundary
  have D0 : 0 ≤ D := by
    have h := hD 1
    simp only [Finset.sum_range_one, Nat.cast_one, mul_one] at h
    exact (sq_nonneg _).trans h
  refine ⟨D,D0,?_⟩
  intro q hq hqa v
  obtain ⟨N,hN⟩ := eventually_atTop.mp (fine_verticalMass_entropy hb hl h1 q)
  have large := (GraphWindow.endpoint_limits hq ha had).1.eventually_ge_atTop N
  filter_upwards [hmass q v hq, large, last hq] with K HK hL hend
  let L := GraphWindow.left q d K
  let M := m q K
  let S := Finset.range M
  let jj := j q K
  let F i := -G q x (L+i) + (Real.log C - Real.log (B x (jj i)))/α
  have strict : StrictMono jj := (GraphWindow.vertical_strictMono hqa).comp (fun _ _ h ↦ Nat.add_lt_add_left h L)
  have normpos l : 0 < B x l := norm_pos_iff.mpr (hnz l)
  have cpos := zero_lt_one.trans_le hC
  have ratio (i : ℕ) : verticalMass μ id W 0 T (k q K i) (jj (i+1)) x /
        verticalMass μ id W 0 T (k q K i) (jj i) x ≤ ENNReal.ofReal (Real.exp (F i)) := by
    have deeper : N ≤ n q K i := hL.trans ((Nat.le_add_right _ _).trans
      (Nat.le_mul_of_pos_left _ hq))
    have hnext : n q K (i+1) = n q K i + q := by dsimp [n]; ring
    have widths := GraphWindow.horizontal_width hb (n q K i)
    have fine := hN _ deeper phase (k q K i) (jj (i+1)) x T hx widths.1 widths.2
      (hnext ▸ (GraphWindow.vertical_width hl₀ h1 (n q K (i+1))).2)
    have coarse := coarse_verticalMass hC hα (fun j : ℕ ↦ phase j) hold
      (k q K i) (jj i) x T hx (GraphWindow.holder_scale hb hl h1 (n q K i)) (hnz _)
    let denom := (B x (jj i)/C)^α⁻¹
    have denPos : 0 < denom := Real.rpow_pos_of_pos (div_pos (normpos _) cpos) _
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-G q x (L+i))) / ENNReal.ofReal denom := by
        exact mul_le_mul' fine (ENNReal.inv_le_inv.mpr coarse)
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos denPos]
        congr 1
        dsimp only [F]
        rw [Real.exp_add, div_eq_mul_inv]
        congr 1
        have eq : (Real.log C - Real.log (B x (jj i)))/α = -Real.log denom := by
          rw [show Real.log denom = α⁻¹ * Real.log (B x (jj i)/C) from Real.log_rpow (div_pos (normpos _) cpos) _,
            Real.log_div (normpos _).ne' cpos.ne']
          ring
        rw [eq, Real.exp_neg, Real.exp_log denPos]
  have prodBound : (∏ i ∈ S, verticalMass μ id W 0 T (k q K i) (jj (i+1)) x /
        verticalMass μ id W 0 T (k q K i) (jj i) x) ≤ ENNReal.ofReal (Real.exp (∑ i ∈ S,F i)) := by
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    exact Finset.prod_le_prod' (fun i _ ↦ ratio i)
  have included : S.image jj ⊆ Finset.range (K+1) := by
    intro l hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((strict.monotone (Finset.mem_range.mp hi).le).trans hend))
  have sqsum : (∑ i ∈ S, (Real.log (B x (jj i)))^2) ≤ D*(K+1) := by
    calc
      _ = ∑ l ∈ S.image jj, (Real.log (B x l))^2 :=
        (Finset.sum_image (fun _ _ _ _ h ↦ strict.injective h)).symm
      _ ≤ ∑ l ∈ Finset.range (K+1), (Real.log (B x l))^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg included (fun _ _ _ ↦ sq_nonneg _)
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using hD (K+1)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ ↦ (1:ℝ)) (fun i ↦ -Real.log (B x (jj i)))
  simp only [one_mul, one_pow, Finset.sum_const, S, Finset.card_range, nsmul_eq_mul, mul_one, neg_sq] at cs
  have loss : (∑ i ∈ S, -Real.log (B x (jj i))) ≤ Real.sqrt ((M:ℝ)*D*(K+1)) := by
    apply Real.le_sqrt_of_sq_le
    apply cs.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left sqsum (Nat.cast_nonneg M)
  have sumG : (∑ i ∈ S,G q x (L+i)) = GraphWindow.windowSum b lam phase q K x := by
    rw [GraphWindow.windowSum,Finset.sum_Ico_eq_sum_range]
  have sumF : (∑ i ∈ S,F i) ≤ -GraphWindow.windowSum b lam phase q K x +
      ((M:ℝ)*Real.log C + Real.sqrt ((M:ℝ)*D*(K+1)))/α := by
    simp only [F,Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.sum_div,Finset.sum_sub_distrib,
      Finset.sum_const,S,Finset.card_range,nsmul_eq_mul] at ⊢
    rw [show (∑ i ∈ Finset.range M,G q x (L+i)) = _ from sumG]
    gcongr
    simpa only [S,Finset.sum_neg_distrib, sub_eq_add_neg] using add_le_add_right loss ((M:ℝ)*Real.log C)
  have horiz := unit_horizontal_mass K x hx
  have hpow : ((2:ℝ)^K)⁻¹ = Real.exp (-(K:ℝ)*Real.log 2) := by
    rw [neg_mul,Real.exp_neg,← Real.log_pow,Real.exp_log (by positivity)]
  have times : ENNReal.ofReal (Real.exp (e₀ v))^K = ENNReal.ofReal (Real.exp ((K:ℝ)*e₀ v)) := by
    rw [Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le]
  change Mass K x ≤ _
  calc
    _ ≤ _ := HK
    _ ≤ ENNReal.ofReal ((2:ℝ)^K)⁻¹ * ENNReal.ofReal (Real.exp (e₀ v))^K *
        ENNReal.ofReal (Real.exp (∑ i ∈ S,F i)) := by
      change μ {y | dyadicLabel K 0 y = dyadicLabel K 0 x} = _ at horiz
      rw [horiz]
      exact mul_le_mul_of_nonneg_left prodBound zero_le
    _ = ENNReal.ofReal (Real.exp (-(K:ℝ)*Real.log 2+K*e₀ v+(∑ i ∈ S,F i))) := by
      rw [hpow,times,Real.exp_add,Real.exp_add,ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      change _ ≤ -(K:ℝ)*Real.log 2 + K/((v:ℝ)+1) - GraphWindow.windowSum b lam phase q K x +
        ((M:ℝ)*Real.log C + Real.sqrt ((M:ℝ)*D*(K+1)))/α
      dsimp only [e₀]
      rw [mul_one_div]
      linarith only [sumF]

end GraphInformation
end Weierstrass
