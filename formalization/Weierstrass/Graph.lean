module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The prescribed-phase cosine graph

Phases are represented by real lifts in turns. The theorem
`series_add_int_phase` proves independence of all these choices. A point
of the graph is encoded as a complex number, with its usual Euclidean metric.
-/

@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace Weierstrass

def term (b lam : ℝ) (phase : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  lam ^ j * Real.cos (2 * Real.pi * (b ^ j * x + phase j))

def series (b lam : ℝ) (phase : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j, term b lam phase j x

theorem series_add_int_phase (b lam : ℝ) (phase : ℕ → ℝ) (k : ℕ → ℤ) :
    series b lam (fun j ↦ phase j + k j) = series b lam phase := by
  funext x
  unfold series
  apply tsum_congr
  intro j
  unfold term
  congr 1
  rw [show 2 * Real.pi * (b ^ j * x + (phase j + k j)) =
    2 * Real.pi * (b ^ j * x + phase j) + (k j : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

theorem norm_term_le {lam : ℝ} (hl : 0 ≤ lam) (b : ℝ) (phase : ℕ → ℝ)
    (j : ℕ) (x : ℝ) : ‖term b lam phase j x‖ ≤ lam ^ j := by
  rw [term, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hl j)]
  exact mul_le_of_le_one_right (pow_nonneg hl j) (Real.abs_cos_le_one _)

theorem summable_term {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1) (b : ℝ)
    (phase : ℕ → ℝ) (x : ℝ) : Summable (fun j ↦ term b lam phase j x) :=
  (summable_geometric_of_lt_one hl h1).of_norm_bounded (fun j ↦ norm_term_le hl b phase j x)

theorem uniform_convergence {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (b : ℝ) (phase : ℕ → ℝ) :
    TendstoUniformly (fun N x ↦ ∑ j ∈ Finset.range N, term b lam phase j x)
      (series b lam phase) atTop :=
  tendstoUniformly_tsum_nat (summable_geometric_of_lt_one hl h1) (norm_term_le hl b phase)

theorem continuous_series {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (b : ℝ) (phase : ℕ → ℝ) : Continuous (series b lam phase) := by
  apply continuous_tsum (u := fun j : ℕ ↦ lam ^ j)
  · intro j
    unfold term
    fun_prop
  · exact summable_geometric_of_lt_one hl h1
  · exact norm_term_le hl b phase

def graphMap (b lam : ℝ) (phase : ℕ → ℝ) (x : ℝ) : ℂ :=
  ⟨x, series b lam phase x⟩

def graph (b lam : ℝ) (phase : ℕ → ℝ) (I : Set ℝ) : Set ℂ :=
  graphMap b lam phase '' I

theorem graph_eq_image (b lam : ℝ) (phase : ℕ → ℝ) (I : Set ℝ) :
    graph b lam phase I = (fun x : ℝ ↦ (⟨x, series b lam phase x⟩ : ℂ)) '' I := rfl

theorem series_eq_tsum (b lam : ℝ) (phase : ℕ → ℝ) (x : ℝ) :
    series b lam phase x = ∑' j : ℕ, lam ^ j * Real.cos (2 * Real.pi * (b ^ j * x + phase j)) :=
  rfl

def graphMeasure (b lam : ℝ) (phase : ℕ → ℝ) (I : Set ℝ) : Measure ℂ :=
  Measure.map (graphMap b lam phase) ((volume I)⁻¹ • volume.restrict I)

theorem continuous_graphMap {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (b : ℝ) (phase : ℕ → ℝ) : Continuous (graphMap b lam phase) := by
  unfold graphMap
  simp only [Complex.mk_eq_add_mul_I]
  exact Complex.continuous_ofReal.add
    ((Complex.continuous_ofReal.comp (continuous_series hl h1 b phase)).mul continuous_const)

theorem graphMeasure_probability {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (b : ℝ) (phase : ℕ → ℝ) {I : Set ℝ} (hi : (interior I).Nonempty)
    (hbd : Bornology.IsBounded I) : IsProbabilityMeasure (graphMeasure b lam phase I) := by
  constructor
  rw [graphMeasure, Measure.map_apply (continuous_graphMap hl h1 b phase).measurable MeasurableSet.univ]
  simp only [preimage_univ, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_pos_of_nonempty_interior volume hi).ne'
    (hbd.measure_lt_top (μ := volume)).ne

/-- The mass of a Euclidean ball about a point on the graph, written in physical coordinates. -/
theorem graphMeasure_ball {lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (b : ℝ) (phase : ℕ → ℝ) (I : Set ℝ) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    graphMeasure b lam phase I (Metric.ball (graphMap b lam phase x) r) =
      (volume I)⁻¹ * volume ({y : ℝ | (y - x) ^ 2 +
        (series b lam phase y - series b lam phase x) ^ 2 < r ^ 2} ∩ I) := by
  have hm := (continuous_graphMap hl h1 b phase).measurable
  rw [graphMeasure, Measure.map_apply hm Metric.isOpen_ball.measurableSet, Measure.smul_apply,
    Measure.restrict_apply (hm Metric.isOpen_ball.measurableSet), smul_eq_mul]
  have hpre : (graphMap b lam phase) ⁻¹' Metric.ball (graphMap b lam phase x) r =
      {y : ℝ | (y - x) ^ 2 + (series b lam phase y - series b lam phase x) ^ 2 < r ^ 2} := by
    ext y
    change dist (graphMap b lam phase y) (graphMap b lam phase x) < r ↔ _
    rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hr.le, Complex.sq_norm, Complex.normSq_apply]
    simp [graphMap, sq]
  rw [hpre]

/-- Orthogonal projection onto the first coordinate recovers the interval. -/
theorem one_le_graph_dim (b lam : ℝ) (phase : ℕ → ℝ) {I : Set ℝ}
    (hI : (interior I).Nonempty) : 1 ≤ dimH (graph b lam phase I) := by
  have himage : Complex.reCLM '' graph b lam phase I = I := by
    rw [graph, image_image]
    exact image_id I
  have h := Complex.reCLM.lipschitz.dimH_image_le (graph b lam phase I)
  rw [himage, Real.dimH_of_nonempty_interior hI, Module.finrank_self, Nat.cast_one] at h
  exact h

theorem graph_dim_le_two (b lam : ℝ) (phase : ℕ → ℝ) (I : Set ℝ) :
    dimH (graph b lam phase I) ≤ 2 := by
  calc
    _ ≤ dimH (univ : Set ℂ) := dimH_mono (subset_univ _)
    _ = 2 := by
      rw [Real.dimH_univ_eq_finrank, Complex.equivRealProdCLM.toLinearEquiv.finrank_eq,
        Module.finrank_prod, Module.finrank_self]
      norm_num

def alpha (b lam : ℝ) := -(Real.log lam) / Real.log b

def ExactDimensional (μ : Measure ℂ) (d : ℝ) : Prop :=
  ∀ᵐ z ∂μ, Tendsto (fun r : ℝ ↦ Real.log (μ (Metric.ball z r)).toReal / Real.log r)
    (𝓝[>] 0) (𝓝 d)

/-- The graph and graph-measure assertions of Theorem 1.1, as a proof target. -/
def MainStatement : Prop :=
  ∀ b lam : ℝ, 1 < b → b⁻¹ < lam → lam < 1 →
    ∀ (phase : ℕ → ℝ) (I : Set ℝ), I.OrdConnected → (interior I).Nonempty →
      dimH (graph b lam phase I) = ENNReal.ofReal (2 - alpha b lam) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b lam phase I) (2 - alpha b lam))

theorem dimension_formula (b lam : ℝ) : 2 - alpha b lam = 2 + Real.log lam / Real.log b := by
  simp [alpha, neg_div]

theorem alpha_mem_Ioo {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1) :
    alpha b lam ∈ Ioo 0 1 := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hlog := Real.log_lt_log (inv_pos.mpr hb0) hl
  rw [Real.log_inv] at hlog
  exact ⟨div_pos (neg_pos.mpr (Real.log_neg hl0 h1)) (Real.log_pos hb),
    (div_lt_iff₀ (Real.log_pos hb)).mpr (by linarith)⟩

private theorem term_increment {b lam : ℝ} (hb : 0 ≤ b) (hl : 0 ≤ lam)
    (phase : ℕ → ℝ) (j : ℕ) (x y : ℝ) :
    |term b lam phase j x - term b lam phase j y| ≤
      (2 * Real.pi * |x - y|) * (b * lam) ^ j := by
  unfold term
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hl j)]
  calc
    _ ≤ lam ^ j * |2 * Real.pi * (b ^ j * x + phase j) -
        2 * Real.pi * (b ^ j * y + phase j)| :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (pow_nonneg hl j)
    _ = _ := by
      rw [show 2 * Real.pi * (b ^ j * x + phase j) - 2 * Real.pi * (b ^ j * y + phase j) =
        (2 * Real.pi * b ^ j) * (x - y) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * b ^ j), mul_pow]
      ring

/-- Split at any frequency cutoff. The two summands bound the low and high frequencies. -/
theorem increment_bound_at_cutoff {b lam : ℝ} (hb : 0 ≤ b) (hl : 0 ≤ lam)
    (h1 : lam < 1) (phase : ℕ → ℝ) (x y : ℝ) (N : ℕ) :
    |series b lam phase x - series b lam phase y| ≤
      (2 * Real.pi * |x - y|) * (∑ j ∈ Finset.range N, (b * lam) ^ j) +
      2 * lam ^ N * (1 - lam)⁻¹ := by
  let f (j : ℕ) := term b lam phase j x - term b lam phase j y
  have sx := summable_term hl h1 b phase x
  have sy := summable_term hl h1 b phase y
  have sf : Summable f := sx.sub sy
  have low : |∑ j ∈ Finset.range N, f j| ≤
      (2 * Real.pi * |x - y|) * (∑ j ∈ Finset.range N, (b * lam) ^ j) := by
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ ↦ term_increment hb hl phase j x y)
  have high : |∑' j : ℕ, f (j + N)| ≤ 2 * lam ^ N * (1 - lam)⁻¹ := by
    rw [← Real.norm_eq_abs]
    apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hl h1).mul_left (2 * lam ^ N))
    intro j
    calc
      ‖f (j + N)‖ ≤ ‖term b lam phase (j + N) x‖ + ‖term b lam phase (j + N) y‖ :=
        norm_sub_le _ _
      _ ≤ lam ^ (j + N) + lam ^ (j + N) :=
        add_le_add (norm_term_le hl b phase _ x) (norm_term_le hl b phase _ y)
      _ = _ := by rw [pow_add]; ring
  change |(∑' j, term b lam phase j x) - (∑' j, term b lam phase j y)| ≤ _
  rw [← sx.tsum_sub sy]
  change |∑' j, f j| ≤ _
  rw [← sf.sum_add_tsum_nat_add N]
  exact (abs_add_le _ _).trans (add_le_add low high)

private theorem inv_rpow_alpha {b lam : ℝ} (hb : 1 < b) (hl : 0 < lam) :
    b⁻¹ ^ alpha b lam = lam := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [Real.rpow_def_of_pos (inv_pos.mpr hb0), Real.log_inv, alpha,
    show -Real.log b * (-Real.log lam / Real.log b) = Real.log lam by
      field_simp [(Real.log_pos hb).ne'], Real.exp_log hl]

/-- The Hölder estimate on displacements of size at most one. Its constant is
independent of the prescribed phases. -/
theorem holder_estimate {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (phase : ℕ → ℝ) (x y : ℝ), |x - y| ≤ 1 →
      |series b lam phase x - series b lam phase y| ≤ C * |x - y| ^ alpha b lam := by
  have hb0 := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hq : 1 < b * lam := (inv_lt_iff_one_lt_mul₀' hb0).mp hl
  let K := 2 * Real.pi / (b * lam - 1) + 2 * (1 - lam)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K / lam, div_pos hK hl0, ?_⟩
  intro phase x y hu
  rcases eq_or_lt_of_le (abs_nonneg (x - y)) with he | hu0
  · have heq : x = y := sub_eq_zero.mp (abs_eq_zero.mp he.symm)
    subst y
    simp [(alpha_mem_Ioo hb hl h1).1.ne']
  obtain ⟨N, hnear, hcut⟩ := exists_nat_pow_near_of_lt_one hu0 hu (inv_pos.mpr hb0)
    ((inv_lt_one₀ hb0).mpr hb)
  have hfreq : |x - y| * (b * lam) ^ N ≤ lam ^ N := by
    refine (mul_le_mul_of_nonneg_right hcut (pow_nonneg (mul_nonneg hb0.le hl0.le) _)).trans_eq ?_
    rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hb0.ne', one_mul]
  have hsum : (∑ j ∈ Finset.range N, (b * lam) ^ j) ≤ (b * lam) ^ N / (b * lam - 1) := by
    rw [geom_sum_eq hq.ne' N]
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hq.le)
  have hlow : (2 * Real.pi * |x - y|) * (∑ j ∈ Finset.range N, (b * lam) ^ j) ≤
      (2 * Real.pi / (b * lam - 1)) * lam ^ N := by
    calc
      _ ≤ (2 * Real.pi * |x - y|) * ((b * lam) ^ N / (b * lam - 1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 * Real.pi / (b * lam - 1)) * (|x - y| * (b * lam) ^ N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfreq (by positivity)
  have hscale : lam ^ (N + 1) ≤ |x - y| ^ alpha b lam := by
    calc
      lam ^ (N + 1) = (b⁻¹ ^ (N + 1) : ℝ) ^ alpha b lam := by
        simpa only [inv_rpow_alpha hb hl0] using
          Real.rpow_pow_comm (inv_pos.mpr hb0).le (alpha b lam) (N + 1)
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hnear.le (alpha_mem_Ioo hb hl h1).1.le
  have hscale' : lam ^ N ≤ |x - y| ^ alpha b lam / lam :=
    (le_div_iff₀ hl0).mpr (by simpa only [pow_succ] using hscale)
  calc
    _ ≤ _ := increment_bound_at_cutoff hb0.le hl0.le h1 phase x y N
    _ ≤ (2 * Real.pi / (b * lam - 1)) * lam ^ N + 2 * lam ^ N * (1 - lam)⁻¹ :=
      add_le_add hlow le_rfl
    _ = K * lam ^ N := by dsimp [K]; ring
    _ ≤ K * (|x - y| ^ alpha b lam / lam) := mul_le_mul_of_nonneg_left hscale' hK.le
    _ = _ := by ring

end Weierstrass
