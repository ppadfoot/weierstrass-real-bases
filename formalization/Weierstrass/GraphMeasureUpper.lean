module

public import Weierstrass.DimensionFromMeasure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Upper local dimension of the graph measure

Counts of small covering sets bound the mass of centers whose own ball has
unusually small mass. A geometric sequence makes those exceptional masses
summable, and interpolation gives all radii.
-/

public noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Weierstrass

private theorem light_centers_of_cover {X ι : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [Fintype ι] (μ : Measure X) (T : Set X) (cover : ι → Set X)
    {R : ℝ} (τ : ℝ≥0∞) (coverT : T ⊆ ⋃ i, cover i)
    (diam : ∀ i, ediam (cover i) < ENNReal.ofReal R) :
    μ {x ∈ T | μ (ball x R) < τ} ≤ Fintype.card ι • τ := by
  classical
  let B := {x ∈ T | μ (ball x R) < τ}
  have hsub : B ⊆ ⋃ i, B ∩ cover i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (coverT hx.1)
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  have hcell (i : ι) : μ (B ∩ cover i) ≤ τ := by
    by_cases h : (B ∩ cover i).Nonempty
    · obtain ⟨z, hz⟩ := h
      refine (measure_mono (t := ball z R) ?_).trans hz.1.2.le
      intro y hy
      exact edist_lt_ofReal.mp ((edist_le_ediam_of_mem hy.2 hz.2).trans_lt (diam i))
    · simp [not_nonempty_iff_eq_empty.mp h]
  exact (measure_mono hsub).trans ((measure_iUnion_fintype_le μ _).trans
    ((Finset.sum_le_card_nsmul _ _ _ (fun i _ => hcell i)).trans_eq (by rw [Finset.card_univ])))

private theorem holder_unit_geometric_mass (μ : Measure ℂ) (f : ℝ → ℝ) {C a s q : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (ha' : a ≤ 1) (hs : 2-a < s)
    (hq : 0 < q) (hq' : q < 1) (u : ℝ)
    (holder : ∀ x y, |x-y| ≤ 1 → |f x-f y| ≤ C * |x-y| ^ a) :
    ∀ᵐ z ∂μ, z ∈ (fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' Icc u (u+1) →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((q^n)^s) ≤ μ (ball z (q^n)) := by
  let T := (fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' Icc u (u+1)
  let bad (n : ℕ) := {z ∈ T | μ (ball z (q^n)) < ENNReal.ofReal ((q^n)^s)}
  let K := (4*C+2) * (1/4 : ℝ)^(a-2)
  let h := q^(a-2+s)
  have hh : 0 ≤ h := Real.rpow_nonneg hq.le _
  have hh' : h < 1 := Real.rpow_lt_one hq.le hq' (by linarith)
  have cost (n : ℕ) : μ (bad n) ≤ ENNReal.ofReal (K*h^n) := by
    let R := q^n
    have hr : 0 < R := pow_pos hq _
    have hr1 : R ≤ 1 := pow_le_one₀ hq.le hq'.le
    obtain ⟨P,Q,cover,diam,coverT,hcard⟩ := holder_unit_square_cover f hC ha ha'
      (r := R/4) (by positivity) (by linarith) u holder
    have hdiam (i) : ediam (cover i) < ENNReal.ofReal R :=
      (diam i).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
    have mass := light_centers_of_cover μ T cover (ENNReal.ofReal (R^s)) coverT hdiam
    apply mass.trans
    rw [nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    have count : (P : ℝ) * Q * R^s ≤ K*h^n := by
      calc
        _ ≤ (4*C+2)*(R/4)^(a-2)*R^s :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hr.le _)
        _ = K*h^n := by
          rw [show R/4 = (1/4)*R by ring, Real.mul_rpow (by norm_num) hr.le]
          dsimp only [K,h]
          rw [Real.rpow_pow_comm hq.le (a-2+s) n]
          change _ = _ * R^(a-2+s)
          rw [Real.rpow_add hr]
          ring
    calc
      _ = ENNReal.ofReal ((P : ℝ)*Q*R^s) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (P : ℝ)*Q),
          ENNReal.ofReal_mul (by positivity : 0 ≤ (P : ℝ))]
        simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal count
  have finite : (∑' n, μ (bad n)) ≠ ⊤ := ne_top_of_le_ne_top
    (((summable_geometric_of_lt_one hh hh').mul_left K).tsum_ofReal_ne_top)
      (ENNReal.tsum_le_tsum cost)
  filter_upwards [ae_eventually_notMem finite] with z hz
  intro zT
  filter_upwards [hz] with n hn
  exact le_of_not_gt (fun hbad => hn ⟨zT,hbad⟩)

private theorem log_bound_of_geometric_mass (μ : Measure ℂ) [IsFiniteMeasure μ]
    {z : ℂ} {s d q : ℝ} (hs : 0 < s) (hsd : s < d) (hq : 0 < q) (hq' : q < 1)
    (h : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((q^n)^s) ≤ μ (ball z (q^n))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.log (μ (ball z r)).toReal / Real.log r ≤ d := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨M,hM⟩ := exists_nat_gt (s/(d-s))
  let L := max N M
  have hsmall : 0 < q^L := pow_pos hq L
  filter_upwards [Ioo_mem_nhdsGT hsmall, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ)<1)] with r hr hr1
  obtain ⟨n,hnlow,hnhi⟩ := exists_nat_pow_near_of_lt_one hr.1 hr1.2.le hq hq'
  have hn : L ≤ n := by
    by_contra! contra
    have hp : q^L ≤ q^(n+1) := pow_le_pow_of_le_one hq.le hq'.le (by omega)
    linarith [hr.2]
  have hN1 : N ≤ n+1 := (Nat.le_max_left N M).trans (hn.trans (Nat.le_succ _))
  have mass := hN (n+1) hN1
  have lower : ENNReal.ofReal ((q^(n+1))^s) ≤ μ (ball z r) :=
    mass.trans (measure_mono (ball_subset_ball hnlow.le))
  have lr : (q^(n+1))^s ≤ (μ (ball z r)).toReal := by
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (pow_pos hq _).le _)] using
      (ENNReal.toReal_mono (measure_ne_top _ _) lower)
  have scaled : (q^n)^d ≤ (q^(n+1))^s := by
    rw [← Real.rpow_natCast_mul hq.le n d, ← Real.rpow_natCast_mul hq.le (n+1) s]
    apply Real.rpow_le_rpow_of_exponent_ge hq hq'.le
    push_cast
    have hm' : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_max_right N M).trans hn
    have := (div_lt_iff₀ (sub_pos.mpr hsd)).mp (hM.trans_le hm')
    linarith
  have rb : r^d ≤ (μ (ball z r)).toReal :=
    ((Real.rpow_le_rpow hr.1.le hnhi (hs.trans hsd).le).trans scaled).trans lr
  apply (div_le_iff_of_neg (Real.log_neg hr.1 hr1.2)).mpr
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hr.1 d) rb
  rwa [Real.log_rpow hr.1] at hlog

/-- For every permitted base, amplitude and phase, the graph measure on a
bounded interval of positive length has upper local dimension at most 2-α
almost everywhere. The proof works on bounded input sets with interior. -/
theorem ae_upper_local_dimension_graphMeasure {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam)
    (h1 : lam < 1) (phase : ℕ → ℝ) {I : Set ℝ} (hi : (interior I).Nonempty)
    (hbd : Bornology.IsBounded I) :
    ∀ᵐ z ∂graphMeasure b lam phase I, ∀ d : ℝ, 2-alpha b lam < d →
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        Real.log ((graphMeasure b lam phase I) (ball z r)).toReal / Real.log r ≤ d := by
  let μ := graphMeasure b lam phase I
  let f := series b lam phase
  let portion (k : ℤ) := graph b lam phase (Icc (k:ℝ) (k+1))
  let U := ⋃ k, portion k
  let q : ℝ := 1/2
  have hq : 0 < q := by norm_num [q]
  have hq' : q < 1 := by norm_num [q]
  have hl₀ := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le
  let : IsProbabilityMeasure μ := graphMeasure_probability hl₀ h1 b phase hi hbd
  have cont := continuous_graphMap hl₀ h1 b phase
  have hUm : MeasurableSet U := MeasurableSet.iUnion
    (fun k : ℤ => (isCompact_Icc.image cont).isClosed.measurableSet)
  have allx (x : ℝ) : graphMap b lam phase x ∈ U :=
    mem_iUnion.mpr ⟨⌊x⌋, x, ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩, rfl⟩
  have full : ∀ᵐ z ∂μ, z ∈ U := by
    apply ae_iff.mpr
    change graphMeasure b lam phase I Uᶜ = 0
    rw [graphMeasure, Measure.map_apply cont.measurable hUm.compl]
    have pre : graphMap b lam phase ⁻¹' Uᶜ = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hx (allx x))
    simp [pre]
  obtain ⟨C, hC, holder⟩ := holder_estimate hb hl h1
  obtain ⟨ha,ha'⟩ := alpha_mem_Ioo hb hl h1
  let S := 2-alpha b lam
  let P (z : ℂ) (k : ℤ) (v : ℚ) := S < (v:ℝ) → z ∈ portion k →
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((q^n)^(v:ℝ)) ≤ μ (ball z (q^n))
  have each (k : ℤ) (v : ℚ) : ∀ᵐ z ∂μ, P z k v := by
    by_cases hv : S < (v:ℝ)
    · have h := holder_unit_geometric_mass μ f hC.le ha.le ha'.le hv hq hq' k (holder phase)
      filter_upwards [h] with z hz
      intro _ hz'
      apply hz
      simpa only [portion, graph_eq_image] using hz'
    · exact .of_forall (fun _ hv' => (hv hv').elim)
  have both : ∀ᵐ z ∂μ, ∀ k : ℤ, ∀ v : ℚ, P z k v :=
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (each k))
  filter_upwards [full, both] with z hz hpoint
  obtain ⟨k,hk⟩ := mem_iUnion.mp hz
  intro d hd
  obtain ⟨v,hv,vd⟩ := exists_rat_btwn hd
  have hvpos : 0 < (v : ℝ) := by linarith only [hv, ha']
  exact log_bound_of_geometric_mass μ hvpos vd hq hq' (hpoint k v hv hk)

/-- The remaining half of the graph-measure dimension formula. -/
@[expose] def LowerLocalDimensionOnBoundedIntervals : Prop :=
  ∀ b lam : ℝ, 1 < b → b⁻¹ < lam → lam < 1 →
    ∀ (phase : ℕ → ℝ) (I : Set ℝ), I.OrdConnected → (interior I).Nonempty →
      Bornology.IsBounded I → ∀ᵐ z ∂graphMeasure b lam phase I,
        ∀ d : ℝ, d < 2-alpha b lam → ∀ᶠ r : ℝ in 𝓝[>] 0,
          d ≤ Real.log ((graphMeasure b lam phase I) (ball z r)).toReal / Real.log r

/-- After the unconditional upper local dimension estimate, the full universal
statement is equivalent to the almost-everywhere lower local bound alone. -/
theorem mainStatement_iff_lowerLocalDimensionOnBoundedIntervals :
    MainStatement ↔ LowerLocalDimensionOnBoundedIntervals := by
  rw [mainStatement_iff_exactDimensionOnBoundedIntervals]
  constructor
  · intro h b lam hb hl h1 phase I hc hi hbd
    filter_upwards [h b lam hb hl h1 phase I hc hi hbd] with z hz
    intro d hd
    exact (hz.eventually (eventually_gt_nhds hd)).mono (fun _ hr => hr.le)
  · intro h b lam hb hl h1 phase I hc hi hbd
    filter_upwards [h b lam hb hl h1 phase I hc hi hbd,
      ae_upper_local_dimension_graphMeasure hb hl h1 phase hi hbd] with z hlo hup
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨c,hac,hc'⟩ := exists_between ha
      exact (hlo c hc').mono (fun _ hr => hac.trans_le hr)
    · intro a ha
      obtain ⟨c,hc',hca⟩ := exists_between ha
      exact (hup c hc').mono (fun _ hr => hr.trans_lt hca)

end Weierstrass
