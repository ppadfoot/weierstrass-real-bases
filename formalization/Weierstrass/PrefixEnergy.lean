module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Common-prefix estimate, Appendix B (initialization)

The parameters may be real: the application takes `p` to be the integer
branching number. `prefixSeries` is the upper bound on averaged collisions
obtained in the manuscript after conditioning on the first differing digit.
-/

public noncomputable section

namespace Weierstrass.PrefixEnergy

@[expose] def prefixTerm (p g r : ℝ) (k : ℕ) := p⁻¹ ^ k * min 1 (r * g⁻¹ ^ k)

@[expose] def prefixSeries (p g r : ℝ) := ∑' k, prefixTerm p g r k

private theorem min_one_le_rpow {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    min 1 x ≤ x ^ t := by
  by_cases h : x ≤ 1
  · rw [min_eq_right h]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx h ht'
  · rw [min_eq_left (le_of_not_ge h)]
    exact Real.one_le_rpow (le_of_not_ge h) ht

theorem ratio_lt_one {p g t : ℝ} (hp : 1 < p) (hg : 0 < g) (hg' : g < 1)
    (ht : t < Real.log p / Real.log g⁻¹) : p⁻¹ * g⁻¹ ^ t < 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hgi : 1 < g⁻¹ := (one_lt_inv₀ hg).mpr hg'
  have hs := (lt_div_iff₀ (Real.log_pos hgi)).mp ht
  rw [← Real.log_rpow (inv_pos.mpr hg) t] at hs
  have h := (Real.log_lt_log_iff (Real.rpow_pos_of_pos (inv_pos.mpr hg) _) hp0).mp hs
  simpa only [div_eq_inv_mul, one_mul] using (div_lt_iff₀ hp0).mpr (by simpa using h)

/-- An explicit bound, valid at *all* positive radii and even at the endpoint
t=1 whenever the mixed geometric ratio is strictly less than 1. -/
theorem prefixSeries_bound {p g r t : ℝ} (hp : 0 < p) (hg : 0 < g) (hr : 0 < r)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hq : p⁻¹ * g⁻¹ ^ t < 1) :
    Summable (prefixTerm p g r) ∧
      prefixSeries p g r ≤ (1 - p⁻¹ * g⁻¹ ^ t)⁻¹ * r ^ t := by
  let q := p⁻¹ * g⁻¹ ^ t
  have hq₀ : 0 ≤ q := mul_nonneg (inv_nonneg.mpr hp.le) (Real.rpow_nonneg (inv_nonneg.mpr hg.le) _)
  have bound (k : ℕ) : prefixTerm p g r k ≤ r ^ t * q ^ k := by
    have hz : 0 < r * g⁻¹ ^ k := by positivity
    calc
      _ ≤ p⁻¹ ^ k * (r * g⁻¹ ^ k) ^ t :=
        mul_le_mul_of_nonneg_left (min_one_le_rpow hz ht₀ ht₁) (by positivity)
      _ = r ^ t * q ^ k := by
        rw [Real.mul_rpow hr.le (by positivity),
          ← Real.rpow_pow_comm (inv_nonneg.mpr hg.le) t k, show q = p⁻¹ * g⁻¹ ^ t from rfl,
          mul_pow]
        ring
  have geom := (hasSum_geometric_of_lt_one hq₀ hq).mul_left (r ^ t)
  have hs : Summable (prefixTerm p g r) := by
    apply Summable.of_nonneg_of_le _ bound geom.summable
    intro k
    dsimp [prefixTerm]
    exact mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, r ^ t * q ^ k := hs.tsum_le_tsum bound geom.summable
    _ = _ := by rw [geom.tsum_eq]; exact mul_comm _ _

/-- For *every* real t strictly below the manuscript's threshold, the
radius-independent constant is positive and the series is O(r^t) on (0,1]. -/
theorem prefixSeries_subcritical {p g t : ℝ} (hp : 1 < p) (hg : 0 < g) (hg' : g < 1)
    (ht : t < min 1 (Real.log p / Real.log (1/g))) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Summable (prefixTerm p g r) ∧ prefixSeries p g r ≤ C * r ^ t := by
  let u := max 0 t
  have hgi : 1 < g⁻¹ := (one_lt_inv₀ hg).mpr hg'
  have hpos : 0 < Real.log p / Real.log g⁻¹ := div_pos (Real.log_pos hp) (Real.log_pos hgi)
  have hu : u < Real.log p / Real.log g⁻¹ := by
    apply max_lt hpos
    simpa only [one_div] using (lt_min_iff.mp ht).2
  have hu₁ : u ≤ 1 := max_le zero_le_one (lt_min_iff.mp ht).1.le
  have hq := ratio_lt_one hp hg hg' hu
  have hC : 0 < (1 - p⁻¹ * g⁻¹ ^ u)⁻¹ := inv_pos.mpr (sub_pos.mpr hq)
  refine ⟨_, hC, ?_⟩
  intro r hr hsmall
  obtain ⟨hs, hb⟩ := prefixSeries_bound (zero_lt_one.trans hp) hg hr (le_max_left 0 t) hu₁ hq
  exact ⟨hs, hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hr hsmall (le_max_right 0 t)) hC.le)⟩

open Set Filter MeasureTheory
open scoped ENNReal

/-- Product-measure collision set of radius r on the real line. -/
@[expose] def band (r : ℝ) := {z : ℝ × ℝ | |z.1-z.2| ≤ r}

theorem band_measurable (r : ℝ) : MeasurableSet (band r) :=
  (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const).measurableSet

/-- The s-energy has infinite integrand on the diagonal when s>0. -/
def energy (μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, (ENNReal.ofReal |z.1-z.2|) ^ (-s) ∂(μ.prod μ)

private def weightedBand (q s : ℝ) (n : ℕ) : ℝ × ℝ → ℝ≥0∞ :=
  (band (q^n)).indicator (fun _ => (ENNReal.ofReal (q^(-s))) ^ (n+1))

private theorem kernel_le_weighted_bands {q s : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hs : 0 < s) (z : ℝ × ℝ) :
    (ENNReal.ofReal |z.1-z.2|) ^ (-s) ≤ 1 + ∑' n, weightedBand q s n z := by
  let d := |z.1-z.2|
  have hd₀ : 0 ≤ d := abs_nonneg _
  let a := ENNReal.ofReal (q^(-s))
  have ha : 1 < a := by
    exact (ENNReal.one_lt_ofReal).mpr
      (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hq hq' (neg_lt_zero.mpr hs))
  change ENNReal.ofReal d ^ (-s) ≤ _
  by_cases hzero : d = 0
  · have band0 (n : ℕ) : z ∈ band (q^n) := by
      change d ≤ q^n
      rw [hzero]
      positivity
    have eq (n : ℕ) : weightedBand q s n z = a^(n+1) := indicator_of_mem (band0 n) _
    simp only [eq, ENNReal.tsum_geometric_add_one, tsub_eq_zero_of_le ha.le, ENNReal.inv_zero,
      ENNReal.mul_top (zero_lt_one.trans ha).ne', add_top, le_top]
  have hd := lt_of_le_of_ne hd₀ (Ne.symm hzero)
  rw [ENNReal.ofReal_rpow_of_pos hd]
  by_cases hsmall : d ≤ 1
  · obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near_of_lt_one hd hsmall hq hq'
    have he : d^(-s) ≤ (q^(-s))^(n+1) := by
      rw [Real.rpow_pow_comm hq.le]
      exact Real.rpow_le_rpow_of_nonpos (pow_pos hq _) hn₁.le (neg_nonpos.mpr hs.le)
    have hmem : z ∈ band (q^n) := hn₂
    have hterm : ENNReal.ofReal (d^(-s)) ≤ weightedBand q s n z := by
      rw [weightedBand, indicator_of_mem hmem, ← ENNReal.ofReal_pow (Real.rpow_nonneg hq.le _)]
      exact ENNReal.ofReal_le_ofReal he
    exact hterm.trans ((ENNReal.le_tsum n).trans (le_add_left le_rfl))
  · have hle : d^(-s) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos (zero_lt_one : (0:ℝ) < 1) (le_of_not_ge hsmall)
          (neg_nonpos.mpr hs.le)
    exact (ENNReal.ofReal_le_one.mpr hle).trans (le_add_right le_rfl)

/-- A direct inequality for the actual singular kernel. It holds for measures
with atoms as well, with the usual extended value on the diagonal. -/
theorem energy_le_scale_sum (μ : Measure ℝ) {q s : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hs : 0 < s) :
    energy μ s ≤ (μ.prod μ) univ +
      ∑' n : ℕ, (ENNReal.ofReal (q^(-s)))^(n+1) * (μ.prod μ) (band (q^n)) := by
  have hm (n : ℕ) : Measurable (weightedBand q s n) :=
    measurable_const.indicator (band_measurable _)
  unfold energy
  calc
    _ ≤ ∫⁻ z, 1 + ∑' n, weightedBand q s n z ∂(μ.prod μ) :=
      lintegral_mono (kernel_le_weighted_bands hq hq' hs)
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_one,
        lintegral_tsum (fun n => (hm n).aemeasurable)]
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (band_measurable _) _

/-- Averaged geometric collision decay gives finiteness of the s-energy of
almost every conditional measure, for each fixed 0<s<t. The only parameter
measurability required here is that of the countably many collision masses. -/
theorem ae_finite_energy_of_geometric_collisions
    {W : Type*} [MeasurableSpace W] (m : Measure W) (ν : W → Measure ℝ)
    [∀ w, IsFiniteMeasure (ν w)] {q s t : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hs : 0 < s) (hst : s < t) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hm : ∀ n : ℕ, AEMeasurable (fun w => ((ν w).prod (ν w)) (band (q^n))) m)
    (havg : ∀ n : ℕ, (∫⁻ w, ((ν w).prod (ν w)) (band (q^n)) ∂m) ≤
        C * (ENNReal.ofReal (q^t)) ^ n) :
    ∀ᵐ w ∂m, energy (ν w) s < ⊤ := by
  let A := ENNReal.ofReal (q^(-s))
  let B := ENNReal.ofReal (q^t)
  let F (n : ℕ) (w : W) := A^(n+1) * ((ν w).prod (ν w)) (band (q^n))
  have hF (n : ℕ) : AEMeasurable (F n) m := aemeasurable_const.mul (hm n)
  have hAB : A*B < 1 := by
    dsimp [A, B]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _), ← Real.rpow_add hq]
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one hq.le hq' (by linarith))
  have hsum : (∫⁻ w, ∑' n, F n w ∂m) < ⊤ := by
    calc
      _ = ∑' n, ∫⁻ w, F n w ∂m := lintegral_tsum hF
      _ ≤ ∑' n : ℕ, (A*C) * (A*B)^n := ENNReal.tsum_le_tsum (fun n => by
        dsimp only [F]
        rw [lintegral_const_mul'' _ (hm n)]
        calc
          _ ≤ A^(n+1) * (C * B^n) := mul_le_mul_right (havg n) _
          _ = _ := by rw [pow_succ, mul_pow]; ac_rfl)
      _ = (A*C) * ∑' n : ℕ, (A*B)^n := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (tsum_geometric_lt_top.mpr hAB)
  have hae := ae_lt_top' (AEMeasurable.tsum hF) hsum.ne
  filter_upwards [hae] with w hw
  exact (energy_le_scale_sum (ν w) hq hq' hs).trans_lt
    (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, hw⟩)

/-- Finite s-energy supplies an almost-everywhere pointwise s-power bound for
all closed balls, with a center-dependent finite real constant. -/
theorem ae_ball_mass_le_of_finite_energy (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) (henergy : energy μ s < ⊤) :
    ∀ᵐ x ∂μ, ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r →
      μ.real (Icc (x-r) (x+r)) ≤ K * r^s := by
  let f (z : ℝ × ℝ) := (ENNReal.ofReal |z.1-z.2|) ^ (-s)
  let U (x : ℝ) := ∫⁻ y, f (x,y) ∂μ
  have hf : Measurable f := (ENNReal.continuous_rpow_const.comp
    (ENNReal.continuous_ofReal.comp (continuous_fst.sub continuous_snd).abs)).measurable
  have hu : (∫⁻ x, U x ∂μ) ≠ ⊤ := by
    rw [show (∫⁻ x, U x ∂μ) = energy μ s from (lintegral_prod f hf.aemeasurable).symm]
    exact henergy.ne
  filter_upwards [ae_lt_top (hf.lintegral_prod_right' (ν := μ)) hu] with x hx
  change U x < ⊤ at hx
  refine ⟨(U x).toReal + 1, by positivity, ?_⟩
  intro r hr
  let a := ENNReal.ofReal (r^s)
  have har : 0 < r^s := Real.rpow_pos_of_pos hr s
  have ha : a ≠ 0 := (ENNReal.ofReal_pos.mpr har).ne'
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcomp (y : ℝ) : (Icc (x-r) (x+r)).indicator (fun _ => a⁻¹) y ≤ f (x,y) := by
    by_cases h : y ∈ Icc (x-r) (x+r)
    · rw [indicator_of_mem h]
      have hdist : |x-y| ≤ r := abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
      dsimp [f, a]
      rw [ENNReal.rpow_neg, ← ENNReal.ofReal_rpow_of_pos hr]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdist) hs.le)
    · rw [indicator_of_notMem h]
      exact zero_le
  have hcmp : a⁻¹ * μ (Icc (x-r) (x+r)) ≤ U x := by
    rw [← lintegral_indicator_const measurableSet_Icc a⁻¹]
    exact lintegral_mono hcomp
  have hb := (ENNReal.mul_le_iff_le_inv (ENNReal.inv_ne_zero.mpr hat)
    (ENNReal.inv_ne_top.mpr ha)).mp hcmp
  rw [inv_inv] at hb
  have hb' := ENNReal.toReal_mono (ENNReal.mul_ne_top hat hx.ne) hb
  rw [ENNReal.toReal_mul, show a.toReal = r^s from ENNReal.toReal_ofReal har.le] at hb'
  change (μ _).toReal ≤ _
  linarith [har]

/-- Lower local dimension at least s, in the eventual lower-bound formulation
of the liminf. Open balls give the same conclusion. The support argument
makes the logarithm of every closed-ball mass well-defined at these centers. -/
theorem ae_lower_local_dimension_of_finite_energy (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) (henergy : energy μ s < ⊤) :
    ∀ᵐ x ∂μ, ∀ u : ℝ, u < s → ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
      u ≤ Real.log (μ.real (Icc (x-r) (x+r))) / Real.log r := by
  filter_upwards [ae_ball_mass_le_of_finite_energy μ hs henergy, μ.support_mem_ae] with x hx hxμ
  obtain ⟨K, hK, hb⟩ := hx
  intro u hu
  have hlog := tendsto_atBot.mp Real.tendsto_log_nhdsGT_zero (-Real.log K / (s-u))
  have hneg := tendsto_atBot.mp Real.tendsto_log_nhdsGT_zero (-1)
  filter_upwards [hlog, hneg, self_mem_nhdsWithin] with r hsmall hrneg hr
  have hr' : 0 < r := hr
  have hm : 0 < μ (Icc (x-r) (x+r)) := (μ.mem_support_iff_forall x).mp hxμ _
    (Icc_mem_nhds (by linarith) (by linarith))
  have hmr : 0 < μ.real (Icc (x-r) (x+r)) := ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  have hmass := Real.log_le_log hmr (hb r hr')
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hr' s).ne', Real.log_rpow hr'] at hmass
  apply (le_div_iff_of_neg (by linarith : Real.log r < 0)).mpr
  have hsmall' := (le_div_iff₀ (sub_pos.mpr hu)).mp hsmall
  linarith only [hmass, hsmall']

/-- The manuscript only needs the averaged prefix estimate on one geometric
sequence to obtain finite energy at any fixed positive subcritical exponent. -/
theorem ae_finite_energy_from_prefix_bound
    {W : Type*} [MeasurableSpace W] (m : Measure W) (ν : W → Measure ℝ)
    [∀ w, IsFiniteMeasure (ν w)] {p g q s : ℝ}
    (hp : 1 < p) (hg : 0 < g) (hg' : g < 1) (hq : 0 < q) (hq' : q < 1)
    (hs : 0 < s) (hs' : s < min 1 (Real.log p / Real.log (1/g)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hm : ∀ n : ℕ, AEMeasurable (fun w => ((ν w).prod (ν w)) (band (q^n))) m)
    (havg : ∀ n : ℕ, (∫⁻ w, ((ν w).prod (ν w)) (band (q^n)) ∂m) ≤
      C * ENNReal.ofReal (prefixSeries p g (q^n))) :
    ∀ᵐ w ∂m, energy (ν w) s < ⊤ := by
  obtain ⟨t, hst, ht⟩ := exists_between hs'
  obtain ⟨K, hK, hbound⟩ := prefixSeries_subcritical hp hg hg' ht
  apply ae_finite_energy_of_geometric_collisions m ν hq hq' hs hst
    (ENNReal.mul_ne_top hC (ENNReal.ofReal_ne_top (r := K))) hm
  intro n
  obtain ⟨_, h⟩ := hbound (q^n) (pow_pos hq _) (pow_le_one₀ hq.le hq'.le)
  calc
    _ ≤ C * ENNReal.ofReal (prefixSeries p g (q^n)) := havg n
    _ ≤ C * ENNReal.ofReal (K * (q^n)^t) := mul_le_mul_right (ENNReal.ofReal_le_ofReal h) _
    _ = _ := by
      rw [ENNReal.ofReal_mul hK.le, ← Real.rpow_pow_comm hq.le,
        ENNReal.ofReal_pow (Real.rpow_nonneg hq.le t), mul_assoc]

/-- The whole lower local dimension threshold holds simultaneously for almost
every parameter and almost every conditional sample. This implication assumes
the averaged first-disagreement estimate, not transversality of its codes. -/
theorem ae_lower_local_dimension_from_prefix_bound
    {W : Type*} [MeasurableSpace W] (m : Measure W) (ν : W → Measure ℝ)
    [∀ w, IsFiniteMeasure (ν w)] {p g q : ℝ}
    (hp : 1 < p) (hg : 0 < g) (hg' : g < 1) (hq : 0 < q) (hq' : q < 1)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hm : ∀ n : ℕ, AEMeasurable (fun w => ((ν w).prod (ν w)) (band (q^n))) m)
    (havg : ∀ n : ℕ, (∫⁻ w, ((ν w).prod (ν w)) (band (q^n)) ∂m) ≤
      C * ENNReal.ofReal (prefixSeries p g (q^n))) :
    ∀ᵐ w ∂m, ∀ᵐ x ∂ν w, ∀ u : ℝ, u < min 1 (Real.log p / Real.log (1/g)) →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
        u ≤ Real.log ((ν w).real (Icc (x-r) (x+r))) / Real.log r := by
  let S := min 1 (Real.log p / Real.log (1/g))
  have hS : 0 < S := by
    apply lt_min zero_lt_one
    apply div_pos (Real.log_pos hp) (Real.log_pos _)
    simpa only [one_div] using (one_lt_inv₀ hg).mpr hg'
  let P (w : W) (x : ℝ) (v : ℚ) :=
    0 < (v : ℝ) → (v : ℝ) < S → ∀ u : ℝ, u < (v : ℝ) →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
        u ≤ Real.log ((ν w).real (Icc (x-r) (x+r))) / Real.log r
  have each (v : ℚ) : ∀ᵐ w ∂m, ∀ᵐ x ∂ν w, P w x v := by
    by_cases hv : 0 < (v : ℝ) ∧ (v : ℝ) < S
    · have he := ae_finite_energy_from_prefix_bound m ν hp hg hg' hq hq' hv.1 hv.2 hC hm havg
      filter_upwards [he] with w hw
      filter_upwards [ae_lower_local_dimension_of_finite_energy (ν w) hv.1 hw] with x hx
      exact fun _ _ => hx
    · exact .of_forall (fun w => .of_forall (fun x h₀ h₁ => (hv ⟨h₀,h₁⟩).elim))
  filter_upwards [ae_all_iff.mpr each] with w hw
  filter_upwards [ae_all_iff.mpr hw] with x hx
  intro u hu
  obtain ⟨v, hv₁, hv₂⟩ := exists_rat_btwn (max_lt hS hu : max 0 u < S)
  exact hx v ((le_max_left 0 u).trans_lt hv₁) hv₂ u ((le_max_right 0 u).trans_lt hv₁)

end Weierstrass.PrefixEnergy
