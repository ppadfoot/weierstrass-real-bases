module

public import Weierstrass.FirstMoment

/-! From a retained occupation moment to the actual real-coset estimate,
including a mesh that may depend on the requested confidence level. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace Weierstrass.Branch

theorem retained_occupation_markov {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (mE : MeasurableSet E) {O : X → ℝ≥0∞} (mO : Measurable O) {δ : ℝ≥0∞}
    (discard : μ Eᶜ ≤ δ) {r C h e : ℝ} (hr : 0<r)
    (moment : (∫⁻ x, E.indicator O x ∂μ) ≤ ENNReal.ofReal (C*r^e)) :
    μ {x | ENNReal.ofReal (r^h) < O x} ≤ δ+ENNReal.ofReal (C*r^(e-h)) := by
  let τ := ENNReal.ofReal (r^h)
  have pos := Real.rpow_pos_of_pos hr h
  have cover : {x | τ < O x} ⊆ Eᶜ ∪ {x | τ ≤ E.indicator O x} := by
    intro x hx
    by_cases h : x∈E
    · right; simpa [h] using hx.le
    · exact Or.inl h
  have markov := meas_ge_le_lintegral_div (μ:=μ) (f:=E.indicator O) (mO.indicator mE).aemeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr pos) ENNReal.ofReal_ne_top
  apply (measure_mono cover).trans ((measure_union_le ..).trans (add_le_add discard _))
  apply markov.trans ((ENNReal.div_le_div_right moment _).trans_eq _)
  rw [← ENNReal.ofReal_div_of_pos pos,Real.rpow_sub hr,mul_div_assoc]

theorem anchored_of_geometric {b l s : ℝ}
    (grid : ∀ h : ℝ, 0<h → h<s → ∀ T : ℝ, 0<T → ∀ ε : ℝ, 0<ε →
      ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ A : ℝ, 0<A → ∀ᶠ k : ℕ in atTop, ∀ ω : PhaseTorus,
        phaseHaar b {z : phaseGroup b | ENNReal.ofReal ((q^k:ℝ)^h) <
          occupation b l T A (q^k) (ω+z.val)} ≤ ENNReal.ofReal ε) : AnchoredEstimate b l s := by
  intro h hh hs T A hT hA
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  obtain ⟨u,hu,huδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have up : 0<(u:ℝ) := by exact_mod_cast (show (0:ℝ≥0)<u by exact_mod_cast hu)
  obtain ⟨q,hq,hq1,mesh⟩ := grid h hh hs T hT u up
  obtain ⟨N,good⟩ := eventually_atTop.mp (mesh (A/q) (div_pos hA hq))
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (pow_pos hq N)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (rp : 0<r) small r1
  obtain ⟨k,lo,hi⟩ := exists_nat_pow_near_of_lt_one rp r1.le hq hq1
  have kn : N≤k+1 := by
    by_contra! w
    exact (small.trans_le (pow_le_pow_of_le_one hq.le hq1.le w.le)).asymm lo
  apply iSup_le
  intro ω
  apply le_trans _ ((good _ kn ω).trans (by simpa only [ENNReal.ofReal_coe_nnreal] using huδ.le))
  apply measure_mono;intro z hz
  have th := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (pow_pos hq _).le lo.le hh.le)
  have scaled : A*r ≤ A/q*q^(k+1) := by
    rw [pow_succ,show A/q*(q^k*q)=A*q^k by field_simp]
    exact mul_le_mul_of_nonneg_left hi hA.le
  exact (th.trans_lt hz).trans_le (measure_mono (fun u hu ↦ ⟨hu.1,hu.2.trans scaled⟩))

end Weierstrass.Branch
