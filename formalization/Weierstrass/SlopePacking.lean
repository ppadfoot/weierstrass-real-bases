module

public import Weierstrass.SlopeRetained
public import Weierstrass.SlopeWordRates

/-! Finite-scale heavy-ball estimate for the polynomial predecessor process.
All three terms are actual parts of the uniform conditional probability. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Weierstrass.Predecessor

theorem collision_integrable {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω) [IsFiniteMeasure m]
    (μ : Ω → Measure ℝ) (mμ : Measurable μ) (h : ∀ w, μ w univ ≤ 1) (r : ℝ) :
    Integrable (fun w ↦ collision (μ w) (μ w) r) m := by
  have hm : Measurable (fun w ↦ collision (μ w) (μ w) r) := by
    have H := ENNReal.measurable_toReal.comp (measurable_diagonal_collision μ mμ h r)
    have N (w : Ω) : 0 ≤ collision (μ w) (μ w) r := measureReal_nonneg
    simpa only [Function.comp_def,ENNReal.toReal_ofReal (N _)] using H
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with w
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ collision (μ w) (μ w) r from measureReal_nonneg)]
  have fin : IsFiniteMeasure (μ w) := ⟨(h w).trans_lt ENNReal.one_lt_top⟩
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  rw [ENNReal.ofReal_one]
  apply (measure_mono (subset_univ _)).trans
  rw [← univ_prod_univ,Measure.prod_prod]
  exact mul_le_one₀ (h w) bot_le (h w)

/-- Passing from prescribed words to the retained measure costs at most
`3·4^k`, uniformly over all deterministic phase strings. -/
theorem retained_collision_cost_rate {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ)
    {t δ : ℝ} (ht : 0≤t) (ht' : t≤1) (hδ : 0≤δ) {A : ℝ} (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ C = 3*max 1 (slopeSliceBound g c n*A) ∧ ∀ k : ℕ, ∀ η : ℕ → ℝ,
      (∫⁻ w, let μ := retainedStatusLaw hp (d+1) a n k ⌊δ*k⌋₊ g c ((p:ℝ)^n*(g^n:ℝ)^t) η w
        ENNReal.ofReal (collision μ μ (A*(g^n)^k))) ≤
      ENNReal.ofReal (C*(k+1:ℝ)*(12*(g^n:ℝ)^(t*(1-δ)))^k) := by
  let q := g^n
  let T := (p:ℝ)^n*q^t
  have pq := pow_pos hg n
  have sq : q≤1 := pow_le_one₀ hg.le hg'.le
  have hT : 0≤T := mul_nonneg (by positivity) (Real.rpow_nonneg pq.le _)
  obtain ⟨K,hK,hEq,iter⟩ := statusWord_collision_iteration_rate hp a ha hg hg' hc hc' hbc hpoly n T hT A hA
    (wordCoefficient q t) (wordCoefficient_ge pq sq ht') (wordCoefficient_rows hp pq t)
  refine ⟨3*K,by positivity,by rw [hEq],?_⟩
  intro k η
  let Ω := Fin (d+1) → UnitAddCircle
  let μ := retainedStatusLaw hp (d+1) a n k ⌊δ*k⌋₊ g c T η
  let I := sparseStatusWords k ⌊δ*k⌋₊
  let V (w : Ω) (v : I) := statusSlopeLaw hp (d+1) a n g c T (List.ofFn v.val) η w
  let R := A*q^k
  let B := K*(k+1:ℝ)*(3*q^(t*(1-δ)))^k
  have bp : 0 ≤ B := by unfold B;positivity
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have bound (v : I) (w : Ω) : V w v univ ≤ 1 :=
    (statusSlopeLaw_domination hp (d+1) a n hg.le hg' c T _ η w univ).trans_eq (baseSlopeLaw_univ hp (d+1) a _ _ _)
  have mb (w : Ω) : μ w univ ≤ 1 := (retainedStatusLaw_domination hp (d+1) a n k _ hg.le hg' c T η w univ).trans_eq (baseSlopeLaw_univ hp (d+1) a _ _ _)
  have mf (w : Ω) : IsFiniteMeasure (μ w) := ⟨(mb w).trans_lt ENNReal.one_lt_top⟩
  have vf (w : Ω) (v : I) : IsFiniteMeasure (V w v) := ⟨(bound v w).trans_lt ENNReal.one_lt_top⟩
  have Vint (v : I) : Integrable (fun w ↦ collision (V w v) (V w v) R) volume :=
    collision_integrable volume (fun w ↦ V w v) (measurable_statusSlopeLaw hp (d+1) a n hg.le hg' c T _ η) (bound v) R
  have mm : Measurable μ := Finset.measurable_fun_sum _ (fun v _ ↦ measurable_statusSlopeLaw hp (d+1) a n hg.le hg' c T _ η)
  have mi := collision_integrable volume μ mm mb R
  have Vintegral (v : I) : (∫ w, collision (V w v) (V w v) R) ≤ B := by
    have bd := iter η (List.ofFn v.val)
    simp only [List.length_ofFn] at bd
    rw [←ofReal_integral_eq_lintegral_ofReal (Vint v) (Eventually.of_forall (fun _ ↦ measureReal_nonneg))] at bd
    apply (ENNReal.ofReal_le_ofReal_iff bp).mp
    apply bd.trans (ENNReal.ofReal_le_ofReal _)
    rw [mul_assoc (K*(k+1:ℝ))]
    exact mul_le_mul_of_nonneg_left (wordCoefficient_sparse pq sq ht hδ v.property) (by positivity)
  have cmp (w : Ω) : μ w ≤ ∑ v : I, V w v := by
    exact (Finset.sum_coe_sort I (fun v ↦ statusSlopeLaw hp (d+1) a n g c T (List.ofFn v) η w)).symm.le
  have est := averaged_retained_collision (volume : Measure Ω) μ V (mul_pos hA (pow_pos pq k)) cmp Vint Vintegral
  rw [←ofReal_integral_eq_lintegral_ofReal mi (.of_forall fun _ ↦ measureReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal (est.trans _)
  have card : (Fintype.card I:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast (show Fintype.card I ≤ 2^k from by simpa using Fintype.card_le_of_injective (fun v : I => v.val) Subtype.val_injective)
  calc
    _ ≤ 3*((2:ℝ)^k)^2*B := by gcongr
    _ = _ := by
      dsimp only [q,B];rw [show (12:ℝ)=2*2*3 by norm_num,mul_pow,mul_pow,mul_pow,mul_pow];ring

theorem retained_collision_cost {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ)
    {t δ : ℝ} (ht : 0≤t) (ht' : t≤1) (hδ : 0≤δ) {A : ℝ} (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, ∀ η : ℕ → ℝ,
      (∫⁻ w, let μ := retainedStatusLaw hp (d+1) a n k ⌊δ*k⌋₊ g c ((p:ℝ)^n*(g^n:ℝ)^t) η w
        ENNReal.ofReal (collision μ μ (A*(g^n)^k))) ≤
      ENNReal.ofReal (C*(k+1:ℝ)*(12*(g^n:ℝ)^(t*(1-δ)))^k) := by
  obtain ⟨C,hC,_,H⟩ := retained_collision_cost_rate hp a ha hg hg' hc hc' hbc hpoly n ht ht' hδ hA
  exact ⟨C,hC,H⟩

end Weierstrass.Predecessor
