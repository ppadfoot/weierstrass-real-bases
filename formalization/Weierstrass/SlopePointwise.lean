module

public import Weierstrass.SlopeQuantitativeStep

/-! Pointwise lower dimension of all actual predecessor slope laws. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

theorem quantitativeSlope_all {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hγ' : γ<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (j : ℕ) :
    QuantitativeSlopeInformation (by omega : 0<p) (d+1) a (γ*c^j) (slopeExponent p (γ*c^j)) := by
  let P (i : ℕ) := QuantitativeSlopeInformation (by omega : 0<p) (d+1) a (γ*c^i) (slopeExponent p (γ*c^i))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (show ∀ᶠ i : ℕ in atTop, P i from quantitativeSlope_initial hp a ha hc hc' hγ hbc hpoly)
  have step (i : ℕ) (H : P (i+1)) : P i := by
    have G := mul_pos hγ (pow_pos hc i)
    have G' : γ*c^i < 1 := (mul_le_of_le_one_right hγ.le (pow_le_one₀ hc.le hc'.le)).trans_lt hγ'
    apply quantitativeSlope_step hp a ha G G' hc hc' hbc hpoly
    simpa only [P,pow_succ,←mul_assoc] using H
  have back (k : ℕ) : ∀ i, N ≤ i+k → P i := by
    induction k with
    | zero => simpa using hN
    | succ k ih => intro i hi;exact step i (ih (i+1) (by omega))
  exact back N j (by omega)

/-- Summable exceptions at a fixed dyadic scale imply an all-radii mass
bound in each conditional law, with arbitrary fixed deterministic phases. -/
theorem ae_conditional_mass_bound {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) {g s : ℝ}
    (info : QuantitativeSlopeInformation hp d a g s) (η : ℕ → ℝ) {h : ℝ} (hh : 0<h) (hs : h<s) :
    ∀ᵐ w : Fin d → UnitAddCircle, ∀ᵐ y ∂baseSlopeLaw hp d a (centralLift w) η g, ∀ᶠ r : ℝ in 𝓝[>] 0,
      baseSlopeLaw hp d a (centralLift w) η g (Icc (y-r) (y+r)) ≤ ENNReal.ofReal (r^h) := by
  let Ω := Fin d → UnitAddCircle
  let q := (1/2:ℝ)
  have qp : 0<q := by norm_num [q]
  have q1 : q<1 := by norm_num [q]
  obtain ⟨K,β,kpos,βpos,bd⟩ := info h hh hs 2 (by norm_num)
  have lim : Tendsto (fun n : ℕ ↦ q^n) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one qp.le q1,Eventually.of_forall (fun n ↦ pow_pos qp n)⟩
  obtain ⟨N,hsml⟩ := eventually_atTop.mp (lim.eventually bd)
  let μ := (volume : Measure Ω).prod unitLaw
  let ν (w : Ω) := baseSlopeLaw hp d a (centralLift w) η g
  let F (w : Ω) (x : ℝ) := codedSlope d (fun j ↦ (a j:ℝ)) p g (centralLift w) η (uniformCode p hp x)
  let A (n : ℕ) := {z : Ω × ℝ | ENNReal.ofReal ((q^n:ℝ)^h) < ν z.1 (Icc (F z.1 z.2-2*q^n) (F z.1 z.2+2*q^n))}
  let v := q^β
  have vp := Real.rpow_pos_of_pos qp β
  have v1 : v<1 := Real.rpow_lt_one qp.le q1 βpos
  have rates (n : ℕ) : μ (A (N+n)) ≤ ENNReal.ofReal (K*v^n) := by
    have B := hsml (N+n) (by omega) η
    change μ (A (N+n)) ≤ ENNReal.ofReal (K*(q^(N+n):ℝ)^β) at B
    rw [pow_rpow_interchange qp.le] at B
    exact B.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one vp.le v1.le (by omega)) kpos.le))
  have summ : (∑' n, μ (A (N+n)))≠⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum rates)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ (mul_pos kpos (pow_pos vp n)).le)
      ((summable_geometric_of_lt_one vp.le v1).mul_left K)]
    exact ENNReal.ofReal_ne_top
  let Q (w : Ω) (y : ℝ) (n : ℕ) := ν w (Icc (y-2*q^n) (y+2*q^n)) ≤ ENNReal.ofReal ((q^n:ℝ)^h)
  have joint : ∀ᵐ z ∂μ, ∀ᶠ n : ℕ in atTop, Q z.1 (F z.1 z.2) n := by
    filter_upwards [ae_eventually_notMem summ] with z hz
    obtain ⟨k,hk⟩ := eventually_atTop.mp hz
    apply eventually_atTop.mpr
    refine ⟨N+k,fun n hn ↦ ?_⟩
    have H := hk (n-N) (by omega)
    rw [show N+(n-N)=n by omega] at H
    exact le_of_not_gt H
  have mQ (w : Ω) (n : ℕ) : MeasurableSet {y | Q w y n} := by
    let S := {z : ℝ×ℝ | z.1-2*q^n≤z.2 ∧ z.2≤z.1+2*q^n}
    have mS : MeasurableSet S := (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add measurable_const))
    exact measurableSet_le (measurable_measure_prodMk_left (ν:=ν w) mS) measurable_const
  have mEv (w : Ω) : MeasurableSet {y | ∀ᶠ n : ℕ in atTop, Q w y n} := by
    simp only [eventually_atTop,Set.ofPred_exists,Set.ofPred_forall]
    exact MeasurableSet.iUnion (fun k ↦ MeasurableSet.iInter (fun n ↦ MeasurableSet.iInter (fun _ ↦ mQ w n)))
  have cond := Measure.ae_ae_of_ae_prod (μ:=(volume : Measure Ω)) (ν:=unitLaw) joint
  filter_upwards [cond] with w hw
  have mF : Measurable (F w) := measurable_coded_sample hp d a (fun _ : ℝ ↦ centralLift w) (fun _ ↦ measurable_const) id measurable_id η g
  have grid : ∀ᵐ y ∂ν w, ∀ᶠ n : ℕ in atTop, Q w y n := (ae_map_iff mF.aemeasurable (mEv w)).mpr hw
  filter_upwards [grid] with y hy
  obtain ⟨k,hk⟩ := eventually_atTop.mp hy
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (pow_pos qp k)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (pr : 0<r) sm sr
  obtain ⟨n,lo,hi⟩ := exists_nat_pow_near_of_lt_one pr sr.le qp q1
  have kn : k≤n+1 := by by_contra! w;exact (sm.trans_le (pow_le_pow_of_le_one qp.le q1.le w.le)).asymm lo
  have wide : r≤2*q^(n+1) := by simpa only [pow_succ,show (2:ℝ)*(q^n*q)=q^n by dsimp [q];ring] using hi
  exact (measure_mono (Icc_subset_Icc (sub_le_sub_left wide _) (add_le_add_right wide _))).trans
    ((hk (n+1) kn).trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (pow_pos qp _).le lo.le hh.le)))

/-- For every prescribed phase sequence, the actual conditional law has
lower local dimension at least the sharp value at every derivative index. -/
theorem ae_slope_lower_dimension_all {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hγ' : γ<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (j : ℕ) (η : ℕ → ℝ) :
    let g := γ*c^j
    let ν := fun w : Fin (d+1) → UnitAddCircle ↦ baseSlopeLaw (by omega : 0<p) (d+1) a (centralLift w) η g
    ∀ᵐ w, ∀ᵐ y ∂ν w, ∀ u : ℝ, u<slopeExponent p g → ∀ᶠ r : ℝ in 𝓝[>] 0,
      u ≤ Real.log ((ν w).real (Icc (y-r) (y+r))) / Real.log r := by
  intro g ν
  have gp := mul_pos hγ (pow_pos hc j)
  have g1 : g<1 := (mul_le_of_le_one_right hγ.le (pow_le_one₀ hc.le hc'.le)).trans_lt hγ'
  have sp : 0<slopeExponent p g := lt_min zero_lt_one (div_pos (Real.log_pos (by exact_mod_cast (show 1<p by omega)))
    (Real.log_pos (by rw [one_div];exact (one_lt_inv₀ gp).mpr g1)))
  let Q (w : Fin (d+1) → UnitAddCircle) (y : ℝ) (v : ℚ) :=
    0<(v:ℝ) → (v:ℝ)<slopeExponent p g → ∀ᶠ r : ℝ in 𝓝[>] 0, ν w (Icc (y-r) (y+r)) ≤ ENNReal.ofReal (r^(v:ℝ))
  have each (v : ℚ) : ∀ᵐ w, ∀ᵐ y ∂ν w, Q w y v := by
    by_cases hv : 0<(v:ℝ) ∧ (v:ℝ)<slopeExponent p g
    · have bd := ae_conditional_mass_bound (by omega : 0<p) a (quantitativeSlope_all hp a ha hc hc' hγ hγ' hbc hpoly j) η hv.1 hv.2
      filter_upwards [bd] with w hw
      filter_upwards [hw] with y hy
      exact fun _ _ ↦ hy
    · exact .of_forall (fun _ ↦ .of_forall (fun _ h h' ↦ (hv ⟨h,h'⟩).elim))
  filter_upwards [ae_all_iff.mpr each] with w hw
  filter_upwards [ae_all_iff.mpr hw,(ν w).support_mem_ae] with y hy supp
  intro u hu
  obtain ⟨v,hv,vS⟩ := exists_rat_btwn (max_lt sp hu : max 0 u<slopeExponent p g)
  filter_upwards [hy v ((le_max_left 0 u).trans_lt hv) vS,self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r bound (rp : 0<r) r1
  have mp : 0<ν w (Icc (y-r) (y+r)) := ((ν w).mem_support_iff_forall y).mp supp _
    (Icc_mem_nhds (by linarith) (by linarith))
  have mr : 0<(ν w).real (Icc (y-r) (y+r)) := ENNReal.toReal_pos mp.ne' (measure_ne_top _ _)
  have H := Real.log_le_log mr (ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg rp.le _) bound)
  rw [Real.log_rpow rp] at H
  exact ((le_max_right 0 u).trans_lt hv).le.trans ((le_div_iff_of_neg (Real.log_neg rp r1)).mpr H)

end Weierstrass.Predecessor
