module

public import Weierstrass.GraphProof
public import Weierstrass.StripRates

/-! The exceptional point at which every term has maximal phase. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology
namespace Weierstrass

def cuspPhase (b x : ℝ) (j : ℕ) := -(b^j*x)

private theorem cusp_difference (b g x t : ℝ) (j : ℕ) :
    term b g (cuspPhase b x) j x-term b g (cuspPhase b x) j (x+t) =
      g^j*(1-Real.cos (2*Real.pi*b^j*t)) := by
  simp only [term,cuspPhase,add_neg_cancel,mul_zero,Real.cos_zero,mul_one]
  rw [show 2*Real.pi*(b^j*(x+t)+ -(b^j*x)) = 2*Real.pi*b^j*t by ring];ring

/-- The signed drop at the prescribed maximum compares to the exact Hölder
power in both directions, for every nonzero displacement through 1/4. -/
theorem cusp_drop {b g : ℝ} (hb : 1 < b) (hg : b⁻¹ < g) (hg1 : g < 1) (x : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 0 < |t| → |t| ≤ 1/4 →
      let drop := series b g (cuspPhase b x) x-series b g (cuspPhase b x) (x+t)
      c*|t|^alpha b g ≤ drop ∧ drop ≤ C*|t|^alpha b g := by
  have bp := zero_lt_one.trans hb
  have gp := (inv_pos.mpr bp).trans hg
  have angP : 0 < Real.pi/(2*b) := by positivity
  have angLE : Real.pi/(2*b) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : 0 < 2*b)]
    nlinarith only [Real.pi_pos,mul_pos Real.pi_pos (sub_pos.mpr hb)]
  have coslt := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) le_rfl angLE angP
  rw [Real.cos_zero] at coslt
  obtain ⟨C,hC,holder⟩ := holder_estimate hb hg hg1
  refine ⟨1-Real.cos (Real.pi/(2*b)),C,sub_pos.mpr coslt,hC,?_⟩
  intro t tp tsize drop
  constructor
  · obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one (show 0 < 4*|t| by positivity)
      (show 4*|t| ≤ 1 by linarith) (inv_pos.mpr bp) (inv_lt_one_of_one_lt₀ hb)
    rw [inv_pow] at up
    rw [pow_succ,inv_pow,←div_eq_mul_inv] at lo
    have pk := pow_pos bp k
    have upper : 4*|t| *b^k ≤ 1 := by
      simpa only [inv_mul_cancel₀ pk.ne'] using mul_le_mul_of_nonneg_right up pk.le
    have lower : 1 < 4*|t| *b^k*b := by
      have := mul_lt_mul_of_pos_right ((div_lt_iff₀ bp).mp lo) pk
      rw [inv_mul_cancel₀ pk.ne'] at this
      linarith only [this]
    have aa : Real.pi/(2*b) ≤ 2*Real.pi*b^k*|t| := by
      rw [div_le_iff₀ (by positivity : 0 < 2*b)]
      nlinarith only [mul_lt_mul_of_pos_left lower Real.pi_pos]
    have ab : 2*Real.pi*b^k*|t| ≤ Real.pi := by
      nlinarith only [mul_le_mul_of_nonneg_left upper Real.pi_pos.le, Real.pi_pos]
    have cosle := Real.cos_le_cos_of_nonneg_of_le_pi angP.le ab aa
    have absCos : Real.cos (2*Real.pi*b^k*t) = Real.cos (2*Real.pi*b^k*|t|) := by
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg ht,mul_neg,Real.cos_neg]
    have amp := (Real.rpow_le_rpow tp.le (show |t| ≤ (b^k)⁻¹ by linarith)
      (alpha_mem_Ioo hb hg hg1).1.le).trans_eq (StripProof.amplitude_as_width hb gp k)
    let Φ := cuspPhase b x
    have pf := summable_term gp.le hg1 b Φ x
    have ps := summable_term gp.le hg1 b Φ (x+t)
    have nonneg (j : ℕ) : 0 ≤ term b g Φ j x-term b g Φ j (x+t) := by
      rw [cusp_difference]
      exact mul_nonneg (pow_pos gp j).le (sub_nonneg.mpr (Real.cos_le_one _))
    have single := (pf.sub ps).le_tsum k (fun j _ => nonneg j)
    change term b g Φ k x-term b g Φ k (x+t) ≤ ∑' j, (term b g Φ j x-term b g Φ j (x+t)) at single
    rw [pf.tsum_sub ps,cusp_difference,absCos] at single
    change _ ≤ (∑' j, term b g Φ j x) - ∑' j, term b g Φ j (x+t)
    apply le_trans _ single
    rw [mul_comm (g^k)]
    exact mul_le_mul (by linarith only [cosle]) amp (Real.rpow_nonneg tp.le _) (by linarith only [cosle,coslt])
  · have bound := holder (cuspPhase b x) x (x+t) (by rw [show x-(x+t)= -t by ring,abs_neg];linarith)
    rw [show x-(x+t)= -t by ring,abs_neg] at bound
    exact (le_abs_self _).trans bound

private theorem power_sandwich {f : ℝ → ℝ} {l u β : ℝ} (hl : 0<l) (hu : 0<u)
    (bounds : ∀ᶠ r : ℝ in 𝓝[>] 0, l*r^β ≤ f r ∧ f r ≤ u*r^β) :
    Tendsto (fun r : ℝ => Real.log (f r)/Real.log r) (𝓝[>] 0) (𝓝 β) := by
  have rate (k : ℝ) (hk : 0<k) : Tendsto (fun r : ℝ => Real.log (k*r^β)/Real.log r)
      (𝓝[>] 0) (𝓝 β) := by
    have shift : Tendsto (fun r : ℝ => Real.log k/Real.log r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
    apply ((zero_add β) ▸ shift.add_const β).congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
    rw [Real.log_mul hk.ne' (Real.rpow_pos_of_pos hr.1 β).ne',Real.log_rpow hr.1,add_div,
      mul_div_cancel_right₀ _ (Real.log_neg hr.1 hr.2).ne]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (rate u hu) (rate l hl)
  · filter_upwards [bounds,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r h hr
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonpos_right (Real.log_le_log ((mul_pos hl (Real.rpow_pos_of_pos hr.1 β)).trans_le h.1) h.2)
      (inv_nonpos.mpr (Real.log_neg hr.1 hr.2).le)
  · filter_upwards [bounds,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r h hr
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonpos_right (Real.log_le_log (mul_pos hl (Real.rpow_pos_of_pos hr.1 β)) h.1)
      (inv_nonpos.mpr (Real.log_neg hr.1 hr.2).le)

/-- The exceptional prescribed maximum has exact local graph-measure
dimension 1/α. The ball is taken in the Euclidean graph, with normalized
Lebesgue measure on the specified bounded parameter set. -/
theorem cusp_local_dimension {b g : ℝ} (hb : 1<b) (hg : b⁻¹<g) (hg1 : g<1)
    {I : Set ℝ} {x : ℝ} (hx : x ∈ interior I) (hI : Bornology.IsBounded I) :
    let F := graphMap b g (cuspPhase b x)
    Tendsto (fun r : ℝ => Real.log ((graphMeasure b g (cuspPhase b x) I) (ball (F x) r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 (alpha b g)⁻¹) ∧ 2-alpha b g < (alpha b g)⁻¹ := by
  intro F
  let α := alpha b g
  obtain ⟨ap,a1⟩ := alpha_mem_Ioo hb hg hg1
  have gp := (inv_pos.mpr (zero_lt_one.trans hb)).trans hg
  refine ⟨?_,?_⟩
  · obtain ⟨c,C,cp,Cp,drop⟩ := cusp_drop hb hg hg1 x
    let K := 1+C
    have kp : 0<K := by dsimp [K];linarith
    let Z := ((volume I)⁻¹).toReal
    have zp : 0<Z := ENNReal.toReal_pos
      (ENNReal.inv_ne_zero.mpr (hI.measure_lt_top (μ:=volume)).ne)
      (ENNReal.inv_ne_top.mpr (Measure.measure_pos_of_nonempty_interior volume ⟨x,hx⟩).ne')
    have cβ := Real.rpow_pos_of_pos (inv_pos.mpr cp) α⁻¹
    have kβ := Real.rpow_pos_of_pos (inv_pos.mpr kp) α⁻¹
    apply power_sandwich (l:=Z*2*(K⁻¹)^α⁻¹) (u:=Z*2*(c⁻¹)^α⁻¹) (by positivity) (by positivity)
    have innerLim := ((Real.continuousAt_rpow_const 0 α⁻¹ (.inr (inv_pos.mpr ap).le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s:=Ioi 0))).const_mul ((K⁻¹)^α⁻¹)
    rw [Real.zero_rpow (inv_pos.mpr ap).ne',mul_zero] at innerLim
    filter_upwards [graphMeasure_ball_interior gp.le hg1 (cuspPhase b x) hx,
      Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4),
      innerLim.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with r mass hr innerSmall
    let R (a : ℝ) := (a⁻¹)^α⁻¹*r^α⁻¹
    have radius (a : ℝ) (aa : 0<a) : 0 < R a :=
      mul_pos (Real.rpow_pos_of_pos (inv_pos.mpr aa) _) (Real.rpow_pos_of_pos hr.1 _)
    have recover (a : ℝ) (aa : 0<a) : (R a)^α = r/a := by
      change ((a⁻¹)^α⁻¹*r^α⁻¹)^α = _
      rw [←Real.mul_rpow (inv_pos.mpr aa).le hr.1.le,Real.rpow_inv_rpow (mul_nonneg (inv_pos.mpr aa).le hr.1.le) ap.ne']
      ring
    have distances {y : ℝ} (yp : 0 < |y-x|) (ys : |y-x|≤1/4) :
        c*|y-x|^α ≤ dist (F y) (F x) ∧ dist (F y) (F x) ≤ K*|y-x|^α := by
      obtain ⟨low,up⟩ := drop (y-x) yp ys
      rw [add_sub_cancel] at low up
      have nonneg : 0 ≤ series b g (cuspPhase b x) x-series b g (cuspPhase b x) y :=
        (mul_nonneg cp.le (Real.rpow_nonneg yp.le _)).trans low
      have im : |(F y-F x).im| = series b g (cuspPhase b x) x-series b g (cuspPhase b x) y := by
        change |series b g (cuspPhase b x) y-series b g (cuspPhase b x) x|=_
        rw [abs_sub_comm,abs_of_nonneg nonneg]
      have re : |(F y-F x).re|=|y-x| := rfl
      rw [dist_eq_norm]
      refine ⟨low.trans (im ▸ Complex.abs_im_le_norm _),?_⟩
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      rw [im,re]
      have t := Real.self_le_rpow_of_le_one yp.le (ys.trans (by norm_num)) a1.le
      dsimp [K];linarith only [t,up]
    have lowSub : ball x (R K) ⊆ F ⁻¹' ball (F x) r := by
      intro y hy
      by_cases eq : y=x
      · simpa [eq] using (mem_ball_self hr.1 : F x ∈ ball (F x) r)
      have yp := abs_pos.mpr (sub_ne_zero.mpr eq)
      change |y-x| < R K at hy
      have ys : |y-x|≤1/4 := hy.le.trans innerSmall.le
      refine (distances yp ys).2.trans_lt ?_
      have := Real.rpow_lt_rpow yp.le hy ap
      rw [recover K kp] at this
      simpa only [mul_comm K] using (lt_div_iff₀ kp).mp this
    have upSub : F ⁻¹' ball (F x) r ⊆ ball x (R c) := by
      intro y hy
      by_cases eq : y=x
      · simpa [eq] using (mem_ball_self (radius c cp) : x ∈ ball x (R c))
      have yp := abs_pos.mpr (sub_ne_zero.mpr eq)
      have yd : dist (F y) (F x)<r := hy
      have hor : |y-x| ≤ dist (F y) (F x) := by
        rw [dist_eq_norm]
        exact Complex.abs_re_le_norm (F y-F x)
      have ys := (hor.trans_lt yd).le.trans hr.2.le
      have p := (distances yp ys).1.trans_lt yd
      have cap : |y-x|^α < (R c)^α := by
        rw [recover c cp]
        exact (lt_div_iff₀ cp).mpr (by simpa only [mul_comm c] using p)
      exact (Real.rpow_lt_rpow_iff yp.le (radius c cp).le ap).mp cap
    have upper := measure_mono (μ:=volume) upSub
    have lower := measure_mono (μ:=volume) lowSub
    rw [Real.volume_ball] at upper lower
    have finVol := upper.trans_lt ENNReal.ofReal_lt_top
    have up := ENNReal.toReal_mono ENNReal.ofReal_ne_top upper
    have lo := ENNReal.toReal_mono finVol.ne lower
    rw [ENNReal.toReal_ofReal (by nlinarith only [radius c cp] : 0 ≤ 2*R c)] at up
    rw [ENNReal.toReal_ofReal (by nlinarith only [radius K kp] : 0 ≤ 2*R K)] at lo
    rw [mass,ENNReal.toReal_mul]
    change _ ≤ Z*(volume (F ⁻¹' ball (F x) r)).toReal ∧ Z*(volume (F ⁻¹' ball (F x) r)).toReal ≤ _
    constructor
    · simpa only [R,mul_assoc] using mul_le_mul_of_nonneg_left lo zp.le
    · simpa only [R,mul_assoc] using mul_le_mul_of_nonneg_left up zp.le
  · rw [← one_div,lt_div_iff₀ ap]
    nlinarith only [sq_pos_of_pos (sub_pos.mpr a1)]

end Weierstrass
