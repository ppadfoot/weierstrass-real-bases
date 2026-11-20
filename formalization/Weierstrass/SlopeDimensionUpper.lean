module

public import Weierstrass.SlopeDescent
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! Upper local dimension of the conditional slope laws at every index.
The ambient bound uses differentiation of Lebesgue measure relative to the
given law. The entropy bound uses the probability of an actual matching prefix. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

/-- Ambient bound for every locally finite measure on the line. -/
theorem ae_line_mass_lower (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] {h : ℝ} (hh : 1<h) :
    ∀ᵐ y ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal (r^h) ≤ μ (Icc (y-r) (y+r)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume μ,Measure.rnDeriv_lt_top volume μ] with y H fin
  let K := (volume.rnDeriv μ y).toReal+1
  have kp : 0<K := by dsimp only [K];positivity
  have Kbig : volume.rnDeriv μ y < ENNReal.ofReal K := by
    rw [←ENNReal.ofReal_toReal fin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff kp).mpr (lt_add_one _)
  have small := (Real.continuousAt_rpow_const 0 (h-1) (.inr (sub_pos.mpr hh).le)).tendsto.mono_left
    (nhdsWithin_le_nhds (s:=Ioi 0))
  rw [Real.zero_rpow (sub_pos.mpr hh).ne'] at small
  filter_upwards [self_mem_nhdsWithin,H.eventually_lt_const Kbig,small.eventually_lt_const (div_pos (by norm_num : (0:ℝ)<2) kp)] with r (rp : 0<r) rat tiny
  have le := (ENNReal.div_le_iff_le_mul (.inr ENNReal.ofReal_ne_top) (.inr (ENNReal.ofReal_pos.mpr kp).ne')).mp rat.le
  rw [Real.volume_closedBall] at le
  have hom : ENNReal.ofReal K*ENNReal.ofReal (r^h) ≤ ENNReal.ofReal (2*r) := by
    rw [←ENNReal.ofReal_mul kp.le];apply ENNReal.ofReal_le_ofReal
    rw [show r^h = r^(h-1)*r by rw [←Real.rpow_add_one rp.ne',sub_add_cancel],←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith only [(lt_div_iff₀ kp).mp tiny]) rp.le
  rw [←Real.closedBall_eq_Icc]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr kp).ne' ENNReal.ofReal_ne_top).mp (hom.trans le)

theorem cylinder_mass_lower {p : ℕ} (hp : 0<p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ)
    {g : ℝ} (hg : 0<g) (hg1 : g<1) (I : ℕ → Fin p) (k : ℕ) :
    let y := codedSlope d (fun i ↦ (a i:ℝ)) p g w η I
    let R := (2*(1-g)⁻¹)*g^k
    ENNReal.ofReal ((p:ℝ)⁻¹^k) ≤ baseSlopeLaw hp d a w η g (Icc (y-R) (y+R)) := by
  let f (I : ℕ → Fin p) := codedSlope d (fun i ↦ (a i:ℝ)) p g w η I
  let u (I : ℕ → Fin p) := truncatedSlope d (fun i ↦ (a i:ℝ)) p g w η I k
  have mf := measurable_coded_sample hp d a (fun _ : ℝ ↦ w) (fun _ ↦ measurable_const) id measurable_id η g
  dsimp only
  simp only [id_eq] at mf
  rw [baseSlopeLaw,Measure.map_apply mf measurableSet_Icc,←uniformCode_cylinder_mass hp I k]
  apply measure_mono
  intro x hx
  let J := uniformCode p hp x
  have eq : u J=u I := by
    apply Finset.sum_congr rfl;intro j hj
    rw [pathState_prefix d (fun i ↦ (a i:ℝ)) (p:ℝ) w (I:=J) (J:=I) (j+1)
      (fun i hi ↦ hx i (by have := Finset.mem_range.mp hj;omega))]
  have h1 := truncatedSlope_tail d (fun i ↦ (a i:ℝ)) (p:ℝ) w η J hg.le hg1 k
  have h2 := truncatedSlope_tail d (fun i ↦ (a i:ℝ)) (p:ℝ) w η I hg.le hg1 k
  change |f J - u J| ≤ _ at h1
  change |f I - u I| ≤ _ at h2
  rw [eq,abs_le] at h1
  rw [abs_le] at h2
  change f I-(2*(1-g)⁻¹)*g^k ≤ f J ∧ f J ≤ f I+(2*(1-g)⁻¹)*g^k
  constructor <;> linarith

theorem entropy_mass_lower_of_cylinders {p : ℕ} (hp : 2≤p) (μ : Measure ℝ) (y : ℝ) {D g h : ℝ}
    (dp : 0<D) (hg : 0<g) (hg1 : g<1) (hh : log p/log (1/g)<h)
    (cyl : ∀ k : ℕ, ENNReal.ofReal ((p:ℝ)⁻¹^k) ≤ μ (Icc (y-D*g^k) (y+D*g^k))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal (r^h) ≤ μ (Icc (y-r) (y+r)) := by
  let s := log p/log (1/g)
  let K := D/g
  have kp : 0<K := div_pos dp hg
  have pp : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
  have den : 0<log (1/g) := log_pos (by rw [one_div];exact (one_lt_inv₀ hg).mpr hg1)
  have sp : 0<s := div_pos (log_pos pp) den
  have exactRate : g^s=(p:ℝ)⁻¹ := by
    apply (log_injOn_pos (Real.rpow_pos_of_pos hg _) (inv_pos.mpr (zero_lt_one.trans pp)))
    rw [log_rpow hg,log_inv]
    dsimp only [s];rw [one_div,log_inv];field_simp [(log_neg hg hg1).ne]
  have lim := (Real.continuousAt_rpow_const 0 (h-s) (.inr (sub_pos.mpr hh).le)).tendsto.mono_left
    (nhdsWithin_le_nhds (s:=Ioi 0))
  rw [Real.zero_rpow (sub_pos.mpr hh).ne'] at lim
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds dp).filter_mono nhdsWithin_le_nhds,
    lim.eventually_lt_const (inv_pos.mpr (Real.rpow_pos_of_pos kp s))] with r (rp : 0<r) rd tiny
  obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one (div_pos rp dp) ((div_le_one dp).mpr rd.le) hg hg1
  have inside : D*g^(k+1) ≤ r := by linarith only [(lt_div_iff₀ dp).mp lo]
  have high : r/K ≤ g^(k+1) := by
    apply (div_le_iff₀ kp).mpr;rw [pow_succ,show g^k*g*K=g^k*D by dsimp only [K];field_simp]
    exact (div_le_iff₀ dp).mp up
  have mass := cyl (k+1)
  apply (ENNReal.ofReal_le_ofReal (q:=((p:ℝ)⁻¹)^(k+1)) _).trans (mass.trans (measure_mono (Icc_subset_Icc
    (sub_le_sub_left inside _) (add_le_add_right inside _))))
  rw [←exactRate,Real.rpow_pow_comm hg.le]
  refine le_trans ?_ (Real.rpow_le_rpow (div_pos rp kp).le high sp.le)
  rw [Real.div_rpow rp.le kp.le,div_eq_mul_inv,show r^h = r^s*r^(h-s) by rw [←Real.rpow_add rp];ring_nf]
  exact mul_le_mul_of_nonneg_left tiny.le (Real.rpow_nonneg rp.le _)

theorem slope_mass_lower {p : ℕ} (hp : 2≤p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ)
    {g h : ℝ} (hg : 0<g) (hg1 : g<1) (hh : slopeExponent p g<h) :
    let μ := baseSlopeLaw (by omega : 0<p) d a w η g
    ∀ᵐ y ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal (r^h) ≤ μ (Icc (y-r) (y+r)) := by
  let μ := baseSlopeLaw (by omega : 0<p) d a w η g
  change ∀ᵐ y ∂μ, _
  rcases lt_or_ge 1 h with h1|h1
  · exact ae_line_mass_lower μ h1
  have gap : log p/log (1/g) < h := (min_lt_iff.mp hh).resolve_left (not_lt.mpr h1)
  let D := 2*(1-g)⁻¹
  have dp : 0<D := mul_pos (by norm_num) (inv_pos.mpr (sub_pos.mpr hg1))
  have mf := measurable_coded_sample (by omega : 0<p) d a (fun _ : ℝ ↦ w) (fun _ ↦ measurable_const) id measurable_id η g
  simp only [id_eq] at mf
  have each (k : ℕ) : ∀ᵐ y ∂μ, ENNReal.ofReal ((p:ℝ)⁻¹^k) ≤ μ (Icc (y-D*g^k) (y+D*g^k)) := by
    let R := D*g^k
    let S := {v : ℝ × ℝ | v.1-R ≤ v.2 ∧ v.2 ≤ v.1+R}
    have ms : MeasurableSet S := (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add measurable_const))
    have mball : Measurable (fun y ↦ μ (Icc (y-R) (y+R))) := measurable_measure_prodMk_left ms
    apply (ae_map_iff mf.aemeasurable (measurableSet_le measurable_const mball)).mpr
    exact .of_forall fun x ↦ cylinder_mass_lower (by omega : 0<p) d a w η hg hg1 (uniformCode p (by omega) x) k
  filter_upwards [ae_all_iff.mpr each] with y hy
  exact entropy_mass_lower_of_cylinders hp μ y dp hg hg1 gap hy

/-- Simultaneous upper logarithmic local dimension for every central state
and every deterministic phase string. -/
theorem slope_upper_local_dimension {p : ℕ} (hp : 2≤p) (d : ℕ) (a : ℕ → ℤ) (w η : ℕ → ℝ)
    {g : ℝ} (hg : 0<g) (hg1 : g<1) :
    let μ := baseSlopeLaw (by omega : 0<p) d a w η g
    ∀ᵐ y ∂μ, ∀ h : ℝ, slopeExponent p g<h → ∀ᶠ r : ℝ in 𝓝[>] 0,
      log (μ.real (Icc (y-r) (y+r)))/log r ≤ h := by
  let μ := baseSlopeLaw (by omega : 0<p) d a w η g
  let S := slopeExponent p g
  have each (v : ℚ) : ∀ᵐ y ∂μ, S<(v:ℝ) → ∀ᶠ r : ℝ in 𝓝[>] 0,
      log (μ.real (Icc (y-r) (y+r)))/log r ≤ v := by
    by_cases hv : S<(v:ℝ)
    · filter_upwards [slope_mass_lower hp d a w η hg hg1 hv] with y hy
      intro _
      filter_upwards [hy,Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with r hm hr
      have bd := ENNReal.toReal_mono (measure_ne_top μ _) hm
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hr.1.le _)] at bd
      apply (div_le_iff_of_neg (log_neg hr.1 hr.2)).mpr
      change (v:ℝ)*log r ≤ log (μ (Icc (y-r) (y+r))).toReal
      simpa only [log_rpow hr.1] using log_le_log (Real.rpow_pos_of_pos hr.1 _) bd
    · exact .of_forall (fun _ hx ↦ (hv hx).elim)
  filter_upwards [ae_all_iff.mpr each] with y hy
  intro h hh
  obtain ⟨v,sv,vh⟩ := exists_rat_btwn hh
  filter_upwards [hy v sv] with r hr using hr.trans vh.le

end Weierstrass.Predecessor
