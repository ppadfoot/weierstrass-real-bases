module

public import Weierstrass.WindowBound

/-! Passing from moving-window physical entropy to a power law for the realized dyadic cell. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Weierstrass.GraphWindow

private theorem boundary_limit {m : ℕ → ℕ} {w D : ℝ} (C α : ℝ)
    (hw : Tendsto (fun K : ℕ ↦ (m K:ℝ)/K) atTop (𝓝 w)) :
    Tendsto (fun K : ℕ ↦ (((m K:ℝ)*C+Real.sqrt ((m K:ℝ)*D*((K:ℝ)+1)))/α)/K)
      atTop (𝓝 ((C/α)*w+(Real.sqrt D/α)*Real.sqrt w)) := by
  have ww : 0 ≤ w := le_of_tendsto_of_tendsto' tendsto_const_nhds hw (fun _ ↦ by positivity)
  have hi : Tendsto (fun K : ℕ ↦ (K:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have other : Tendsto (fun K : ℕ ↦ 1+(K:ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=(1:ℝ))).add hi
  have root := Real.continuous_sqrt.continuousAt.tendsto.comp ((hw.mul_const D).mul other)
  have goal := ((hw.mul_const C).add root).div_const α
  rw [mul_one,Real.sqrt_mul ww] at goal
  convert goal.congr' ?_ using 1
  · congr 1
    ring
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with K hK
    have hK₀ : 0 < (K:ℝ) := Nat.cast_pos.mpr hK
    have rootEq : ((m K:ℝ)/K*D*(1+(K:ℝ)⁻¹)) = ((m K:ℝ)*D*((K:ℝ)+1))/(K:ℝ)^2 := by
      field_simp
    dsimp only [Function.comp_apply]
    rw [rootEq,Real.sqrt_div' _ (sq_nonneg _),Real.sqrt_sq hK₀.le]
    ring

private theorem cell_pow_eq (s : ℝ) (K : ℕ) :
    (((1/2:ℝ)^s)^K) = Real.exp (-(K:ℝ)*Real.log 2*s) := by
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (1/2:ℝ)),one_div,Real.log_inv,← Real.exp_nat_mul]
  congr 1
  ring

/-- For each strictly subcritical exponent, the density-one boundary estimate,
held simultaneously over the block lengths, gives a summation proof on the
actual prescribed phase orbit. -/
theorem cell_decay_at_information {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (H : AnchoredEstimate b l v) (φ : ℤ → ℝ) (T C : ℝ)
    (G : WindowMassBound b l φ T C) {s : ℝ} (hs : s < 1+v*(1-alpha b l)) :
    ∀ᵐ x ∂standardLaw, ∀ᶠ K : ℕ in atTop, cellMass b l φ T K x ≤
      ENNReal.ofReal (((1/2:ℝ)^s)^K) := by
  let a := verticalRate l
  let d := horizontalRate b
  let α := alpha b l
  have hα : 0 < α := (alpha_mem_Ioo hb hl hl').1
  have ha1 : α < 1 := (alpha_mem_Ioo hb hl hl').2
  have hA : 0 < 1-α := sub_pos.mpr ha1
  have rates := rates_admissible hb hl hl'
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have choose : max 0 ((s-1)/(1-α)) < v := max_lt hv
    ((div_lt_iff₀ hA).mpr (by change s < 1+v*(1-α) at hs; linarith only [hs]))
  obtain ⟨h₀,h₀lo,h₀hi⟩ := exists_between choose
  obtain ⟨h,hhlo,hh⟩ := exists_between h₀hi
  have hh₀ : 0 < h₀ := (le_max_left _ _).trans_lt h₀lo
  have hpos := hh₀.trans hhlo
  let δ := 1-h₀/h
  have hδ : 0 < δ := sub_pos.mpr ((div_lt_one hpos).mpr hhlo)
  have dprod : (1-δ)*h = h₀ := by dsimp [δ]; field_simp; ring
  have margin : s < 1+(1-δ)*h*(1-α) := by
    rw [dprod]
    have hh' := (div_lt_iff₀ hA).mp ((le_max_right _ _).trans_lt h₀lo)
    linarith
  let c (q : ℕ) := (1-δ)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2)
  let w (q : ℕ) := ((q:ℝ)*a)⁻¹-((q:ℝ)*d)⁻¹
  let P (q : ℕ) (x : ℝ) := ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop,
    w q*c q-ε ≤ windowSum b l φ q K x/(K:ℝ)
  have entropy : ∀ᶠ q : ℕ in atTop, ∀ᵐ x ∂standardLaw, P q x := by
    have H' := anchored_physical_entropy hb hl hl' hv1 H
      hpos hh hδ φ rates.1 rates.2 0
    simpa only [P,w,c,a,d,windowSum,standardLaw, Measure.restrict_congr_set (α:=ℝ) (μ:=volume)
      (Ico_ae_eq_Ioc (a:=0) (b:=1)),zero_add] using H'
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp entropy
  have allq : ∀ᵐ x ∂standardLaw, ∀ q : ℕ, Q ≤ q → P q x := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : Q ≤ q
    · exact (hQ q hq).mono fun _ h _ ↦ h
    · exact .of_forall fun _ h ↦ (hq h).elim
  filter_upwards [G,allq] with x gx hx
  obtain ⟨D,hD,g⟩ := gx
  let C' := Real.log C/α
  let A' := Real.sqrt D/α
  have rate := entropy_rate_limit hb hl hl' hpos δ C' A'
  have good := rate.eventually (eventually_gt_nhds (show s-1 < (1-δ)*h*(1-α) by linarith only [margin]))
  have grows : Tendsto (fun q : ℕ ↦ (q:ℝ)*a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const rates.1
  obtain ⟨q,hqQ,hqpos,hqa,hqgain⟩ := (Eventually.and (eventually_ge_atTop Q)
    ((eventually_gt_atTop (0:ℕ)).and ((grows.eventually_ge_atTop 1).and good))).exists
  change s-1 < (w q*c q-C'*w q-A'*Real.sqrt (w q))/Real.log 2 at hqgain
  let p := w q*c q
  let B := C'*w q+A'*Real.sqrt (w q)
  have gap : 0 < p-B-(s-1)*Real.log 2 := by
    have H' := (lt_div_iff₀ logTwo).mp hqgain
    dsimp [p,B]; linarith
  let e := (p-B-(s-1)*Real.log 2)/4
  have he : 0 < e := div_pos gap (by norm_num)
  have invlim := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  obtain ⟨k,hk⟩ := (invlim.eventually (eventually_lt_nhds he)).exists
  have width := (endpoint_limits hqpos rates.1 rates.2).2.2.2.1
  have boundary := boundary_limit (D:=D) (Real.log C) α width
  change Tendsto (fun K : ℕ ↦ ((((windowLength b l q K:ℕ):ℝ)*Real.log C +
    Real.sqrt (((windowLength b l q K:ℕ):ℝ)*D*((K:ℝ)+1)))/α)/K) atTop (𝓝 B) at boundary
  have loss := boundary.eventually (eventually_lt_nhds (show B < B+e by linarith only [he]))
  filter_upwards [g q hqpos hqa k,hx q hqQ e he,loss,eventually_gt_atTop (0:ℕ)] with K hg hsum hcost hK
  apply hg.trans
  rw [cell_pow_eq]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have Kpos : 0 < (K:ℝ) := Nat.cast_pos.mpr hK
  have hsum' := (le_div_iff₀ Kpos).mp hsum
  have hcost' := (div_lt_iff₀ Kpos).mp hcost
  have hstep := mul_le_mul_of_nonneg_left hk.le Kpos.le
  have he' : (K:ℝ)*e*4 = (p-B-(s-1)*Real.log 2)*K := by dsimp [e]; ring
  change -(K:ℝ)*Real.log 2+K/((k:ℝ)+1)-windowSum b l φ q K x+
    (((windowLength b l q K:ℕ):ℝ)*Real.log C+
      Real.sqrt (((windowLength b l q K:ℕ):ℝ)*D*((K:ℝ)+1)))/α ≤ _
  change (p-e)*(K:ℝ) ≤ _ at hsum'
  change (K:ℝ)*(1/((k:ℝ)+1)) ≤ _ at hstep
  rw [mul_one_div] at hstep
  nlinarith only [hsum',hcost',hstep,he',mul_nonneg Kpos.le he.le]

/-- The endpoint used for the all-phase exact dimension statement. -/
theorem cell_decay_of_window_mass {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (H : AnchoredEstimate b l 1) (φ : ℤ → ℝ) (T C : ℝ)
    (G : WindowMassBound b l φ T C) {s : ℝ} (hs : s < 2-alpha b l) :
    ∀ᵐ x ∂standardLaw, ∀ᶠ K : ℕ in atTop, cellMass b l φ T K x ≤
      ENNReal.ofReal (((1/2:ℝ)^s)^K) :=
  cell_decay_at_information hb hl hl' zero_lt_one le_rfl H φ T C G (by linarith only [hs])

end Weierstrass.GraphWindow
