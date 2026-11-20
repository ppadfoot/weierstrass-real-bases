module

public import Weierstrass.StripLinearization

/-! # Reversal of the past slope and physical reanchoring on the phase torus -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Weierstrass.StripProof
open CriticalRay

private theorem τpos : 0 < τ := by dsimp [τ]; positivity

def angleTerm (b g : ℝ) (c d : ℤ → ℝ) (z : PhaseTorus) (x : ℝ) (j : ℤ) : ℝ :=
  g^j*c j*(angleCos (z j+↑(b^j*d j*x))-angleCos (z j))

private def lift (z : PhaseTorus) (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (z j)
private theorem coe_lift (z : PhaseTorus) (j : ℤ) : (↑(lift z j) : UnitAddCircle) = z j :=
  AddCircle.coe_equivIco

private theorem term_lift (b g : ℝ) (c d : ℤ → ℝ) (z : PhaseTorus) (x : ℝ) (j : ℤ) :
    angleTerm b g c d z x j = rayTerm b g c d (lift z) x j := by
  unfold angleTerm rayTerm
  rw [← coe_lift z j,← AddCircle.coe_add,angleCos_coe,angleCos_coe]

theorem hasSum_angleTerm {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (z : PhaseTorus) (x : ℝ) :
    HasSum (angleTerm b g c d z x) (circleRay b g c d z x) := by
  apply Summable.hasSum
  exact (summable_rayTerm hb hg hg1 hbg hc hd (lift z) x).congr (fun j => (term_lift _ _ _ _ _ _ _).symm)

theorem angleTerm_lipschitz {b g : ℝ} (hb : 0 < b) (hg : 0 < g) {c d : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (z : PhaseTorus) (x : ℝ) (j : ℤ) :
    |angleTerm b g c d z x j| ≤ τ*|x| *(b*g)^j := by
  rw [term_lift]; unfold rayTerm
  have cosb := Real.abs_cos_sub_cos_le (τ*(lift z j+b^j*d j*x)) (τ*lift z j)
  rw [show τ*(lift z j+b^j*d j*x)-τ*lift z j=τ*b^j*d j*x by ring,
    abs_mul,abs_mul,abs_mul,abs_of_pos τpos,abs_of_pos (zpow_pos hb _)] at cosb
  rw [abs_mul,abs_mul,abs_of_pos (zpow_pos hg _),mul_zpow]
  calc
    _ ≤ (g^j*1)*(τ*b^j*1*|x|) := by gcongr; exacts [hc j,cosb.trans (by gcongr; exact hd j)]
    _ = _ := by ring

theorem angleTerm_bounded {g : ℝ} (hg : 0 < g) (b : ℝ) {c : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (d : ℤ → ℝ) (z : PhaseTorus) (x : ℝ) (j : ℤ) : |angleTerm b g c d z x j| ≤ 2*g^j := by
  rw [term_lift]; unfold rayTerm
  rw [abs_mul,abs_mul,abs_of_pos (zpow_pos hg _)]
  have diff (s t : ℝ) : |Real.cos s-Real.cos t| ≤ 2 := (abs_sub _ _).trans
    (by linarith [Real.abs_cos_le_one s,Real.abs_cos_le_one t])
  calc
    _ ≤ (g^j*1)*2 := by gcongr; exacts [hc j,diff _ _]
    _ = _ := by ring

/-- Reindex and reanchor the actual circle-valued physical model. -/
theorem circleRay_recenter_scale {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (z : PhaseTorus) (n : ℤ) (x y : ℝ) :
    circleRay b g c d z (x+b^(-n)*y) - circleRay b g c d z x =
      g^n * circleRay b g (fun j => c (j+n)) (fun j => d (j+n))
        (fun j => z (j+n) + ↑(b^(j+n)*d (j+n)*x)) y := by
  let ζ := lift z
  have eqz : (fun j => (↑(ζ j) : UnitAddCircle)) = z := funext (coe_lift z)
  have eqn : (fun i => (↑(ζ (i+n)+b^(i+n)*d (i+n)*x) : UnitAddCircle)) =
      (fun i => z (i+n)+↑(b^(i+n)*d (i+n)*x)) := by funext i; simp [ζ,coe_lift]
  have hcirc (t : ℝ) : circleRay b g c d z t = rayIncrement b g c d ζ t :=
    (congrArg (fun w => circleRay b g c d w t) eqz).symm.trans (circleRay_real _ _ _ _ _ _)
  rw [hcirc,hcirc,← eqn,circleRay_real]
  exact rayIncrement_recenter_scale hb hg hg1 hbg hc hd ζ n x y

/-- The extra quarter turn converts the derivative of the forcing to the phase convention of the dual cosine. -/
def dualPhase (z : PhaseTorus) (j : ℤ) : UnitAddCircle := z (-j)+↑(1/4:ℝ)

def dualWeight (c d : ℤ → ℝ) (j : ℤ) := c (-j)*d (-j)

theorem dualWeight_bound {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (j : ℤ) :
    |dualWeight c d j| ≤ 1 := by rw [dualWeight,abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (hd _)).trans (hc _)

private theorem phase_mode {b g ρ : ℝ} (c d e : ℤ → ℝ) (z : PhaseTorus) (h : ℝ) {j : ℤ} (hj : j < 0) :
    pastTerm b g c d (z+transverseOrbit ρ e h) j - pastTerm b g c d z j =
      τ*angleTerm ρ⁻¹ (b*g)⁻¹ (dualWeight c d) (fun i => e (-i)) (dualPhase z) h (-j) := by
  simp only [pastTerm,if_pos hj,angleTerm,dualWeight,dualPhase,neg_neg,inv_zpow,zpow_neg,inv_inv,
    forcingDerivative,Pi.add_apply,transverseOrbit]
  rw [show z j+↑(ρ^j*e j*h)+(↑(1/4:ℝ):UnitAddCircle) =
    z j+↑(1/4:ℝ)+↑(ρ^j*e j*h) by abel]
  ring

/-- The difference between the past-slope increment and the full dual increment is
Lipschitz, uniformly in the entire phase sequence and all weights. -/
theorem reversed_slope_comparison {b g ρ : ℝ} (hbg : 1 < b*g) (hr : 0 < ρ)
    (hdual : 1 < ρ⁻¹*(b*g)⁻¹) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (h : ℝ) :
    |pastSlope b g c d (z+transverseOrbit ρ e h)-pastSlope b g c d z -
      τ*circleRay ρ⁻¹ (b*g)⁻¹ (dualWeight c d) (fun i => e (-i)) (dualPhase z) h| ≤
      τ^2*(1-(ρ⁻¹*(b*g)⁻¹)⁻¹)⁻¹*|h| := by
  let q := ρ⁻¹*(b*g)⁻¹
  let f := angleTerm ρ⁻¹ (b*g)⁻¹ (dualWeight c d) (fun i => e (-i)) (dualPhase z) h
  have hs := (hasSum_angleTerm (inv_pos.mpr hr) (inv_pos.mpr (zero_lt_one.trans hbg))
    (inv_lt_one_of_one_lt₀ hbg) hdual (dualWeight_bound hc hd) (fun i => he (-i)) (dualPhase z) h)
  have re : HasSum (fun j : ℤ => τ*f (-j)) (τ*circleRay ρ⁻¹ (b*g)⁻¹ (dualWeight c d)
      (fun i => e (-i)) (dualPhase z) h) := ((Equiv.neg ℤ).hasSum_iff.mpr hs).mul_left τ
  have F := ((summable_past hbg hc hd (z+transverseOrbit ρ e h)).hasSum.sub
    (summable_past hbg hc hd z).hasSum).sub re
  let w := fun j : ℤ => if 0 ≤ j then (q⁻¹)^j else 0
  have hg0 := hasSum_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hdual)).le (inv_lt_one_of_one_lt₀ hdual)
  have hw : HasSum w (1-q⁻¹)⁻¹ := by
    have H := (show HasSum (fun n : ℕ => w n) (1-q⁻¹)⁻¹ by simpa [w,q] using hg0).of_nat_of_neg_add_one
      (show HasSum (fun n : ℕ => w (-(n+1:ℤ))) 0 by
        apply hasSum_zero.congr_fun
        intro n; change w (-(n+1:ℤ)) = 0; rw [show w (-(n+1:ℤ)) = 0 from if_neg (by omega)])
    simpa only [add_zero] using H
  apply F.norm_le_of_bounded ((hw.mul_left (τ^2)).mul_right |h|)
  intro j
  change |pastTerm b g c d (z+transverseOrbit ρ e h) j-pastTerm b g c d z j - τ*f (-j)| ≤ τ^2*w j*|h|
  by_cases hj : j < 0
  · rw [phase_mode c d e z h hj]; simp [w,f,show ¬0 ≤ j by omega]
  · simp only [pastTerm,if_neg hj,sub_self,zero_sub,abs_neg,abs_mul,abs_of_pos τpos,w,if_pos (by omega : 0 ≤ j)]
    have hh := angleTerm_lipschitz (inv_pos.mpr hr) (inv_pos.mpr (zero_lt_one.trans hbg))
      (dualWeight_bound hc hd) (fun i => he (-i)) (dualPhase z) h (-j)
    calc
      _ ≤ τ*(τ*|h| *q^(-j)) := mul_le_mul_of_nonneg_left hh τpos.le
      _ = _ := by rw [inv_zpow,zpow_neg]; ring

theorem measurable_pastSlope (b g : ℝ) (c d : ℤ → ℝ) : Measurable (pastSlope b g c d) := by
  apply Measurable.tsum
  intro j
  by_cases hj : j < 0
  · simp only [pastTerm,if_pos hj,forcingDerivative]
    have ac : Continuous angleCos := Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)
    exact measurable_const.mul (measurable_const.mul ((ac.comp ((continuous_apply j).add continuous_const)).measurable))
  · simp only [pastTerm,if_neg hj]; exact measurable_const

theorem measurable_transverseOrbit (ρ : ℝ) (e : ℤ → ℝ) : Measurable (transverseOrbit ρ e) := by
  apply measurable_pi_lambda; intro j
  exact (AddCircle.continuous_mk' (1:ℝ)).measurable.comp (measurable_const.mul measurable_id)

def rayBound (b g T : ℝ) := (2+τ*T)*∑' j : ℤ, tails g (b*g) j

/-- A bound valid for every phase and every permitted pair of profiles. -/
theorem circleRay_uniform_bound {b g T : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (z : PhaseTorus) {x : ℝ} (hx : |x| ≤ T) : |circleRay b g c d z x| ≤ rayBound b g T := by
  have tp := τpos
  have tpos := (abs_nonneg x).trans hx
  apply (hasSum_angleTerm hb hg hg1 hbg hc hd z x).norm_le_of_bounded
    ((summable_tails hg.le hg1 hbg).hasSum.mul_left (2+τ*T))
  intro j
  rw [Real.norm_eq_abs,tails]
  split_ifs
  · exact (angleTerm_bounded hg _ hc _ _ _ j).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (mul_nonneg tp.le tpos)) (zpow_pos hg _).le)
  · apply (angleTerm_lipschitz hb hg hc hd z x j).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hx tp.le])
      (zpow_pos (zero_lt_one.trans hbg) _).le

/-- The normalized slope direction used by the physical strip model, at a relative time u. -/
def direction (b g ρ : ℝ) (c d e : ℤ → ℝ) (z : PhaseTorus) (m : ℕ) (u : ℝ) : ℝ :=
  (((b*g)⁻¹)^m)⁻¹*(pastSlope b g c d (z+transverseOrbit ρ e (ρ^m*u))-pastSlope b g c d z)

theorem measurable_direction (b g ρ : ℝ) (c d e : ℤ → ℝ) (m : ℕ) :
    Measurable (fun p : PhaseTorus × ℝ => direction b g ρ c d e p.1 m p.2) :=
  measurable_const.mul (((measurable_pastSlope _ _ _ _).comp (measurable_fst.add
    ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_snd)))).sub
    ((measurable_pastSlope _ _ _ _).comp measurable_fst))

def reversedParameters (c d e : ℤ → ℝ) (m : ℕ) : RayParameters :=
  (fun j => dualWeight c d (j+m), fun j => e (-(j+m)))

def reversedEnvironment (z : PhaseTorus) (m : ℕ) : PhaseTorus := fun j => dualPhase z (j+m)

def dualError (b g ρ : ℝ) := τ^2*(1-(ρ⁻¹*(b*g)⁻¹)⁻¹)⁻¹

/-- Centered B3 test on the actual normalized slope map of a stable cell. The error
is uniformly O((ρ/γ)^m), including displacements of both signs. -/
theorem direction_recenter {b g ρ : ℝ} (hbg : 1 < b*g) (hr : 0 < ρ) (hdual : 1 < ρ⁻¹*(b*g)⁻¹)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (m : ℕ) (u v : ℝ) :
    |direction b g ρ c d e z m v - direction b g ρ c d e z m u -
      τ*circleRay ρ⁻¹ (b*g)⁻¹ (reversedParameters c d e m).1 (reversedParameters c d e m).2
        (reversedEnvironment (z+transverseOrbit ρ e (ρ^m*u)) m) (v-u)| ≤
      dualError b g ρ*(ρ/(b*g)⁻¹)^m*|v-u| := by
  let z' := z+transverseOrbit ρ e (ρ^m*u)
  have hh := reversed_slope_comparison hbg hr hdual hc hd he z' (ρ^m*(v-u))
  have cm := circleRay_recenter_scale (inv_pos.mpr hr) (inv_pos.mpr (zero_lt_one.trans hbg))
    (inv_lt_one_of_one_lt₀ hbg) hdual (dualWeight_bound hc hd) (fun j => he (-j))
    (dualPhase z') (m:ℤ) 0 (v-u)
  have z0 (w : PhaseTorus) (b g : ℝ) (c d : ℤ → ℝ) : circleRay b g c d w 0 = 0 := by simp [circleRay]
  simp only [zpow_neg,zpow_natCast,inv_pow,inv_inv,zero_add,mul_zero,AddCircle.coe_zero,add_zero,
    z0, sub_zero] at cm
  have zz : z'+transverseOrbit ρ e (ρ^m*(v-u)) = z+transverseOrbit ρ e (ρ^m*v) := by
    dsimp [z']; rw [add_assoc,← transverseOrbit_add]; congr 2; ring
  rw [zz,cm] at hh
  have gp : 0 < ((b*g)⁻¹)^m := pow_pos (inv_pos.mpr (zero_lt_one.trans hbg)) _
  have H := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr gp.le)
  rw [← abs_of_pos (inv_pos.mpr gp),← abs_mul] at H
  apply le_trans (le_of_eq ?_) (H.trans_eq ?_)
  · congr 1
    unfold direction reversedParameters reversedEnvironment
    dsimp only [Prod.fst,Prod.snd]
    dsimp only [z']
    rw [inv_pow]
    field_simp [(zero_lt_one.trans hbg).ne']
    ring

  · rw [abs_of_pos (inv_pos.mpr gp),abs_mul,abs_of_pos (pow_pos hr m),div_pow]
    dsimp [dualError]; ring

end Weierstrass.StripProof
