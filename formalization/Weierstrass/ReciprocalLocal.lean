module

public import Weierstrass.ReciprocalRegularity
public import Weierstrass.ReciprocalCover

/-! Comparing the neighboring transverse environments in Proposition 2. -/
@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace Weierstrass.Reciprocal
open CriticalRay StripProof

private theorem τpos : 0 < τ := by dsimp [τ]; positivity

private theorem orbit_add_from (ρ : ℝ) (e : ℤ → ℝ) (z : PhaseTorus) (x y : ℝ) :
    z+transverseOrbit ρ e x+transverseOrbit ρ e (y-x) = z+transverseOrbit ρ e y := by
  rw [add_assoc,← transverseOrbit_add,add_sub_cancel]

def slopeConstant (b g ρ : ℝ) :=
  2*|dualError b g ρ|+τ*|rayBound ρ⁻¹ (b*g)⁻¹ 2|

private theorem difference_direction {b g ρ : ℝ} (hbg : 1 < b*g) (hρ : 0 < ρ)
    (hdual : 1 < ρ⁻¹*(b*g)⁻¹) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (z : PhaseTorus) (m : ℕ) (y : ℝ) :
    |direction b g ρ c d e z m y - τ*circleRay ρ⁻¹ (b*g)⁻¹ (reversedParameters c d e m).1
      (reversedParameters c d e m).2 (reversedEnvironment z m) y| ≤
      dualError b g ρ*(ρ/(b*g)⁻¹)^m*|y| := by
  have zero : transverseOrbit ρ e 0 = 0 := by ext; simp [transverseOrbit]
  simpa only [direction, mul_zero,zero,add_zero,sub_self,sub_zero] using direction_recenter hbg hρ hdual hc hd he z m 0 y

/-- A bounded displacement at stable scale m changes the past slope by at most
a fixed multiple of the dual amplitude to power m. -/
theorem past_difference_small {b g ρ : ℝ} (hbg : 1 < b*g) (hρ : 0 < ρ)
    (hrγ : ρ < (b*g)⁻¹) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (z : PhaseTorus) (m : ℕ) (h : ℝ)
    (hh : |h| ≤ 2*ρ^m) :
    |pastSlope b g c d (z+transverseOrbit ρ e h)-pastSlope b g c d z| ≤ slopeConstant b g ρ * ((b*g)⁻¹)^m := by
  let γ := (b*g)⁻¹
  have gp : 0 < γ := inv_pos.mpr (zero_lt_one.trans hbg)
  have gp' := pow_pos gp m
  have hdual : 1 < ρ⁻¹*(b*g)⁻¹ := by rw [inv_mul_eq_div,one_lt_div hρ]; exact hrγ
  let y := h/ρ^m
  have hy : |y| ≤ 2 := by dsimp [y]; rw [abs_div,abs_of_pos (pow_pos hρ _),div_le_iff₀ (pow_pos hρ _)]; exact hh
  have F := difference_direction hbg hρ hdual hc hd he z m y
  let dF := circleRay ρ⁻¹ γ (reversedParameters c d e m).1 (reversedParameters c d e m).2 (reversedEnvironment z m) y
  have hp : |dF| ≤ rayBound ρ⁻¹ γ 2 :=
    circleRay_uniform_bound (inv_pos.mpr hρ) gp (inv_lt_one_of_one_lt₀ hbg) hdual
      (fun j ↦ dualWeight_bound hc hd _) (fun j ↦ he _) _ hy
  have ratio : (ρ/γ)^m ≤ 1 := pow_le_one₀ (div_pos hρ gp).le ((div_le_one gp).mpr hrγ.le)
  have err : dualError b g ρ*(ρ/γ)^m*|y| ≤ |dualError b g ρ| *1*2 :=
    mul_le_mul (mul_le_mul (le_abs_self _) ratio (pow_nonneg (div_pos hρ gp).le _) (abs_nonneg _))
      hy (abs_nonneg _) (by positivity)
  have lim : |direction b g ρ c d e z m y| ≤ slopeConstant b g ρ := by
    have tr := abs_sub_le (direction b g ρ c d e z m y) (τ*dF) 0
    rw [sub_zero,sub_zero,abs_mul,abs_of_pos τpos] at tr
    change |direction b g ρ c d e z m y - τ*dF| ≤ _ at F
    unfold slopeConstant; dsimp only [γ] at *
    linarith [F.trans err,mul_le_mul_of_nonneg_left (hp.trans (le_abs_self _)) τpos.le]
  rw [direction,show ρ^m*y=h from by dsimp [y]; field_simp,abs_mul,
    abs_of_pos (inv_pos.mpr gp'),inv_mul_eq_div,div_le_iff₀ gp'] at lim
  exact lim

def targetConstant (b g ρ α A K : ℝ) :=
  (slopeConstant b g ρ + 2*K + |regularityConstant b g ρ α A| *2^α + 2*|dualError b g ρ|)/τ

private theorem actual_secant_slope {b g ρ α A Q : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hfast : b*g*ρ < 1) (hα : 0 < α) (ha : α ≤ 1)
    (hslow : 1 < b^2*g*ρ^α) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (m M : ℕ) (z : PhaseTorus) {t h : ℝ}
    (ht : |t| ≤ A) (htpos : 0 < |t|) (hh : |h| ≤ 2*ρ^m)
    (hpow : (ρ^m)^α ≤ ((b*g)⁻¹)^M)
    (v₁ : |circleRay b g c d z t| ≤ Q*((b*g)⁻¹)^M*|t|)
    (v₂ : |circleRay b g c d (z+transverseOrbit ρ e h) t| ≤ Q*((b*g)⁻¹)^M*|t|) :
    |pastSlope b g c d (z+transverseOrbit ρ e h)-pastSlope b g c d z| ≤
      (2*Q+|regularityConstant b g ρ α A| *2^α)*((b*g)⁻¹)^M := by
  have shrink : |h| ≤ 2 := hh.trans (mul_le_of_le_one_right (by norm_num) (pow_le_one₀ hρ.le hρ1))
  have mag : |h|^α ≤ 2^α*((b*g)⁻¹)^M := by
    refine (Real.rpow_le_rpow (abs_nonneg h) hh hα.le).trans ?_
    rw [Real.mul_rpow (by norm_num) (pow_pos hρ _).le]
    gcongr
  have err := regularity hb hg hg1 hbg hρ hfast hα ha hslow hc hd he z t h ht shrink
  let H := pastSlope b g c d (z+transverseOrbit ρ e h)-pastSlope b g c d z
  let f := circleRay b g c d (z+transverseOrbit ρ e h) t - circleRay b g c d z t
  let C := regularityConstant b g ρ α A
  change |f-t*H| ≤ C*|t| * |h|^α at err
  have fbound : |f| ≤ Q*((b*g)⁻¹)^M*|t|+Q*((b*g)⁻¹)^M*|t| := (abs_sub _ _).trans (add_le_add v₂ v₁)
  have ebound : C*|t| * |h|^α ≤ |C| *|t| * (2^α*((b*g)⁻¹)^M) := by gcongr; exact le_abs_self C
  have tr := abs_sub_le (t*H) f 0
  rw [sub_zero,sub_zero,abs_sub_comm (t*H),abs_mul] at tr
  apply le_of_mul_le_mul_left (a := |t|) _ htpos
  dsimp only [C] at *
  nlinarith only [tr,err.trans ebound,fbound]


/-- The good dual test at one retained reference point bounds the length of
the occupied neighborhood at the next stable scale, including neighboring
points whose phase need not itself pass the dual test. -/
theorem retained_neighborhood_step {b g ρ α A Q σ : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hρ : 0 < ρ) (hrγ : ρ < (b*g)⁻¹) (hα : 0 < α) (ha : α ≤ 1)
    (hslow : 1 < b^2*g*ρ^α) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (m M : ℕ) (hmM : m ≤ M)
    (half : ρ^M ≤ ρ^m/2) (powcontrol : (ρ^m)^α ≤ ((b*g)⁻¹)^M)
    (z₀ : PhaseTorus) (t : ℝ) (ht : |t| ≤ A) (htp : 0 < |t|) (E : Set ℝ)
    (sig : ∀ x ∈ E, |circleRay b g c d (z₀+transverseOrbit ρ e x) t| ≤ Q*((b*g)⁻¹)^M*|t|)
    (test : ∀ x ∈ E, rayOccupation ρ⁻¹ (b*g)⁻¹ (reversedParameters c d e m)
      (reversedEnvironment (z₀+transverseOrbit ρ e x) m) 2 (targetConstant b g ρ α A Q) (((b*g)⁻¹)^(M-m)) ≤
        ENNReal.ofReal ((((b*g)⁻¹)^(M-m))^σ)) :
    volume (neighborhood E (ρ^M)) ≤ ENNReal.ofReal ((((b*g)⁻¹)^(M-m))^σ) * volume (neighborhood E (ρ^m)) := by
  let γ := (b*g)⁻¹
  have gp : 0 < γ := inv_pos.mpr (zero_lt_one.trans hbg)
  have gr : γ < 1 := inv_lt_one_of_one_lt₀ hbg
  have hρ1 : ρ < 1 := hrγ.trans gr
  have hfast : b*g*ρ < 1 := by rw [← lt_div_iff₀' (zero_lt_one.trans hbg),one_div]; exact hrγ
  have hdual : 1 < ρ⁻¹*γ := by rw [inv_mul_eq_div,one_lt_div hρ]; exact hrγ
  let u := ρ^m
  let v := ρ^M
  have up : 0 < u := pow_pos hρ _
  have vp : 0 < v := pow_pos hρ _
  let z (x : ℝ) := z₀+transverseOrbit ρ e x
  let H (x : ℝ) := pastSlope b g c d (z x)
  let sc := slopeConstant b g ρ
  let rc := |regularityConstant b g ρ α A| *2^α
  let K := targetConstant b g ρ α A Q
  let de := |dualError b g ρ|
  let a := γ^(M-m)
  have gp' := pow_pos gp m
  have gm : γ^M = γ^m*a := by rw [← pow_add, Nat.add_sub_of_le hmM]
  have ratio : (ρ/γ)^m ≤ a := by
    rw [div_pow,div_le_iff₀ gp']
    have rate : u ≤ u^α := by
      convert min_one_le_rpow hα ha up.le using 1
      rw [min_eq_right (pow_le_one₀ hρ.le hρ1.le)]
    exact rate.trans (powcontrol.trans_eq (gm.trans (mul_comm _ _)))
  apply neighborhood_step E up half
  intro y hy
  obtain ⟨x,hx,yx⟩ := neighborhood_mem.mp hy
  let S := {q : ℝ | q ∈ Icc (-2) 2 ∧ |circleRay ρ⁻¹ γ (reversedParameters c d e m).1
      (reversedParameters c d e m).2 (reversedEnvironment (z x) m) q| ≤ K*a}
  let φ (s : ℝ) := u⁻¹*(s-x)
  have sub : ball y (u/2) ∩ neighborhood E v ⊆ φ ⁻¹' S := by
    intro s hs
    obtain ⟨r,hr,sr⟩ := neighborhood_mem.mp hs.2
    have sy := hs.1
    rw [mem_ball,Real.dist_eq] at sy
    have sx : |s-x| ≤ 2*u := (abs_sub_le s y x).trans (by linarith)
    have rx : |r-x| ≤ 2*u := by
      have dist := abs_sub_le r s x
      rw [abs_sub_comm r s] at dist
      linarith [abs_sub_le s y x,dist]
    have sr' : |s-r| ≤ 2*v := by linarith
    have hsr := past_difference_small hbg hρ hrγ hc hd he (z r) M (s-r) sr'
    have trans (d a : ℝ) : z d+transverseOrbit ρ e (a-d) = z a := orbit_add_from _ _ _ _ _
    rw [trans] at hsr
    have hrx := actual_secant_slope hb hg hg1 hbg hρ hρ1.le hfast hα ha hslow hc hd he m M (z x)
      ht htp rx powcontrol (sig x hx) (by rw [trans]; exact sig r hr)
    rw [trans] at hrx
    have dst : |H s-H x| ≤ (sc+2*Q+rc)*γ^M := by
      have tr := abs_sub_le (H s) (H r) (H x)
      change |H s-H r| ≤ sc*γ^M at hsr
      change |H r-H x| ≤ (2*Q+rc)*γ^M at hrx
      linarith
    have φsmall : |φ s| ≤ 2 := by dsimp [φ]; rw [inv_mul_eq_div,abs_div,abs_of_pos up,div_le_iff₀ up]; exact sx
    have eq := difference_direction hbg hρ hdual hc hd he (z x) m (φ s)
    have del : |direction b g ρ c d e (z x) m (φ s)| ≤ (sc+2*Q+rc)*a := by
      change |(γ^m)⁻¹*(pastSlope b g c d (z x+transverseOrbit ρ e (u*(φ s)))-pastSlope b g c d (z x))| ≤ _
      rw [show u*(φ s)=s-x from by dsimp [φ]; field_simp,trans,inv_mul_eq_div,abs_div,abs_of_pos gp',div_le_iff₀ gp']
      exact dst.trans_eq (by rw [gm]; ring)
    let F := circleRay ρ⁻¹ γ (reversedParameters c d e m).1 (reversedParameters c d e m).2 (reversedEnvironment (z x) m) (φ s)
    let Y := direction b g ρ c d e (z x) m (φ s)
    have err : |Y-τ*F| ≤ 2*de*a := by
      change |Y-τ*F| ≤ dualError b g ρ*(ρ/γ)^m*|φ s| at eq
      refine eq.trans (le_trans (mul_le_mul (mul_le_mul (le_abs_self _) ratio (pow_nonneg (div_pos hρ gp).le _) (abs_nonneg _))
        φsmall (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_pos gp _).le)) ?_)
      dsimp only [de]; exact le_of_eq (by ring)
    change φ s ∈ Icc (-2) 2 ∧ |F| ≤ K*a
    refine ⟨abs_le.mp φsmall,?_⟩
    have tr := abs_sub_le (τ*F) Y 0
    rw [sub_zero,sub_zero,abs_sub_comm (τ*F),abs_mul,abs_of_pos τpos] at tr
    apply le_of_mul_le_mul_left (a := τ) _ τpos
    calc
      _ ≤ 2*de*a+(sc+2*Q+rc)*a := tr.trans (add_le_add err del)
      _ = _ := by dsimp only [K,targetConstant,sc,rc,de]; field_simp [τpos.ne']; ring
  have measureφ : volume (φ ⁻¹' S) = ENNReal.ofReal u * volume S := by
    change volume ((fun y : ℝ ↦ y+(-x)) ⁻¹' ((u⁻¹ * ·) ⁻¹' S)) = _
    rw [measure_preimage_add_right,Real.volume_preimage_mul_left (inv_ne_zero up.ne'),inv_inv,abs_of_pos up]
  exact (measure_mono sub).trans (measureφ.le.trans (mul_le_mul_right (test x hx) _))


end Weierstrass.Reciprocal
