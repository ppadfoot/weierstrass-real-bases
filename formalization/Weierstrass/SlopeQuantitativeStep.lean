module

public import Weierstrass.SlopeQuantitative

/-! Downward induction with quantitative tail probabilities. The number of
blocks is fixed before the block length grows; the radius mesh then has
fixed ratio and the transverse sublevel coefficient grows only exponentially. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

theorem badSlope_exponential {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) {c g s t v : ℝ}
    (hg : 0<g) (hc : 0<c) (h1 : g*c<1) (v0 : 0<v) (vs : v<s) (test : (g*c)^v ≤ g^t)
    (info : QuantitativeSlopeInformation hp d a (g*c) s) :
    ∃ K v : ℝ, 0<K ∧ 0<v ∧ v<1 ∧ ∀ᶠ n : ℕ in atTop, ∀ η,
      statusMass hp d a n g c ((p:ℝ)^n*(g^n:ℝ)^t) [true] η ≤ ENNReal.ofReal (K*v^n) := by
  let h := g*c
  have ph := mul_pos hg hc
  have Apos : 0<4*(1-h)⁻¹+1 := by have := inv_pos.mpr (sub_pos.mpr h1);dsimp only [h];linarith
  have lim : Tendsto (fun n : ℕ ↦ h^n) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one ph.le h1,Eventually.of_forall (fun n ↦ pow_pos ph n)⟩
  obtain ⟨K,β,hK,hβ,bd⟩ := info v v0 vs _ Apos
  refine ⟨K,h^β,hK,Real.rpow_pos_of_pos ph _, Real.rpow_lt_one ph.le h1 hβ,?_⟩
  filter_upwards [lim.eventually bd] with n valid
  intro η
  have pp : 0<(p:ℝ) := by exact_mod_cast hp
  have pp' := pow_pos pp n
  have th : (h^n:ℝ)^v ≤ ((p:ℝ)^n*(g^n:ℝ)^t)*(p:ℝ)⁻¹^n := by
    rw [pow_rpow_interchange ph.le,pow_rpow_interchange hg.le,inv_pow,
      show (p:ℝ)^n*(g^t)^n*((p:ℝ)^n)⁻¹ = (g^t)^n by field_simp]
    exact pow_le_pow_left₀ (Real.rpow_nonneg ph.le _) test _
  apply (statusMass_bad_le_derivative hp d a n g c _ ph.le h1 (by positivity) η).trans
  apply (slopeHeavy_mono hp d a h _ le_rfl th).trans
  rw [←pow_rpow_interchange (show 0≤h from ph.le) n β]
  exact valid (fun k => η k+Real.pi/2)

theorem fixed_blocks_budget {g H e : ℝ} (hg : 0<g) (hg' : g<1) (_hH : 0<H) (he : 0<e) :
    ∃ k : ℕ, 0<k ∧ 2*H*(g^e)^k<1 := by
  have zero := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hg.le e) (Real.rpow_lt_one hg.le hg' he)
  have lim : Tendsto (fun k : ℕ ↦ 2*H*(g^e)^k) atTop (𝓝 0) := by simpa using zero.const_mul (2*H)
  exact ((eventually_gt_atTop 0).and (lim.eventually_lt_const zero_lt_one)).exists

theorem quantitativeSlope_step {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0)
    (info : QuantitativeSlopeInformation (by omega : 0<p) (d+1) a (g*c) (slopeExponent p (g*c))) :
    QuantitativeSlopeInformation (by omega : 0<p) (d+1) a g (slopeExponent p g) := by
  have hp' : 0<p := by omega
  apply quantitativeSlope_from_mesh
  intro σ hs hem
  obtain ⟨t,st,te⟩ := exists_between hem
  have tp := hs.trans st
  have t1 := te.trans_le (min_le_left _ _)
  obtain ⟨v,vp,ve,hv⟩ := choose_slope_transfer (by exact_mod_cast (show 1<p by omega)) hg hg' hc hc' tp te
  let δ := (t-σ)/(2*t)
  have dp : 0<δ := div_pos (sub_pos.mpr st) (by positivity)
  let e := t*(1-δ)-σ
  have ep : 0<e := by
    have dd : (2*t)*δ=t-σ := by dsimp [δ];field_simp
    dsimp [e];nlinarith only [dd,st]
  have h1 := (mul_lt_of_lt_one_right hg hc').trans hg'
  obtain ⟨K,v',hK,v'p,v'1,bad⟩ := badSlope_exponential hp' a hg hc h1 vp ve hv info
  let H := ((g*c)⁻¹)^2
  have H1 : 1≤H := by have inv := (one_lt_inv₀ (mul_pos hg hc)).mpr h1;unfold H;nlinarith
  have Hp := zero_lt_one.trans_le H1
  obtain ⟨k,kp,room⟩ := fixed_blocks_budget hg hg' Hp ep
  let tail := 2*H*(g^e)^k
  have tailp : 0<tail := mul_pos (by positivity) (pow_pos (Real.rpow_pos_of_pos hg _) _)
  let V := max v' (max (1/2:ℝ) tail)
  have vV := le_max_left v' (max (1/2:ℝ) tail)
  have halfV := (le_max_left (1/2:ℝ) tail).trans (le_max_right v' _)
  have tailV := (le_max_right (1/2:ℝ) tail).trans (le_max_right v' _)
  refine ⟨g^k,pow_pos hg _,pow_lt_one₀ hg.le hg' kp.ne',?_⟩
  intro A hA
  let S := slopeSliceBound g c 0
  have Sp : 0<S := slopeSliceBound_pos hg hg' hc 0
  let B := 3*(1+S*A)
  have Bp : 0<B := by dsimp only [B];positivity
  let C := B*(k+1:ℝ)*12^k
  have Cp : 0<C := by dsimp only [C];positivity
  refine ⟨K/δ+3+C,V,by positivity,v'p.trans_le vV,max_lt v'1 (max_lt (by norm_num) room),?_⟩
  filter_upwards [bad,eventually_gt_atTop (0:ℕ)] with n bn np
  have K2 : (1:ℝ)<2^n := one_lt_pow₀ (by norm_num) np.ne'
  obtain ⟨D,hD,hEq,bound⟩ := slopeHeavy_mesh_rate hp' a ha hg hg' hc hc' hbc hpoly n tp.le t1.le dp hA
    K2 (mul_nonneg hK.le (pow_nonneg v'p.le n)) bn
  intro η
  have gn : (g^k)^n=(g^n)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [gn]
  apply (bound k σ η).trans (ENNReal.ofReal_le_ofReal _)
  have Hn := one_le_pow₀ H1 (n:=n)
  have Dbd : D ≤ B*H^n := by
    rw [hEq,slopeSliceBound_rate hg hc]
    change 3*max 1 (S*H^n*A) ≤ B*H^n
    calc
      _ ≤ 3*(H^n+S*H^n*A) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply max_le (Hn.trans (le_add_of_nonneg_right (by positivity))) (le_add_of_nonneg_left (by positivity))
      _ = _ := by dsimp only [B];ring
  have Kbd : K*v'^n/δ ≤ (K/δ)*V^n := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ v'p.le vV _) (div_nonneg hK.le dp.le)
  have Mbd : (3:ℝ)/2^n ≤ 3*V^n := by
    rw [div_eq_mul_inv,←inv_pow]
    simpa only [V,one_div] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) halfV n) (by norm_num : (0:ℝ)≤3)
  have eb : (g^n:ℝ)^e=(g^e)^n := pow_rpow_interchange hg.le n e
  have far : (2:ℝ)^n*D*(k+1:ℝ)*(12*(g^n:ℝ)^e)^k ≤ C*V^n := by
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Dbd (by positivity)) (by positivity)) (by positivity)) _
    calc
      _ = C*tail^n := by
        rw [eb];dsimp only [C,tail]
        simp only [mul_pow,←pow_mul]
        rw [Nat.mul_comm n k];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ tailp.le tailV n) Cp.le
  change K*v'^n/δ+3/2^n+2^n*D*(k+1:ℝ)*(12*(g^n:ℝ)^e)^k ≤ (K/δ+3+C)*V^n
  rw [add_mul,add_mul]
  exact add_le_add (add_le_add Kbd Mbd) far

end Weierstrass.Predecessor
