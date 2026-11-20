module

public import Weierstrass.StripRates
public import Weierstrass.StripEstimate

/-! Simultaneous physical and dual strip meshes on every sufficiently fine grid. -/
@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace Weierstrass.StripProof

def stripWidth (b g K : ℝ) (m : ℕ) := K*(b⁻¹/(b*g)⁻¹)^m

theorem stripWidth_eq {b : ℝ} (hb : 0 < b) (g K : ℝ) (m : ℕ) : stripWidth b g K m = K*g^m := by
  unfold stripWidth;rw [div_inv_eq_mul,inv_mul_cancel_left₀ hb.ne']

theorem stripWidth_limits {b g K : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hK : 0 < K) :
    Tendsto (stripWidth b g K) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr;constructor
  · change Tendsto (fun m : ℕ ↦ stripWidth b g K m) _ _
    simpa only [stripWidth_eq hb,mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg1).const_mul K
  · exact Eventually.of_forall (fun n ↦ by simpa only [stripWidth_eq hb,Set.mem_Ioi] using mul_pos hK (pow_pos hg n))

theorem stripWidth_radius {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (K : ℝ) (m : ℕ) :
    ((b*g)⁻¹)^m*stripWidth b g K m = K*(b⁻¹)^m := by
  rw [stripWidth,div_pow];field_simp

private theorem posPowerLimit {a : ℕ → ℝ} (h : Tendsto a atTop (𝓝[>] 0)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n ↦ (a n)^s) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff] at h ⊢
  refine ⟨?_,h.2.mono (fun n hn ↦ Real.rpow_pos_of_pos hn s)⟩
  simpa only [Function.comp_def,Real.zero_rpow hs.ne'] using
    ((Real.continuousAt_rpow_const 0 s (.inr hs.le)).tendsto.comp h.1)

def stripMeshIndex (b g l : ℝ) : ℕ := open Classical in
  if c : ∃ n : ℕ, l ≤ (b^n)⁻¹ ∧ (b^n)⁻¹ ≤ b*l ∧ ∀ {Δ s : ℝ}, 0 < Δ → 0 ≤ s →
    Δ*l/g^n ≤ Δ*l^(1-alpha b g) ∧ (b^n)⁻¹*(Δ*l/g^n)^s ≤ b*Δ^s*l^(1+(1-alpha b g)*s)
  then c.choose else 0

private theorem meshIndex_spec {b g l : ℝ} (hb : 1 < b) (hg : b⁻¹ < g) (hg1 : g < 1)
    (hl : 0 < l) (hl1 : l ≤ 1) :
    l ≤ (b^stripMeshIndex b g l)⁻¹ ∧ (b^stripMeshIndex b g l)⁻¹ ≤ b*l ∧ ∀ {Δ s : ℝ}, 0 < Δ → 0 ≤ s →
    Δ*l/g^(stripMeshIndex b g l) ≤ Δ*l^(1-alpha b g) ∧
    (b^(stripMeshIndex b g l))⁻¹*(Δ*l/g^(stripMeshIndex b g l))^s ≤ b*Δ^s*l^(1+(1-alpha b g)*s) := by
  unfold stripMeshIndex;rw [dif_pos (strip_physical_scale hb hg hg1 hl hl1)]
  exact (strip_physical_scale hb hg hg1 hl hl1).choose_spec

theorem width_mesh_tendsto {b g K : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hK : 0 < K)
    {J : ℕ} (hJ : 0 < J) (j : ℕ) :
    Tendsto (fun m ↦ paperMesh (stripWidth b g K m) J (j+1)) atTop (𝓝[>] 0) := by
  apply posPowerLimit (stripWidth_limits hb hg hg1 hK)
  exact div_pos (by exact_mod_cast Nat.succ_pos j) (by exact_mod_cast hJ)

theorem width_mesh_bounds {b g K s : ℝ} (hb : 1 < b) (hg : b⁻¹ < g) (hg1 : g < 1) (hK : 1 ≤ K)
    (hs : 0 ≤ s) {J : ℕ} (hJ : 0 < J) : ∀ᶠ m : ℕ in atTop,
    let d := stripWidth b g K m
    let Δ := ((b*g)⁻¹)^m
    0 < d ∧ d ≤ 1 ∧ ∀ j < J, let l := paperMesh d J (j+1); let n := stripMeshIndex b g l
      (b⁻¹/(b*g)⁻¹)^m ≤ l ∧ l ≤ (b^n)⁻¹ ∧
      (b^n)⁻¹*(Δ*l/g^n)^s ≤ (b*Δ^s)*l^(1+(1-alpha b g)*s) ∧ Δ*l/g^n ≤ Δ := by
  have bp := zero_lt_one.trans hb
  have gp := (inv_pos.mpr bp).trans hg
  have kp := zero_lt_one.trans_le hK
  have jd : 0 < (J:ℝ) := by exact_mod_cast hJ
  have lim := tendsto_nhdsWithin_iff.mp (stripWidth_limits bp gp hg1 kp)
  filter_upwards [lim.1.eventually_lt_const (show (0:ℝ)<1 by norm_num),lim.2] with m small pos
  refine ⟨pos,small.le,?_⟩;intro j hj
  let d := stripWidth b g K m
  let l := paperMesh d J (j+1)
  have e : 0 ≤ ((j+1:ℕ):ℝ)/J := by positivity
  have e1 : ((j+1:ℕ):ℝ)/J ≤ 1 := (div_le_one jd).mpr (by exact_mod_cast hj)
  have lp : 0 < l := Real.rpow_pos_of_pos pos _
  have lu : l ≤ 1 := Real.rpow_le_one pos.le small.le e
  have dl : d ≤ l := (Real.rpow_one d) ▸ Real.rpow_le_rpow_of_exponent_ge pos small.le e1
  have rate := meshIndex_spec hb hg hg1 lp lu
  have dp := pow_pos (inv_pos.mpr (mul_pos bp gp)) m
  have hbase : 0 ≤ (b⁻¹/(b*g)⁻¹)^m := by positivity
  refine ⟨(le_mul_of_one_le_left hbase hK).trans dl,rate.1,(rate.2.2 dp hs).2,?_⟩
  exact (rate.2.2 dp hs).1.trans (mul_le_of_le_one_right dp.le
    (Real.rpow_le_one lp.le lu (sub_nonneg.mpr (alpha_mem_Ioo hb hg hg1).2.le)))

theorem width_physical_tendsto {b g K : ℝ} (hb : 1 < b) (hg : b⁻¹ < g) (hg1 : g < 1) (hK : 1 ≤ K)
    {J j : ℕ} (hj : j < J) : Tendsto (fun m : ℕ ↦ let l := paperMesh (stripWidth b g K m) J (j+1)
      ((b*g)⁻¹)^m*l/g^(stripMeshIndex b g l)) atTop (𝓝[>] 0) := by
  have bp := zero_lt_one.trans hb
  have gp := (inv_pos.mpr bp).trans hg
  have bg : 1 < b*g := by simpa only [mul_inv_cancel₀ bp.ne'] using mul_lt_mul_of_pos_left hg bp
  have pos (m : ℕ) : 0 < (let l := paperMesh (stripWidth b g K m) J (j+1); ((b*g)⁻¹)^m*l/g^(stripMeshIndex b g l)) := by
    have dpos : 0 < stripWidth b g K m := by rw [stripWidth_eq bp];positivity
    apply div_pos (mul_pos (pow_pos (inv_pos.mpr (mul_pos bp gp)) _) (Real.rpow_pos_of_pos dpos _)) (pow_pos gp _)
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall pos⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ (pos n).le) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (mul_pos bp gp).le) (inv_lt_one_of_one_lt₀ bg))
  filter_upwards [width_mesh_bounds hb hg hg1 hK (s:=0) le_rfl (Nat.zero_lt_of_lt hj)] with m hm
  exact (hm.2.2 j hj).2.2.2

theorem strip_cost_tendsto {b g K s p u : ℝ} (hb : 1 < b) (hg : 0 < g) (hK : 0 < K)
    (hu : u < (1-alpha b g)*s + (1-(1-alpha b g))*p) :
    Tendsto (fun m : ℕ ↦ (((b*g)⁻¹)^m)^s*(stripWidth b g K m)^p / ((b⁻¹^m:ℝ)^u)) atTop (𝓝 0) := by
  have bp := zero_lt_one.trans hb
  let β := 1-alpha b g
  let w := β*s+(1-β)*p
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr bp.le) (inv_lt_one_of_one_lt₀ hb)
  have rp (m : ℕ) := pow_pos (inv_pos.mpr bp) m
  have eq (m : ℕ) : ((b*g)⁻¹)^m=(b⁻¹^m:ℝ)^β := by simpa only [β,inv_pow] using dual_as_width hb hg m
  have ep : 0 < w-u := sub_pos.mpr hu
  have L := (Real.continuousAt_rpow_const 0 (w-u) (.inr ep.le)).tendsto.comp lim
  rw [Real.zero_rpow ep.ne'] at L
  have LK := L.const_mul (K^p)
  rw [mul_zero] at LK
  apply LK.congr'
  filter_upwards with m
  have wid : stripWidth b g K m = K*(b⁻¹)^m/((b⁻¹)^m)^β := by
    rw [←eq];unfold stripWidth;rw [div_pow];ring
  rw [wid,eq,strip_final_power (rp m) hK,Function.comp_apply,Real.rpow_sub (rp m)]
  dsimp only [w];ring

end Weierstrass.StripProof
