module

public import Weierstrass.SlopeDescent

/-! Polynomial exceptional probabilities for the conditional slope measures. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

def QuantitativeSlopeInformation {p : ℕ} (hp : 0<p) (d : ℕ) (a : ℕ → ℤ) (g s : ℝ) : Prop :=
  ∀ h : ℝ, 0<h → h<s → ∀ A : ℝ, 0<A → ∃ K β : ℝ, 0<K ∧ 0<β ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ η, slopeHeavy hp d a g η (A*r) (r^h) ≤ ENNReal.ofReal (K*r^β)

theorem pow_rpow_interchange {g : ℝ} (hg : 0≤g) (n : ℕ) (s : ℝ) : (g^n:ℝ)^s = (g^s)^n := by
  rw [←Real.rpow_natCast_mul hg,←Real.rpow_mul_natCast hg,mul_comm]

theorem quantitativeSlope_from_mesh {p d : ℕ} {hp : 0<p} {a : ℕ → ℤ} {g s : ℝ}
    (mesh : ∀ h : ℝ, 0<h → h<s → ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ A : ℝ, 0<A → ∃ K v : ℝ,
      0<K ∧ 0<v ∧ v<1 ∧ ∀ᶠ n : ℕ in atTop, ∀ η, slopeHeavy hp d a g η (A*q^n) ((q^n:ℝ)^h) ≤ ENNReal.ofReal (K*v^n)) :
    QuantitativeSlopeInformation hp d a g s := by
  intro h hh hs A hA
  obtain ⟨q,hq,hq',grid⟩ := mesh h hh hs
  obtain ⟨K,v,hK,hv,hv',good⟩ := grid (A/q) (div_pos hA hq)
  let β := Real.log v/Real.log q
  have bpos : 0<β := div_pos_of_neg_of_neg (Real.log_neg hv hv') (Real.log_neg hq hq')
  have qβ : q^β=v := by
    rw [Real.rpow_def_of_pos hq,show Real.log q*β=Real.log v by dsimp only [β];field_simp [(Real.log_neg hq hq').ne],Real.exp_log hv]
  obtain ⟨N,goodN⟩ := eventually_atTop.mp good
  refine ⟨K,β,hK,bpos,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (pow_pos hq N)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (pr : 0<r) sm sr
  obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one pr sr.le hq hq'
  have kn : N≤k+1 := by by_contra! w;exact (sm.trans_le (pow_le_pow_of_le_one hq.le hq'.le w.le)).asymm lo
  intro η
  apply le_trans _ ((goodN _ kn η).trans (ENNReal.ofReal_le_ofReal _))
  · apply slopeHeavy_mono hp d a g η _ (Real.rpow_le_rpow (pow_pos hq _).le lo.le hh.le)
    rw [pow_succ,show A/q*(q^k*q)=A*q^k by field_simp];exact mul_le_mul_of_nonneg_left up hA.le
  · rw [←qβ,←pow_rpow_interchange hq.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pow_pos hq _).le lo.le bpos.le) hK.le

theorem quantitativeSlope_initial {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, QuantitativeSlopeInformation (by omega : 0<p) (d+1) a (γ*c^j) (slopeExponent p (γ*c^j)) := by
  have jt : Tendsto (fun j : ℕ ↦ γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_sharp_initial_information hp a ha hc hc' hγ hbc hpoly,jt.eventually_lt_const zero_lt_one] with j hj small
  let g := γ*c^j
  have gp := mul_pos hγ (pow_pos hc j)
  have pp : 1<(p:ℝ) := by exact_mod_cast (show 1<p by omega)
  apply quantitativeSlope_from_mesh
  intro h hh hr
  refine ⟨g,gp,small,?_⟩
  intro A hA
  obtain ⟨K,hK,bd⟩ := hj A hA
  let v := (p:ℝ)⁻¹*(g⁻¹)^h
  have vp : 0<v := mul_pos (inv_pos.mpr (zero_lt_one.trans pp)) (Real.rpow_pos_of_pos (inv_pos.mpr gp) _)
  have v1 : v<1 := PrefixEnergy.ratio_lt_one pp gp small (by simpa only [one_div] using hr.trans_le (min_le_right _ _))
  refine ⟨K,v,hK,vp,v1,?_⟩
  filter_upwards [bd] with k B
  intro η
  apply (B η ((g^k:ℝ)^h) (Real.rpow_pos_of_pos (pow_pos gp _) _)).trans_eq
  congr 1
  rw [pow_rpow_interchange gp.le,show v = (p:ℝ)⁻¹/(g^h) by dsimp only [v];rw [Real.inv_rpow gp.le,div_eq_mul_inv],div_pow]
  ring

theorem slopeSliceBound_rate {g c : ℝ} (hg : 0<g) (hc : 0<c) (n : ℕ) :
    slopeSliceBound g c n = slopeSliceBound g c 0 * (((g*c)⁻¹)^2)^n := by
  have hp : g*c≠0 := (mul_pos hg hc).ne'
  have mp : min 1 (2*Real.pi*c)≠0 := (lt_min zero_lt_one (show 0<2*Real.pi*c by positivity)).ne'
  unfold slopeSliceBound
  simp only [pow_zero,mul_one,mul_pow,←pow_mul,inv_pow]
  rw [Nat.mul_comm]
  field_simp

end Weierstrass.Predecessor
