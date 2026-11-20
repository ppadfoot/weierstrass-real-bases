module

public import Weierstrass.PredecessorProof

/-! Actual phase-uniform slope information, stated at arbitrary positive radii. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

def slopeHeavy {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g : ℝ) (η : ℕ → ℝ) (R τ : ℝ) : ℝ≥0∞ :=
  ((volume : Measure (Fin d → UnitAddCircle)).prod unitLaw) {z |
    let y := codedSlope d (fun i => (a i:ℝ)) p g (centralLift z.1) η (uniformCode p hp z.2)
    ENNReal.ofReal τ < baseSlopeLaw hp d a (centralLift z.1) η g (Icc (y-R) (y+R))}

def SlopeInformation {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g s : ℝ) : Prop :=
  ∀ h : ℝ, 0<h → h<s → ∀ A : ℝ, 0<A → ∀ ε : ℝ, 0<ε → ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ η, slopeHeavy hp d a g η (A*r) (r^h) ≤ ENNReal.ofReal ε

theorem slopeHeavy_mono {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g : ℝ) (η : ℕ → ℝ)
    {R S τ θ : ℝ} (hr : R≤S) (ht : θ≤τ) :
    slopeHeavy hp d a g η R τ ≤ slopeHeavy hp d a g η S θ := by
  apply measure_mono;intro z hz
  exact ((ENNReal.ofReal_le_ofReal ht).trans_lt hz).trans_le (measure_mono (Set.Icc_subset_Icc (sub_le_sub_left hr _) (add_le_add_right hr _)))

/-- Each tolerance may use its own fixed geometric progression, with a uniform
bound in the arbitrary input string. The radius constant may depend on this progression. -/
theorem slopeInformation_from_mesh {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {g s : ℝ}
    (H : ∀ h : ℝ, 0<h → h<s → ∀ ε : ℝ, 0<ε → ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ A : ℝ, 0<A →
        ∀ᶠ k : ℕ in atTop, ∀ η, slopeHeavy hp d a g η (A*q^k) ((q^k:ℝ)^h) ≤ ENNReal.ofReal ε) :
    SlopeInformation hp d a g s := by
  intro h hh hs A hA ε hε
  obtain ⟨q,hq,hq1,mesh⟩ := H h hh hs ε hε
  obtain ⟨N,good⟩ := eventually_atTop.mp (mesh (A/q) (div_pos hA hq))
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (pow_pos hq N)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (rp : 0<r) small r1
  obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one rp r1.le hq hq1
  have kn : N ≤ k+1 := by
    by_contra! w
    exact (small.trans_le (pow_le_pow_of_le_one hq.le hq1.le w.le)).asymm lo
  intro η
  apply (slopeHeavy_mono hp d a g η _ (Real.rpow_le_rpow (pow_pos hq _).le lo.le hh.le)).trans (good _ kn η)
  rw [pow_succ,show A/q*(q^k*q)=A*q^k by field_simp]
  exact mul_le_mul_of_nonneg_left up hA.le

/-- Phase-uniform sharp initialization of the induction at every sufficiently
high index, now at every real radius with the exact entropy exponent. -/
theorem slopeInformation_initial {p d : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0 < c) (hc' : c < 1) (hγ : 0 < γ) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) :
    ∀ᶠ j : ℕ in atTop, SlopeInformation (by omega : 0<p) (d+1) a (γ*c^j) (min 1 (Real.log p/Real.log (1/(γ*c^j)))) := by
  have jt : Tendsto (fun j : ℕ => γ*c^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc').const_mul γ
  filter_upwards [haar_sharp_initial_information hp a ha hc hc' hγ hbc hpoly,jt.eventually_lt_const zero_lt_one] with j hj small
  let g := γ*c^j
  have gp : 0<g := mul_pos hγ (pow_pos hc j)
  have pp : 1 < (p:ℝ) := by exact_mod_cast (show 1<p by omega)
  apply slopeInformation_from_mesh
  intro h hh hr ε hε
  refine ⟨g,gp,small,?_⟩
  intro A hA
  obtain ⟨K,hK,bd⟩ := hj A hA
  let v := (p:ℝ)⁻¹*(g⁻¹)^h
  have vpos : 0<v := mul_pos (inv_pos.mpr (zero_lt_one.trans pp)) (Real.rpow_pos_of_pos (inv_pos.mpr gp) _)
  have v1 : v < 1 := PrefixEnergy.ratio_lt_one pp gp small (by simpa only [one_div] using hr.trans_le (min_le_right _ _))
  have lim : Tendsto (fun k : ℕ ↦ K*v^k) atTop (𝓝 0) := by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one vpos.le v1).const_mul K
  filter_upwards [bd,lim.eventually_lt_const hε] with k hbk hsmall
  intro η
  apply (hbk η ((g^k:ℝ)^h) (Real.rpow_pos_of_pos (pow_pos gp _) _)).trans
  apply ENNReal.ofReal_le_ofReal
  apply le_trans _ hsmall.le
  have scale : (g^k:ℝ)^h = (g^h)^k := by rw [←Real.rpow_natCast_mul gp.le,←Real.rpow_mul_natCast gp.le,mul_comm]
  rw [scale,show v = (p:ℝ)⁻¹/(g^h) by dsimp only [v];rw [Real.inv_rpow gp.le,div_eq_mul_inv],div_pow]
  ring_nf;exact le_rfl

end Weierstrass.Predecessor
