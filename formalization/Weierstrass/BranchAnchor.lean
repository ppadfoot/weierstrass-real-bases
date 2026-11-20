module

public import Weierstrass.BranchGridMoment
public import Weierstrass.BranchGridLoss
public import Weierstrass.BranchMarkov

/-! The predecessor branch of the lower bound on the actual phase group. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped ENNReal Topology BigOperators
namespace Weierstrass.Branch

theorem anchored_of_slopeInformation {b l s : ℝ} (hb : 1<b) (hl : b⁻¹<l) (hl1 : l<1)
    (E : PrimitiveEquation b) (s1 : s≤1) (info : SlopeInformation (positive_digits E) (E.d+1) E.a (b*l)⁻¹ s) :
    AnchoredEstimate b l s := by
  have bp := zero_lt_one.trans hb
  have lp := (inv_pos.mpr bp).trans hl
  let γ := (b*l)⁻¹
  let c := b⁻¹
  have gp : 0<γ := inv_pos.mpr (mul_pos bp lp)
  have g1 : γ<1 := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' bp).mp hl)
  have cp : 0<c := inv_pos.mpr bp
  have c1 : c<1 := inv_lt_one_of_one_lt₀ hb
  apply anchored_of_geometric
  intro h hh hs T hT ε hε
  obtain ⟨G⟩ := grid_exists gp g1 cp c1 hh hs s1
  refine ⟨G.q,G.q_pos,G.q_lt_one,?_⟩
  intro A hA
  let D := prefixRadius γ T A
  let depth (i : Fin G.K) (j : Fin G.L) := G.depth i j
  let step (i : Fin G.K) (j : Fin G.L) := G.step i j
  let C := 2*T*((G.K:ℝ)+1)
  have half : 0<ε/2 := half_pos hε
  have σp := (hh.trans G.h_lt).trans G.e_lt
  have discard := gridGood_loss (positive_digits E) E.a E.leading gp g1 info σp G.σ_lt c D half depth step
    (fun i j ↦ G.growth i i.isLt j j.isLt)
  have exp : 0<G.e-h := sub_pos.mpr G.h_lt
  have lim : Tendsto (fun m : ℕ ↦ C*((G.q^m:ℝ)^(G.e-h))) atTop (𝓝 0) := by
    have small := tendsto_pow_atTop_nhds_zero_of_lt_one G.q_pos.le G.q_lt_one
    have rpow := Real.continuous_rpow_const exp.le
    simpa only [Real.zero_rpow exp.ne',mul_zero,Function.comp_apply] using tendsto_const_nhds (x:=C) |>.mul ((rpow.tendsto 0).comp small)
  filter_upwards [discard,lim.eventually_lt_const half] with m msmall mdecay
  intro ω
  let r := G.q^m
  let U := {z : PhaseTorus | ENNReal.ofReal (r^h) < occupation b l T A r z}
  have mU : MeasurableSet U := measurableSet_lt measurable_const (measurable_occupation b l T A r)
  apply bounded_haar_shift bp.ne' E mU _ ω
  intro z
  let Good := gridGood (positive_digits E) (E.d+1) E.a γ c D G.σ (angularTail z) depth step m
  have mGood : MeasurableSet Good := measurableSet_gridGood .. 
  have moment := grid_retained_moment hb hl hl1 E G z hT hA m Good mGood (by
    intro v hv i hi j hj;exact hv ⟨i,hi⟩ ⟨j,hj⟩)
  have mO := (measurable_occupation b l T A r).comp (measurable_aux_phase bp.ne' E z)
  apply (retained_occupation_markov (centerAndSeed (E.d+1)) mGood mO (msmall (angularTail z)) (pow_pos G.q_pos m) (h:=h) moment).trans
  have second : C*r^(G.e-h) ≤ ε/2 := mdecay.le
  exact (add_le_add_right (ENNReal.ofReal_le_ofReal second) _).trans_eq (by rw [←ENNReal.ofReal_add half.le half.le,add_halves])

theorem predecessor_anchored {b l : ℝ} (hb : 1<b) (hl : b⁻¹<l) (hl1 : l<1) (E : PrimitiveEquation b) (digits : 2≤E.p) :
    AnchoredEstimate b l (slopeExponent E.p (b*l)⁻¹) := by
  have bp := zero_lt_one.trans hb
  have gp := inv_pos.mpr (mul_pos bp ((inv_pos.mpr bp).trans hl))
  have g1 := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' bp).mp hl)
  apply anchored_of_slopeInformation hb hl hl1 E (min_le_left ..)
  simpa only [pow_zero,mul_one,slopeExponent] using slopeInformation_all digits E.a E.leading (inv_pos.mpr bp)
    (inv_lt_one_of_one_lt₀ hb) gp g1 (mul_inv_cancel₀ bp.ne') E.polynomial_relation 0

theorem branching_anchored {b l : ℝ} (hb : 1<b) (hl : b⁻¹<l) (hl1 : l<1) (E : PrimitiveEquation b) (digits : 2≤E.p)
    (room : b*l ≤ E.p) : AnchoredEstimate b l 1 := by
  have bp := zero_lt_one.trans hb
  have big := (inv_lt_iff_one_lt_mul₀' bp).mp hl
  have eq : slopeExponent E.p (b*l)⁻¹ = 1 := by
    unfold slopeExponent
    rw [one_div,inv_inv,min_eq_left]
    apply (one_le_div (Real.log_pos big)).mpr
    exact Real.log_le_log (zero_lt_one.trans big) room
  exact eq ▸ predecessor_anchored hb hl hl1 E digits

end Weierstrass.Branch
