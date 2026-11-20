module

public import Weierstrass.DescentHeavy
public import Weierstrass.DescentReanchor
public import Weierstrass.PairGraph

/-! The physical transverse differentiation estimate of §6 for arbitrary deterministic
angular weights, including the passage from finite meshes to all positive radii. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Real Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal Topology
namespace Weierstrass.Descent
open Angular
local instance theoremGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance theoremGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem sampled_of_mesh {B : ℂ} {g s : ℝ} {P : Set RayParameters}
    (H : ∀ σ : ℝ, 0<σ → σ<s → ∀ ε : ℝ, 0<ε → ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ A : ℝ, 0<A →
      ∀ᶠ k : ℕ in atTop, ∀ ω : PhaseTorus, ∀ p ∈ P,
        heavy B g 3 p ω (A*q^k) ((q^k:ℝ)^σ) ≤ ENNReal.ofReal ε) : SampledInformation B g s P := by
  intro h hh hs A ε hA hε
  obtain ⟨q,hq,hq1,mesh⟩ := H h hh hs ε hε
  obtain ⟨N,good⟩ := eventually_atTop.mp (mesh (A/q) (div_pos hA hq))
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (pow_pos hq N)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r (rp : 0<r) small r1
  obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one rp r1.le hq hq1
  have kn : N ≤ k+1 := by
    by_contra! w
    exact (small.trans_le (pow_le_pow_of_le_one hq.le hq1.le w.le)).asymm lo
  intro ω p hp
  simp only [Real.closedBall_eq_Icc]
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  change heavy B g 3 p ω (A*r) (r^h) ≤ _
  apply (heavy_mono B g 3 p ω _ (Real.rpow_le_rpow (pow_pos hq _).le lo.le hh.le)).trans (good _ kn ω p hp)
  rw [pow_succ,show A/q*(q^k*q)=A*q^k by field_simp]
  exact mul_le_mul_of_nonneg_left up hA.le

theorem choose_derivative_exponent {g ρ s t : ℝ} (hg : 0<g) (hg1 : g<1)
    (hr : 0<ρ) (hr1 : ρ<1) (ht : 0<t) (h : t < log (g*ρ)*s/log g) :
    ∃ v : ℝ, 0<v ∧ v<s ∧ (g*ρ)^v ≤ g^t := by
  have G := log_neg hg hg1
  have hp := mul_pos hg hr
  have F := log_neg hp ((mul_lt_of_lt_one_right hg hr1).trans hg1)
  have room : (t*log g)/log (g*ρ) < s := by
    apply (div_lt_iff_of_neg F).mpr
    linarith only [(lt_div_iff_of_neg G).mp h]
  obtain ⟨v,lo,hi⟩ := exists_between room
  refine ⟨v,(div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht G) F).trans lo,hi,?_⟩
  apply (log_le_log_iff (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hg _)).mp
  rw [log_rpow hp,log_rpow hg]
  linarith only [(div_lt_iff_of_neg F).mp lo]

theorem all_differentiation_rules : ConjugatePair.AllDifferentiationRules := by
  intro B ζ v₀ ρ e g s hb hg hg1 hr hr1 hh _hs _hs1 he orbit k info
  have bp := zero_lt_one.trans hb
  have hbg := hh.trans (mul_lt_mul_of_pos_left (mul_lt_of_lt_one_right hg hr1) bp)
  apply rayInformation_of_sampled hb hg hg1 hbg
  apply sampled_of_mesh
  intro σ hσ gap ε hε
  obtain ⟨t,st,te⟩ := exists_between gap
  have tp := hσ.trans st
  have t1 := te.trans_le (min_le_left _ _)
  obtain ⟨v,vp,ve,test⟩ := choose_derivative_exponent hg hg1 hr hr1 tp (te.trans_le (min_le_right _ _))
  obtain ⟨δ,M,err,dp,_,M1,ep,budget⟩ := Predecessor.finite_mesh_information_budget hg hg1 hσ st hε
  have small := badShare_small bp hg hg1 hr hr1 hh vp ve info ep
  have mesh : ∀ᶠ n : ℕ in atTop, 2 ≤ ‖B‖^n := (tendsto_pow_atTop_atTop_of_one_lt hb).eventually_ge_atTop 2
  obtain ⟨n,bn,sn,pn,hn⟩ := (budget.and (small.and ((eventually_ge_atTop 1).and mesh))).exists
  let q := g^n
  have qp := pow_pos hg n
  refine ⟨q,qp,pow_lt_one₀ hg.le hg1 (by omega),?_⟩
  have W (p : RayParameters) (hp : p ∈ physicalFamily B ζ v₀ k) :
      (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ shiftedParameters p n ∈ physicalFamily B ζ v₀ k :=
    ⟨hp.1.1.bounded,hp.1.2.bounded,shiftedParameters_mem (norm_pos_iff.mp bp) hp _⟩
  have ptest : ((g*ρ)^n:ℝ)^v ≤ q^t := by
    have eq (x : ℝ) (px : 0<x) (v : ℝ) : (x^n:ℝ)^v=(x^v)^n := by
      rw [←Real.rpow_natCast_mul px.le,←Real.rpow_mul_natCast px.le,mul_comm]
    dsimp only [q];rw [eq _ (mul_pos hg hr),eq _ hg]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (mul_pos hg hr).le _) test _
  have bad (p : RayParameters) (hp : p ∈ physicalFamily B ζ v₀ k) {T : ℝ} (T1 : 1 ≤ T) (T3 : T ≤ 3) (ω : PhaseTorus) :=
    sn ω p e hp.1.1.bounded hp.1.2.bounded he.bounded ⟨⟨hp.1.1.mul he,hp.1.2⟩,hp.2⟩ T1 T3
      (arity_pos ‖B‖ T n) (mesh_inherits hn T1).2 ptest
  intro A hA
  obtain ⟨C,hC,H⟩ := physical_heavy_mesh bp hg hg1 hr hr1 hh n hn he.bounded orbit W hA tp.le t1.le dp M1 ep.le bad
  filter_upwards [bn C hC] with i ok
  intro ω p hp
  exact (H i σ (T:=3) (by norm_num) le_rfl hp ω).trans (ENNReal.ofReal_le_ofReal ok)

end Weierstrass.Descent

namespace Weierstrass.ConjugatePair
open Angular

/-- Proposition 6.2 on every finite level of the permitted weighted family.
The two permitted transverse directions are chosen in the same angular family. -/
theorem contracting_family {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) (hb : 1<‖σ a‖)
    (c0 : 0<‖τ a‖) (c1 : ‖τ a‖<1) {ζ v : Circle} (base : AdmissibleBase ζ v) (w w' : ℂ)
    (ew : Weight ζ v 1 (rayProjection (τ a) w)) (ew' : Weight ζ v 1 (rayProjection (σ a)⁻¹ w'))
    {g : ℝ} (hg : ‖σ a‖⁻¹<g) (hg1 : g<1) : FamilyBound (σ a) ζ v g 1 := by
  by_cases h : -log ‖τ a‖=log ‖σ a‖
  · have eq : ‖τ a‖=‖σ a‖⁻¹ := by
      apply log_injOn_pos c0 (inv_pos.mpr (zero_lt_one.trans hb))
      rw [log_inv,←h,neg_neg]
    exact (equal σ τ a hb eq base w w' ew ew' hg hg1).1
  · exact any_unequal σ τ a hb c0 c1 h base w w' ew ew' hg hg1 Descent.all_differentiation_rules

end Weierstrass.ConjugatePair

namespace Weierstrass
/-- Every contracting conjugate, including nonreal images, at every admissible
amplitude and for every fixed phase sequence. -/
theorem graph_and_measure_contracting_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K)
    {b g : ℝ} (hσ : σ a=(b:ℂ)) (hb : 1<b) (c0 : 0<‖τ a‖) (c1 : ‖τ a‖<1)
    (hg : b⁻¹ < g) (hg1 : g<1) (phase : ℕ → ℝ) (I : Set ℝ) (hI : I.OrdConnected) (hi : (interior I).Nonempty) :
    dimH (graph b g phase I) = ENNReal.ofReal (2-alpha b g) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b g phase I) (2-alpha b g)) :=
  graph_of_anchored_estimate hb hg hg1
    (anchored_of_contracting_conjugate σ τ a hσ hb c0 c1 hg hg1 Descent.all_differentiation_rules) phase I hI hi
end Weierstrass
