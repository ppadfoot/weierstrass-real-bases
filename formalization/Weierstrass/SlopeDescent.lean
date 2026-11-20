module

public import Weierstrass.SlopeLimits

/-! Sharp information at every derivative index of the polynomial predecessor
process, uniformly in all phase strings on all real radii. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.Predecessor

def slopeExponent (p : ℕ) (g : ℝ) := min 1 (Real.log p/Real.log (1/g))

theorem choose_slope_transfer {p : ℕ} (_hp : 1<(p:ℝ)) {c g t : ℝ} (hg : 0<g) (hg' : g<1)
    (hc : 0<c) (hc' : c<1) (ht : 0<t) (hr : t<slopeExponent p g) :
    ∃ v : ℝ, 0<v ∧ v<slopeExponent p (g*c) ∧ (g*c)^v ≤ g^t := by
  let L := Real.log (1/g)
  let M := Real.log (1/(g*c))
  have Lp : 0<L := Real.log_pos (by rw [one_div];exact (one_lt_inv₀ hg).mpr hg')
  have h := mul_pos hg hc
  have hl : g*c < g := mul_lt_of_lt_one_right hg hc'
  have LM : L<M := Real.log_lt_log (one_div_pos.mpr hg) ((one_div_lt_one_div_of_lt h hl))
  have Mp := Lp.trans LM
  have t1 : t<1 := hr.trans_le (min_le_left _ _)
  have tl : t*L < Real.log p := (lt_div_iff₀ Lp).mp (hr.trans_le (min_le_right _ _))
  have vroom : t*L/M < slopeExponent p (g*c) := lt_min
    ((div_lt_one Mp).mpr ((mul_lt_of_lt_one_left Lp t1).trans LM))
    ((div_lt_div_iff_of_pos_right Mp).mpr tl)
  obtain ⟨v,v0,v1⟩ := exists_between vroom
  refine ⟨v,(div_pos (mul_pos ht Lp) Mp).trans v0,v1,?_⟩
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos h _) (Real.rpow_pos_of_pos hg _)).mp
  rw [Real.log_rpow h,Real.log_rpow hg]
  have ee := (div_lt_iff₀ Mp).mp v0
  simp only [M,L,one_div,Real.log_inv] at ee
  linarith only [ee]

theorem slopeInformation_step {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0)
    (info : SlopeInformation (by omega : 0<p) (d+1) a (g*c) (slopeExponent p (g*c))) :
    SlopeInformation (by omega : 0<p) (d+1) a g (slopeExponent p g) := by
  have hp' : 0<p := by omega
  apply slopeInformation_from_mesh
  intro σ hs hem ε hε
  obtain ⟨t,st,te⟩ := exists_between hem
  have tp := hs.trans st
  have t1 := te.trans_le (min_le_left _ _)
  obtain ⟨v,vp,ve,hv⟩ := choose_slope_transfer (by exact_mod_cast (show 1<p by omega)) hg hg' hc hc' tp te
  obtain ⟨δ,K,e,hδ,_,hK,he,budget⟩ := finite_mesh_information_budget hg hg' hs st hε
  have h1 := (mul_lt_of_lt_one_right hg hc').trans hg'
  have bad := badSlope_eventually hp' a hg hc h1 vp ve hv info he
  obtain ⟨n,bn,badn,np⟩ := (budget.and (bad.and (eventually_ge_atTop 1))).exists
  let q := g^n
  have qp := pow_pos hg n
  refine ⟨q,qp,pow_lt_one₀ hg.le hg' (by omega),?_⟩
  intro A hA
  obtain ⟨C,hC,bd⟩ := slopeHeavy_mesh hp' a ha hg hg' hc hc' hbc hpoly n tp.le t1.le hδ hA hK he.le badn
  filter_upwards [bn C hC] with k ok
  intro η
  exact (bd k σ η).trans (ENNReal.ofReal_le_ofReal ok)

/-- Every index, including j=0. The upper radius coefficient and the entire
phase sequence are arbitrary and the radius ranges over all positive reals. -/
theorem slopeInformation_all {p d : ℕ} (hp : 2≤p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c γ : ℝ} (hc : 0<c) (hc' : c<1) (hγ : 0<γ) (hγ' : γ<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (j : ℕ) :
    SlopeInformation (by omega : 0<p) (d+1) a (γ*c^j) (slopeExponent p (γ*c^j)) := by
  let P (i : ℕ) := SlopeInformation (by omega : 0<p) (d+1) a (γ*c^i) (slopeExponent p (γ*c^i))
  have init : ∀ᶠ i : ℕ in atTop, P i := slopeInformation_initial hp a ha hc hc' hγ hbc hpoly
  obtain ⟨N,hN⟩ := eventually_atTop.mp init
  have step (i : ℕ) (H : P (i+1)) : P i := by
    have G := mul_pos hγ (pow_pos hc i)
    have G' : γ*c^i < 1 := (mul_le_of_le_one_right hγ.le (pow_le_one₀ hc.le hc'.le)).trans_lt hγ'
    apply slopeInformation_step hp a ha G G' hc hc' hbc hpoly
    simpa only [P,pow_succ,←mul_assoc] using H
  have back (k : ℕ) : ∀ i, N ≤ i + k → P i := by
    induction k with
    | zero => simpa using hN
    | succ k ih => intro i hi;exact step i (ih (i+1) (by omega))
  exact back N j (by omega)

end Weierstrass.Predecessor
