module

public import Weierstrass.StripBootstrap
public import Weierstrass.StripGridRates
public import Weierstrass.StripBudget

/-! # B1 for weighted physical and conjugate rays of equal rate -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Weierstrass.StripProof
open CriticalRay

local instance gainPhaseMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance gainPhaseBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- The equal-rate step B1 for arbitrary families of actual bounded profiles on the
original and dual conjugate phase groups. The profile hypotheses identify the two
sampled motions and the rays occurring after the reindexings. -/
theorem rayInformation_equal_rate {K : Type*} [Field K] (σ τ' : K →+* ℂ) (a : K)
    (hb : 1 < ‖σ a‖) (equal : ‖τ' a‖ = ‖σ a‖⁻¹) {g s t : ℝ}
    (hg : ‖σ a‖⁻¹ < g) (hg1 : g < 1) (hs : 0 < s) (ht : 0 < t)
    {P O V : Set RayParameters} (direct : RayInformation (σ a) g s O)
    (dual : RayInformation (τ' a)⁻¹ (‖σ a‖*g)⁻¹ t V)
    (families : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧
      (∀ x, transverseOrbit ‖σ a‖ p.2 x ∈ complexPhaseGroup (σ a)) ∧
      (∀ n : ℕ, shiftedParameters p n ∈ O) ∧ ∃ e : ℤ → ℝ, (∀ j, |e j| ≤ 1) ∧
        (∀ x, transverseOrbit ‖σ a‖⁻¹ e x ∈ complexPhaseGroup (σ a)) ∧
        ∀ m, reversedParameters p.1 p.2 e m ∈ V) :
    RayInformation (σ a) g (stripGain (1-alpha ‖σ a‖ g) s t) P := by
  let b := ‖σ a‖
  let β := 1-alpha b g
  have bp : 0 < b := zero_lt_one.trans hb
  have invp := inv_pos.mpr bp
  have gp := invp.trans hg
  have bg : 1 < b*g := by
    have bb : b⁻¹ < g := hg
    simpa only [mul_inv_cancel₀ bp.ne'] using mul_lt_mul_of_pos_left bb bp
  have hB : σ a ≠ 0 := norm_ne_zero_iff.mp bp.ne'
  have hC : τ' a ≠ 0 := norm_ne_zero_iff.mp (equal ▸ invp.ne')
  have dp := inv_pos.mpr (zero_lt_one.trans bg)
  have dualOK : 1 < (b⁻¹)⁻¹*(b*g)⁻¹ := by
    rw [inv_inv,← div_eq_mul_inv,lt_div_iff₀ (zero_lt_one.trans bg)]
    nlinarith [mul_lt_mul_of_pos_left hg1 bp]
  have errpos : 0 ≤ dualError b g b⁻¹ := by
    unfold dualError
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ dualOK).le))
  apply rayInformation_of_geometric invp (inv_lt_one_of_one_lt₀ hb)
  intro h hh hu T A hT hA ε hε
  obtain ⟨s',t',ss,ss',tt,tt',J,hJ,gain⟩ := strip_gain_slack hs ht hu
  have jp : 0 < J := by omega
  obtain ⟨M,η,δ,hM,hη,hδ,budget⟩ := strip_probability_budget J hT hε
  let := physicalLaw_probability hT
  let K₀ := 1+A+2*physicalError b g T
  have k1 : 1 ≤ K₀ := by dsimp [K₀]; linarith [physicalError_nonneg bp gp T]
  have kp := zero_lt_one.trans_le k1
  let d := stripWidth b g K₀
  let Δ := fun m : ℕ => ((b*g)⁻¹)^m
  let ℓ := fun m j => paperMesh (d m) J (j+1)
  let n := fun m j => stripMeshIndex b g (ℓ m j)
  let v := fun m j => Δ m*ℓ m j/g^(n m j)
  let D := 1+β*s'
  let p₀ := min 1 (D+t'-1)-1/(J:ℝ)
  have eqp : p₀ = min 1 (β*s'+t')-1/(J:ℝ) := by unfold p₀ D; ring_nf
  have dl : Tendsto Δ atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one dp.le (inv_lt_one_of_one_lt₀ bg),Eventually.of_forall (fun m => pow_pos dp m)⟩
  let C := physicalCost b g T J*b
  have cv : Tendsto (fun m : ℕ => C*((Δ m)^s'*(d m)^p₀/((b⁻¹^m)^h))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (strip_cost_tendsto (K:=K₀) hb gp kp (u:=h) (s:=s') (p:=p₀) (eqp ▸ gain)).const_mul C
  have height := dl.eventually (physical_haar_test hB (physicalLaw T) direct ss ss' (T:=1+2*T) (A:=1) (by linarith) zero_lt_one hη)
  have phys : ∀ᶠ m : ℕ in atTop, ∀ j ∈ Finset.range J, ∀ ω p, shiftedParameters p (n m j) ∈ O →
      ((complexPhaseHaar (σ a)).prod (physicalLaw T)).real (physicalFailure g ω p (n m j) 2 2 (v m j) s') ≤ η := by
    apply (eventually_all_finset (Finset.range J)).mpr
    intro j hj
    have lim := width_physical_tendsto (K:=K₀) hb hg hg1 k1 (Finset.mem_range.mp hj)
    filter_upwards [lim.eventually (physical_haar_test hB (physicalLaw T) direct ss ss'
      (T:=2) (A:=2) (by norm_num) (by norm_num) hη)] with m hm
    exact fun ω p hp => hm ω p (n m j) hp
  have stab : ∀ᶠ m : ℕ in atTop, ∀ j ∈ Finset.range J, ∀ ω (p : RayParameters) e, reversedParameters p.1 p.2 e m ∈ V →
      ((complexPhaseHaar (σ a)).prod stableLaw).real (stableFailure (b*g)⁻¹ b⁻¹ ω p e m 1
        ((2+dualError b g b⁻¹)/τ) (ℓ m j) t') ≤ η := by
    apply (eventually_all_finset (Finset.range J)).mpr
    intro j _
    have lim := width_mesh_tendsto (K:=K₀) bp gp hg1 kp jp j
    have av := stable_haar_test σ τ' a hC dual tt tt' (T:=1) (A:=(2+dualError b g b⁻¹)/τ) zero_lt_one
      (div_pos (by linarith) (by dsimp [τ]; positivity)) hη
    filter_upwards [lim.eventually av] with m hm
    intro ω p e hp
    have h' := hm ω p.1 p.2 e m hp
    simpa only [stableFailure,norm_inv,equal,inv_inv,b] using h'
  filter_upwards [height,phys,stab,width_mesh_bounds (K:=K₀) hb hg hg1 k1 ss.le jp,cv.eventually_lt_const hδ] with m hheight hphys hstab bounds small
  intro ω p hp
  obtain ⟨hc,hd,tp,sh,e,he,te,rev⟩ := families p hp
  have rad : A*b⁻¹^m+2*(physicalError b g T*b⁻¹^m) ≤ Δ m*d m := by
    rw [show Δ m*d m=K₀*b⁻¹^m from stripWidth_radius bp gp K₀ m]
    dsimp only [K₀]; nlinarith [pow_pos invp m]
  have actual := finite_strip_bootstrap (h:=h) hb gp hg1 bg hT hA hc hd he tp te ω m J jp (n m) hM
    bounds.1 bounds.2.1 rad (fun j hj => ⟨(bounds.2.2 j hj).1,(bounds.2.2 j hj).2.1⟩)
    (fun j hj => (bounds.2.2 j hj).2.2.1) (hheight ω p 0 (sh 0))
    (fun j hj => hphys j (Finset.mem_range.mpr hj) ω p (sh _))
    (fun j hj => hstab j (Finset.mem_range.mpr hj) ω p e (rev m))
  apply actual.trans
  apply le_trans (le_of_eq ?_) (budget small.le)
  dsimp only [C,Δ,d,p₀,D,β,b]
  rw [div_div_eq_mul_div]
  ring

end Weierstrass.StripProof
