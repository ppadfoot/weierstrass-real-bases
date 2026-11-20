module

public import Weierstrass.StripPhysical
public import Weierstrass.StripHeavy
public import Weierstrass.StripSamples
public import Weierstrass.StripRates

/-! # Finite-scale equal-rate bootstrap on the physical Haar law -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Weierstrass.StripProof
open CriticalRay

local instance bootstrapPhaseMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance bootstrapPhaseBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

/-- All deletion and correlation terms for one physical scale, without conditioning on
any exceptional environment. The two families of tests are averaged in their actual cosets. -/
theorem finite_strip_bootstrap {B : ℂ} {g T A h : ℝ} (hb : 1 < ‖B‖) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < ‖B‖*g) (hT : 0 < T) (hA : 0 < A) {p : RayParameters} {e : ℤ → ℝ}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (tp : ∀ x, transverseOrbit ‖B‖ p.2 x ∈ complexPhaseGroup B)
    (te : ∀ x, transverseOrbit ‖B‖⁻¹ e x ∈ complexPhaseGroup B)
    (ω : PhaseTorus) (m J : ℕ) (hJ : 0 < J) (n : ℕ → ℕ) {d D t s M ε : ℝ} (hM : 1 < M)
    (hpos : 0 < d) (hd1 : d ≤ 1)
    (hR : A*‖B‖⁻¹^m+2*(physicalError ‖B‖ g T*‖B‖⁻¹^m) ≤ ((‖B‖*g)⁻¹)^m*d)
    (mesh : ∀ j < J, (‖B‖⁻¹/(‖B‖*g)⁻¹)^m ≤ paperMesh d J (j+1) ∧ paperMesh d J (j+1) ≤ (‖B‖^(n j))⁻¹)
    (rate : ∀ j < J, (‖B‖^(n j))⁻¹*((((‖B‖*g)⁻¹)^m*paperMesh d J (j+1))/(g^(n j)))^s ≤
      (‖B‖*(((‖B‖*g)⁻¹)^m)^s)*(paperMesh d J (j+1))^D)
    (height : ((complexPhaseHaar B).prod (physicalLaw T)).real (physicalFailure g ω p 0 (1+2*T) 1 (((‖B‖*g)⁻¹)^m) s) ≤ ε)
    (phys : ∀ j < J, ((complexPhaseHaar B).prod (physicalLaw T)).real (physicalFailure g ω p (n j) 2 2
      ((((‖B‖*g)⁻¹)^m*paperMesh d J (j+1))/g^(n j)) s) ≤ ε)
    (stab : ∀ j < J, ((complexPhaseHaar B).prod stableLaw).real (stableFailure (‖B‖*g)⁻¹ ‖B‖⁻¹ ω p e m 1
      ((2+dualError ‖B‖ g ‖B‖⁻¹)/τ) (paperMesh d J (j+1)) t) ≤ ε) :
    (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal ((‖B‖⁻¹^m)^h) <
      rayOccupation ‖B‖ g p (ω+z.val) T A (‖B‖⁻¹^m)} ≤
    J*ε+(1+2*T)*((J+1)*ε+3/M+
      (M/((‖B‖⁻¹^m)^h/(1+2*T)))*(physicalCost ‖B‖ g T J*(‖B‖*(((‖B‖*g)⁻¹)^m)^s)*d^(min 1 (D+t-1)-1/J))) := by
  let := physicalLaw_probability hT
  let b := ‖B‖
  let Δ := ((b*g)⁻¹)^m
  let r := b⁻¹^m
  let ℓ := fun j => paperMesh d J (j+1)
  let rad := fun j => Δ*ℓ j/g^(n j)
  let P : ℕ → Set (complexPhaseGroup B × ℝ) := fun j =>
    if j=0 then physicalFailure g ω p 0 (1+2*T) 1 Δ s else physicalFailure g ω p (n (j-1)) 2 2 (rad (j-1)) s
  let S : ℕ → Set (complexPhaseGroup B × ℝ) := fun j =>
    stableFailure (b*g)⁻¹ b⁻¹ ω p e m 1 ((2+dualError b g b⁻¹)/τ) (ℓ j) t
  let Q := retainedSamples (RaySeed.sampleInterval T) (Finset.range (J+1)) P
  let U := retainedSamples (Icc 0 1) (Finset.range J) S
  have mP (j : ℕ) : MeasurableSet (P j) := by
    dsimp only [P]; split <;> exact measurable_physicalFailure _ _ _ _ _ _ _ _
  have mS (j : ℕ) : MeasurableSet (S j) := measurable_stableFailure _ _ _ _ _ _ _ _ _ _
  have mQ : MeasurableSet Q := retainedSamples_meas measurableSet_Icc _ (fun j _ => mP j)
  have mU : MeasurableSet U := retainedSamples_meas measurableSet_Icc _ (fun j _ => mS j)
  have dp : 0 < Δ := pow_pos (inv_pos.mpr (zero_lt_one.trans hbg)) _
  have rp : 0 < r := pow_pos (inv_pos.mpr (zero_lt_one.trans hb)) _
  have Pbound (j : ℕ) (hj : j ∈ Finset.range (J+1)) : ((complexPhaseHaar B).prod (physicalLaw T)).real (P j) ≤ ε := by
    rcases j with _|j
    · simpa only [P,if_pos rfl] using height
    · simpa only [P,if_neg (Nat.succ_ne_zero _),Nat.add_one_sub_one] using phys j (by simpa using hj)
  have lossQ := deletedSamples_mass (complexPhaseHaar B) (physicalLaw T) measurableSet_Icc
    (physicalLaw_supported T) (Finset.range (J+1)) Pbound
  have lossU := deletedSamples_mass (complexPhaseHaar B) stableLaw measurableSet_Icc
    (show ∀ᵐ u ∂stableLaw, u ∈ Icc 0 1 from ae_restrict_mem measurableSet_Icc)
    (Finset.range J) (fun j hj => stab j (Finset.mem_range.mp hj))
  have loseQ : ((complexPhaseHaar B).prod (physicalLaw T)).real Qᶜ ≤ (J+1)*ε := by simpa only [Q,RaySeed.sampleInterval,Finset.card_range,Nat.cast_succ] using lossQ
  have loseU : ((complexPhaseHaar B).prod stableLaw).real Uᶜ ≤ J*ε := by simpa only [Finset.card_range] using lossU
  let cost := physicalCost b g T J*(b*Δ^s)*d^(min 1 (D+t-1)-1/J)
  refine (haar_retention_bound (h:=h) (q:=r) (cost:=cost) (zero_lt_one.trans hb) hg hg1 hbg hT hA rp hc hd e ω tp te Q U mQ mU hM ?_).trans ?_
  swap
  · exact add_le_add loseU (mul_le_mul_of_nonneg_left (add_le_add (add_le_add loseQ le_rfl) le_rfl) (by linarith))
  intro z
  let Qz := Prod.mk z ⁻¹' Q
  let Uz := Prod.mk z ⁻¹' U
  have GQ {x : ℝ} (hx : x ∈ Qz) := retainedSamples_good (show (z,x) ∈ Q from hx)
  have GU {u : ℝ} (hu : u ∈ Uz) := retainedSamples_good (show (z,u) ∈ U from hu)
  apply retained_physical_collision hb hg hg1 hbg hT hc hd he (ω+z.val) m J hJ n hpos hd1
    (mul_nonneg (zero_lt_one.trans hb).le (Real.rpow_pos_of_pos dp _).le) hR mesh rate
    (mQ.preimage (measurable_prodMk_left (x:=z))) (mU.preimage (measurable_prodMk_left (x:=z)))
    (fun _ hx => (GQ hx).1) (fun _ hu => (GU hu).1)
  · intro x hx
    have good := (GQ hx).2 0 (by simp)
    have v : rayOccupation b g (shiftedParameters p 0) (physicalEnvironment b p.2 (ω+z.val) 0 x) (1+2*T) 1 Δ ≤
        ENNReal.ofReal (Δ^s) := le_of_not_gt (by simpa only [P,if_pos rfl,physicalFailure,Set.mem_ofPred_eq,Nat.cast_zero,b] using good)
    exact v.trans (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (Real.rpow_pos_of_pos dp _).le hb.le))
  · intro j hj x hx
    have good := (GQ hx).2 (j+1) (by simpa using hj)
    exact le_of_not_gt (by simpa only [P,if_neg (Nat.succ_ne_zero _),Nat.add_one_sub_one,physicalFailure,Set.mem_ofPred_eq,rad,ℓ,Δ,b] using good)
  · intro j hj u hu
    have good := (GU hu).2 j (Finset.mem_range.mpr hj)
    exact le_of_not_gt (by simpa only [S,stableFailure,Set.mem_ofPred_eq,inv_inv,ℓ,b] using good)

end Weierstrass.StripProof
