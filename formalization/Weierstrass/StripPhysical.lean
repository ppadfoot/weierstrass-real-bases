module

public import Weierstrass.StripGeometry
public import Weierstrass.StripHaarTests

/-! # The strip estimate for the equal-rate physical cosine model -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Weierstrass.StripProof
open CriticalRay

def physicalError (b g T : ℝ) :=
  (2*τ+3*τ^3*(1+T)^2)*(∑' j : ℤ, tails (g*b⁻¹) (b*g) j)

theorem physicalError_nonneg {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (T : ℝ) : 0 ≤ physicalError b g T := by
  unfold physicalError
  have tp : 0 < τ := by dsimp [τ]; positivity
  refine mul_nonneg (by positivity) (tsum_nonneg (fun j => ?_))
  unfold tails; split <;> positivity

def directionRadius (b g : ℝ) :=
  max 1 (τ*rayBound b (b*g)⁻¹ 1+dualError b g b⁻¹)

def interactionRange (b g T : ℝ) := ⌈1+2*(1+T)*(1+directionRadius b g)⌉₊

def physicalCost (b g T : ℝ) (J : ℕ) :=
  2*(2*(interactionRange b g T:ℝ)+1)*stripConstant J (1+T) (directionRadius b g) 1

def shiftedHeight (b g : ℝ) (p : RayParameters) (e : ℤ → ℝ) (z : PhaseTorus) (m : ℕ) (u : ℝ) :=
  circleRay b g p.1 p.2 (z+transverseOrbit b⁻¹ e (b⁻¹^m*u))

set_option maxHeartbeats 2600000 in
/-- After the centered information tests have passed, the raw physical collision on all
retained inputs satisfies B5, uniformly in the phases, weights, and total strip count. -/
theorem retained_physical_collision {b g T : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hT : 0 < T) {p : RayParameters} {e : ℤ → ℝ}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (m J : ℕ) (hJ : 0 < J) (n : ℕ → ℕ) {d B D t s R : ℝ}
    (hpos : 0 < d) (hd1 : d ≤ 1) (hB : 0 ≤ B)
    (hR : R+2*(physicalError b g T*b⁻¹^m) ≤ ((b*g)⁻¹)^m*d)
    (mesh : ∀ j < J, (b⁻¹/(b*g)⁻¹)^m ≤ paperMesh d J (j+1) ∧ paperMesh d J (j+1) ≤ (b^(n j))⁻¹)
    (rate : ∀ j < J, (b^(n j))⁻¹*((((b*g)⁻¹)^m*paperMesh d J (j+1))/(g^(n j)))^s ≤
      B*(paperMesh d J (j+1))^D)
    {Q U : Set ℝ} (mQ : MeasurableSet Q) (mU : MeasurableSet U)
    (IQ : Q ⊆ RaySeed.sampleInterval T) (IU : U ⊆ Icc 0 1)
    (height : ∀ x ∈ Q, rayOccupation b g (shiftedParameters p 0) (physicalEnvironment b p.2 z 0 x)
      (1+2*T) 1 (((b*g)⁻¹)^m) ≤ ENNReal.ofReal B)
    (physical : ∀ j < J, ∀ x ∈ Q, rayOccupation b g (shiftedParameters p (n j))
      (physicalEnvironment b p.2 z (n j) x) 2 2 ((((b*g)⁻¹)^m*paperMesh d J (j+1))/g^(n j)) ≤
        ENNReal.ofReal (((((b*g)⁻¹)^m*paperMesh d J (j+1))/g^(n j))^s))
    (stable : ∀ j < J, ∀ u ∈ U, rayOccupation b (b*g)⁻¹ (reversedParameters p.1 p.2 e m)
      (reversedEnvironment (z+transverseOrbit b⁻¹ e (b⁻¹^m*u)) m) 1 ((2+dualError b g b⁻¹)/τ)
        (paperMesh d J (j+1)) ≤ ENNReal.ofReal ((paperMesh d J (j+1))^t)) :
    ∫ u in U, Weierstrass.collision (((physicalLaw T).restrict Q).map (shiftedHeight b g p e z m u)) R ∂stableLaw ≤
      physicalCost b g T J * B * d^(min 1 (D+t-1) - 1/J) := by
  let := physicalLaw_probability hT
  let Y := circleRay b g p.1 p.2 z
  let Δ := ((b*g)⁻¹)^m
  let r := b⁻¹^m
  let ϑ := direction b g b⁻¹ p.1 p.2 e z m
  let σ := (stableLaw.restrict U).map ϑ
  let μ := stripLaw (physicalLaw T) Q Y Δ
  let ℓ := fun j => paperMesh d J (j+1)
  have bp := zero_lt_one.trans hb
  have gp := inv_pos.mpr (zero_lt_one.trans hbg)
  have dp : 0 < Δ := pow_pos gp m
  have rp : 0 < r := pow_pos (inv_pos.mpr bp) m
  have lp (j : ℕ) : 0 < ℓ j := Real.rpow_pos_of_pos hpos _
  have dual : 1 < (b⁻¹)⁻¹*(b*g)⁻¹ := by
    rw [inv_inv,←div_eq_mul_inv,lt_div_iff₀ (zero_lt_one.trans hbg)]
    nlinarith [mul_lt_mul_of_pos_left hg1 bp]
  have mY : Measurable Y := measurable_ray_time b g p z
  have mF (u : ℝ) : Measurable (shiftedHeight b g p e z m u) :=
    measurable_ray_time b g p (z+transverseOrbit b⁻¹ e (b⁻¹^m*u))
  have mθ : Measurable ϑ := measurable_direction_time b g b⁻¹ p e z m
  have ybound (x : ℝ) (hx : x ∈ Q) : |Y x| ≤ rayBound b g (1+T) :=
    circleRay_uniform_bound bp hg hg1 hbg hc hd z (sample_radius hT (IQ hx))
  obtain ⟨I,hcover⟩ := finite_height_cover dp ybound
  have est := stable_mean_comparison (physicalLaw T) stableLaw Q U mY (shiftedHeight b g p e z m) mF
    mθ dp hR (I := I) (hcover := hcover) (mU := mU)
  have model (u : ℝ) (hu : u ∈ U) (x : ℝ) (hx : x ∈ Q) :
      |shiftedHeight b g p e z m u x - (Y x+Δ*ϑ u*x)| ≤ physicalError b g T*r := by
    have h := equal_rate_linearization_on hb hg hg1 hbg hc hd he z (sample_radius hT (IQ hx)) (r*u)
    have hfac : Δ*ϑ u*x = x*(pastSlope b g p.1 p.2 (z+transverseOrbit b⁻¹ e (r*u))-pastSlope b g p.1 p.2 z) := by
      dsimp [ϑ,direction,Δ,r]; field_simp [(zero_lt_one.trans hbg).ne']
    rw [hfac]
    have a : |r*u| ≤ r := by rw [abs_mul,abs_of_pos rp,abs_of_nonneg (IU hu).1]; exact mul_le_of_le_one_right rp.le (IU hu).2
    exact (by simpa only [sub_add_eq_sub_sub,shiftedHeight,Y,r,physicalError] using h :
      |shiftedHeight b g p e z m u x - (Y x+x*(pastSlope b g p.1 p.2 (z+transverseOrbit b⁻¹ e (r*u))-pastSlope b g p.1 p.2 z))| ≤
        physicalError b g T*|r*u|).trans (mul_le_mul_of_nonneg_left a (physicalError_nonneg bp hg _))
  apply (est model).trans
  apply strip_estimate I μ σ (S := 1+T) (T := directionRadius b g) (A := 1) (B := B) (D := D) (t := t) (L := interactionRange b g T) hpos hd1 hJ (le_max_left _ _) zero_le_one hB (Nat.le_ceil _)
  · rw [map_measureReal_apply mθ MeasurableSet.univ,preimage_univ,measureReal_restrict_apply_univ]
    exact measureReal_le_one
  · exact (sum_strip_mass _ mY mQ dp I).trans (by simp)
  · intro i _
    apply retained_strip_mass _ mY Q hB _ i
    intro x hx
    exact ENNReal.toReal_le_of_le_ofReal hB ((centered_height_mass bp hg hg1 hbg hT hc hd z (IQ hx) Δ).trans (height _ hx))
  · intro i _
    exact physical_support _ mQ mY dp (by linarith) (fun x hx => sample_radius hT (IQ hx)) i
  · apply (ae_map_iff mθ.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).mpr
    filter_upwards [ae_restrict_mem mU] with u hu
    exact (equal_rate_direction_bound hb hg hg1 hbg hc hd he z m (IU hu)).trans (le_max_right _ _)
  · intro j hj x
    rw [one_mul]
    apply retained_direction_bound _ mθ U (lp _).le (Real.rpow_pos_of_pos (lp _) _).le _ x
    intro u hu
    apply ENNReal.toReal_le_of_le_ofReal (Real.rpow_pos_of_pos (lp _) _).le
    apply (centered_direction_mass hbg (inv_pos.mpr bp) dual hc hd he z m (IU hu) (mesh j hj).1).trans
    simpa only [inv_inv] using stable j hj u hu
  · intro i _ j hj x
    apply retained_physical_bound _ mY Q dp (mul_nonneg hB (Real.rpow_pos_of_pos (lp _) _).le) _ i x
    intro y hy
    apply le_trans _ (rate j hj)
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (inv_pos.mpr (pow_pos bp _)).le
      (Real.rpow_pos_of_pos (div_pos (mul_pos dp (lp _)) (pow_pos hg _)) _).le)
    apply ((physicalLaw_le hT _).trans (Measure.restrict_le_self _)).trans
    apply (centered_physical_mass bp hg hg1 hbg hc hd z y (n j) (mesh j hj).2).trans
    rw [ENNReal.ofReal_mul (inv_pos.mpr (pow_pos bp _)).le]
    gcongr
    exact physical j hj y hy

end Weierstrass.StripProof
