module

public import Weierstrass.ReciprocalEstimate

/-! Reciprocal transfer of the full family of anchored occupation exponents, §2. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Weierstrass.Reciprocal
open CriticalRay Angular

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

set_option maxHeartbeats 650000 in
private theorem interpolate_mean {B : ℂ} (g : ℝ) (P : Set RayParameters) {h T K ε R V C : ℝ}
    (hh : 0 < h) (hK : 0 < K) (hε : 0 < ε) (hR : 0 < R) (hR1 : R < 1)
    (hV : 0 < V) (comparison : V < R^h)
    (mean : ∃ N : ℕ, ∀ n ≥ N, ∀ ω : PhaseTorus, ∀ p ∈ P, ∃ G : Set (complexPhaseGroup B),
      MeasurableSet G ∧ complexPhaseHaar B Gᶜ ≤ ENNReal.ofReal (ε/2) ∧
      ∫⁻ t in Icc (-T) T, complexPhaseHaar B {z | z ∈ G ∧ |circleRay ‖B‖ g p.1 p.2 (ω+z.val) t| ≤ K*R^n} ≤
        ENNReal.ofReal (C*V^n)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ω : PhaseTorus, ∀ p ∈ P, (complexPhaseHaar B).real {z : complexPhaseGroup B |
      ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p (ω+z.val) T K r} ≤ ε := by
  have epos := half_pos hε
  obtain ⟨N,bound⟩ := mean
  have hp := Real.rpow_pos_of_pos hR h
  have gain : V/R^h < 1 := (div_lt_one hp).mpr comparison
  have lim : Tendsto (fun n : ℕ ↦ (C/R^h)*(V/R^h)^n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C/R^h)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hV hp).le gain)
  obtain ⟨N',numeric⟩ := eventually_atTop.1 (lim.eventually_lt_const epos)
  let nmin := max N N'
  have near : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R^nmin := nhdsWithin_le_nhds (Iio_mem_nhds (pow_pos hR nmin))
  filter_upwards [self_mem_nhdsWithin,near] with r hr hsmall
  have hr0 : 0 < r := hr
  obtain ⟨n,lo,hi⟩ := exists_nat_pow_near_of_lt_one hr0 (hsmall.le.trans (pow_le_one₀ hR.le hR1.le)) hR hR1
  have cut : nmin ≤ n := by
    by_contra! contra
    have := pow_le_pow_of_le_one hR.le hR1.le (show n+1 ≤ nmin by omega)
    linarith
  intro ω p hpP
  obtain ⟨G,hG,smallG,integral⟩ := bound n ((Nat.le_max_left _ _).trans cut) ω p hpP
  let τ := (R^(n+1))^h
  have tp : 0 < τ := Real.rpow_pos_of_pos (pow_pos hR _) _
  have mark := retained_markov (complexPhaseHaar B) ‖B‖ g p.1 p.2 ω hG T (K*R^n) τ tp _ integral
  have major := numeric n ((Nat.le_max_right _ _).trans cut)
  have frac : ENNReal.ofReal (C*V^n)/ENNReal.ofReal τ ≤ ENNReal.ofReal (ε/2) := by
    rw [← ENNReal.ofReal_div_of_pos tp]
    apply ENNReal.ofReal_le_ofReal
    calc
      C*V^n/τ = (C/R^h)*(V/R^h)^n := by
        dsimp [τ]; rw [← Real.rpow_pow_comm hR.le, pow_succ,div_pow]; ring
      _ ≤ _ := major.le
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  refine le_trans (le_trans (measure_mono ?_) mark) ((add_le_add smallG frac).trans_eq ?_)
  · intro z hz
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (pow_pos hR _).le lo.le hh.le))
    apply lt_of_lt_of_le hz
    apply measure_mono
    rintro t ⟨ht,ht'⟩
    exact ⟨ht,ht'.trans (mul_le_mul_of_nonneg_left hi hK.le)⟩
  · rw [← ENNReal.ofReal_add epos.le epos.le,add_halves]

/-- Proposition 2 for the uniformly tested angular families at each finite
complexity. A single additional physical-ray factor is needed on the dual side. -/
theorem reciprocal_transfer {B D : ℂ} (hb : 1 < ‖B‖) (hD : D ≠ 0) {g ρ s : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < ‖B‖*g) (hρ : 0 < ρ) (hrγ : ρ < (‖B‖*g)⁻¹)
    (normD : ‖D‖=ρ⁻¹) (rev : (complexPhaseGroup B).map reversePhase=complexPhaseGroup D)
    (hs1 : s ≤ 1) {ζ v₀ : Circle} {e : ℤ → ℝ} (he : Weight ζ v₀ 1 e)
    (orbit : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) (k : ℕ)
    (dual : RayInformation D (‖B‖*g)⁻¹ s (physicalFamily D ζ v₀ (k+1))) :
    RayInformation B g s (physicalFamily B ζ v₀ k) := by
  intro h hh hhs T K hT hK ε hε
  obtain ⟨σ,hσ,hσs⟩ := exists_between hhs
  obtain ⟨α,αp,αl,slow,a,ap,step⟩ := exponent_and_step hb hbg hρ hrγ
  obtain ⟨d,P,_,Pl,sep⟩ := choose_depths hh hσ ap
  let γ := (‖B‖*g)⁻¹
  let L := P-1
  let R := physicalRate γ a d L
  let V := retainedRate γ σ a d L
  have gp : 0 < γ := inv_pos.mpr (zero_lt_one.trans hbg)
  have gl : γ < 1 := inv_lt_one_of_one_lt₀ hbg
  have Rpos : 0 < R := pow_pos gp _
  have Rsmall : R < 1 := pow_lt_one₀ gp.le gl (by dsimp [L]; positivity)
  have Vpos : 0 < V := Real.rpow_pos_of_pos (pow_pos gp _) _
  have gain : V < R^h := by
    dsimp [R,V,retainedRate,physicalRate]
    rw [← Real.rpow_natCast_mul gp.le,← Real.rpow_natCast_mul gp.le]
    apply Real.rpow_lt_rpow_of_exponent_gt gp gl
    have order : a^d ≤ (a+1)^d := Nat.pow_le_pow_left (by omega) _
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub order,show L+1=P by dsimp [L]; omega]
    dsimp only [L]
    rw [Nat.cast_pow a d]
    nlinarith only [sep]
  apply interpolate_mean g _ hh hK hε Rpos Rsmall Vpos gain
  exact retained_mean hb hD hg hg1 hbg hρ hrγ αp αl.le slow normD rev (hh.trans hσ) hσs
    (hσs.le.trans hs1) hT hK (half_pos hε) he orbit k dual a d L ap step

/-- Specialization in which the reciprocal Haar transport is supplied by the
two embeddings themselves. -/
theorem reciprocal_transfer_conjugate {K : Type*} [Field K] (σ τ : K →+* ℂ) (u : K)
    (hb : 1 < ‖σ u‖) (hc : τ u ≠ 0) {g s : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < ‖σ u‖*g) (hrγ : ‖τ u‖ < (‖σ u‖*g)⁻¹) (hs1 : s ≤ 1)
    {ζ v₀ : Circle} (w : ℂ) (he : Weight ζ v₀ 1 (rayProjection (τ u) w)) (k : ℕ)
    (dual : RayInformation (τ u)⁻¹ (‖σ u‖*g)⁻¹ s (physicalFamily (τ u)⁻¹ ζ v₀ (k+1))) :
    RayInformation (σ u) g s (physicalFamily (σ u) ζ v₀ k) :=
  reciprocal_transfer hb (inv_ne_zero hc) hg hg1 hbg (norm_pos_iff.mpr hc) hrγ (norm_inv _)
    (reversePhase_group_conjugate σ τ u) hs1 he (transverseOrbit_mem σ τ u hc w) k dual

end Weierstrass.Reciprocal
