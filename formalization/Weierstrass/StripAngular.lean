module

public import Weierstrass.StripGain
public import Weierstrass.ReciprocalPhases

/-! # The equal-rate step on every angular weight complexity -/
@[expose] public noncomputable section
open Set
namespace Weierstrass.StripProof
open CriticalRay Angular

/-- Shifting the physical scale translates the weight phases and rescales the time
on the same physical subgroup. Membership is uniform in all signs. -/
theorem shiftedParameters_mem {B : ℂ} (hB : B ≠ 0) {ζ v₀ : Circle} {k : ℕ} {p : RayParameters}
    (hp : p ∈ physicalFamily B ζ v₀ k) (n : ℤ) :
    shiftedParameters p n ∈ physicalFamily B ζ v₀ k := by
  obtain ⟨⟨hc,hd⟩,hm⟩ := hp
  refine ⟨⟨hc.shift n,hd.shift n⟩,?_⟩
  intro x
  have eq : transverseOrbit ‖B‖ (shiftedParameters p n).2 x = shiftPhase n (transverseOrbit ‖B‖ p.2 (‖B‖^(-n)*x)) := by
    funext j
    change (↑(‖B‖^j*p.2 (j+n)*x) : UnitAddCircle) = ↑(‖B‖^(j+n)*p.2 (j+n)*(‖B‖^(-n)*x))
    rw [zpow_add₀ (norm_ne_zero_iff.mpr hB),zpow_neg]
    congr 1; field_simp
  rw [eq,← shiftPhase_group hB n]
  exact AddSubgroup.mem_map_of_mem _ (hm _)

/-- B1 for fixed angular complexity and its immediate dual successor. -/
theorem equal_rate_angular_conjugate {K : Type*} [Field K] (σ τ' : K →+* ℂ) (a : K)
    (hb : 1 < ‖σ a‖) (equal : ‖τ' a‖ = ‖σ a‖⁻¹) {g s t : ℝ}
    (hg : ‖σ a‖⁻¹ < g) (hg1 : g < 1) (hs : 0 < s) (ht : 0 < t)
    {ζ v₀ : Circle} (w : ℂ) (he : Weight ζ v₀ 1 (rayProjection (τ' a) w)) (k : ℕ)
    (direct : RayInformation (σ a) g s (physicalFamily (σ a) ζ v₀ k))
    (dual : RayInformation (τ' a)⁻¹ (‖σ a‖*g)⁻¹ t (physicalFamily (τ' a)⁻¹ ζ v₀ (k+1))) :
    RayInformation (σ a) g (stripGain (1-alpha ‖σ a‖ g) s t) (physicalFamily (σ a) ζ v₀ k) := by
  have hB : σ a ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans hb).ne'
  have hρ : 0 < ‖τ' a‖ := equal ▸ inv_pos.mpr (zero_lt_one.trans hb)
  have hC : τ' a ≠ 0 := norm_ne_zero_iff.mp hρ.ne'
  have te := transverseOrbit_mem σ τ' a hC w
  apply rayInformation_equal_rate σ τ' a hb equal hg hg1 hs ht direct dual
  intro p hp
  exact ⟨hp.1.1.bounded,hp.1.2.bounded,hp.2,fun n => shiftedParameters_mem hB hp n,
    rayProjection (τ' a) w,he.bounded,equal ▸ te,fun m => Reciprocal.reversedParameters_mem (inv_ne_zero hC) hρ
      (norm_inv _) (reversePhase_group_conjugate σ τ' a) hp he te m⟩

end Weierstrass.StripProof
