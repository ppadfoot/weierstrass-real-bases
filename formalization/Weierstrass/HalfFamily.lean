module

public import Weierstrass.AngularWeights
public import Weierstrass.HalfSeed

/-! The half-exponent initialization for the angular products in §2. -/
@[expose] public noncomputable section
open Set
namespace Weierstrass.Angular

/-- Physical projections carry the phase along its Haar subgroup. The
absolute-value product condition controls weights at positive frequencies. -/
def physicalFamily (B : ℂ) (ζ v₀ : Circle) (k : ℕ) : Set RayParameters :=
  {p | p ∈ rayFamily ζ v₀ k ∧ ∀ x, CriticalRay.transverseOrbit ‖B‖ p.2 x ∈ complexPhaseGroup B}

theorem rayInformation_half_family {B : ℂ} (hb : 1 < ‖B‖) {g ρ : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hq : 1 < ‖B‖*g) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hQ : (‖B‖*g)*ρ < 1) (hbQ : 1 < ((‖B‖*g)*ρ)*‖B‖)
    {ζ v₀ : Circle} (base : AdmissibleBase ζ v₀) {e : ℤ → ℝ} (he : Weight ζ v₀ 1 e)
    (hmem : ∀ x, CriticalRay.transverseOrbit ρ e x ∈ complexPhaseGroup B) (k : ℕ) :
    RayInformation B g (1/2) (physicalFamily B ζ v₀ k) := by
  obtain ⟨δ,hδ,hit⟩ := permitted_weight_windows base (k+2)
  apply RaySeed.rayInformation_half hb hg hg1 hq hρ hρ1 hQ hbQ hδ (k+2+1)
  rintro p ⟨⟨hc,hd⟩,hm⟩
  refine ⟨hm,e,⟨hc.bounded,hd.bounded,he.bounded,?_⟩,hmem⟩
  intro n
  obtain ⟨j,hj⟩ := hit _ ((hc.mul hd).mul he) n
  exact ⟨j,by simpa only [Nat.cast_add] using hj⟩

end Weierstrass.Angular
