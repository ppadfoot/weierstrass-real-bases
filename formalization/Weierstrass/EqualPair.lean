module

public import Weierstrass.PhysicalPair
public import Weierstrass.StripAngular
public import Weierstrass.CriticalGraph

/-! Equal-rate closure for the two actual conjugate multipliers. Both
orientations are at their own amplitudes, and the reversed forcing uses the
field element `a⁻¹`. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Real
namespace Weierstrass.ConjugatePair
open Angular CriticalRay

private theorem half_equal {B : ℂ} (hb : 1 < ‖B‖) {g : ℝ} (hg : ‖B‖⁻¹ < g) (hg1 : g < 1)
    {ζ v : Circle} (base : AdmissibleBase ζ v) {e : ℤ → ℝ} (he : Weight ζ v 1 e)
    (hm : ∀ x, transverseOrbit ‖B‖⁻¹ e x ∈ complexPhaseGroup B) : FamilyBound B ζ v g (1/2) := by
  have bp := zero_lt_one.trans hb
  have gp := (inv_pos.mpr bp).trans hg
  have bg : 1 < ‖B‖*g := by simpa only [mul_inv_cancel₀ bp.ne'] using mul_lt_mul_of_pos_left hg bp
  have eq : ‖B‖*g*‖B‖⁻¹ = g := by field_simp
  exact fun k ↦ rayInformation_half_family hb gp hg1 bg (inv_pos.mpr bp) (inv_lt_one_of_one_lt₀ hb)
    (by rw [eq];exact hg1) (by rw [eq,mul_comm];exact bg) base he hm k

private theorem alpha_dual {b g : ℝ} (hb : 1 < b) (hg : 0 < g) :
    alpha b (b*g)⁻¹ = 1-alpha b g := by
  have bp := zero_lt_one.trans hb
  rw [alpha,alpha,log_inv,neg_neg,log_mul bp.ne' hg.ne'];field_simp [(log_pos hb).ne'];ring

theorem equal {K : Type*} [Field K] (σ τ : K →+* ℂ) (a : K) (hb : 1 < ‖σ a‖)
    (rate : ‖τ a‖ = ‖σ a‖⁻¹) {ζ v : Circle} (base : AdmissibleBase ζ v)
    (w w' : ℂ) (hw : Weight ζ v 1 (rayProjection (τ a) w))
    (hw' : Weight ζ v 1 (rayProjection (σ a)⁻¹ w')) {g : ℝ} (hg : ‖σ a‖⁻¹ < g) (hg1 : g < 1) :
    FamilyBound (σ a) ζ v g 1 ∧ FamilyBound (τ a)⁻¹ ζ v (‖σ a‖*g)⁻¹ 1 := by
  let b := ‖σ a‖
  let γ := (b*g)⁻¹
  have bp : 0 < b := zero_lt_one.trans hb
  have gp := (inv_pos.mpr bp).trans hg
  have hgb : b⁻¹ < g := hg
  have bg : 1 < b*g := by simpa only [mul_inv_cancel₀ bp.ne'] using mul_lt_mul_of_pos_left hgb bp
  have hγ : 0 < γ := inv_pos.mpr (zero_lt_one.trans bg)
  have hγ1 : γ < 1 := inv_lt_one_of_one_lt₀ bg
  have bd : ‖(τ a)⁻¹‖ = b := by rw [norm_inv,rate,inv_inv]
  have revAdm : b⁻¹ < γ := (inv_lt_inv₀ bp (zero_lt_one.trans bg)).mpr (by simpa using mul_lt_mul_of_pos_left hg1 bp)
  have invol : (b*γ)⁻¹ = g := by dsimp [γ];field_simp
  have bne : σ a ≠ 0 := norm_pos_iff.mp bp
  have cne : τ a ≠ 0 := norm_pos_iff.mp (rate ▸ inv_pos.mpr bp)
  have hA := alpha_mem_Ioo hb hg hg1
  have nrev : ‖τ (a⁻¹)‖ = b := by simpa only [map_inv₀] using bd
  have rr : ‖σ (a⁻¹)‖ = ‖τ (a⁻¹)‖⁻¹ := by rw [map_inv₀,norm_inv,nrev]
  have hwr : Weight ζ v 1 (rayProjection (σ (a⁻¹)) w') := by rwa [map_inv₀]
  have seed := half_equal hb hg hg1 base hw (fun x ↦ rate ▸ transverseOrbit_mem σ τ a cne w x)
  have seedR := half_equal (B:=(τ a)⁻¹) (bd ▸ hb) (bd ▸ revAdm) hγ1 base hw' (fun x ↦ by
    have h := transverseOrbit_mem τ σ (a⁻¹) (by simpa only [map_inv₀] using inv_ne_zero bne) w' x
    simpa only [map_inv₀,norm_inv,bd] using h)
  have step (s t : ℝ) (hs : 0<s) (ht : 0<t) (d : FamilyBound (σ a) ζ v g s)
      (r : FamilyBound (τ a)⁻¹ ζ v γ t) : FamilyBound (σ a) ζ v g (Bootstrap.stripExponent (1-alpha b g) s t) := by
    intro k
    simpa only [Bootstrap.stripExponent,StripProof.stripGain,min_def,b] using
      StripProof.equal_rate_angular_conjugate σ τ a hb rate hg hg1 hs ht w hw k (d k) (r (k+1))
  have back (s t : ℝ) (hs : 0<s) (ht : 0<t) (r : FamilyBound (τ a)⁻¹ ζ v γ s)
      (d : FamilyBound (σ a) ζ v g t) : FamilyBound (τ a)⁻¹ ζ v γ (Bootstrap.stripExponent (alpha b g) s t) := by
    intro k
    have hh := StripProof.equal_rate_angular_conjugate τ σ (a⁻¹) (nrev ▸ hb) rr (nrev ▸ revAdm) hγ1 hs ht w' hwr k
      (by simpa only [map_inv₀] using r k)
      (by simpa only [map_inv₀,bd,invol,inv_inv] using d (k+1))
    rw [nrev,show alpha b γ=1-alpha b g from alpha_dual hb gp,sub_sub_cancel] at hh
    simpa only [map_inv₀,Bootstrap.stripExponent,StripProof.stripGain,min_def] using hh
  have both := Bootstrap.equalRateClosure Bootstrap.realArchimedeanIncrements hA.1 hA.2
    (FamilyBound (σ a) ζ v g) (FamilyBound (τ a)⁻¹ ζ v γ) (strict_family.mpr seed) (strict_family.mpr seedR)
    (fun s t hs _ ht _ x y ↦ strict_family.mpr (step s t hs ht (strict_family.mp x) (strict_family.mp y)))
    (fun s t hs _ ht _ y x ↦ strict_family.mpr (back s t hs ht (strict_family.mp y) (strict_family.mp x)))
  exact ⟨strict_family.mp both.1,strict_family.mp both.2⟩

end Weierstrass.ConjugatePair
