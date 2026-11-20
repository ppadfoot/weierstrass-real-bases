module

public import Weierstrass.SeedOverlap

/-! The anchored exponent 1/2 of §3, with all Haar translates, all prescribed
weights of the stated family and all positive radii. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex Weierstrass.CriticalRay
open scoped BigOperators Topology ENNReal
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def GoodWeight (D : ℕ) (δ : ℝ) (c d e : ℤ → ℝ) : Prop :=
  (∀ j, |c j| ≤ 1) ∧ (∀ j, |d j| ≤ 1) ∧ (∀ j, |e j| ≤ 1) ∧
  ∀ m : ℕ, ∃ k : Fin D, δ ≤ |(c (m+k.val:ℕ)*d (m+k.val:ℕ))*e (m+k.val:ℕ)|

private theorem cost_shrinks {h : ℝ} (hh : h < 1/2) (T A κ : ℝ) (N : ℕ) :
    Tendsto (fun r : ℝ ↦ (9*(1+2*T)*(1+2*T)/(r^h)^2)*N*(4*(A*r)/κ))
      (𝓝[>] 0) (𝓝 0) := by
  let C := 9*(1+2*T)*(1+2*T)*N*(4*A/κ)
  have ep : 0 < 1-2*h := by linarith
  have lim := ((Real.continuousAt_rpow_const 0 (1-2*h) (.inr ep.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s:=Ioi 0))).const_mul C
  rw [Real.zero_rpow ep.ne',mul_zero] at lim
  apply lim.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.rpow_sub hr,Real.rpow_one,show 2*h=h*(2:ℕ) by ring,Real.rpow_mul_natCast hr.le]
  dsimp only [C];ring

/-- Pair estimates tend to zero uniformly over the entire nondegenerate
profile family for every fixed pair of different transverse translations. -/
theorem pair_vanish {B : ℂ} (hb : 1 < ‖B‖) {g ρ δ : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hq : 1 < ‖B‖*g) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (hQ : (‖B‖*g)*ρ < 1) (hbQ : 1 < ((‖B‖*g)*ρ)*‖B‖)
    (hδ : 0 < δ) (D : ℕ) (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] [μ.InnerRegularCompactLTTop]
    {h T A v a b : ℝ} (hh : h < 1/2) (hT : 0 < T) (hA : 0 < A) (hv : 0 < v) (hne : a ≠ b) :
    ∀ᶠ r in 𝓝[>] 0, ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ), GoodWeight D δ c d e →
    (μ.prod inputLaw).real (heavyAt g ρ (c,d) e ω T A r h a ∩ heavyAt g ρ (c,d) e ω T A r h b) ≤ v := by
  let rad (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have cv : Tendsto rad atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n,small⟩ := (uniform_circle_small_derivative hb hq hρ hρ' hQ hbQ hδ D μ a b hne cv
    (half_pos hv)).exists
  have hk : 0 < rad n := by dsimp [rad];positivity
  obtain ⟨s,hs,osc⟩ := uniform_slope_modulus (zero_lt_one.trans hb) hg hq hρ hQ a b (half_pos hk)
  obtain ⟨N,hN⟩ := exists_nat_ge (1/s)
  have cov : 1 ≤ N*s := (div_le_iff₀ hs).mp hN
  have limit := cost_shrinks hh T A (rad n) N
  filter_upwards [limit.eventually_lt_const (half_pos hv),self_mem_nhdsWithin] with r cost (hr : 0 < r)
  intro ω c d e ⟨hc,hd,he,good⟩
  have pair := pair_mass_bound hb hg hg1 hq hρ hQ μ hc hd he ω hT hA hr hk (half_pos hv).le h a b N cov
    (fun z ↦ osc c d e hc hd he ω z.val) (fun t ↦ (small c d e hc hd he good ω t).le)
  linarith only [cost,pair]

/-- The full initial anchored estimate, under the manuscript's (H1) and
finite-window condition (H2). The group containment hypotheses are geometric
and are supplied by the conjugate-embedding and orbit theorems. -/
theorem rayInformation_half {B : ℂ} (hb : 1 < ‖B‖) {g ρ δ : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hq : 1 < ‖B‖*g) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (hQ : (‖B‖*g)*ρ < 1) (hbQ : 1 < ((‖B‖*g)*ρ)*‖B‖)
    (hδ : 0 < δ) (D : ℕ) {P : Set RayParameters}
    (weights : ∀ p ∈ P, (∀ t, transverseOrbit ‖B‖ p.2 t ∈ complexPhaseGroup B) ∧
      ∃ e, GoodWeight D δ p.1 p.2 e ∧ ∀ t, transverseOrbit ρ e t ∈ complexPhaseGroup B) :
    RayInformation B g (1/2) P := by
  classical
  let μ := complexPhaseHaar B
  have : μ.InnerRegularCompactLTTop := by dsimp [μ,complexPhaseHaar];infer_instance
  intro h _ hh T A hT hA ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (half_pos hε)
  let m := n+1
  have hm : 0 < (m:ℝ) := by dsimp [m];positivity
  have mlarge : 1/(m:ℝ) < ε/2 := by simpa [m] using hn
  let v := ε/(2*(m:ℝ))
  have hv : 0 < v := by dsimp [v];positivity
  have perPair (i j : Fin m) : ∀ᶠ r in 𝓝[>] 0, i ≠ j → ∀ (ω : PhaseTorus) (c d e : ℤ → ℝ),
     GoodWeight D δ c d e → (μ.prod inputLaw).real
       (heavyAt g ρ (c,d) e ω T A r h i.val ∩ heavyAt g ρ (c,d) e ω T A r h j.val) ≤ v := by
    by_cases hij : i = j
    · exact .of_forall fun _ no ↦ (no hij).elim
    · have hj : (i.val:ℝ) ≠ (j.val:ℝ) := by exact_mod_cast (fun eq ↦ hij (Fin.ext eq) : i.val ≠ j.val)
      exact (pair_vanish hb hg hg1 hq hρ hρ' hQ hbQ hδ D μ hh hT hA hv hj).mono (fun _ p _ ↦ p)
  have all := eventually_all.mpr (fun i ↦ eventually_all.mpr (perPair i))
  filter_upwards [all] with r hr
  intro ω p hp
  obtain ⟨point,e,good,te⟩ := weights p hp
  let E (i : Fin m) := heavyAt (B:=B) g ρ p e ω T A r h i.val
  let p₀ := μ.real {z : complexPhaseGroup B | ENNReal.ofReal (r^h) < rayOccupation ‖B‖ g p (ω+z.val) T A r}
  have eq (i : Fin m) : (μ.prod inputLaw).real (E i) = p₀ :=
    congrArg ENNReal.toReal (heavyAt_mass μ _ _ p _ ω _ _ _ _ _ point (te _))
  have H := packing_events (μ.prod inputLaw) E (fun _ ↦ heavyAt_meas _ _ _ _ _ _ _ _ _ _)
    hv.le eq (fun i j no ↦ hr i j no ω p.1 p.2 e good) Finset.univ
  simp only [Finset.card_univ,Fintype.card_fin] at H
  change p₀ ≤ ε
  have c : (m:ℝ)^2*v = (m:ℝ)*ε/2 := by dsimp [v];field_simp
  rw [c] at H
  have one := (div_lt_iff₀ hm).mp mlarge
  apply le_of_not_gt
  intro hpe
  nlinarith only [H,one,mul_lt_mul_of_pos_left hpe hm]

end Weierstrass.RaySeed
