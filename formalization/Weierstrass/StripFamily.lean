module

public import Weierstrass.StripEstimate

/-! # The full finite strip-family estimate B5 -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Weierstrass.StripProof

private theorem collision_vanishes (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S T s u θ d : ℝ} (hd : d ≤ 1) (hθ : |θ| ≤ T)
    (hm : ∀ᵐ p ∂μ, p ∈ box 0 S) (hn : ∀ᵐ p ∂ν, p ∈ box 0 S)
    (hfar : 1+2*S*(1+T) < |s-u|) : collision μ ν s u θ d = 0 := by
  have hb (p : Plane) (hp : p ∈ box 0 S) : |p.2 + θ*p.1| ≤ S*(1+T) := by
    have h1 : |p.1| ≤ S := abs_le.mpr (by simpa using hp.1)
    have h2 : |p.2| ≤ S := abs_le.mpr (by simpa using hp.2)
    calc
      _ ≤ |p.2|+|θ*p.1| := abs_add_le _ _
      _ ≤ S+T*S := by rw [abs_mul]; exact add_le_add h2 (mul_le_mul hθ h1 (abs_nonneg _) ((abs_nonneg _).trans hθ))
      _ = _ := by ring
  let C : Set (Plane × Plane) := {p | |project s θ p.1 - project u θ p.2| ≤ d}
  have outside : ∀ᵐ p ∂μ.prod ν, p ∉ C := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (ν := ν)).ae hm,(Measure.quasiMeasurePreserving_snd (μ := μ)).ae hn] with p h1 h2
    intro hc
    have hp := abs_le.mp (hb p.1 h1)
    have hq := abs_le.mp (hb p.2 h2)
    have hc' : |project s θ p.1-project u θ p.2| ≤ d := hc
    obtain ⟨a,b⟩ := abs_le.mp hc'
    unfold project at a b
    have near : |s-u| ≤ 1+2*S*(1+T) := abs_le.mpr ⟨by linarith,by linarith⟩
    exact hfar.not_ge near
  have nul : (μ.prod ν) C = 0 := by simpa using ae_iff.mp outside
  change ((μ.prod ν) C).toReal = 0
  rw [nul,ENNReal.toReal_zero]

/-- **B3 and B4 imply B5.** The bound is independent of the number of nonempty
strips. L bounds the interaction range of their integer offsets from the common
physical support and the direction support. -/
theorem strip_estimate (I : Finset ℤ) (μ : ℤ → Measure Plane) (σ : Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure σ]
    {d S T A B D t : ℝ} {J L : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hJ : 0 < J) (hT : 1 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 1+2*S*(1+T) ≤ L)
    (hσmass : σ.real univ ≤ 1) (htotal : ∑ i ∈ I, (μ i).real univ ≤ 1)
    (hmass : ∀ i ∈ I, (μ i).real univ ≤ B)
    (hphys : ∀ i ∈ I, ∀ᵐ p ∂μ i, p ∈ box 0 S) (hθ : ∀ᵐ θ ∂σ, |θ| ≤ T)
    (hσ : ∀ j < J, ∀ x, σ.real (Icc x (x+paperMesh d J (j+1))) ≤ A*(paperMesh d J (j+1))^t)
    (hμ : ∀ i ∈ I, ∀ j < J, ∀ z, (μ i).real (box z (paperMesh d J (j+1))) ≤ B*(paperMesh d J (j+1))^D) :
    ∑ i ∈ I, ∑ k ∈ I, ∫ θ, collision (μ i) (μ k) i k θ d ∂σ ≤
      (2*(2*L+1)*stripConstant J S T A) * B * d^(min 1 (D+t-1) - 1/J) := by
  classical
  let M := fun i => (μ i).real univ
  let F := fun i k => ∫ θ, collision (μ i) (μ k) i k θ d ∂σ
  let C := stripConstant J S T A * d^(min 1 (D+t-1) - 1/J) * B
  let near := fun (i k : ℤ) => |i-k| ≤ (L:ℤ)
  have symmN (i k : ℤ) : near i k ↔ near k i := by dsimp [near]; rw [abs_sub_comm]
  have row (i : ℤ) : ((I.filter (near i)).card:ℝ) ≤ 2*L+1 := by
    have sub : I.filter (near i) ⊆ Finset.Icc (i-L) (i+L) := by
      intro k hk; have hh := abs_le.mp (Finset.mem_filter.mp hk).2
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have card := Finset.card_le_card sub
    rw [Int.card_Icc] at card
    exact_mod_cast (show (I.filter (near i)).card ≤ 2*L+1 by omega)
  have charge (i : ℤ) (hi : i ∈ I) (k : ℤ) (hk : k ∈ I) :
      F i k ≤ (if near i k then C*M i else 0) + (if near k i then C*M k else 0) := by
    by_cases h : near i k
    · rw [if_pos h,if_pos ((symmN i k).mp h),← mul_add]
      exact pair_strip_estimate (μ i) (μ k) σ hd hd1 hJ hT hA hB hσmass (hmass _ hi)
        (hmass _ hk) (hphys _ hi) (hphys _ hk) hθ hσ (hμ _ hi) (hμ _ hk) _ _
    · rw [if_neg h,if_neg (fun hh => h ((symmN i k).mpr hh)),zero_add]
      have far : (L:ℝ) < |(i:ℝ)-(k:ℝ)| := by exact_mod_cast (lt_of_not_ge h)
      have hz : F i k = 0 := integral_eq_zero_of_ae (hθ.mono fun θ hθ' =>
        collision_vanishes _ _ hd1 hθ' (hphys _ hi) (hphys _ hk) (hL.trans_lt far))
      exact hz.le
  have Cpos : 0 ≤ C := by dsimp [C,stripConstant]; positivity
  have one (i : ℤ) : ∑ k ∈ I, (if near i k then C*M i else 0) ≤ (2*L+1)*(C*M i) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (row i) (mul_nonneg Cpos measureReal_nonneg)
  have single : ∑ i ∈ I, ∑ k ∈ I, (if near i k then C*M i else 0) ≤ (2*L+1)*C := by
    apply (Finset.sum_le_sum (fun i _ => one i)).trans
    simp_rw [← mul_assoc,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ (2*(L:ℝ)+1)*C)).trans_eq (mul_one _)
  apply (Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun k hk => charge i hi k hk))).trans
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i k => if near k i then C*M k else 0)]
  apply (add_le_add single single).trans_eq
  dsimp [C]; ring

end Weierstrass.StripProof
