module

public import Weierstrass.StripSieve

/-! # Single-mesh directional band law and its projection energy -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Weierstrass.StripProof

/-- Extending a one-mesh direction bound to larger intervals costs only their length
divided by the mesh. Endpoints may carry atoms. -/
theorem interval_from_mesh (σ : Measure ℝ) [IsFiniteMeasure σ] {l A : ℝ}
    (hl : 0 < l) (hσ : ∀ x, σ.real (Icc x (x+l)) ≤ A) (x : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    σ.real (Icc x (x+w)) ≤ (w/l+2)*A := by
  have hA : 0 ≤ A := measureReal_nonneg.trans (hσ 0)
  have aux (n : ℕ) : σ.real (Icc x (x+(n+1:ℝ)*l)) ≤ (n+1:ℝ)*A := by
    induction n with
    | zero => simpa using hσ x
    | succ n ih =>
      let y := x+(n+1:ℝ)*l
      have inc : Icc x (x+((n+1:ℕ)+1:ℝ)*l) ⊆ Icc x y ∪ Icc y (y+l) := by
        intro t ht; by_cases hh : t ≤ y
        · exact Or.inl ⟨ht.1,hh⟩
        · refine Or.inr ⟨le_of_not_ge hh,?_⟩
          dsimp [y]; push_cast at ht; linarith [ht.2]
      calc
        _ ≤ σ.real (Icc x y ∪ Icc y (y+l)) := measureReal_mono inc
        _ ≤ σ.real (Icc x y) + σ.real (Icc y (y+l)) := measureReal_union_le _ _
        _ ≤ (n+1:ℝ)*A + A := add_le_add ih (hσ y)
        _ = _ := by push_cast; ring
  let n := ⌈w/l⌉₊
  have hn : w/l ≤ n := Nat.le_ceil _
  have hle : w ≤ (n+1:ℝ)*l := by have := (div_le_iff₀ hl).mp hn; linarith
  have hsm : (n : ℝ) < w/l+1 := Nat.ceil_lt_add_one (div_nonneg hw hl.le)
  exact (measureReal_mono (Icc_subset_Icc le_rfl (by linarith))).trans ((aux n).trans
    (mul_le_mul_of_nonneg_right (by linarith) hA))

/-- Integer radial frequencies in direction θ. -/
def ray (k : ℤ) (θ : ℝ) : Plane := (k*θ,k)

theorem measurable_ray (k : ℤ) : Measurable (ray k) := by unfold ray; fun_prop

def bandLaw (σ : Measure ℝ) (J : Finset ℤ) : Measure Plane := ∑ k ∈ J, σ.map (ray k)

instance (σ : Measure ℝ) [IsFiniteMeasure σ] (J : Finset ℤ) : IsFiniteMeasure (bandLaw σ J) := by
  unfold bandLaw; infer_instance

/-- The angular law and radial spacing imply a unit-square mass bound for the
singular image measure of the band. -/
theorem band_unit_box (σ : Measure ℝ) [IsFiniteMeasure σ] (J : Finset ℤ) {l q A : ℝ}
    (hl : 0 < l) (hq : 0 < q) (hfreq : ∀ k ∈ J, q ≤ |(k:ℝ)|)
    (hσ : ∀ x, σ.real (Icc x (x+l)) ≤ A) (z : Plane) :
    (bandLaw σ J).real (box z 1) ≤ 3*(2/(q*l)+2)*A := by
  classical
  let H := fun k => (σ.map (ray k)).real (box z 1)
  let T := Finset.Icc (⌊z.2⌋-1) (⌊z.2⌋+1)
  have eqsum : (bandLaw σ J).real (box z 1) = ∑ k ∈ J, H k := by
    simp only [bandLaw,H,measureReal_def,Measure.finsetSum_apply]
    exact ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)
  have supp (k : ℤ) (hk : k ∉ T) : H k = 0 := by
    have fl := Int.floor_le z.2
    have fr := Int.lt_floor_add_one z.2
    have hnot : (k:ℝ) ∉ Icc (z.2-1) (z.2+1) := by
      rintro ⟨a,b⟩; apply hk
      apply Finset.mem_Icc.mpr
      have ha : (⌊z.2⌋:ℝ)-1 ≤ k := by linarith
      have hb : (k:ℝ) < (⌊z.2⌋:ℝ)+2 := by linarith
      have hh : k < ⌊z.2⌋+2 := by exact_mod_cast hb
      exact ⟨by exact_mod_cast ha, by omega⟩
    dsimp [H]; rw [map_measureReal_apply (measurable_ray _) (measurable_box _ _)]
    rw [show ray k ⁻¹' box z 1 = ∅ from eq_empty_iff_forall_notMem.mpr fun _ hh => hnot hh.2]
    exact measureReal_empty
  have per (k : ℤ) (hk : k ∈ J) : H k ≤ (2/(q*l)+2)*A := by
    have hab := hfreq k hk
    have hp : 0 < |(k:ℝ)| := hq.trans_le hab
    have kn : (k:ℝ) ≠ 0 := abs_pos.mp hp
    have area : (ray k ⁻¹' box z 1) ⊆ Icc (z.1/k-1/q) (z.1/k-1/q+2/q) := by
      intro t ht
      have h1 : z.1-1 ≤ (k:ℝ)*t := ht.1.1
      have h2 : (k:ℝ)*t ≤ z.1+1 := ht.1.2
      have ht' : |(k:ℝ)*(t-z.1/k)| ≤ 1 := by
        rw [mul_sub, show (k:ℝ)*(z.1/k)=z.1 by field_simp]; exact abs_le.mpr ⟨by linarith,by linarith⟩
      rw [abs_mul] at ht'
      have hc : |t-z.1/k| ≤ 1/q := (le_div_iff₀ hq).mpr
        ((mul_le_mul_of_nonneg_left hab (abs_nonneg _)).trans (by linarith [ht']))
      rcases abs_le.mp hc with ⟨a,b⟩
      rw [show (2:ℝ)/q=1/q+1/q by ring]; constructor <;> linarith
    have hi := interval_from_mesh σ hl hσ (z.1/k-1/q) (show 0 ≤ 2/q by positivity)
    rw [div_div] at hi
    exact (le_of_eq (map_measureReal_apply (measurable_ray _) (measurable_box _ _))).trans
      ((measureReal_mono area).trans hi)
  rw [eqsum,← Finset.sum_filter_of_ne (s := J) (p := fun k => k ∈ T) (fun k _ hk => by
    by_contra hn; exact hk (supp k hn))]
  have hA : 0 ≤ A := measureReal_nonneg.trans (hσ 0)
  calc
    _ ≤ ∑ _k ∈ J.filter (· ∈ T), (2/(q*l)+2)*A :=
      Finset.sum_le_sum fun k hk => per k (Finset.mem_filter.mp hk).1
    _ = ((J.filter (· ∈ T)).card : ℝ) * ((2/(q*l)+2)*A) := by simp
    _ ≤ (T.card:ℝ) * ((2/(q*l)+2)*A) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (show J.filter (· ∈ T) ⊆ T from fun _ h => (Finset.mem_filter.mp h).2))
      (by positivity)
    _ = _ := by
      have hc : T.card = 3 := by dsimp [T]; rw [Int.card_Icc]; omega
      rw [hc]; push_cast; ring

/-- Fourier energy along the actual projections in a finite radial band. The direction law
is tested on length-l intervals and the physical law on radius-l squares, precisely the
two geometric inputs B3 and B4. -/
theorem directional_band_energy (μ : Measure Plane) (σ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ] (J : Finset ℤ) {l q T S A B : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) (hq : 0 < q) (hT : 1 ≤ T)
    (hfreq : ∀ k ∈ J, q ≤ |(k:ℝ)| ∧ |(k:ℝ)| ≤ l⁻¹)
    (hθ : ∀ᵐ θ ∂σ, |θ| ≤ T) (hσ : ∀ x, σ.real (Icc x (x+l)) ≤ A)
    (hp : ∀ᵐ p ∂μ, p ∈ box 0 S) (hμ : ∀ z, μ.real (box z l) ≤ B) :
    ∑ k ∈ J, ∫ θ, ‖fourier μ (ray k θ)‖^2 ∂σ ≤
      8*Real.exp (2+2*S^2)*Real.pi^2*(T/l)^2*(3*(2/(q*l)+2)*A)*B*μ.real univ := by
  let R := T/l
  have hR : 1 ≤ R := (le_div_iff₀ hl).mpr (by linarith)
  have hs : ∀ᵐ u ∂bandLaw σ J, u ∈ box 0 R := by
    unfold bandLaw
    rw [ae_finsetSum_measure_iff]
    intro k hk
    apply (ae_map_iff (measurable_ray k).aemeasurable (measurable_box 0 R)).mpr
    filter_upwards [hθ] with θ hθ
    have hk' := (hfreq k hk).2
    have hmag : |(k:ℝ)*θ| ≤ R := by
      rw [abs_mul]; exact (mul_le_mul hk' hθ (abs_nonneg _) (inv_nonneg.mpr hl.le)).trans_eq
        (by dsimp [R]; ring)
    have hmag2 : |(k:ℝ)| ≤ R := hk'.trans (by dsimp [R]; rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hl])
    exact ⟨by simpa [ray] using abs_le.mp hmag,by simpa [ray] using abs_le.mp hmag2⟩
  have hb (z : Plane) : μ.real (box z R⁻¹) ≤ B := by
    apply (measureReal_mono (s₂ := box z l) ?_).trans (hμ z)
    have sm : R⁻¹ ≤ l := by dsimp [R]; rw [inv_div]; exact (div_le_iff₀ (by linarith)).mpr (by nlinarith)
    intro p pp; rcases pp with ⟨⟨x,y⟩,a,b⟩
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  have H := band_energy μ (bandLaw σ J) hR hs (band_unit_box σ J hl hq (fun k hk => (hfreq k hk).1) hσ)
    hp hb
  have iF (k : ℤ) : Integrable (fun u => ‖fourier μ u‖^2) (σ.map (ray k)) :=
    (integrable_const ((μ.real univ)^2)).mono' ((measurable_fourier μ).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (fourier_bound _ _) _)
  unfold bandLaw at H
  rw [integral_finsetSum_measure (fun k _ => iF k)] at H
  simpa only [integral_map (measurable_ray _).aemeasurable
    ((measurable_fourier μ).norm.pow_const 2).aestronglyMeasurable] using H

end Weierstrass.StripProof
