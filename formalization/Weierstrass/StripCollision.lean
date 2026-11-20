module

public import Weierstrass.StripBand

/-! # From Fejér collisions to directional Fourier bands -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Weierstrass.StripProof

def project (s θ : ℝ) (p : Plane) : ℝ := s+p.2+θ*p.1

def collision (μ ν : Measure Plane) (s t θ d : ℝ) : ℝ :=
  (μ.prod ν).real {p | |project s θ p.1 - project t θ p.2| ≤ d}

def integers (N : ℕ) := Finset.Icc (-(N:ℤ)) (N:ℤ)

private theorem proj_fourier (μ : Measure Plane) (s θ : ℝ) (k : ℤ) :
    ‖coefficient μ (project s θ) k‖ = ‖fourier μ (ray k θ)‖ := by
  have H (p : Plane) : character ((k:ℝ)*project s θ p) =
      character (k*s)*character (dot p (ray k θ)) := by
    rw [← character_add]; congr 1; simp [project,dot,ray]; ring
  simp only [coefficient,H,integral_const_mul,norm_mul,norm_character,one_mul,fourier]

private theorem fejer_count {N : ℕ} (P : ℤ → ℝ) (hP : ∀ k, 0 ≤ P k) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, P ((a:ℤ)-b) ≤
      N * ∑ k ∈ integers N, P k := by
  classical
  calc
    _ ≤ ∑ _a ∈ Finset.range N, ∑ k ∈ integers N, P k := by
      apply Finset.sum_le_sum; intro a ha
      let f := fun b : ℕ => (a:ℤ)-b
      have inj : Function.Injective f := by intro x y e; dsimp [f] at e; omega
      have sub : (Finset.range N).image f ⊆ integers N := by
        intro k hk
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
        apply Finset.mem_Icc.mpr
        have := Finset.mem_range.mp ha; have := Finset.mem_range.mp hb
        dsimp [f]; omega
      rw [← Finset.sum_image (f := P) inj.injOn]
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun k _ _ => hP k)
    _ = _ := by simp

/-- A pair of translated physical strip projections at a fixed direction, with exactly one
factor N⁻¹ remaining after collecting equal frequencies in the Fejér kernel. -/
theorem collision_fourier (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s t θ : ℝ) {d : ℝ} {N : ℕ} (hN : 0 < N) (hd : (N:ℝ)*d ≤ 1) :
    collision μ ν s t θ d ≤ (2/N) * ∑ k ∈ integers N,
      (‖fourier μ (ray k θ)‖^2 + ‖fourier ν (ray k θ)‖^2) := by
  let P := fun k : ℤ => (‖fourier μ (ray k θ)‖^2 + ‖fourier ν (ray k θ)‖^2)/2
  have hf (r : ℝ) : Measurable (project r θ) := by unfold project; fun_prop
  have HH := projected_collision_le μ ν (hf s) (hf t) hd
  have h (a b : ℕ) (m : Measure Plane) (r : ℝ) : ‖coefficient m (project r θ) ((a:ℝ)-b)‖ =
      ‖fourier m (ray ((a:ℤ)-b) θ)‖ := by simpa using proj_fourier m r θ ((a:ℤ)-b)
  simp_rw [h] at HH
  have K := HH.trans (fejer_count P (by intro k; dsimp [P]; positivity))
  unfold P at K
  rw [← Finset.sum_div] at K
  change (N:ℝ)^2/4 * collision μ ν s t θ d ≤ _ at K
  have npos : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [div_mul_eq_mul_div,(le_div_iff₀ npos)]
  apply (mul_le_mul_iff_of_pos_left npos).mp
  nlinarith only [K]

def radialEnergy (μ : Measure Plane) (σ : Measure ℝ) (k : ℤ) : ℝ :=
  ∫ θ, ‖fourier μ (ray k θ)‖^2 ∂σ

theorem radialEnergy_nonneg (μ : Measure Plane) (σ : Measure ℝ) (k : ℤ) :
    0 ≤ radialEnergy μ σ k := integral_nonneg fun _ => sq_nonneg _

private theorem integrable_ray (μ : Measure Plane) (σ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ] (k : ℤ) :
    Integrable (fun θ => ‖fourier μ (ray k θ)‖^2) σ :=
  (integrable_const ((μ.real univ)^2)).mono' (((measurable_fourier μ).comp (measurable_ray k)).norm.pow_const
    2).aestronglyMeasurable (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (fourier_bound _ _) _)

/-- The averaged mixed collision, for different strip measures and arbitrary strip indices. -/
theorem mean_collision_fourier (μ ν : Measure Plane) (σ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure σ] (s t : ℝ) {d : ℝ}
    {N : ℕ} (hN : 0 < N) (hd : (N:ℝ)*d ≤ 1) :
    ∫ θ, collision μ ν s t θ d ∂σ ≤ (2/N) *
      ((∑ k ∈ integers N, radialEnergy μ σ k) + ∑ k ∈ integers N, radialEnergy ν σ k) := by
  let H := fun (k : ℤ) (θ : ℝ) => ‖fourier μ (ray k θ)‖^2+‖fourier ν (ray k θ)‖^2
  have hi (k : ℤ) : Integrable (H k) σ := (integrable_ray μ σ _).add (integrable_ray ν σ _)
  calc
    _ ≤ ∫ θ, (2/N)* ∑ k ∈ integers N, H k θ ∂σ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => measureReal_nonneg)
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul _)
        (ae_of_all _ fun θ => collision_fourier μ ν s t θ hN hd)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k),← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl; intro k _
      exact integral_add (integrable_ray μ σ k) (integrable_ray ν σ k)

end Weierstrass.StripProof
