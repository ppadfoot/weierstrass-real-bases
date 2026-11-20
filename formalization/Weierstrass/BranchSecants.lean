module

public import Weierstrass.PredecessorProof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The normalized secant of the past of the polynomial Weierstrass solenoid.
Integration over a unit segment removes the removable singularity at zero. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped BigOperators Interval
namespace Weierstrass.Branch

def sineMean (x v : ℝ) := ∫ t in (0:ℝ)..1, Real.sin (x+v*t)

@[simp] theorem sineMean_zero (x : ℝ) : sineMean x 0 = Real.sin x := by simp [sineMean]

theorem sineMean_mul (x v : ℝ) : -v*sineMean x v = Real.cos (x+v)-Real.cos x := by
  have hD (t : ℝ) : HasDerivAt (fun u : ℝ ↦ Real.cos (x+v*u)) (-v*Real.sin (x+v*t)) t := by
    convert ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul v)).cos using 1 <;> simp;ring
  have cI : Continuous (fun t : ℝ ↦ -v*Real.sin (x+v*t)) := by fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (fun u _ ↦ hD u) (cI.intervalIntegrable ..)
  simpa only [sineMean,intervalIntegral.integral_const_mul,mul_one,mul_zero,add_zero] using H

theorem sineMean_bound (x v : ℝ) : |sineMean x v| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
    (fun t _ ↦ (show ‖Real.sin (x+v*t)‖ ≤ 1 from Real.abs_sin_le_one _))
  simpa [sineMean, Real.norm_eq_abs] using h

theorem sineMean_sub (x v : ℝ) : |sineMean x v-Real.sin x| ≤ |v| := by
  have cI : Continuous (fun t : ℝ ↦ Real.sin (x+v*t)) := by fun_prop
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t : ℝ ↦ Real.sin (x+v*t)-Real.sin x)
    (a:=0) (b:=1) (C:=|v|) (fun t ht ↦ by
      have tt : t ∈ Ioc (0:ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using ht
      apply (Real.abs_sin_sub_sin_le _ _).trans
      rw [add_sub_cancel_left,abs_mul,abs_of_pos tt.1];exact mul_le_of_le_one_right (abs_nonneg _) tt.2)
  rw [intervalIntegral.integral_sub (cI.intervalIntegrable ..) intervalIntegrable_const] at H
  simpa [sineMean,Real.norm_eq_abs] using H

/-- Each term is normalized so that at a zero increment the infinite sum is
exactly the conditional slope `codedSlope`, before the factor 2πγ. -/
def secantTerm {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) (k : ℕ) :=
  g^k*sineMean (2*Real.pi*pathState d a a₀ w I (k+1) 0+η k) (2*Real.pi*c^(k+1)*u)

def partialSecant {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) (k : ℕ) :=
  ∑ i ∈ Finset.range k, secantTerm d a a₀ g c w η I u i

def fullSecant {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) :=
  ∑' k, secantTerm d a a₀ g c w η I u k

theorem secant_summable {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ c : ℝ) {g : ℝ} (hg : 0 ≤ g) (h1 : g < 1)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) : Summable (secantTerm d a a₀ g c w η I u) := by
  apply (summable_geometric_of_lt_one hg h1).of_norm_bounded
  intro n
  rw [secantTerm,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hg _)]
  exact mul_le_of_le_one_right (pow_nonneg hg _) (sineMean_bound ..)

theorem secant_remainder {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ c : ℝ) {g : ℝ} (hg : 0 ≤ g) (h1 : g < 1)
    (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) (k : ℕ) :
    |fullSecant d a a₀ g c w η I u-partialSecant d a a₀ g c w η I u k| ≤ (1-g)⁻¹*g^k := by
  have hs := secant_summable d a a₀ c hg h1 w η I u
  unfold fullSecant partialSecant
  rw [←hs.sum_add_tsum_nat_add k,add_sub_cancel_left,←Real.norm_eq_abs]
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hg h1).mul_right (g^k))
  intro j
  rw [secantTerm,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hg _),←pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hg _) (sineMean_bound ..)

theorem secant_prefix_append {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ)
    (I : ℕ → Fin p) (u : ℝ) (n k : ℕ) :
    partialSecant d a a₀ g c w η I u (n+k) = partialSecant d a a₀ g c w η I u n +
      g^n*partialSecant d a a₀ g c (pathState d a a₀ w I n) (fun i ↦ η (n+i)) (fun i ↦ I (n+i)) (c^n*u) k := by
  unfold partialSecant
  rw [Finset.sum_range_add,Finset.mul_sum];congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [secantTerm,pow_add, Nat.add_assoc n i 1,pathState_append]
  ring_nf

theorem secant_offset {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) {g c : ℝ} (hg : 0 ≤ g)
    (h1 : g < 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) (w η : ℕ → ℝ) (I : ℕ → Fin p) (u : ℝ) (k : ℕ) :
    |partialSecant d a a₀ g c w η I u k-partialSecant d a a₀ g c w η I 0 k| ≤
      (1-g)⁻¹*(2*Real.pi*|u|) := by
  unfold partialSecant;rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k, |secantTerm d a a₀ g c w η I u j-secantTerm d a a₀ g c w η I 0 j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j ∈ Finset.range k, g^j*(2*Real.pi*|u|) := by
      apply Finset.sum_le_sum;intro j _
      simp only [secantTerm,mul_zero,sineMean_zero,←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hg _)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hg _)
      apply (sineMean_sub ..).trans
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*c^(j+1))]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hc hc1)) (abs_nonneg _)
    _ ≤ (1-g)⁻¹ * (2*Real.pi*|u|) := by
      rw [←Finset.sum_mul];gcongr
      exact ((summable_geometric_of_lt_one hg h1).sum_le_tsum _ (fun _ _ ↦ pow_nonneg hg _)).trans_eq (hasSum_geometric_of_lt_one hg h1).tsum_eq

theorem partialSecant_zero {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (n : ℕ) :
    partialSecant d a a₀ g c w η I 0 n = truncatedSlope d a a₀ g w η I n := by
  simp [partialSecant,secantTerm,truncatedSlope]

theorem fullSecant_zero {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) :
    fullSecant d a a₀ g c w η I 0 = codedSlope d a a₀ g w η I := by simp [fullSecant,secantTerm,codedSlope]

theorem measurable_sineMean : Measurable (Function.uncurry sineMean) := by
  have eq (v : ℝ × ℝ) : sineMean v.1 v.2 = if v.2=0 then Real.sin v.1 else (Real.cos v.1-Real.cos (v.1+v.2))/v.2 := by
    split
    · rename_i h;rw [h,sineMean_zero]
    · rename_i h;apply (eq_div_iff h).mpr;linarith only [sineMean_mul v.1 v.2]
  change Measurable (fun v : ℝ × ℝ ↦ sineMean v.1 v.2)
  simp_rw [eq];apply Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
  · fun_prop
  · fun_prop

end Weierstrass.Branch
