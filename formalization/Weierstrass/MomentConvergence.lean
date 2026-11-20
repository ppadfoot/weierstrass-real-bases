module

public import Weierstrass.ConcentrationLimit
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! A moment-to-concentration theorem used for the critical, weighted blocks.
Only the limiting law needs an exponential moment at each real parameter. -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology BigOperators ENNReal Nat
namespace Weierstrass.CriticalRay

def expPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N+1), ((k.factorial:ℂ)⁻¹)*((t:ℂ)*I)^k

/-- Global imaginary-axis remainder. It has no exponential growth in the sample
value, so finite polynomial moments suffice for the approximating measures. -/
theorem imaginary_exp_remainder (N : ℕ) (t : ℝ) :
    ‖Complex.exp ((t:ℂ)*I)-expPolynomial N t‖ ≤ |t|^(N+1)/(N.factorial:ℝ) := by
  let c := (t:ℂ)*I
  let f (s : ℝ) := Complex.exp (c*(s:ℂ))
  have hder (s : ℝ) : HasDerivAt f (c*f s) s := by
    simpa [f,mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x:=s)).const_mul c).cexp
  have allD (k : ℕ) : iteratedDeriv k f = fun s ↦ c^k*f s := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext s
      simpa [pow_succ,mul_assoc] using ((hder s).const_mul (c^k)).deriv
  have smooth (k : ℕ) : ContDiff ℝ k f := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  let J := Icc (0:ℝ) 1
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc zero_lt_one
  have within (k : ℕ) (s : ℝ) (hs : s ∈ J) : iteratedDerivWithin k f J s = c^k*f s := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hJ (smooth k).contDiffAt hs,allD]
  have un (s : ℝ) : ‖f s‖ = 1 := by
    change ‖Complex.exp ((t*I)*s)‖ = _
    rw [show (t*I)*s = (↑(t*s):ℂ)*I by push_cast; ring,Complex.norm_exp_ofReal_mul_I]
  have bd := taylor_mean_remainder_bound (a:=0) (b:=1) (x:=1) (n:=N) (C:=|t|^(N+1))
    zero_le_one (smooth (N+1)).contDiffOn (right_mem_Icc.mpr zero_le_one)
    (fun s hs ↦ by rw [within _ s hs,norm_mul,un,mul_one,norm_pow]; simp [c])
  have poly : taylorWithinEval f N J 0 1 = expPolynomial N t := by
    rw [taylor_within_apply,expPolynomial]
    apply Finset.sum_congr rfl
    intro k _
    rw [within _ 0 (left_mem_Icc.mpr zero_le_one)]
    simp [f,c,Complex.real_smul]
  change ‖f 1-taylorWithinEval f N J 0 1‖ ≤ _ at bd
  rw [poly] at bd
  simpa [f,c] using bd

private def momentPolynomial (μ : Measure ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N+1), (k.factorial:ℂ)⁻¹*((t:ℂ)*I)^k*↑(∫ x : ℝ, x^k ∂μ)

private theorem integrated_polynomial {μ : Measure ℝ} (finite : ∀ k : ℕ, Integrable (fun x : ℝ ↦ x^k) μ)
    (N : ℕ) (t : ℝ) : ∫ x : ℝ, expPolynomial N (t*x) ∂μ = momentPolynomial μ N t := by
  let A (k : ℕ) := (k.factorial:ℂ)⁻¹*((t:ℂ)*I)^k
  have rep (x : ℝ) : expPolynomial N (t*x) = ∑ k ∈ Finset.range (N+1), A k*(↑(x^k):ℂ) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [A]
    push_cast
    rw [show (t:ℂ)*x*I = ((t:ℂ)*I)*x by ring,mul_pow]
    ring
  simp_rw [rep]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul,integral_complex_ofReal]
  · intro k _
    exact (Complex.ofRealCLM.integrable_comp (finite k)).const_mul _

private theorem integrated_remainder {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (finite : ∀ k : ℕ, Integrable (fun x : ℝ ↦ x^k) μ) (m : ℕ) (t : ℝ) :
    let N := 2*m+1
    ‖charFun μ t - momentPolynomial μ N t‖ ≤
      (|t|^(N+1)/(N.factorial:ℝ)) * (∫ x : ℝ, x^(N+1) ∂μ) := by
  let N := 2*m+1
  let c := |t|^(N+1)/(N.factorial:ℝ)
  let F (x : ℝ) := Complex.exp (↑(t*x)*I)
  let P (x : ℝ) := expPolynomial N (t*x)
  have each (x : ℝ) : ‖F x-P x‖ ≤ c*x^(N+1) := by
    have p := imaginary_exp_remainder N (t*x)
    have h : |x|^(N+1) = x^(N+1) := by
      rw [←abs_pow,abs_of_nonneg (Even.pow_nonneg (show Even (N+1) from ⟨m+1,by dsimp [N]; omega⟩) _)]
    rw [abs_mul,mul_pow,h] at p
    exact p.trans_eq (by unfold c; ring)
  have intF : Integrable F μ := by
    apply Integrable.of_bound (C:=1)
    · dsimp [F]; fun_prop
    · exact .of_forall fun x ↦ (Complex.norm_exp_ofReal_mul_I _).le
  have intP : Integrable P μ := by
    apply integrable_finsetSum
    intro k _
    have eq (x : ℝ) : ((k.factorial:ℂ)⁻¹ * (↑(t*x)*I)^k) =
        ((k.factorial:ℂ)⁻¹*((t:ℂ)*I)^k)*(↑(x^k):ℂ) := by
      push_cast
      rw [show (t:ℂ)*x*I = ((t:ℂ)*I)*x by ring,mul_pow]
      ring
    simp_rw [eq]
    exact (Complex.ofRealCLM.integrable_comp (finite k)).const_mul _
  change ‖charFun μ t - momentPolynomial μ N t‖ ≤ c*_
  rw [charFun_apply_real, ← integrated_polynomial finite N t]
  simp_rw [← Complex.ofReal_mul]
  change ‖(∫ x, F x ∂μ)-(∫ x, P x ∂μ)‖ ≤ c*_
  rw [← integral_sub intF intP, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((finite _).const_mul c) (.of_forall each)

private theorem gaussian_remainder_vanishes (t : ℝ) :
    let N (m : ℕ) := 2*m+1
    Tendsto (fun m ↦ (|t|^(N m+1)/((N m).factorial:ℝ))*
      (∫ x : ℝ, x^(N m+1) ∂gaussianReal 0 1)) atTop (𝓝 0) := by
  let N (m : ℕ) := 2*m+1
  let ν := gaussianReal 0 1
  let u (x : ℝ) := |t| * |x|
  let f (m : ℕ) (x : ℝ) := u x * ((u x)^(N m)/((N m).factorial:ℝ))
  let B (x : ℝ) := Real.exp ((2*|t|)*|x|)
  have intB : Integrable B ν := integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (2*|t|)) (integrable_exp_mul_gaussianReal _)
  have hu (x : ℝ) : 0 ≤ u x := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have bound (m : ℕ) : ∀ᵐ x ∂ν, ‖f m x‖ ≤ B x := by
    apply Eventually.of_forall
    intro x
    have hp := Real.pow_div_factorial_le_exp (u x) (hu x) (N m)
    have hu' := Real.add_one_le_exp (u x)
    have bd := mul_le_mul (show u x ≤ Real.exp (u x) by linarith only [hu']) hp
      (div_nonneg (pow_nonneg (hu x) _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
    change ‖u x*(u x^(N m)/((N m).factorial:ℝ))‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply bd.trans_eq
    rw [←Real.exp_add]
    congr 1
    dsimp [u]; ring
  have growth : Tendsto N atTop atTop := tendsto_atTop_mono (fun m ↦ (show m ≤ N m by dsimp [N]; omega)) tendsto_id
  have cv (x : ℝ) : Tendsto (fun m ↦ f m x) atTop (𝓝 0) := by
    have cv' := ((Real.summable_pow_div_factorial (u x)).tendsto_atTop_zero.comp growth).const_mul (u x)
    simpa only [f,Function.comp_apply,mul_zero] using cv'
  have dec := tendsto_integral_of_dominated_convergence (μ:=ν) (F:=f) (f:=fun _ ↦ (0:ℝ)) B
    (fun m ↦ by dsimp [f,u]; fun_prop) intB bound (.of_forall cv)
  simp only [integral_zero] at dec
  apply dec.congr
  intro m
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have p : |x|^(N m+1) = x^(N m+1) := by
    rw [←abs_pow,abs_of_nonneg (Even.pow_nonneg (show Even (N m+1) from ⟨m+1,by dsimp [N]; omega⟩) x)]
  change u x*((u x)^(N m)/((N m).factorial:ℝ)) = _
  rw [show u x*((u x)^(N m)/((N m).factorial:ℝ)) = (|t| * |x|)^(N m+1)/((N m).factorial:ℝ) by
    rw [pow_succ]; dsimp [u]; ring,mul_pow,p]
  ring

/-- The method of moments for the standard normal law, without any uniform
exponential-integrability assumption on the approximating laws. -/
theorem weak_gaussian_of_moments (ν : ℕ → ProbabilityMeasure ℝ)
    (finite : ∀ j k : ℕ, Integrable (fun x : ℝ ↦ x^k) (ν j : Measure ℝ))
    (mom : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x : ℝ, x^k ∂(ν j : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x^k ∂gaussianReal 0 1))) :
    Tendsto ν atTop (𝓝 (⟨gaussianReal 0 1,inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  let γ := gaussianReal 0 1
  have gfinite (k : ℕ) : Integrable (fun x : ℝ ↦ x^k) γ := by
    have norm := (memLp_id_gaussianReal' (μ:=0) (v:=1) (k:ℝ≥0∞) (by simp)).integrable_norm_pow' (p:=k)
    exact norm.mono' (by fun_prop) (.of_forall fun x ↦ (norm_pow x k).le)
  have pol (N : ℕ) : Tendsto (fun j ↦ momentPolynomial (ν j) N t) atTop (𝓝 (momentPolynomial γ N t)) := by
    apply tendsto_finsetSum
    intro k _
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (mom k)).const_mul _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have e : 0 < ε/5 := by positivity
  obtain ⟨m,hm⟩ := ((gaussian_remainder_vanishes t).eventually_lt_const e).exists
  let N := 2*m+1
  let C := |t|^(N+1)/(N.factorial:ℝ)
  let R := C*(∫ x : ℝ, x^(N+1) ∂γ)
  change R < ε/5 at hm
  have rem := ((mom (N+1)).const_mul C).eventually_lt_const (show R < 2*(ε/5) by linarith)
  have vals := Metric.tendsto_nhds.mp (pol N) (ε/5) e
  filter_upwards [rem,vals] with j hj hp
  have b₁ := integrated_remainder (finite j) m t
  have b₂ := integrated_remainder gfinite m t
  change ‖charFun (ν j) t-momentPolynomial (ν j) N t‖ ≤ C*_ at b₁
  change ‖charFun γ t-momentPolynomial γ N t‖ ≤ R at b₂
  change dist (charFun (ν j) t) (charFun γ t) < ε
  rw [←dist_eq_norm] at b₁ b₂
  have tr₁ := dist_triangle (charFun (ν j) t) (momentPolynomial (ν j) N t) (charFun γ t)
  have tr₂ := dist_triangle (momentPolynomial (ν j) N t) (momentPolynomial γ N t) (charFun γ t)
  rw [dist_comm (charFun γ t) _] at b₂
  linarith only [tr₁,tr₂,b₁,b₂,hp,hj,hm,e]

/-- Uniform interval anticoncentration for any sequence converging in moments
to the standard normal, including moving centers and non-monotone widths. -/
theorem shrinking_band_of_gaussian_moments (ν : ℕ → ProbabilityMeasure ℝ)
    (finite : ∀ j k : ℕ, Integrable (fun x : ℝ ↦ x^k) (ν j : Measure ℝ))
    (mom : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x : ℝ, x^k ∂(ν j : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x^k ∂gaussianReal 0 1))) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      (ν j : Measure ℝ).real (Icc (v-r j) (v+r j)) < ε := by
  apply shrinking_band_of_weak (weak_gaussian_of_moments ν finite mom) _ hr
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact fun x ↦ measure_singleton (μ:=gaussianReal 0 1) x

end Weierstrass.CriticalRay
