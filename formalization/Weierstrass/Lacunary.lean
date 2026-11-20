module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Weighted lacunary character averages on translated unit intervals (Appendix A) -/

@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped ComplexConjugate BigOperators Topology ENNReal

namespace Weierstrass.Lacunary

/-- The real frequency `t` is measured in radians. -/
def wave (t x : ℝ) : ℂ := Complex.exp ((t:ℂ)*I*(x:ℂ))

private theorem norm_wave (t x : ℝ) : ‖wave t x‖ = 1 := by
  simp [wave, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem wave_sub (t v x : ℝ) : wave t x * conj (wave v x) = wave (t-v) x := by
  unfold wave
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]; ring

private theorem integral_wave {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ‖∫ x in Ioc u (u+1), wave t x‖ ≤ 2 / |t| := by
  have coeff : (t:ℂ)*I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  rw [← intervalIntegral.integral_of_le (show u ≤ u+1 by linarith)]
  unfold wave
  rw [integral_exp_mul_complex coeff, norm_div, Complex.norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg t)
  apply (norm_sub_le _ _).trans
  change ‖wave t (u+1)‖ + ‖wave t u‖ ≤ 2
  norm_num [norm_wave]

/-- A deterministic unit coefficient can absorb any prescribed phase. -/
def term (D g : ℝ) (w : ℕ → ℂ) (n : ℕ) (x : ℝ) : ℂ := w n * wave (D*g^n) x

def partialSum (D g : ℝ) (w : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, term D g w k x

def average (D g : ℝ) (w : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ := (N:ℂ)⁻¹ * partialSum D g w N x

private theorem catom (D g : ℝ) (w : ℕ → ℂ) (k : ℕ) : Continuous (term D g w k) := by
  unfold term wave; fun_prop

private theorem cpartial (D g : ℝ) (w : ℕ → ℂ) (N : ℕ) : Continuous (partialSum D g w N) := by
  exact continuous_finsetSum _ fun k _ => catom D g w k

/-- An off-diagonal correlation is summably small in the earlier index. -/
private theorem correlation {D g : ℝ} (hD : D ≠ 0) (hg : 1 < g) (u : ℝ)
    (w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ = 1) {k N : ℕ} (hk : k < N) :
    ‖∫ x in Ioc u (u+1), term D g w k x * conj (term D g w N x)‖ ≤
    (2/(|D| *(g-1))) * (g⁻¹)^k := by
  let t := D*g^k - D*g^N
  have hg0 : 0 < g := by linarith
  have hgstep : g^k*g ≤ g^N := by rw [← pow_succ]; exact pow_le_pow_right₀ hg.le hk
  have sep : g^k*(g-1) ≤ g^N-g^k := by linarith
  have pos : 0 < g^N-g^k := lt_of_lt_of_le (by positivity : 0 < g^k*(g-1)) sep
  have t_abs : |t| = |D| *(g^N-g^k) := by
    dsimp [t]; rw [← mul_sub, abs_mul, abs_of_neg (by linarith : g^k-g^N < 0)]; ring
  have ht : t ≠ 0 := abs_pos.mp (t_abs ▸ mul_pos (abs_pos.mpr hD) pos)
  have eq (x : ℝ) : term D g w k x * conj (term D g w N x) =
      (w k*conj (w N))*wave t x := by
    unfold term; rw [map_mul, ← wave_sub]; ring
  simp_rw [eq,integral_const_mul,Complex.norm_mul,Complex.norm_conj,hw,one_mul]
  calc
    _ ≤ 2/|t| := integral_wave ht u
    _ ≤ 2/(|D| *(g^k*(g-1))) := by
      rw [t_abs]; apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left sep (abs_nonneg D)
    _ = _ := by rw [inv_pow]; field_simp [(abs_pos.mpr hD).ne', (sub_pos.mpr hg).ne', hg0.ne']

private theorem norm_term (D g : ℝ) (w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ = 1) (k : ℕ) (x : ℝ) :
    ‖term D g w k x‖ = 1 := by simp [term,hw,norm_wave]

/-- Mean square of the partialSum sum grows at most linearly, uniformly over unit coefficients
and the horizontal origin `u`. -/
theorem partial_mean_square {D g : ℝ} (hD : D ≠ 0) (hg : 1 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℕ → ℂ), (∀ k, ‖w k‖ = 1) → ∀ (u : ℝ) (N : ℕ),
      ∫ x in Ioc u (u+1), ‖partialSum D g w N x‖^2 ≤ C*N := by
  let A := 2/(|D| *(g-1))
  let K := A*(1-g⁻¹)⁻¹
  have hg0 := zero_lt_one.trans hg
  have hgi := (inv_lt_one₀ hg0).mpr hg
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨1+2*K, by positivity, ?_⟩
  intro w hw u
  let μ := volume.restrict (Ioc u (u+1))
  have crossint (k N : ℕ) : Integrable (fun x => term D g w k x * conj (term D g w N x)) μ :=
    ((catom D g w k).mul (Complex.continuous_conj.comp (catom D g w N))).integrableOn_Ioc
  have cross (N : ℕ) : ‖∫ x, partialSum D g w N x * conj (term D g w N x) ∂μ‖ ≤ K := by
    simp only [partialSum,Finset.sum_mul]
    rw [integral_finsetSum _ (fun k _ => crossint k N)]
    calc
      _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, A*(g⁻¹)^k :=
        Finset.sum_le_sum fun k hk => correlation hD hg u w hw (Finset.mem_range.mp hk)
      _ ≤ K := by
        rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ hA.le
        have geom := hasSum_geometric_of_lt_one (inv_pos.mpr hg0).le hgi
        rw [← geom.tsum_eq]; exact geom.summable.sum_le_tsum _ (fun _ _ => by positivity)
  have μone : μ.real univ = 1 := by simp [μ,Measure.real,Real.volume_Ioc]
  intro N
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    let S := partialSum D g w N
    let F := term D g w N
    let T (x : ℝ) := S x * conj (F x)
    have cT : Continuous T := (cpartial D g w N).mul (Complex.continuous_conj.comp (catom D g w N))
    have id (x : ℝ) : ‖partialSum D g w (N+1) x‖^2 = ‖S x‖^2 + 1 + 2*(T x).re := by
      simp only [partialSum,Finset.sum_range_succ,Complex.sq_norm,Complex.normSq_add]
      change Complex.normSq (S x) + Complex.normSq (F x) + _ = _
      rw [← Complex.sq_norm (F x),norm_term _ _ _ hw,one_pow]; rfl
    have si : Integrable (fun x => ‖S x‖^2) μ := ((cpartial D g w N).norm.pow 2).integrableOn_Ioc
    have ti : Integrable (fun x => (T x).re) μ := (Complex.continuous_re.comp cT).integrableOn_Ioc
    have tir : ∫ x, (T x).re ∂μ = (∫ x, T x ∂μ).re := integral_re cT.integrableOn_Ioc
    have bound : (∫ x, T x ∂μ).re ≤ K := (Complex.re_le_norm _).trans (cross N)
    change (∫ x, ‖partialSum D g w (N+1) x‖^2 ∂μ) ≤ _
    simp_rw [id]
    have si1 : Integrable (fun x => ‖S x‖^2 + 1) μ := si.add (integrable_const 1)
    rw [integral_add si1 (ti.const_mul 2),
      integral_add si (integrable_const 1), integral_const, μone, one_smul,
      integral_const_mul, tir, Nat.cast_succ]
    change (∫ x, ‖S x‖^2 ∂μ) ≤ _ at ih
    linarith

/-- The `O(1/N)` second-moment estimate from Appendix A for arbitrary phases. -/
theorem average_mean_square {D g : ℝ} (hD : D ≠ 0) (hg : 1 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℕ → ℂ), (∀ k, ‖w k‖ = 1) → ∀ (u : ℝ) (N : ℕ), 0 < N →
      ∫ x in Ioc u (u+1), ‖average D g w N x‖^2 ≤ C/N := by
  obtain ⟨C,hC,h⟩ := partial_mean_square hD hg
  refine ⟨C,hC,?_⟩
  intro w hw u N hN
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  simp only [average,Complex.norm_mul,norm_inv,Complex.norm_natCast,mul_pow,integral_const_mul]
  calc
    _ ≤ ((N:ℝ)⁻¹)^2 * (C*N) := mul_le_mul_of_nonneg_left (h w hw u N) (by positivity)
    _ = _ := by field_simp

private theorem caverage (D g : ℝ) (w : ℕ → ℂ) (N : ℕ) : Continuous (average D g w N) :=
  continuous_const.mul (cpartial D g w N)

/-- Along the square subsequence, summating the second moments gives almost sure convergence. -/
theorem average_squares_ae {D g : ℝ} (hD : D ≠ 0) (hg : 1 < g)
    (w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ = 1) (u : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioc u (u+1)),
      Tendsto (fun j : ℕ => average D g w (j^2) x) atTop (𝓝 0) := by
  obtain ⟨C, hC, bound⟩ := average_mean_square hD hg
  let μ := volume.restrict (Ioc u (u+1))
  let F (j : ℕ) (x : ℝ) := ‖average D g w (j^2) x‖^2
  let E (j : ℕ) (x : ℝ) := ENNReal.ofReal (F j x)
  have cF (j : ℕ) : Continuous (F j) := (caverage D g w _).norm.pow 2
  have nn (j : ℕ) (x : ℝ) : 0 ≤ F j x := sq_nonneg _
  have mE (j : ℕ) : Measurable (E j) := ENNReal.continuous_ofReal.measurable.comp (cF j).measurable
  have mom (j : ℕ) : ∫⁻ x, E j x ∂μ ≤ ENNReal.ofReal (C/(j:ℝ)^2) := by
    dsimp [E]
    rw [← ofReal_integral_eq_lintegral_ofReal (cF j).integrableOn_Ioc (.of_forall (nn j))]
    apply ENNReal.ofReal_le_ofReal
    by_cases hj : j = 0
    · subst j; simp [F,average]
    · simpa only [Nat.cast_pow] using bound w hw u (j^2) (pow_pos (Nat.pos_of_ne_zero hj) 2)
  have sumBound : Summable (fun j : ℕ => C/(j:ℝ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left C
  have finite : (∫⁻ x, ∑' j, E j x ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun i => (mE i).aemeasurable)]
    exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum mom) sumBound.tsum_ofReal_ne_top.lt_top).ne
  filter_upwards [ae_lt_top (Measurable.tsum mE) finite] with x hx
  have he := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have hreal : Tendsto (fun j => F j x) atTop (𝓝 0) := by
    simpa only [Function.comp_def,E,ENNReal.toReal_zero,ENNReal.toReal_ofReal (nn _ _)] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp he
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,F, Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hreal

/-- Interpolation between consecutive square indices uses the unit norm of each term. -/
private theorem interpolate (D g : ℝ) (w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ = 1) (x : ℝ)
    (h : Tendsto (fun j : ℕ => average D g w (j^2) x) atTop (𝓝 0)) :
    Tendsto (fun N => average D g w N x) atTop (𝓝 0) := by
  have sqrtTop : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    exact eventually_atTop.mpr ⟨n^2, fun _ h => Nat.le_sqrt'.mpr h⟩
  have sqnorm := (tendsto_zero_iff_norm_tendsto_zero.mp h).comp sqrtTop
  have invnorm : Tendsto (fun N : ℕ => 2/(N.sqrt:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sqrtTop)).const_mul (2:ℝ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) _ (by simpa using sqnorm.add invnorm)
  filter_upwards [eventually_ge_atTop 1] with N hN
  let j := N.sqrt
  have hj : 0 < j := Nat.le_sqrt'.mpr (by simpa using hN)
  have hsq : j^2 ≤ N := Nat.sqrt_le' N
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hjpos : 0 < (j:ℝ) := by exact_mod_cast hj
  have hsqR : (j:ℝ)^2 ≤ N := by exact_mod_cast hsq
  have hrem : (N:ℝ) - (j:ℝ)^2 ≤ 2*j := by
    have hn := Nat.sqrt_le_add N
    change N ≤ j*j+j+j at hn
    have hr : (N:ℝ) ≤ (j:ℝ)*(j:ℝ)+j+j := by exact_mod_cast hn
    nlinarith
  have normDiff : ‖partialSum D g w N x - partialSum D g w (j^2) x‖ ≤ (N:ℝ)-(j:ℝ)^2 := by
    unfold partialSum
    rw [← Finset.sum_Ico_eq_sub _ hsq]
    apply (norm_sum_le _ _).trans
    simp [norm_term _ _ _ hw, Nat.cast_sub hsq]
  have split := norm_add_le (partialSum D g w (j^2) x)
    (partialSum D g w N x - partialSum D g w (j^2) x)
  rw [add_sub_cancel] at split
  have avgnorm (n : ℕ) : ‖average D g w n x‖ = ‖partialSum D g w n x‖ / (n:ℝ) := by
    simp [average,div_eq_inv_mul]
  change ‖average D g w N x‖ ≤ ‖average D g w (j^2) x‖ + 2/(j:ℝ)
  rw [avgnorm N,div_le_iff₀ hNpos]
  have prev : ‖partialSum D g w (j^2) x‖ ≤ ‖average D g w (j^2) x‖ * N := by
    calc
      _ = ‖average D g w (j^2) x‖ * (j:ℝ)^2 := by
        rw [avgnorm,Nat.cast_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqR (norm_nonneg _)
  have rem : 2*(j:ℝ) ≤ (2/j : ℝ)*N := by
    calc
      _ = (2/j : ℝ)*(j:ℝ)^2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqR (by positivity)
  linarith

/-- Almost-sure vanishing on every translated unit interval for an arbitrary
fixed sequence of unit weights. In the manuscript use `D = 2π∑ᵢhᵢbⁱ` and `g = b^q`. -/
theorem average_tendsto_zero_ae {D g : ℝ} (hD : D ≠ 0) (hg : 1 < g)
    (w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ = 1) (u : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioc u (u+1)),
      Tendsto (fun N => average D g w N x) atTop (𝓝 0) :=
  (average_squares_ae hD hg w hw u).mono fun x hx => interpolate D g w hw x hx

/-- A single exceptional null set suffices for any countable family of fixed
characters, ratios, and deterministic phase sequences. -/
theorem countable_averages_tendsto_zero_ae {ι : Type*} [Countable ι]
    (D g : ι → ℝ) (w : ι → ℕ → ℂ) (hD : ∀ i, D i ≠ 0) (hg : ∀ i, 1 < g i)
    (hw : ∀ i k, ‖w i k‖ = 1) (u : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioc u (u+1)), ∀ i,
      Tendsto (fun N => average (D i) (g i) (w i) N x) atTop (𝓝 0) :=
  ae_all_iff.mpr fun i => average_tendsto_zero_ae (hD i) (hg i) (w i) (hw i) u

/-- Any comparable-length window is obtained by subtracting its two prefix sums.
Here the hypotheses specify the limits of the endpoint indices divided by the
window length. They are finite for endpoints asymptotic to distinct positive
multiples of a common scale, as in the graph comparison. -/
theorem window_of_prefix_limit (D g : ℝ) (w : ℕ → ℂ) (x : ℝ)
    (hx : Tendsto (fun N => average D g w N x) atTop (𝓝 0))
    (l r : ℕ → ℕ) (hl : Tendsto l atTop atTop) (hr : Tendsto r atTop atTop)
    (order : ∀ᶠ n in atTop, l n ≤ r n) {a b : ℝ}
    (ha : Tendsto (fun n => (l n:ℝ) / ((r n-l n:ℕ):ℝ)) atTop (𝓝 a))
    (hb : Tendsto (fun n => (r n:ℝ) / ((r n-l n:ℕ):ℝ)) atTop (𝓝 b)) :
    Tendsto (fun n => (((r n-l n:ℕ):ℂ)⁻¹ * ∑ k ∈ Finset.Ico (l n) (r n), term D g w k x))
      atTop (𝓝 0) := by
  have haC : Tendsto (fun n => (l n:ℂ) / ((r n-l n:ℕ):ℂ)) atTop (𝓝 (a:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_natCast] using
      (Complex.continuous_ofReal.tendsto a).comp ha
  have hbC : Tendsto (fun n => (r n:ℂ) / ((r n-l n:ℕ):ℂ)) atTop (𝓝 (b:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_natCast] using
      (Complex.continuous_ofReal.tendsto b).comp hb
  have ident (N : ℕ) : (N:ℂ)*average D g w N x = partialSum D g w N x := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [average,partialSum]
    · rw [average,← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast hN),one_mul]
  have trend := (hbC.mul (hx.comp hr)).sub (haC.mul (hx.comp hl))
  simp only [mul_zero,sub_zero] at trend
  apply trend.congr'
  filter_upwards [order] with n hn
  rw [Finset.sum_Ico_eq_sub _ hn]
  change _ = (((r n-l n:ℕ):ℂ)⁻¹) * (partialSum D g w (r n) x - partialSum D g w (l n) x)
  rw [← ident (r n), ← ident (l n)]
  simp only [Function.comp_apply,div_eq_mul_inv]; ring

end Weierstrass.Lacunary
