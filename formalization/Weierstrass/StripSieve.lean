module

public import Weierstrass.StripEnergy

/-! # Two-sided planar Fourier localization for a singular band measure -/

@[expose] public noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators

namespace Weierstrass.StripProof

private theorem bell_symm (a : ℝ) (u v : Plane) : bell a u v = bell a v u := by
  unfold bell; congr 2 <;> ring_nf

private theorem bell_freq_weight {R : ℝ} (hR : 1 ≤ R) {u : Plane} (hu : u ∈ box 0 R)
    (v : Plane) :
    bell (1/2) u v ≤ Real.exp (1/2) * bell (1/4) v u * bell (1/(8*R^2)) 0 v := by
  have R2 : 1 ≤ R^2 := by nlinarith [sq_nonneg (R-1)]
  have coord (s x : ℝ) (hs : s ∈ Icc (0-R) (0+R)) :
      x^2 ≤ 2*R^2*(x-s)^2 + 2*R^2 := by
    rcases hs with ⟨hs,hs'⟩
    have := mul_nonneg (by linarith : 0 ≤ R-s) (by linarith : 0 ≤ R+s)
    nlinarith [sq_nonneg ((x-s)-s),mul_nonneg (sub_nonneg.mpr R2) (sq_nonneg (x-s))]
  have x := coord u.1 v.1 hu.1
  have y := coord u.2 v.2 hu.2
  simp only [bell,Prod.fst_zero,Prod.snd_zero,sub_zero,← Real.exp_add,Real.exp_le_exp]
  field_simp [show 0 < R by linarith]
  nlinarith

/-- Spreading a band with independent Gaussian jitter produces an absolutely continuous
density dominated by a broader Gaussian times its largest unit-square mass. -/
theorem gaussian_band_density (ν : Measure Plane) [IsFiniteMeasure ν] {R A : ℝ}
    (hR : 1 ≤ R) (hs : ∀ᵐ u ∂ν, u ∈ box 0 R)
    (hν : ∀ z, ν.real (box z 1) ≤ A) (v : Plane) :
    ∫ u, bell (1/2) u v ∂ν ≤ 2*Real.pi*Real.exp 1*A*bell (1/(8*R^2)) 0 v := by
  have bdd (a : ℝ) (ha : 0 ≤ a) (p q : Plane) : bell a p q ≤ 1 := by
    have small (x : ℝ) : Real.exp (-a*x^2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _))
    exact mul_le_one₀ (small _) (Real.exp_pos _).le (small _)
  have it (a : ℝ) (ha : 0 ≤ a) : Integrable (bell a v) ν :=
    (integrable_const (1:ℝ)).mono' (measurable_bell _ _).aestronglyMeasurable
      (ae_of_all _ fun u => by rw [Real.norm_eq_abs,abs_of_pos (bell_pos _ _ _)]; exact bdd a ha v u)
  have iu : Integrable (fun u => bell (1/2) u v) ν := by
    exact (it (1/2) (by norm_num)).congr (ae_of_all _ fun u => bell_symm _ _ _)
  have H := gaussian_of_box_bound ν (r := 1) (a := 1/4) (by norm_num) (by norm_num) hν v
  have fac : ∫ u, bell (1/4) v u ∂ν ≤ Real.exp (1/2) * (2*Real.pi) * A := by
    norm_num at H ⊢
    linarith
  let k := bell (1/(8*R^2)) 0 v
  calc
    _ ≤ ∫ u, Real.exp (1/2) * bell (1/4) v u * k ∂ν := by
      apply integral_mono_ae iu (((it _ (by norm_num)).const_mul _).mul_const _)
      filter_upwards [hs] with u hu using bell_freq_weight hR hu v
    _ = Real.exp (1/2)*(∫ u, bell (1/4) v u ∂ν)*k := by rw [integral_mul_const,integral_const_mul]
    _ ≤ Real.exp (1/2) * (Real.exp (1/2)*(2*Real.pi)*A)*k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left fac (Real.exp_pos _).le) (bell_pos _ _ _).le
    _ = _ := by rw [show (1:ℝ)=1/2+1/2 by norm_num, Real.exp_add]; dsimp [k]; ring

/-- Characteristic coefficient obtained by removing the Gaussian physical damping with a
positive measure change. -/
def dampedFourier (μ : Measure Plane) (ξ : Plane) : ℂ :=
  ∫ p, (bell (1/2) 0 p : ℂ) * character (dot p ξ) ∂μ

theorem damped_eq_gaussian_average (μ : Measure Plane) [IsFiniteMeasure μ] (ξ : Plane) :
    dampedFourier μ ξ = ∫ v, fourier μ (ξ+v) ∂gaussian := by
  let F := fun (v p : Plane) => character (dot p (ξ+v))
  have cm : Continuous (Function.uncurry F) := by unfold Function.uncurry F dot; apply continuous_character.comp; fun_prop
  have it : Integrable (Function.uncurry F) (gaussian.prod μ) :=
    (integrable_const (1:ℝ)).mono' cm.aestronglyMeasurable (ae_of_all _ fun _ => (norm_character _).le)
  change _ = ∫ v, ∫ p, F v p ∂μ ∂gaussian
  rw [integral_integral_swap it]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  have H (v : Plane) : F v p = character (dot p v) * character (dot p ξ) := by
    unfold F; rw [← character_add]; congr 1; simp [dot]; ring
  simp_rw [H,integral_mul_const,gaussian_character]
  congr 2
  unfold bell; rw [← Real.exp_add]; simp; ring_nf

theorem damped_fourier_le (μ : Measure Plane) [IsFiniteMeasure μ] (ξ : Plane) :
    ‖dampedFourier μ ξ‖^2 ≤ ∫ v, ‖fourier μ (ξ+v)‖^2 ∂gaussian := by
  let f := fun v => ‖fourier μ (ξ+v)‖
  have mf : Measurable f := ((measurable_fourier μ).comp (measurable_const.add measurable_id)).norm
  have hf : Integrable f gaussian := (integrable_const (μ.real univ)).mono' mf.aestronglyMeasurable
    (ae_of_all _ fun v => by change ‖‖fourier μ (ξ+v)‖‖ ≤ _; rw [norm_norm]; exact fourier_bound _ _)
  have hi : Integrable (fun v => (f v)^2) gaussian :=
    (integrable_const ((μ.real univ)^2)).mono' (mf.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (fourier_bound _ _) _)
  rw [damped_eq_gaussian_average]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
  let m := ∫ v, f v ∂gaussian
  have eqn (v : Plane) : (f v-m)^2 = (f v)^2 - 2*m*f v + m^2 := by ring
  have H : 0 ≤ ∫ v, (f v-m)^2 ∂gaussian := integral_nonneg (fun v => sq_nonneg (f v-m))
  simp_rw [eqn] at H
  rw [integral_add (f := fun v => (f v)^2 - 2*m*f v) (g := fun _ => m^2)
    (hi.sub (hf.const_mul _)) (integrable_const _),
    integral_sub (f := fun v => (f v)^2) (g := fun v => 2*m*f v) hi (hf.const_mul _),
    integral_const_mul,integral_const] at H
  simp only [probReal_univ,one_smul] at H
  change m^2 ≤ ∫ v, (f v)^2 ∂gaussian
  change 0 ≤ (∫ v, (f v)^2 ∂gaussian) - 2*m*m + m^2 at H
  nlinarith

private theorem box_mono (z : Plane) {r s : ℝ} (h : r ≤ s) : box z r ⊆ box z s := by
  intro p hp; rcases hp with ⟨⟨h1,h2⟩,h3,h4⟩
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem measurable_dampedFourier (μ : Measure Plane) [IsFiniteMeasure μ] :
    Measurable (dampedFourier μ) := by
  have me : Measurable (fun p : Plane × Plane => fourier μ (p.1 + p.2)) :=
    (measurable_fourier μ).comp (measurable_fst.add measurable_snd)
  rw [show dampedFourier μ = (fun x => ∫ y, fourier μ (x+y) ∂gaussian) from
    funext (damped_eq_gaussian_average μ)]
  exact (me.stronglyMeasurable.integral_prod_right' (ν := gaussian)).measurable

/-- The sharp two-sided large-sieve bound prior to removing the physical Gaussian damping.
The frequency measure may be singular and only its masses at unit mesh are used. -/
theorem damped_band_energy (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R A B : ℝ} (hR : 1 ≤ R) (hs : ∀ᵐ u ∂ν, u ∈ box 0 R)
    (hν : ∀ z, ν.real (box z 1) ≤ A) (hμ : ∀ z, μ.real (box z R⁻¹) ≤ B) :
    ∫ u, ‖dampedFourier μ u‖^2 ∂ν ≤
      8 * Real.exp 2 * Real.pi^2 * R^2 * A * B * μ.real univ := by
  have rpos : 0 < R := by linarith
  have apos : 0 ≤ A := measureReal_nonneg.trans (hν 0)
  let F := fun v => ‖fourier μ v‖^2
  have mF : Measurable F := (measurable_fourier μ).norm.pow_const 2
  have fb (v : Plane) : F v ≤ (μ.real univ)^2 := pow_le_pow_left₀ (norm_nonneg _) (fourier_bound μ v) _
  let K := fun (p : Plane × Plane) => bell (1/2) p.1 p.2
  have mK : Measurable K := by unfold K bell; fun_prop
  have iK : Integrable K (ν.prod volume) := by
    apply (integrable_prod_iff mK.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun _ => integrable_bell (by norm_num) _, ?_⟩
    have hc (s : Plane) : ∫ v, ‖K (s,v)‖ = Real.pi/(1/2) := by
      simp only [K, Real.norm_eq_abs,abs_of_pos (bell_pos _ _ _),integral_bell (by norm_num : 0 < (1/2:ℝ))]
    simp_rw [hc]; exact integrable_const _
  let H := fun p : Plane × Plane => K p * F p.2
  have iH : Integrable H (ν.prod volume) := by
    apply (iK.mul_const ((μ.real univ)^2)).mono' (mK.mul (mF.comp measurable_snd)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    change ‖K p * F p.2‖ ≤ K p * (μ.real univ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (bell_pos _ _ _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (fb _) (bell_pos _ _ _).le
  have bh : ∀ z, μ.real (box z (2*R)⁻¹) ≤ B := fun z =>
    (measureReal_mono (box_mono _ (inv_anti₀ rpos (by linarith)))).trans (hμ z)
  have fe := physical_gaussian_energy μ (show 0 < 2*R by positivity) bh 0
  change (∫ v, F (0+(2*R) • v) ∂gaussian) ≤ _ at fe
  rw [integral_gaussian_scaled F 0 (by positivity)] at fe
  rw [show 2*(2*R)^2 = 8*R^2 by ring] at fe
  let G := fun v => bell (1/(8*R^2)) 0 v * F v
  have gi : Integrable G := by
    apply ((integrable_bell (show 0 < 1/(8*R^2) by positivity) 0).mul_const ((μ.real univ)^2)).mono'
      ((measurable_bell _ _).mul mF).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    change ‖bell (1/(8*R^2)) 0 v * F v‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (bell_pos _ _ _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (fb _) (bell_pos _ _ _).le
  have giBound : ∫ v, G v ≤ (2*Real.pi*(2*R)^2)*(Real.exp 1 * Real.pi * B * μ.real univ) := by
    calc
      _ = (2*Real.pi*(2*R)^2) * ((2*Real.pi*(2*R)^2)⁻¹ * ∫ v, G v) := by
        field_simp [rpos.ne',Real.pi_ne_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left fe (by positivity)
  let C := 2*Real.pi*Real.exp 1*A
  have cf : (∫ u, ∫ v, H (u,v) ∂volume ∂ν) ≤ C * ∫ v, G v := by
    rw [← integral_prod _ iH,integral_prod_symm _ iH,← integral_const_mul]
    apply integral_mono_ae iH.integral_prod_right (gi.const_mul C) (ae_of_all _ fun v => ?_)
    change (∫ s, bell (1/2) s v * F v ∂ν) ≤ C * (bell (1/(8*R^2)) 0 v * F v)
    rw [integral_mul_const,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (gaussian_band_density ν hR hs hν v) (sq_nonneg _)
  have integrand (u : Plane) : (∫ v, F (u+v) ∂gaussian) =
      (2*Real.pi)⁻¹ * ∫ v, H (u,v) := by
    simpa [H,K] using integral_gaussian_scaled F u (R := 1) (by norm_num)
  calc
    _ ≤ ∫ u, (2*Real.pi)⁻¹ * ∫ v, H (u,v) ∂volume ∂ν := by
      apply integral_mono_of_nonneg (ae_of_all _ fun u => sq_nonneg _)
        (iH.integral_prod_left.const_mul _) (ae_of_all _ fun u => ?_)
      change ‖dampedFourier μ u‖^2 ≤ (2*Real.pi)⁻¹ * ∫ v, H (u,v)
      rw [← integrand]; exact damped_fourier_le μ u
    _ = (2*Real.pi)⁻¹ * ∫ u, ∫ v, H (u,v) ∂volume ∂ν := integral_const_mul _ _
    _ ≤ (2*Real.pi)⁻¹ * (C * ((2*Real.pi*(2*R)^2)*(Real.exp 1 * Real.pi * B * μ.real univ))) :=
      mul_le_mul_of_nonneg_left (cf.trans (mul_le_mul_of_nonneg_left giBound (by dsimp [C]; positivity)))
        (by positivity)
    _ = _ := by
      dsimp [C]; rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
      field_simp [Real.pi_ne_zero]; ring

/-- The two-sided Fourier estimate for an arbitrary compactly supported physical
measure and an arbitrary singular band measure. Each side is tested at one mesh only. -/
theorem band_energy (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R A B S : ℝ} (hR : 1 ≤ R) (hs : ∀ᵐ u ∂ν, u ∈ box 0 R)
    (hν : ∀ z, ν.real (box z 1) ≤ A) (hp : ∀ᵐ p ∂μ, p ∈ box 0 S)
    (hμ : ∀ z, μ.real (box z R⁻¹) ≤ B) :
    ∫ u, ‖fourier μ u‖^2 ∂ν ≤
      8*Real.exp (2+2*S^2)*Real.pi^2*R^2*A*B*μ.real univ := by
  let E := Real.exp (S^2)
  let w := fun p => min E (bell (1/2) 0 p)⁻¹
  have mp : Measurable w := measurable_const.min (measurable_bell _ _).inv
  have w0 (p : Plane) : 0 ≤ w p := le_min (Real.exp_pos _).le (inv_nonneg.mpr (bell_pos _ _ _).le)
  let ξ := μ.withDensity (fun p => ENNReal.ofReal (w p))
  have dom : ξ ≤ ENNReal.ofReal E • μ := by
    rw [← withDensity_const]; exact withDensity_mono (ae_of_all _ fun p => ENNReal.ofReal_le_ofReal (min_le_left _ _))
  let _ := μ.smul_finite (c := ENNReal.ofReal E) ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure ξ := isFiniteMeasure_of_le _ dom
  have mass (s : Set Plane) : ξ.real s ≤ E*μ.real s := by
    have H := ENNReal.toReal_mono (measure_ne_top (ENNReal.ofReal E • μ) s) (dom s)
    simpa [measureReal_def,Measure.smul_apply,ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0 ≤ E from (Real.exp_pos _).le)] using H
  have hd (u : Plane) : dampedFourier ξ u = fourier μ u := by
    unfold dampedFourier fourier ξ
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun p => ENNReal.ofReal (w p))
      (ENNReal.measurable_ofReal.comp mp)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hp] with p ph
    obtain ⟨⟨s1,s2⟩,s3,s4⟩ := ph
    have sqb (x : ℝ) (h : 0-S ≤ x) (h' : x ≤ 0+S) : x^2 ≤ S^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ S-x) (by linarith : 0 ≤ S+x)]
    have invb : (bell (1/2) 0 p)⁻¹ ≤ E := by
      simp only [bell,Prod.fst_zero,Prod.snd_zero,sub_zero,← Real.exp_add,← Real.exp_neg,E,Real.exp_le_exp]
      linarith [sqb _ s1 s2, sqb _ s3 s4]
    rw [ENNReal.toReal_ofReal (w0 p),Complex.real_smul]
    dsimp only [w]
    rw [min_eq_right invb, Complex.ofReal_inv, ← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (bell_pos _ _ _).ne'),one_mul]
  have hb' (z : Plane) : ξ.real (box z R⁻¹) ≤ E*B :=
    (mass _).trans (mul_le_mul_of_nonneg_left (hμ _) (Real.exp_pos _).le)
  have H := damped_band_energy ξ ν hR hs hν hb'
  simp_rw [hd] at H
  apply H.trans
  have apos : 0 ≤ A := measureReal_nonneg.trans (hν 0)
  have bpos : 0 ≤ B := measureReal_nonneg.trans (hμ 0)
  have final := mul_le_mul_of_nonneg_left (mass univ)
    (show 0 ≤ 8*Real.exp 2*Real.pi^2*R^2*A*(E*B) by dsimp [E]; positivity)
  apply final.trans_eq
  dsimp [E]; rw [show 2+2*S^2=2+(S^2+S^2) by ring,Real.exp_add,Real.exp_add]; ring

end Weierstrass.StripProof
