module

public import Weierstrass.PhaseAverages
public import Weierstrass.GraphWindow
public import Weierstrass.EntropyCutoff

/-! The continuous entropy test at the actual physical environments.
The null set here is chosen after the phases, as in Theorem 1.1. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Weierstrass

local instance entropyBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

theorem scale_environment_eq {b : ℝ} (hb : b ≠ 0) (φ : ℤ → ℝ) (q j : ℕ) (x : ℝ) :
    (fun i ↦ (↑(environment b φ (q*j) x i) : AddCircle (1:ℝ))) =
      (fun i ↦ (↑(φ ((q*j:ℕ)+i)) : AddCircle (1:ℝ))) + phaseOrbit b ((b^q)^j*x) := by
  funext i
  change (↑(b^(((q*j:ℕ):ℤ)+i)*x+φ ((q*j:ℕ)+i)) : AddCircle (1:ℝ)) =
    (↑(φ ((q*j:ℕ)+i)) : AddCircle (1:ℝ)) + ↑(b^i*((b^q)^j*x))
  rw [← AddCircle.coe_add,zpow_add₀ hb,zpow_natCast,pow_mul]
  congr 1
  ring

/-- A coset-uniform bound on the mean of a continuous observable provides
an eventual lower bound on its sum divided by the target depth K. -/
theorem physical_window_floor {b : ℝ} (hb : 1 < b) (φ : ℤ → ℝ)
    {q : ℕ} {a d : ℝ} (hq : 0 < q) (ha : 0 < a) (had : a < d)
    (v : ℝ) (f : C(PhaseTorus,ℝ)) (c : ℝ)
    (hc : ∀ ω : PhaseTorus, c ≤ ∫ z : phaseGroup b, f (ω+z.val) ∂phaseHaar b) :
    ∀ᵐ x ∂volume.restrict (Ioc v (v+1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ K : ℕ in atTop, ((q*a)⁻¹-(q*d)⁻¹)*c-ε ≤
        (∑ j ∈ Finset.Ico (GraphWindow.left q d K) (GraphWindow.right q a K),
          f (fun i ↦ ↑(environment b φ (q*j) x i)))/(K:ℝ) := by
  classical
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let l := GraphWindow.left q d
  let r := GraphWindow.right q a
  let n (K : ℕ) := r K-l K
  let S (K : ℕ) := Finset.Ico (l K) (r K)
  let ψ (j : ℕ) : PhaseTorus := fun i ↦ ↑(φ ((q*j:ℕ)+i))
  let H (j : ℕ) := ∫ z : phaseGroup b, f (ψ j+z.val) ∂phaseHaar b
  let F : C(PhaseTorus,ℂ) := ⟨fun z ↦ (f z:ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  obtain ⟨leftLim,rightLim,ord,width,lw,rw'⟩ := GraphWindow.endpoint_limits hq ha had
  have hb₀ := (zero_lt_one.trans hb).ne'
  have hq' : 1 < b^q := one_lt_pow₀ hb hq.ne'
  have wf := phase_window_haar_comparison b (b^q) hq' ψ l r leftLim rightLim
    (ord.mono fun _ h ↦ h.le) lw rw' v
  filter_upwards [wf] with x hx
  let y (j : ℕ) := f (fun i ↦ ↑(environment b φ (q*j) x i))
  have integral_eq (j : ℕ) :
      (∫ z : phaseGroup b, F (ψ j+z.val) ∂phaseHaar b) = (H j:ℂ) := by
    change (∫ z : phaseGroup b, (↑(f (ψ j+z.val)) : ℂ) ∂phaseHaar b) = _
    rw [integral_complex_ofReal]
  have yeq (j : ℕ) : F (ψ j + phaseOrbit b ((b^q)^j*x)) = (y j:ℂ) := by
    change ↑(f _) = (↑(f _):ℂ)
    rw [scale_environment_eq hb₀]
  have avg : Tendsto (fun K : ℕ ↦ (∑ j ∈ S K, (y j-H j))/(n K:ℝ)) atTop (𝓝 0) := by
    have bound := (Complex.continuous_re.tendsto 0).comp (hx F)
    apply bound.congr
    intro K
    change (((n K:ℂ)⁻¹ * ∑ j ∈ S K, (F (ψ j + phaseOrbit b ((b^q)^j*x)) -
      ∫ z : phaseGroup b, F (ψ j+z.val) ∂phaseHaar b))).re = _
    simp only [integral_eq,yeq,← Complex.ofReal_sub,← Complex.ofReal_sum,
      ← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
    ring
  let w := ((q:ℝ)*a)⁻¹-((q:ℝ)*d)⁻¹
  have lim : Tendsto (fun K : ℕ ↦ ((n K:ℝ)/K)*(c+(∑ j ∈ S K, (y j-H j))/(n K:ℝ)))
      atTop (𝓝 (w*c)) := by simpa only [add_zero] using width.mul (tendsto_const_nhds.add avg)
  intro ε hε
  have eventual := lim.eventually (eventually_gt_nhds (show w*c-ε < w*c by linarith))
  filter_upwards [eventual,ord,eventually_gt_atTop (0:ℕ)] with K hk hK hk₀
  have hn : 0 < (n K:ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hK)
  have hsum : (n K:ℝ)*c ≤ ∑ j ∈ S K, H j := by
    exact (show (n K:ℝ)*c = ∑ _j ∈ S K, c by simp [S,n,nsmul_eq_mul]).le.trans
      (Finset.sum_le_sum fun j _ ↦ hc (ψ j))
  apply hk.le.trans
  change _ ≤ (∑ j ∈ S K, y j)/(K:ℝ)
  rw [Finset.sum_sub_distrib]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk₀)).mpr
  field_simp [hn.ne', (Nat.cast_pos.mpr hk₀ : 0 < (K:ℝ)).ne']
  nlinarith only [hsum,hn]

/-- (G1) on the prescribed physical orbit, with the window normalized by target depth. -/
theorem anchored_physical_entropy {b l s : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (hs : s ≤ 1) (H : AnchoredEstimate b l s) {h δ : ℝ} (hh : 0 < h) (hh' : h < s)
    (hδ : 0 < δ) (φ : ℤ → ℝ) {a d : ℝ} (ha : 0 < a) (had : a < d) (v : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ᵐ x ∂volume.restrict (Ioc v (v+1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ K : ℕ in atTop, (((q:ℝ)*a)⁻¹-(q*d)⁻¹)*
        ((1-δ)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2))-ε ≤
        (∑ j ∈ Finset.Ico (GraphWindow.left q d K) (GraphWindow.right q a K),
          graphEntropy b l q (fun i ↦ ↑(environment b φ (q*j) x i)))/(K:ℝ) := by
  filter_upwards [eventually_gt_atTop (0:ℕ),anchored_entropy_floor hb hl hl' hs H hh hh' hδ]
    with q hq hfloor
  exact physical_window_floor hb φ hq ha had v ⟨_,continuous_graphEntropy hb hl hl' q⟩ _ hfloor

end Weierstrass
