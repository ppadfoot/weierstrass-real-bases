module

public import Weierstrass.Partition
public import Weierstrass.PredecessorProof

/-! A deterministic estimate for the intersection of two heavy-output tests.
The bound uses the derivative of their difference and holds at every radius. -/
public noncomputable section
open Set Filter MeasureTheory Weierstrass.Partition
open scoped BigOperators Topology ENNReal
namespace Weierstrass.RaySeed

set_option maxHeartbeats 1800000 in
private theorem heavy_grid (ν : Measure ℝ) [IsFiniteMeasure ν] {R τ : ℝ}
    (hR : 0 < R) (hτ : 0 < τ) :
    ∃ I : Finset ℤ, I.card*τ ≤ 3*ν.real univ ∧
      ∀ x, τ < ν.real (Icc (x-R) (x+R)) → ∃ i ∈ I, x ∈ cell R i := by
  classical
  let f (i : ℤ) := ν.real (cell R i)
  let tri (i : ℤ) := f (i-1)+f i+f (i+1)
  have hf : HasSum f (ν.real univ) := by simpa [f] using hasSum_cell ν hR
  have shift (k : ℤ) : HasSum (fun i : ℤ ↦ f (i+k)) (ν.real univ) := ((Equiv.addRight k).hasSum_iff).mpr hf
  have ht : HasSum tri (3*ν.real univ) := by
    simpa [tri,sub_eq_add_neg,show ν.real univ+ν.real univ+ν.real univ=3*ν.real univ by ring] using ((shift (-1)).add hf).add (shift 1)
  have ev : ∀ᶠ i in cofinite, tri i < τ := ht.summable.tendsto_cofinite_zero.eventually_lt_const hτ
  have fin : {i | τ ≤ tri i}.Finite := by
    have t := mem_cofinite.mp ev
    simpa [Set.compl_ofPred] using t
  let I := fin.toFinset
  have memI (i : ℤ) : i ∈ I ↔ τ ≤ tri i := fin.mem_toFinset
  refine ⟨I,?_,?_⟩
  · calc
      (I.card:ℝ)*τ = ∑ _ ∈ I, τ := by simp
      _ ≤ ∑ i ∈ I, tri i := Finset.sum_le_sum (fun i h ↦ (memI i).mp h)
      _ ≤ _ := (ht.summable.sum_le_tsum _ (fun i _ ↦ by dsimp [tri,f];positivity)).trans_eq ht.tsum_eq
  · intro x hx
    let i := ⌊x/R⌋
    have hi : x ∈ cell R i := (mem_cell_iff hR).mpr rfl
    refine ⟨i,(memI i).mpr (le_trans hx.le ?_),hi⟩
    apply (measureReal_mono (μ:=ν) (ball_subset_triple hi)).trans
    apply (measureReal_union_le (μ:=ν) _ _).trans
    exact add_le_add (measureReal_union_le _ _) le_rfl

/-- If both image points have balls of radius R and mass greater than τ,
their difference lies in one of at most (3/τ)^2 prescribed target bands for probability laws.
A large derivative on the counted subset gives the explicit bound below.
No regularity of the two individual image laws is assumed. -/
theorem heavy_pair_bound {f g D' : ℝ → ℝ} (ν ξ : Measure ℝ)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (deriv : ∀ x, HasDerivAt (fun y ↦ f y-g y) (D' x) x)
    {κ δ R τ : ℝ} (hk : 0 < κ) (hR : 0 < R) (hτ : 0 < τ)
    (osc : ∀ x y, |x-y| ≤ δ → |D' x-D' y| ≤ κ/2)
    (N : ℕ) (a T : ℝ) (bound : T ≤ a+N*δ) :
    volume {x | x ∈ Icc a T ∧ τ < ν.real (Icc (f x-R) (f x+R)) ∧
      τ < ξ.real (Icc (g x-R) (g x+R)) ∧ κ < |D' x|} ≤
      ENNReal.ofReal (((9*ν.real univ*ξ.real univ)/τ^2)*(N:ℝ)*(4*R/κ)) := by
  classical
  obtain ⟨I,iC,ic⟩ := heavy_grid ν hR hτ
  obtain ⟨J,jC,jc⟩ := heavy_grid ξ hR hτ
  let P := I ×ˢ J
  let U (p : ℤ × ℤ) := Predecessor.transverseBand (fun y ↦ f y-g y) D' a (a+N*δ)
    (((p.1:ℝ)-p.2)*R) R κ
  apply (measure_mono (t:=(⋃ p ∈ P, U p)) _).trans
  · apply (measure_biUnion_finset_le (μ:=volume) P U).trans
    have cost p : volume (U p) ≤ N*ENNReal.ofReal (4*R/κ) :=
      Predecessor.sublevel_on_pieces deriv hk osc _ _ _ _ hR.le
    apply (Finset.sum_le_sum (fun p _ ↦ cost p)).trans
    simp only [P,Finset.card_product,Finset.sum_const,nsmul_eq_mul,Nat.cast_mul]
    rw [← ENNReal.ofReal_natCast (n:=I.card),← ENNReal.ofReal_natCast (n:=J.card),
      ← ENNReal.ofReal_natCast (n:=N),← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have ci : (I.card:ℝ) ≤ 3*ν.real univ/τ := (le_div_iff₀ hτ).mpr iC
    have cj : (J.card:ℝ) ≤ 3*ξ.real univ/τ := (le_div_iff₀ hτ).mpr jC
    have c : (I.card:ℝ)*J.card ≤ 9*ν.real univ*ξ.real univ/τ^2 :=
      (mul_le_mul ci cj (by positivity) (by positivity)).trans_eq (by ring)
    apply le_trans (mul_le_mul_of_nonneg_right c (by positivity : 0 ≤ (N:ℝ)*(4*R/κ)))
    ring_nf
    exact le_rfl
  · rintro x ⟨hx,hf,hg,hd⟩
    obtain ⟨i,hi,fit⟩ := ic _ hf
    obtain ⟨j,hj,git⟩ := jc _ hg
    refine mem_iUnion.mpr ⟨(i,j),mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hi,hj⟩,?_,⟩⟩
    change x ∈ Icc a (a+N*δ) ∧ |(f x-g x)-(((i:ℝ)-j)*R)| ≤ R ∧ κ < |D' x|
    refine ⟨⟨hx.1,hx.2.trans bound⟩,?_,hd⟩
    have fx := Int.floor_eq_iff.mp ((mem_cell_iff hR).mp fit)
    have gx := Int.floor_eq_iff.mp ((mem_cell_iff hR).mp git)
    have fit := And.intro ((le_div_iff₀ hR).mp fx.1) ((div_lt_iff₀ hR).mp fx.2)
    have git := And.intro ((le_div_iff₀ hR).mp gx.1) ((div_lt_iff₀ hR).mp gx.2)
    apply abs_le.mpr
    constructor <;> nlinarith only [fit.1,fit.2,git.1,git.2]

end Weierstrass.RaySeed
