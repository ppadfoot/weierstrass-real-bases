module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Separation of sparse signed sums of powers (Section 4)

For every complex base of norm greater than one, sums of up to a fixed number
of signed nonnegative powers take only finitely many values in each bounded
ball. The uniform gap can therefore be used for arbitrary choices of exponents,
including repeated exponents and exact cancellations.
-/

public noncomputable section
open Set
open scoped BigOperators

namespace Weierstrass.SparseGap

private def BoundedlyFinite (S : Set ℂ) : Prop :=
  ∀ R : ℝ, {z | z ∈ S ∧ ‖z‖ ≤ R}.Finite

private theorem translated {S : Set ℂ} (hS : BoundedlyFinite S) (a : ℂ) :
    BoundedlyFinite ((fun y => a+y) '' S) := by
  intro R
  apply ((hS (R+‖a‖)).image (fun y => a+y)).subset
  rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  calc
    ‖y‖ = ‖(a+y)-a‖ := by congr 1; abel
    _ ≤ ‖a+y‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ R+‖a‖ := by linarith

private def dilates (B : ℂ) (S : Set ℂ) : Set ℂ :=
  {z | ∃ y ∈ S, ∃ n : ℕ, B^n*y = z}

private theorem finite_dilates {B : ℂ} (hb : 1 < ‖B‖) {S : Set ℂ}
    (hS : BoundedlyFinite S) : BoundedlyFinite (dilates B S) := by
  intro R
  let orbit (y : ℂ) := {z : ℂ | (∃ n : ℕ, B^n*y = z) ∧ ‖z‖ ≤ R}
  have oneOrbit (y : ℂ) : (orbit y).Finite := by
    by_cases hy : y = 0
    · subst y
      apply (Set.finite_singleton (0:ℂ)).subset
      rintro _ ⟨⟨n,rfl⟩,_⟩; simp
    · have hy0 := norm_pos_iff.mpr hy
      obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (R/‖y‖) hb
      apply ((Set.finite_Iio N).image (fun n => B^n*y)).subset
      rintro _ ⟨⟨n,rfl⟩,hn⟩
      refine ⟨n, ?_, rfl⟩
      change n < N
      by_contra! hnN
      have hbound := (div_lt_iff₀ hy0).mp (hN.trans_le (pow_le_pow_right₀ hb.le hnN))
      rw [Complex.norm_mul, Complex.norm_pow] at hn
      exact hn.not_gt hbound
  apply ((hS R).biUnion (fun y _ => oneOrbit y)).subset
  rintro _ ⟨⟨y,hy,n,rfl⟩,hbound⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨y, ⟨hy, ?_⟩, ⟨n,rfl⟩, hbound⟩
  have h1 : 1 ≤ ‖B‖ ^ n := one_le_pow₀ hb.le
  rw [Complex.norm_mul, Complex.norm_pow] at hbound
  exact (le_mul_of_one_le_left (norm_nonneg y) h1).trans hbound

/-- Recursive description obtained by factoring out a smallest power. -/
private def sparse (B : ℂ) : ℕ → Set ℂ
  | 0 => {0}
  | q+1 => insert 0 (dilates B (((fun y => (1:ℂ)+y) '' sparse B q) ∪
                                ((fun y => (-1:ℂ)+y) '' sparse B q)))

private theorem finite_sparse {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) : BoundedlyFinite (sparse B q) := by
  induction q with
  | zero => intro R; exact (Set.finite_singleton _).subset (fun _ h => h.1)
  | succ q ih =>
    have pos := translated ih (1:ℂ)
    have neg := translated ih (-1:ℂ)
    have hu : BoundedlyFinite (((fun y => (1:ℂ)+y) '' sparse B q) ∪
                                ((fun y => (-1:ℂ)+y) '' sparse B q)) := by
      intro R
      apply ((pos R).union (neg R)).subset
      rintro z ⟨h,hR⟩
      exact h.elim (fun h => Or.inl ⟨h,hR⟩) (fun h => Or.inr ⟨h,hR⟩)
    intro R
    apply ((finite_dilates hb hu R).insert 0).subset
    rintro z ⟨h,hR⟩
    exact h.elim Or.inl (fun h => Or.inr ⟨h,hR⟩)

/-- A shared factor when every occurring exponent is at least `k`. -/
private theorem factor_power {ι : Type*} (B : ℂ) (s : Finset ι) (e : ι → ℕ) (w : ι → ℂ)
    {k : ℕ} (hk : ∀ i ∈ s, k ≤ e i) :
    ∑ i ∈ s, w i * B^(e i) = B^k * ∑ i ∈ s, w i * B^(e i-k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, mul_comm (B^k), mul_assoc, ← pow_add,
    Nat.add_sub_of_le (hk i hi)]

private theorem sum_mem {ι : Type*} (B : ℂ) (q : ℕ) (s : Finset ι) (e : ι → ℕ)
    (w : ι → ℂ) (hw : ∀ i ∈ s, w i = 1 ∨ w i = -1) (hcard : s.card ≤ q) :
    ∑ i ∈ s, w i * B^(e i) ∈ sparse B q := by
  classical
  induction q generalizing s e with
  | zero =>
    have he : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    simp [he,sparse]
  | succ q ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨j,hj,hmin⟩ := s.exists_min_image e hs
      let t := s.erase j
      have sub i (hi : i ∈ t) := Finset.mem_of_mem_erase hi
      let tail := ∑ i ∈ t, w i * B^(e i-e j)
      have htail : tail ∈ sparse B q := ih t (fun i => e i-e j) (fun i hi => hw i (sub i hi)) (by
        dsimp [t]; rw [Finset.card_erase_of_mem hj]; omega)
      apply Or.inr
      refine ⟨w j+tail, ?_, e j, ?_⟩
      · rcases hw j hj with h | h
        · exact Or.inl ⟨tail,htail,by rw [h]⟩
        · exact Or.inr ⟨tail,htail,by rw [h]⟩
      · rw [mul_add, mul_comm (B^(e j)) (w j)]
        change w j*B^(e j) + B^(e j)*(∑ i ∈ t, w i*B^(e i-e j)) = _
        rw [← factor_power B t e w (fun i hi => hmin i (sub i hi))]
        exact s.add_sum_erase (fun i => w i*B^(e i)) hj
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
      exact Or.inl rfl

/-- All actual signed sums with at most `q` indexed occurrences. -/
@[expose] def signedPowerSums (B : ℂ) (q : ℕ) : Set ℂ :=
  {z | ∃ k ≤ q, ∃ (e : Fin k → ℕ) (w : Fin k → ℂ),
    (∀ i, w i = 1 ∨ w i = -1) ∧ z = ∑ i, w i * B^(e i)}

/-- In every bounded ball there are only finitely many sparse sum values. -/
theorem bounded_signed_sums_finite {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) (R : ℝ) :
    {z | z ∈ signedPowerSums B q ∧ ‖z‖ ≤ R}.Finite := by
  apply (finite_sparse hb q R).subset
  rintro _ ⟨⟨k,hk,e,w,hw,rfl⟩,hR⟩
  exact ⟨sum_mem B q Finset.univ e w (fun i _ => hw i) (by simpa using hk),hR⟩

private theorem gap_sparse {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ sparse B q, z ≠ 0 → c ≤ ‖z‖ := by
  classical
  let S := {z : ℂ | z ∈ sparse B q ∧ ‖z‖ ≤ 1 ∧ z ≠ 0}
  have hS : S.Finite := (finite_sparse hb q 1).subset (fun _ h => ⟨h.1,h.2.1⟩)
  by_cases hne : S.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hS.toFinset.exists_min_image (fun z => ‖z‖) (by simpa using hne)
    have hzS : z ∈ S := hS.mem_toFinset.mp hz
    refine ⟨‖z‖,norm_pos_iff.mpr hzS.2.2,?_⟩
    intro y hy hnon
    by_cases hy1 : ‖y‖ ≤ 1
    · exact hmin y (hS.mem_toFinset.mpr ⟨hy,hy1,hnon⟩)
    · exact hzS.2.1.trans (le_of_not_ge hy1)
  · refine ⟨1,zero_lt_one,fun z hz hn => ?_⟩
    by_contra! h
    exact hne ⟨z,hz,h.le,hn⟩

/-- Positive separation from zero, uniform in the finite index type, signs and exponents. -/
theorem signed_sum_gap {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι : Type} (s : Finset ι) (e : ι → ℕ) (w : ι → ℂ),
      (∀ i ∈ s, w i = 1 ∨ w i = -1) → s.card ≤ q →
      (∑ i ∈ s, w i * B^(e i)) ≠ 0 → c ≤ ‖∑ i ∈ s, w i * B^(e i)‖ := by
  obtain ⟨c,hc,hgap⟩ := gap_sparse hb q
  exact ⟨c,hc,fun s e w hw hcard => hgap _ (sum_mem B q s e w hw hcard)⟩

/-- Any zero relation splits across a sufficiently large gap. Integer exponents
permit the two-sided frequency blocks used in the proof by moments. -/
theorem separated_relation_splits {B : ℂ} (hb : 1 < ‖B‖) (q : ℕ) :
    ∃ J : ℕ, ∀ {ι : Type} (lo hi : Finset ι) (e : ι → ℤ) (w : ι → ℂ) (k : ℤ),
      lo.card ≤ q → hi.card ≤ q →
      (∀ i ∈ lo, w i = 1 ∨ w i = -1) → (∀ i ∈ hi, w i = 1 ∨ w i = -1) →
      (∀ i ∈ lo, e i ≤ k) → (∀ i ∈ hi, k + (J:ℤ) ≤ e i) →
      (∑ i ∈ lo, w i * B^(e i)) + (∑ i ∈ hi, w i * B^(e i)) = 0 →
      (∑ i ∈ lo, w i * B^(e i)) = 0 ∧ (∑ i ∈ hi, w i * B^(e i)) = 0 := by
  obtain ⟨c,hc,gap⟩ := signed_sum_gap hb q
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt ((q:ℝ)/c) hb
  have hbpos : 0 < ‖B‖ := by linarith
  have hnB : B ≠ 0 := norm_pos_iff.mp hbpos
  refine ⟨J,?_⟩
  intro ι lo hi e w k hcl hch hwl hwh hel heh zero
  let lower := ∑ i ∈ lo, w i * B^(e i)
  let upper := ∑ i ∈ hi, w i * B^(e i)
  change lower + upper = 0 at zero
  change lower = 0 ∧ upper = 0
  have opp : lower = -upper := eq_neg_of_add_eq_zero_left zero
  have leLower : ‖lower‖ ≤ q * ‖B‖^k := by
    calc
      ‖lower‖ ≤ ∑ i ∈ lo, ‖w i * B^(e i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ lo, ‖B‖^k := by
        apply Finset.sum_le_sum
        intro i h
        have h1 : ‖(1:ℂ)‖ = 1 := by simpa only [Nat.cast_one] using Complex.norm_natCast 1
        have hw : ‖w i‖ = 1 := by rcases hwl i h with h | h <;> simp [h,h1]
        rw [Complex.norm_mul,Complex.norm_zpow,hw,one_mul]
        exact zpow_le_zpow_right₀ hb.le (hel i h)
      _ ≤ q * ‖B‖^k := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcl) (zpow_pos hbpos _).le
  let m := k + (J:ℤ)
  let offset (i : ι) := (e i - m).toNat
  let tail := ∑ i ∈ hi, w i * B^(offset i)
  have factor : upper = B^m * tail := by
    dsimp [upper,tail]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i h
    have add : m + ((offset i:ℕ):ℤ) = e i := by
      rw [show ((offset i:ℕ):ℤ) = e i - m from Int.toNat_sub_of_le (heh i h)]; abel
    calc
      _ = w i * B^(m + ((offset i:ℕ):ℤ)) := by rw [add]
      _ = _ := by rw [zpow_add₀ hnB, zpow_natCast]; ring
  have separated : (q:ℝ) * ‖B‖^k < ‖B‖ ^ m * c := by
    have h := mul_lt_mul_of_pos_left ((div_lt_iff₀ hc).mp hJ) (zpow_pos hbpos k)
    dsimp [m]; rw [zpow_add₀ hbpos.ne', zpow_natCast]; linarith
  have upper_zero : upper = 0 := by
    by_contra hnu
    have hnt : tail ≠ 0 := by intro h; exact hnu (by rw [factor,h,mul_zero])
    have small : c ≤ ‖tail‖ := gap hi offset w hwh hch hnt
    have big : ‖B‖^m * c ≤ ‖upper‖ := by
      rw [factor,Complex.norm_mul,Complex.norm_zpow]
      exact mul_le_mul_of_nonneg_left small (zpow_pos hbpos _).le
    rw [opp,norm_neg] at leLower
    exact (separated.trans_le big).not_ge leLower
  exact ⟨by rw [opp,upper_zero,neg_zero],upper_zero⟩

/-- A two-term zero relation consists of an equal-time opposite-sign pair.
The forward implication even applies to arbitrary complex unit weights. -/
theorem two_term_relation_iff {B u v : ℂ} (hb : 1 < ‖B‖) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (i j : ℤ) : u*B^i + v*B^j = 0 ↔ i = j ∧ u = -v := by
  constructor
  · intro rel
    have opp : u*B^i = -(v*B^j) := eq_neg_of_add_eq_zero_left rel
    have hn := congrArg (fun z : ℂ => ‖z‖) opp
    simp only [norm_neg, Complex.norm_mul, Complex.norm_zpow, hu, hv, one_mul] at hn
    have hij := (zpow_right_strictMono₀ hb).injective hn
    subst j
    have hB : B ≠ 0 := norm_pos_iff.mp (by linarith)
    rw [← add_mul] at rel
    exact ⟨rfl,eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp rel).resolve_right (zpow_ne_zero _ hB))⟩
  · rintro ⟨rfl,rfl⟩; ring

end Weierstrass.SparseGap
