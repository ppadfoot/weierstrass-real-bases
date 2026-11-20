module

public import Std

public section

/-!
# The countable-grid estimate for retained collisions (Section 5)

The proof uses Lean's ordered-field interface. In particular it does not select a
numerical precision or truncate the grid. The measure-theoretic interpretation of the
input cell masses and of their square sums is separate from the scalar estimate.
-/
namespace Weierstrass.Grid

open Std Lean.Grind

variable {K : Type u} [Field K] [LE K] [LT K] [LawfulOrderLT K]
  [IsLinearOrder K] [OrderedRing K]

/-- A ball centered in a half-open cell lies in its three-cell enlargement. -/
theorem ball_in_triple {a R x y : K} (hx₁ : a ≤ x) (hx₂ : x < a + R)
    (hy₁ : x - R ≤ y) (hy₂ : y ≤ x + R) :
    a - R ≤ y ∧ y < a + 2 * R := by grind

/-- Pairs from one half-open cell lie in the closed collision band. -/
theorem same_cell_collision {a R x y : K} (hx₁ : a ≤ x) (hx₂ : x < a + R)
    (hy₁ : a ≤ y) (hy₂ : y < a + R) : x - R ≤ y ∧ y ≤ x + R := by grind

/-- Total of the cell masses with indices from c-n to c+n, inclusive. -/
def window (f : Int → K) (c : Int) : Nat → K
  | 0 => f c
  | n+1 => window f c n + f (c - (n+1 : Nat)) + f (c + (n+1 : Nat))

/-- The mass of three consecutive half-open cells. -/
def triple (f : Int → K) (i : Int) := f (i-1) + f i + f (i+1)

/-- The usual countable sum of nonnegative cell masses, specified as the least
upper bound of the centered finite partial sums. -/
def IsGridTotal (f : Int → K) (s : K) : Prop :=
  (∀ n, window f 0 n ≤ s) ∧ ∀ b, (∀ n, window f 0 n ≤ b) → s ≤ b

omit [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
private theorem window_add (f g : Int → K) (c : Int) (n : Nat) :
    window (fun i => f i + g i) c n = window f c n + window g c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [window, ih]; grind

omit [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
private theorem window_mul (a : K) (f : Int → K) (c : Int) (n : Nat) :
    window (fun i => a * f i) c n = a * window f c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [window, ih]; grind

omit [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
private theorem window_shift (f : Int → K) (j c : Int) (n : Nat) :
    window (fun i => f (i+j)) c n = window f (c+j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [window, ih]
    rw [show c - (n+1 : Nat) + j = c + j - (n+1 : Nat) by omega,
        show c + (n+1 : Nat) + j = c + j + (n+1 : Nat) by omega]

omit [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
theorem triple_overlap (f : Int → K) (c : Int) (n : Nat) :
    window (triple f) c n = window f (c-1) n + window f c n + window f (c+1) n := by
  change window (fun i => (f (i-1) + f i) + f (i+1)) c n = _
  rw [window_add (fun i => f (i-1) + f i) (fun i => f (i+1)),
      window_add (fun i => f (i-1)) f]
  simp only [Int.sub_eq_add_neg, window_shift]

private theorem window_mono {f g : Int → K} (h : ∀ i, f i ≤ g i) (c : Int) (n : Nat) :
    window f c n ≤ window g c n := by
  induction n with
  | zero => exact h c
  | succ n ih =>
    have := h (c - (n+1 : Nat))
    have := h (c + (n+1 : Nat))
    simp only [window]
    grind

private theorem window_increases {f : Int → K} (h : ∀ i, 0 ≤ f i)
    (c : Int) {n m : Nat} (hnm : n ≤ m) : window f c n ≤ window f c m := by
  induction hnm with
  | refl => exact Std.le_refl _
  | step hnm ih =>
    rename_i m
    have := h (c - (m+1 : Nat))
    have := h (c + (m+1 : Nat))
    simp only [window]
    grind

/-- The cost of one cell. Here b is the full mass of the enlarged cell, t the
retained mass of the original cell, and e its retained mass on the heavy event. -/
theorem cell_charge {M τ b t e : K} (hM : 0 < M) (hτ : 0 < τ) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (het : e ≤ t) (hheavy : e = 0 ∨ τ < b) :
    e ≤ M⁻¹ * b + (M/τ) * (t*t) := by
  have hmi := Field.IsOrdered.inv_nonneg_iff.mpr (Std.le_of_lt hM)
  have hti := Field.IsOrdered.inv_nonneg_iff.mpr (Std.le_of_lt hτ)
  have hu := OrderedRing.mul_nonneg hmi hb
  have hv := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (Std.le_of_lt hM) hti)
                    (OrderedRing.mul_nonneg ht ht)
  rw [Field.div_eq_mul_inv]
  rcases hheavy with he | he
  · grind
  · by_cases hm : M * t ≤ b
    · have h := (Field.IsOrdered.le_mul_inv_iff_mul_le t b hM).mpr (by grind)
      grind
    · have hprod := OrderedRing.mul_le_mul_of_nonneg_right (show τ ≤ M*t by grind) ht
      have h := (Field.IsOrdered.le_mul_inv_iff_mul_le t (M * t * t) hτ).mpr (by grind)
      grind

/-- Countable-grid form of the full-ball lemma. `full` and `kept` are all
masses on a cell, and `heavy` and `keptHeavy` are their restrictions to the
heavy event. The hypotheses express finite subprobability mass, domination
on the complement of the event, the three-cell ball containment, and the
collision bound from pairs in the same cell. -/
theorem full_ball_from_grid
    (full kept heavy keptHeavy : Int → K) (M τ retained event collision : K)
    (hM : 0 < M) (hτ : 0 < τ)
    (full0 : ∀ i, 0 ≤ full i) (kept0 : ∀ i, 0 ≤ kept i)
    (heavy0 : ∀ i, 0 ≤ heavy i)
    (retainedPart : ∀ i, keptHeavy i ≤ kept i)
    (complement : ∀ i, heavy i + kept i ≤ full i + keptHeavy i)
    (ball : ∀ i, keptHeavy i = 0 ∨ τ < triple full i)
    (prob : ∀ c n, window full c n ≤ 1)
    (sameCell : ∀ n, window (fun i => kept i * kept i) 0 n ≤ collision)
    (retainedSum : IsGridTotal kept retained) (eventSum : IsGridTotal heavy event) :
    event ≤ 1 - retained + 3/M + (M/τ) * collision := by
  let Q := 1 + 3/M + (M/τ) * collision
  have hiM := Field.IsOrdered.inv_nonneg_iff.mpr (Std.le_of_lt hM)
  have hiτ := Field.IsOrdered.inv_nonneg_iff.mpr (Std.le_of_lt hτ)
  have hcoef : 0 ≤ M/τ := by
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_nonneg (Std.le_of_lt hM) hiτ
  have localCharge (i : Int) :
      heavy i + kept i ≤ full i + (M⁻¹ * triple full i + (M/τ)*(kept i * kept i)) := by
    have hf : 0 ≤ triple full i := by
      have := full0 (i-1)
      have := full0 i
      have := full0 (i+1)
      unfold triple
      grind
    have hh := cell_charge hM hτ hf (kept0 i) (retainedPart i) (ball i)
    have hc := complement i
    grind
  have bound (n : Nat) : window heavy 0 n + window kept 0 n ≤ Q := by
    have charge := window_mono localCharge 0 n
    simp only [window_add, window_mul] at charge
    have overlap := triple_overlap full 0 n
    have cheap : window (triple full) 0 n ≤ 3 := by
      have := prob (0-1) n
      have := prob 0 n
      have := prob (0+1) n
      grind
    have hc := OrderedRing.mul_le_mul_of_nonneg_left cheap hiM
    have hs := OrderedRing.mul_le_mul_of_nonneg_left (sameCell n) hcoef
    have hf := prob 0 n
    dsimp [Q]
    rw [Field.div_eq_mul_inv 3 M]
    grind
  have combined (n m : Nat) : window heavy 0 n + window kept 0 m ≤ Q := by
    have hh := window_increases heavy0 0 (Nat.le_max_left n m)
    have hk := window_increases kept0 0 (Nat.le_max_right n m)
    have hb := bound (max n m)
    grind
  have fixed (n : Nat) : retained ≤ Q - window heavy 0 n :=
    retainedSum.2 _ (fun m => by have := combined n m; grind)
  have he := eventSum.2 (Q-retained) (fun n => by have := fixed n; grind)
  dsimp [Q] at he
  grind

end Weierstrass.Grid
