module

public import Weierstrass.DyadicRates
public import Weierstrass.GraphInformation

/-! The finite-scale estimate from the likelihood product, in physical coordinates. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Weierstrass.GraphWindow

def standardLaw : Measure ℝ := volume.restrict (Ico 0 1)

def cellMass (b l : ℝ) (φ : ℤ → ℝ) (T : ℝ) (K : ℕ) (x : ℝ) : ℝ≥0∞ :=
  let W := series b l (fun j : ℕ ↦ φ j)
  standardLaw {y | (GraphInformation.dyadicLabel K 0 y, GraphInformation.dyadicLabel K T (W y)) =
    (GraphInformation.dyadicLabel K 0 x, GraphInformation.dyadicLabel K T (W x))}

def windowSum (b l : ℝ) (φ : ℤ → ℝ) (q K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico (left q (horizontalRate b) K) (right q (verticalRate l) K),
    graphEntropy b l q (fun i ↦ ↑(environment b φ (q*j) x i))

def windowLength (b l : ℝ) (q K : ℕ) : ℕ := right q (verticalRate l) K-left q (horizontalRate b) K

def WindowMassBound (b l : ℝ) (φ : ℤ → ℝ) (T C : ℝ) : Prop :=
  ∀ᵐ x ∂standardLaw, ∃ D : ℝ, 0 ≤ D ∧
    ∀ q : ℕ, 0 < q → 1 ≤ q*verticalRate l → ∀ k : ℕ, ∀ᶠ K : ℕ in atTop,
      let m : ℝ := windowLength b l q K
      cellMass b l φ T K x ≤ ENNReal.ofReal (Real.exp
        (-(K:ℝ)*Real.log 2 + K/((k:ℝ)+1) - windowSum b l φ q K x +
          (m*Real.log C + Real.sqrt (m*D*((K:ℝ)+1)))/alpha b l))

end Weierstrass.GraphWindow
