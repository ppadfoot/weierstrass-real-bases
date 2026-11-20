# Hausdorff dimension of Weierstrass graphs for every real base

Lean 4 formalization of Timofei Iuzhakov’s manuscript, version 1.0.2. The main theorem is `Weierstrass.main_theorem : Weierstrass.MainStatement`. The statement, proof and published manuscript are available separately. [Definitions](Weierstrass/Graph.lean) · [Main proof](Weierstrass/MainTheorem.lean) · [Manuscript on Zenodo](https://doi.org/10.5281/zenodo.24379076) · [Version 1.0.2 on GitHub](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.0.2)

For every real $b>1$, every $1/b<\lambda<1$, and every prescribed real sequence $\varphi_j$, let

$$
 W(x)=\sum_{j=0}^{\infty}\lambda^j\cos\bigl(2\pi(b^j x+\varphi_j)\bigr).
$$

On every interval with nonempty interior, the Hausdorff dimension of its graph is $2+\log\lambda/\log b$. On every bounded such interval, the image of normalized Lebesgue measure under $x\mapsto(x,W(x))$ is exact dimensional with this exponent. The measure conclusion takes the limit over all positive radii decreasing to zero for almost every point with respect to the graph measure. The graph lives in the complex plane with its Euclidean metric. The phases are real representatives modulo one. The zero sequence gives the classical cosine function. A second statement writes the graph and measure explicitly with phases taking values directly in the additive circle. [Circle-valued statement](Weierstrass/CirclePhaseStatement.lean)

## Reproduce the verification

Use Lean 4.33.1, Lake and Python 3. Run the following commands from the directory containing this file. The toolchain, mathlib commit and package manifest are included.

~~~sh
lake update
lake exe cache get
python3 verify.py --full
~~~

The verifier compiles the project from its Lean sources in an empty build directory with warnings treated as errors. It checks that the public entry point includes every project module, admits only `propext`, `Classical.choice` and `Quot.sound` among transitive axioms, and type-checks the following independent declaration.

~~~lean
import Weierstrass

example : Weierstrass.MainStatement := Weierstrass.main_theorem

#print axioms Weierstrass.main_theorem
~~~

## Manuscript concordance

The names in the right column belong to the namespace `Weierstrass`. The accompanying proof map records the hypotheses and the dependencies used for the two appendices. [Detailed theorem map](THEOREM_MAP.md)

| Manuscript result | Checked declaration and source |
| --- | --- |
| Theorem 1.1, graph and graph measure | [`main_theorem` and `graph_and_measure_real_base`](Weierstrass/MainTheorem.lean) |
| Proposition 2.1, reciprocal transfer | [`Reciprocal.reciprocal_transfer_conjugate`](Weierstrass/ReciprocalTransfer.lean) |
| Lemma 3.1, initial exponent | [`RaySeed.half_seed_H3`](Weierstrass/HalfSeedSampled.lean), [`RaySeed.rayInformation_half`](Weierstrass/HalfSeed.lean) and [`Angular.rayInformation_half_family`](Weierstrass/HalfFamily.lean) |
| Proposition 4.1, critical estimate | [`CriticalRay.critical_occupation`](Weierstrass/CriticalOccupation.lean) |
| Proposition 5.1, improvement at equal rates | [`StripProof.equal_rate_angular_conjugate`](Weierstrass/StripAngular.lean) |
| Lemma 5.2, full ball mass from retained collisions | [`fullBallFromRetainedCollisions`](Weierstrass/FullBall.lean) |
| Proposition 6.1, transverse differentiation | [`Descent.all_differentiation_rules`](Weierstrass/DescentTheorem.lean) |
| Proposition 6.2, contracting conjugate | [`ConjugatePair.contracting_family` and `graph_and_measure_contracting_conjugate`](Weierstrass/DescentTheorem.lean) |
| Proposition A.1, graph comparison | [`graph_lower_of_anchored_information`](Weierstrass/GraphInformationLower.lean) and [`graph_of_anchored_estimate`](Weierstrass/GraphComparison.lean) |
| Theorem B.1, conditional exact dimension at every derivative index | [`Predecessor.conditional_slope_exact_dimension`](Weierstrass/ConditionalDimension.lean) |
| Theorem B.2, conditional slopes and graph dimension | [`Branch.conditional_slopes_graph`](Weierstrass/BranchConditionalGraph.lean) |

The algebraic classification uses the primitive minimal polynomial, including nonmonic polynomials. If the magnitude of the constant coefficient is smaller than $b\lambda$, a contracting conjugate exists. At equality and above, the predecessor argument gives the full anchored exponent. The transcendental branch uses the phase group directly. [Algebraic classification](Weierstrass/AlgebraicSplit.lean) · [Predecessor estimate](Weierstrass/BranchAnchor.lean) · [Transcendental graph theorem](Weierstrass/GraphComparison.lean)

Additional proofs include the dependence of the exceptional point on the phase sequence and the absolute-continuity and square-integrable-density criteria for conditional slope laws. [Exceptional point](Weierstrass/ExceptionalCusp.lean) · [Density criteria](Weierstrass/DensityCriterion.lean) · [Actual conditional law](Weierstrass/BranchDensity.lean) · [Explicit amplitude step count](Weierstrass/AmplitudeStepBudget.lean) · [Phase-uniform information limit](Weierstrass/SlopeUniformLimit.lean)
