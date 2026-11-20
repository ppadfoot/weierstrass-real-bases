# Hausdorff dimension of Weierstrass cosine graphs for real bases

**Timofei Iuzhakov** · Manuscript version **1.1.0** · 20 November 2026

[Article and abstract](https://ppadfoot.github.io/weierstrass-real-bases/) · [Archived preprint (DOI 10.5281/zenodo.24395193)](https://doi.org/10.5281/zenodo.24395193) · [Read the paper (PDF)](iuzhakov-weierstrass-real-bases.pdf) · [LaTeX source](iuzhakov-weierstrass-real-bases.tex) · [Lean 4 proof](formalization/Weierstrass/MainTheorem.lean) · [Download the formalization (ZIP)](https://github.com/ppadfoot/weierstrass-real-bases/releases/download/v1.1.0/weierstrass-lean.zip) · [BibTeX](CITATION.bib)

This paper addresses the **Hausdorff dimension of the graph of the classical Weierstrass function** for real, possibly non-integer bases. In the zero-phase case the function is the cosine series

$$
W(x)=\sum_{j=0}^{\infty}\lambda^j\cos(2\pi b^j x),
\qquad b>1,\quad b^{-1}<\lambda<1.
$$

Theorem 1.1, formally verified in Lean 4, proves that the Hausdorff dimension of its graph on every interval of positive length is $2+\log(\lambda)/\log(b)$ for every real base $b>1$, including non-integer bases. The theorem also allows an arbitrary fixed sequence of phases inside the cosines. On every bounded interval of positive length it gives the same dimension for the natural graph measure, obtained by mapping uniform input on the interval to the graph.

## The Weierstrass dimension conjecture

Mandelbrot’s conjecture concerns the Hausdorff dimension of the graph of the classical cosine series. The base $b$ is the frequency ratio between successive terms, so allowing every real frequency ratio $b>1$ includes non-integer bases. Mauldin and Williams give the formulation for real bases on p. 794. [Ren and Shen, historical account, p. 1059](https://archive.ymsc.tsinghua.edu.cn/pacm_download/21/11971-Ren-Shen2021_Article_ADichotomyForTheWeierstrass-ty.pdf#page=3) · [Mauldin and Williams](https://sites.itservices.cas.unt.edu/~mauldin/papers/no60.pdf)

### What is known after Shen’s theorem?

Weixiao Shen proved the formula for every integer base $b\ge 2$ and every $1/b<\lambda<1$ in the classical zero-phase case. What happens for a non-integer base such as $b=3/2$? Hunt’s random-phase theorem gives the predicted dimension for almost every phase sequence at each real base. The Lean-verified theorem in this preprint applies to each prescribed phase sequence, including the all-zero sequence, for every real $b>1$. [Shen](https://arxiv.org/abs/1505.03986) · [Hunt](https://doi.org/10.1090/S0002-9939-98-04387-1) ([open PDF](https://user.eng.umd.edu/~bhunt/papers/hdimw.pdf)) · [Iuzhakov, preprint v1.1.0](https://doi.org/10.5281/zenodo.24395193)

For integer bases, Ledrappier related the dimension of the natural graph measure to the distribution of slopes. Ruan and Zhang proved the graph dimension formula for integer $b\ge7$ when every term has the same phase $\theta$. Ren and Shen’s Corollary 1.1 gives the formula for every integer $b\ge2$ and every such $\theta$. The preprint linked above considers a prescribed sequence $\theta_j$ that may vary from term to term. [Ren and Shen, Corollary 1.1](https://doi.org/10.1007/s00222-021-01060-2) · [Ledrappier](https://doi.org/10.1090/conm/135/1185095) · [Ruan and Zhang, Theorem 1.1](https://www.global-sci.com/ata/article/view/8206)

The lower bound is the main difficulty. The argument estimates how much time a rescaled two-sided increment spends near zero. It uses independence of the phases under Haar measure at transcendental bases, and either the finite number of possible predecessor phases or a contracting conjugate at algebraic bases.

## Lean 4 formalization

Version 1.1.0 includes the complete machine-checked proof of the graph and graph-measure theorem for all real bases, along with the source, theorem map and verification log. In the Lean project, `Weierstrass.main_theorem : Weierstrass.MainStatement` is the unconditional theorem. Its statement quantifies over the base, amplitude, prescribed phases and interval. A second statement writes the phases directly in the additive circle. [Mathematical definitions](formalization/Weierstrass/Graph.lean) · [Main theorem](formalization/Weierstrass/MainTheorem.lean) · [Circle-valued phases](formalization/Weierstrass/CirclePhaseStatement.lean)

The clean build checked all 11 numbered results in the manuscript and audited 1,643 public declarations using Lean 4.33.1 and the pinned version of mathlib. To repeat it, download and extract the [proof archive](https://github.com/ppadfoot/weierstrass-real-bases/releases/download/v1.1.0/weierstrass-lean.zip). In the extracted directory containing `lean-toolchain` and `verify.py`, run the following commands with Lean, Lake and Python 3 installed.

```sh
lake update
lake exe cache get
python3 verify.py --full
```

The final check verifies the main theorem and reports its transitive axioms as `propext`, `Classical.choice` and `Quot.sound`. The theorem map gives the corresponding Lean declarations for each numbered result. [Theorem map](formalization/THEOREM_MAP.md) · [Reproduction guide](formalization/README.md)

## Version history

Version 1.0.2 clarified the order of limits in Section 6 and the normalization in Section 5. Version 1.0.1 expanded the historical references and added open copies of cited papers. The author used GPT (OpenAI) and Claude (Anthropic) to test conjectures, derive and check formulas, draft arguments and develop the Lean formalization. [Version 1.0.2 on GitHub](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.0.2) · [Version 1.0.2 on Zenodo](https://doi.org/10.5281/zenodo.24379076)

To find this preprint by subject on GitHub, search repositories for [Weierstrass non-integer dimension](https://github.com/search?q=Weierstrass+non-integer+dimension&type=repositories). The same [public repository search in JSON](https://api.github.com/search/repositories?q=Weierstrass+non-integer+dimension) gives the repository URL for readers using a search assistant.

## Verify the Zenodo preprint

1. Open the [version record on Zenodo](https://zenodo.org/records/24395193). Check the author **Timofei Iuzhakov**, version **1.1.0**, and DOI **10.5281/zenodo.24395193**. To find it by subject, try [Weierstrass AND "Hausdorff dimension" in Zenodo](https://zenodo.org/search?q=Weierstrass%20AND%20%22Hausdorff%20dimension%22&sort=bestmatch).
2. Download the PDF, LaTeX source, `weierstrass-lean.zip` and `verification.log` from **Files**. Save them in the same folder as [SHA256SUMS from the GitHub v1.1.0 tag](https://raw.githubusercontent.com/ppadfoot/weierstrass-real-bases/v1.1.0/SHA256SUMS). In that folder run `shasum -a 256 -c SHA256SUMS` on macOS or `sha256sum -c SHA256SUMS` on Linux. Check that each filename in the checksum list is followed by `OK`. This verifies that the downloaded files match the release.
3. To review the mathematics, start with **Theorem 1.1**. It gives separate assertions for the graph and for the image of uniform measure on a bounded interval. Section 1.2 identifies the proof for each arithmetic type of base. Trace the lower bound through the sections and appendices cited for that type. An equation number, the hypotheses at that step, and the implication in question let another reader reproduce a proof check.

## How to cite this preprint

Iuzhakov, Timofei (2026). *Hausdorff dimension of Weierstrass cosine graphs for real bases* (preprint, version 1.1.0). Zenodo. [DOI 10.5281/zenodo.24395193](https://doi.org/10.5281/zenodo.24395193)

[Download BibTeX](CITATION.bib) · [Citation metadata](CITATION.cff) · [GitHub release v1.1.0](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.1.0)

For LaTeX, paste this entry into your `.bib` file and use `\cite{iuzhakov2026weierstrass}` in the text.

```bibtex
@unpublished{iuzhakov2026weierstrass,
  author   = {Iuzhakov, Timofei},
  title    = {Hausdorff dimension of {Weierstrass} cosine graphs for real bases},
  year     = {2026},
  month    = nov,
  note     = {Preprint with a kernel-checked Lean 4 formalization, version 1.1.0, dated 20 November 2026},
  doi      = {10.5281/zenodo.24395193},
  url      = {https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.1.0},
  keywords = {classical Weierstrass function, Hausdorff dimension, non-integer bases,
              prescribed phases, exact-dimensional measures, Lean 4, formal verification}
}
```
