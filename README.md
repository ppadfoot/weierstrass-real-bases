# Hausdorff dimension of Weierstrass cosine graphs for real bases

**Timofei Iuzhakov** · Manuscript version **1.0.1** · 19 November 2026

[Read the paper (PDF)](iuzhakov-weierstrass-real-bases.pdf) · [LaTeX source](iuzhakov-weierstrass-real-bases.tex) · [BibTeX](CITATION.bib)

This paper addresses the **Hausdorff dimension of the graph of the classical Weierstrass function** for real, possibly non-integer bases. In the zero-phase case the function is the cosine series

$$
W(x)=\sum_{j=0}^{\infty}\lambda^j\cos(2\pi b^j x),
\qquad b>1,\quad b^{-1}<\lambda<1.
$$

This manuscript proposes a proof that the Hausdorff dimension of its graph on every interval of positive length is $2+\log(\lambda)/\log(b)$ for every real base $b>1$, including non-integer bases. The proposed theorem also allows an arbitrary fixed sequence of phases inside the cosines. On every bounded interval of positive length it gives the same dimension for the natural graph measure, obtained by mapping uniform input on the interval to the graph.

## The conjecture and earlier results

Mauldin and Williams record the real-base Weierstrass graph dimension conjecture on p. 794. Shen proved the formula for every integer base with zero phases. Hunt proved it for real bases for almost every sequence of random phases. The claim investigated here includes each non-integer base and each prescribed phase sequence, including zero phases. [Mauldin and Williams](https://sites.itservices.cas.unt.edu/~mauldin/papers/no60.pdf) · [Shen](https://arxiv.org/abs/1505.03986) · [Hunt](https://doi.org/10.1090/S0002-9939-98-04387-1) ([open PDF](https://user.eng.umd.edu/~bhunt/papers/hdimw.pdf))

For integer bases, Ledrappier related the dimension of the natural graph measure to the distribution of slopes. Ruan and Zhang proved the graph dimension formula for every integer base $b\ge7$ when the same arbitrary phase is used in every term. [Ledrappier](https://doi.org/10.1090/conm/135/1185095) · [Ruan and Zhang, Theorem 1.1](https://www.global-sci.com/ata/article/view/8206)

The lower bound is the main difficulty. The argument estimates how much time a rescaled two-sided increment spends near zero. It uses independence of the phases under Haar measure at transcendental bases, and either the finite number of possible predecessor phases or a contracting conjugate at algebraic bases.

## Version and verification

Version 1.0.1 expands the historical references, adds open copies of cited papers and supplies a permanent citation link. The author used GPT (OpenAI) and Claude (Anthropic) to test conjectures, derive and check formulas, draft arguments, and help formalize parts of the proof in Lean 4. Machine verification of the full theorem remains incomplete. The [SHA-256 checksums](SHA256SUMS) identify the PDF and LaTeX source of this version.

## Citation

Timofei Iuzhakov. *Hausdorff dimension of Weierstrass cosine graphs for real bases*. Manuscript, version 1.0.1, 19 November 2026. [Version 1.0.1](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.0.1) · [Citation metadata](CITATION.cff)

## По-русски

В рукописи предложено доказательство формулы для хаусдорфовой размерности графика классической функции Вейерштрасса при любом вещественном основании $b>1$ и $1/b<\lambda<1$. Утверждение включает нецелые основания и любую заранее заданную последовательность фаз.
