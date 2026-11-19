# Hausdorff dimension of Weierstrass cosine graphs for real bases

**Timofei Iuzhakov** · Manuscript version **1.0.2** · 19 November 2026

[Archived preprint (DOI 10.5281/zenodo.24379076)](https://doi.org/10.5281/zenodo.24379076) · [Read the paper (PDF)](iuzhakov-weierstrass-real-bases.pdf) · [LaTeX source](iuzhakov-weierstrass-real-bases.tex) · [BibTeX](CITATION.bib)

This paper addresses the **Hausdorff dimension of the graph of the classical Weierstrass function** for real, possibly non-integer bases. In the zero-phase case the function is the cosine series

$$
W(x)=\sum_{j=0}^{\infty}\lambda^j\cos(2\pi b^j x),
\qquad b>1,\quad b^{-1}<\lambda<1.
$$

This manuscript proposes a proof that the Hausdorff dimension of its graph on every interval of positive length is $2+\log(\lambda)/\log(b)$ for every real base $b>1$, including non-integer bases. The proposed theorem also allows an arbitrary fixed sequence of phases inside the cosines. On every bounded interval of positive length it gives the same dimension for the natural graph measure, obtained by mapping uniform input on the interval to the graph.

## The Weierstrass dimension conjecture

Mandelbrot conjectured the graph dimension formula above for the classical cosine series. Mauldin and Williams give the formulation for real bases on p. 794. [Ren and Shen, historical account, p. 1059](https://archive.ymsc.tsinghua.edu.cn/pacm_download/21/11971-Ren-Shen2021_Article_ADichotomyForTheWeierstrass-ty.pdf#page=3) · [Mauldin and Williams](https://sites.itservices.cas.unt.edu/~mauldin/papers/no60.pdf)

### What is known after Shen’s theorem?

Weixiao Shen proved the formula for every integer base $b\ge 2$ and every $1/b<\lambda<1$ in the classical zero-phase case. What happens for a non-integer base such as $b=3/2$? Hunt’s random-phase theorem gives the predicted dimension for almost every phase sequence at each real base. This preprint proposes a proof for each prescribed phase sequence, including the all-zero sequence, for every real $b>1$. [Shen](https://arxiv.org/abs/1505.03986) · [Hunt](https://doi.org/10.1090/S0002-9939-98-04387-1) ([open PDF](https://user.eng.umd.edu/~bhunt/papers/hdimw.pdf)) · [Iuzhakov, preprint v1.0.2](https://doi.org/10.5281/zenodo.24379076)

For integer bases, Ledrappier related the dimension of the natural graph measure to the distribution of slopes. Ruan and Zhang proved the graph dimension formula for every integer base $b\ge7$ when the same arbitrary phase is used in every term. [Ledrappier](https://doi.org/10.1090/conm/135/1185095) · [Ruan and Zhang, Theorem 1.1](https://www.global-sci.com/ata/article/view/8206)

The lower bound is the main difficulty. The argument estimates how much time a rescaled two-sided increment spends near zero. It uses independence of the phases under Haar measure at transcendental bases, and either the finite number of possible predecessor phases or a contracting conjugate at algebraic bases.

## Version and verification

Version 1.0.2 distinguishes the fixed contraction rate from the auxiliary parameter in the ball-mass lemma, gives the order of limits in Section 6 and makes the normalization in Section 5 explicit. The [SHA-256 checksums](SHA256SUMS) identify the archived PDF and LaTeX source for version 1.0.2.

Version 1.0.1 expands the historical references, adds open copies of cited papers and supplies a permanent citation link. The author used GPT (OpenAI) and Claude (Anthropic) to test conjectures, derive and check formulas, draft arguments, and help formalize parts of the proof in Lean 4. Machine verification of the full theorem remains incomplete. The previous release is available on [GitHub](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.0.1) and [Zenodo](https://doi.org/10.5281/zenodo.24378509).

## Citation

Timofei Iuzhakov. *Hausdorff dimension of Weierstrass cosine graphs for real bases*. Manuscript, version 1.0.2, 19 November 2026. [Version 1.0.2](https://github.com/ppadfoot/weierstrass-real-bases/releases/tag/v1.0.2) · [Zenodo DOI](https://doi.org/10.5281/zenodo.24379076) · [Citation metadata](CITATION.cff)

## Гипотеза Вейерштрасса о размерности графика

Что известно после теоремы Шэня? Для классического косинусного ряда с нулевыми фазами Шэнь доказал формулу при каждом целом основании $b\ge 2$. Для нецелого основания, например $b=3/2$, возникает тот же вопрос о хаусдорфовой размерности. [Теорема Шэня](https://arxiv.org/abs/1505.03986)

В рукописи предложено доказательство формулы для хаусдорфовой размерности графика классической функции Вейерштрасса при любом вещественном основании $b>1$ и $1/b<\lambda<1$. Утверждение включает нецелые основания и любую заранее заданную последовательность фаз. [Препринт, версия 1.0.2](https://doi.org/10.5281/zenodo.24379076)
