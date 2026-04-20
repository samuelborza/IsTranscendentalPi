# IsTranscendentalPi

This repository contains a Lean 4 formalization of the transcendence of $\pi$, which appears as Theorem 53 on Freek Wiedijk’s list of 100 classic theorems for proof assistants; see [Freek Wiedijk’s list](https://www.cs.ru.nl/~freek/100/) for progress across multiple theorem provers, and the [Lean 100 page](https://leanprover-community.github.io/100.html), which tracks the status of these theorems specifically in `Lean`/`mathlib`.

The transcendence of $\pi$ was first proved by Lindemann in 1882 [^Lindemann1882] as a corollary of the more general Lindemann-Weierstrass theorem, which states that if $\alpha_1, \ldots, \alpha_n$ are algebraic numbers linearly independent over $\mathbb{Q}$, then $e^{\alpha_1}, \ldots, e^{\alpha_n}$ are algebraically independent. On Freek Wiedijk's list, this result appears as Theorem 54. There is also ongoing work to formalize the Lindemann-Weierstrass theorem in mathlib; see [Astrainfinita](https://github.com/astrainfinita)'s `mathlib4` fork, in particular the [`transcendental` branch](https://github.com/astrainfinita/mathlib4/tree/transcendental), as well as the current [`Mathlib/NumberTheory/Transcendental/Lindemann`](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/NumberTheory/Transcendental/Lindemann) development in the main `mathlib4` repository.

It is, however, also possible to give a direct proof of the transcendence of $\pi$ without using the Lindemann-Weierstrass theorem; this repository presents the self-contained and elegant proof given by Niven in 1939 [^Niven1939]. This project also benefited from the Coq formalization of the same proof by Bernard, Bertot, Rideau, and Strub [^BernardEtAl2016], as well as from Eberl's Isabelle formalization [^Eberl2018].

## Project history

This project began as James Huang's final project for the master's course *Formalising Mathematics* in the 2023-2024 academic year, taught by [Prof Kevin Buzzard](https://www.ma.imperial.ac.uk/~buzzard/); see the [*Formalising Mathematics* course notes](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/). The original goal proved too ambitious for the course project alone, but after the end of the course James Huang and [Samuël Borza](https://samuelborza.github.io/) teamed up to rework and complete the formalization. The present repository is the result of this collaboration.

## Sketch of the proof

We argue by contradiction, assuming that $\pi$ is algebraic. Then $i\pi$ is algebraic as well, so there exists a monic polynomial $B \in \mathbb{Q}[X]$ such that
$$
B(i\pi)=0.
$$
By the [fundamental theorem of algebra](https://en.wikipedia.org/wiki/Fundamental_theorem_of_algebra), we may write
$$
B(X)=\prod_{j=1}^d (X-\beta_j),
$$
where $\beta_1,\dots,\beta_d \in \mathbb{C}$ are the roots of $B$, one of which is $i\pi$.
Since $e^{i\pi}=-1$ by [Euler's identity](https://en.wikipedia.org/wiki/Euler%27s_identity), one obtains
$$
\prod_{j=1}^d (1+e^{\beta_j})=0,
$$
and, after expanding this product, one gets
$$ 
\sum_{\substack{I \subseteq \{1,\dots,d\} \\ \sum_{j \in I}\beta_j = 0}} e^{\sum_{j \in I}\beta_j}
+
\sum_{\substack{I \subseteq \{1,\dots,d\} \\ \sum_{j \in I}\beta_j \neq 0}} e^{\sum_{j \in I}\beta_j}
=0.
$$
Equivalently,
$$
\sum_{i = 1}^n e^{\alpha_i} = -k := -\left(\#\left\{ I \subseteq \{1,\dots,d\} \;\middle|\; \sum_{j \in I}\beta_j = 0 \right\}\right),
$$
where
$$
A=\{\alpha_1,\dots,\alpha_n\}:=\left\{\sum_{j \in I}\beta_j \;\middle|\; I \subseteq \{1,\dots,d\},\ \sum_{j \in I}\beta_j \neq 0\right\}.
$$

The next step is to package these numbers $\alpha_1,\dots,\alpha_n$ as the roots of a new polynomial $T'$, so that
$$
\prod_{I \subseteq \{1,\dots,d\}}
\left(X-\sum_{j \in I}\beta_j\right) = X^{k - 1} T'(X) := X^{k} (X - \alpha_1) \cdots (X - \alpha_n).
$$

By [Vieta's formulas](https://en.wikipedia.org/wiki/Vieta%27s_formulas), the $r$-th coefficient of $T'(X)$ is
$$
(-1)^{n-r} e_{n-r}(\alpha_1,\dots,\alpha_n),
$$
where $e_{n-r}$ denotes the $(n-r)$-th [elementary symmetric polynomial](https://en.wikipedia.org/wiki/Elementary_symmetric_polynomial). Note that this coefficient can also be obtained by evaluating the multivariate polynomial
$$
C_r(X_1, \dots, X_d) := (-1)^{N-(k+r)}\, e_{N-(k+r)}\left(\left(\sum_{j \in I} X_j\right)_{I \subseteq \{1,\dots,d\}}\right)
$$
at $(\beta_1,\dots,\beta_d)$, where
$N:=\#\left\{ I \subseteq \{1,\dots,d\}\right\} = 2^d$. The polynomial $C_r$ being symmetric, the [fundamental theorem of symmetric polynomials](https://en.wikipedia.org/wiki/Elementary_symmetric_polynomial#Fundamental_theorem_of_symmetric_polynomials) implies that $C_r$ can be expressed as a polynomial in the elementary symmetric polynomials
$$
e_1(X_1,\dots,X_d),\ \dots \,e_d(X_1,\dots,X_d).
$$
Evaluating at $(\beta_1,\dots,\beta_d)$, it follows that $C_r(\beta_1,\dots,\beta_d)$ can be expressed in terms of the elementary symmetric polynomials in the roots of $B$, and hence, by Vieta's formulas, in terms of the coefficients of $B$. Therefore, $T' \in \mathbb{Q}[X]$. By clearing denominators, one obtains an integer polynomial $T \in \mathbb{Z}[X]$ and a nonzero integer $c \in \mathbb{Z}$ such that $T = c\,T'$.

Following Niven, the proof then introduces the auxiliary polynomial
$$
F_p(X)=X^{p-1}T(X)^p, \qquad p \in \N \setminus \{0\}.
$$
An integration-by-parts and the previous identity $\sum_j e^{\alpha_j}=-k$ then shows that
$$
c^{np} \sum_{j=1}^n e^{\alpha_j}\int_0^1 \alpha_j e^{-t \alpha_j} F_p(t \alpha_j)\,dt
=
-(p-1)!\left(kc^{np} T(0)^p + p\left(kc^{np} G_p(0) + c^{np}\sum_{j=1}^n G_p(\alpha_j)\right)\right).
$$
where
$$
G_p := \frac{1}{p!}\sum_{i=p}^{\deg(F_p)} F_p^{(i)}.
$$
Since $T \in \mathbb{Z}[X]$, one has $G_p = \sum_{i=p}^{\deg(F_p)} \frac{i!}{p!}\,S_{p,i}$ for some $S_{p,i} \in \mathbb{Z}[X]$, and thus $G_p \in \mathbb{Z}[X]$.

By bounding $F_p(t \alpha_j)$ uniformly for $t\in[0,1]$, and then using $|e^{-t \alpha_j}|\le e^{|\alpha_j|}$ to control the integrand, it follows that for all sufficiently large $p$,
$$
\left\|c^{np}\sum_{j=1}^n e^{\alpha_j}\int_0^1 \alpha_j e^{-t \alpha_j}F_p(t \alpha_j)\,dt\right\|<(p-1)!.
$$

A contradiction would follow from showing that $c^{np}\sum_{j=1}^n G_p(\alpha_j) \in \mathbb{Z}$. Indeed, in that case the quantity
$$
kc^{np} T(0)^p + p\left(kc^{np} G_p(0) + c^{np}\sum_{j=1}^n G_p(\alpha_j)\right)
$$
is also an integer, and in fact a nonzero integer for all sufficiently large prime numbers $p$. If it were zero, then $p$ would divide $k\,c^{np}\,T(0)^p$, and hence would divide $k\,c\,T(0)$. But $k\,c\,T(0)\neq 0$ is a fixed integer, so it can be divisible by only finitely many primes. Therefore, for all sufficiently large prime numbers $p$, one has
$$
\left\|(p-1)!\left(kc^{np} T(0)^p + p\left(kc^{np} G_p(0) + c^{np}\sum_{j=1}^n G_p(\alpha_j)\right)\right)\right\|\geq (p-1)!,
$$
contradicting the previous bound.

It remains to show that $c^{np}\sum_{j=1}^n G_p(\alpha_j) \in \mathbb{Z}$. We write

$$
c^{np-1}\sum_{j=1}^n G_p(\alpha_j)
=
\sum_{i=p}^{\deg(F_p)} \frac{c^{np-1}}{p!}\sum_{j=1}^n F_p^{(i)}(\alpha_j),
$$
and introduce the polynomial
$$
R_{p,i}(X_1,\dots,X_n)
:=
\sum_{k=0}^{\deg(F_p)}
c^{\,np-1-k}\,\frac{i!}{p!}\,\bigl[S_{p,i}\bigr]_k\,(X_1^k+\cdots+X_n^k) \in \mathbb{Z}[X].
$$
The polynomial $R_{p,i}$ is chosen specifically so that
$$
\begin{aligned}
R_{p,i}(c \alpha_1,\dots,c \alpha_n)
&=
\sum_{k=0}^{\deg(F_p)}
c^{\,np-1-k}\,\frac{i!}{p!}\,\bigl[S_{p,i}\bigr]_k
\bigl((c \alpha_1)^k+\cdots+(c \alpha_n)^k\bigr) \\
&=
\sum_{k=0}^{\deg(F_p)}
\frac{c^{\,np-1}}{p!}\, i!\,\bigl[S_{p,i}\bigr]_k
\bigl(\alpha_1^k+\cdots+\alpha_n^k\bigr) \\
&=
\frac{c^{np-1}}{p!}\sum_{j=1}^n \sum_{k=0}^{\deg(F_p)}
i!\,\bigl[S_{p,i}\bigr]_k\,\alpha_j^k \\
&=
\frac{c^{np-1}}{p!}\sum_{j=1}^n F_p^{(i)}(\alpha_j).
\end{aligned}
$$

Furthermore, the numbers $c\alpha_1,\dots,c\alpha_n \in \mathbb{C}$ are the roots of the monic polynomial
$$
c^n\,T'(X/c)=X^n+a_{n-1}X^{n-1}+c\,a_{n-2}X^{n-2}+\cdots+c^{n-2}a_1X+c^{n-1}a_0 \in \mathbb{Z}[X],
$$
where $T(X)=cX^n+a_{n-1}X^{n-1}+\cdots+a_1X+a_0$.


The polynomial $R_{p,i}(X_1,\dots,X_n)$ is clearly symmetric. By the fundamental theorem of symmetric polynomials once again, it can therefore be expressed as a polynomial in the elementary symmetric polynomials in $X_1,\dots,X_n$. Since $(c \alpha_1,\dots,c \alpha_n)$ are the roots of the monic polynomial with integer coefficients introduced above, it follows that $R_{p,i}(c \alpha_1,\dots,c \alpha_n)$ is an integer.

Therefore, we conclude that
$$
c^{np-1}\sum_{j=1}^n G_p(\alpha_j)
=
\sum_{i=p}^{\deg(F_p)} R_{p,i}(c \alpha_1,\dots,c \alpha_n) \in \mathbb{Z},
$$
and the proof is complete.





## File structure

We briefly explain the role of each file, following the order in which the argument is assembled in the proof.

- `IsTranscendentalPi/IncrementalDerivatives.lean`:

  Develops the basic differential identities for functions of the form $t \mapsto f(tx)$ and $t \mapsto e^{-tx}$. These lemmas are used to differentiate the expressions that later appear in $\int_0^1 x e^{-tx}T(tx)\,dt$ and in the repeated integration-by-parts argument.
- `IsTranscendentalPi/SymmetricPolynomials.lean`:

  Contains the symmetric-polynomial machinery used throughout the construction of $T'$. In particular, it shows how symmetric expressions in roots can be rewritten in terms of polynomial coefficients via the elementary symmetric polynomials and Vieta's formulas.
- `IsTranscendentalPi/ComplexExponential.lean`:

  Proves the combinatorial-exponential identities coming from $\prod_{j=1}^d (1+e^{\beta_j})$. It defines subset sums and nonzero subset sums, and derives the relation $\sum_{i=1}^n e^{\alpha_i}=-k$ from the root condition $B(i\pi)=0$.
- `IsTranscendentalPi/CalculusOnPoly.lean`:

  Introduces the integral
  $
  \int_0^1 x e^{-tx}T(tx)\,dt
  $
  and proves the basic integration-by-parts identity that rewrites it in terms of sums of derivatives of $T$. This is the calculus core that later gets specialized to the auxiliary polynomials $F_p$.
- `IsTranscendentalPi/NivenPolynomials.lean`:

  Introduces Niven's auxiliary polynomials $F_p$, $S_{p,i}$, and $G_p$, and proves their fundamental algebraic properties. In particular, it relates $G_p$ to the higher derivatives of $F_p$ and computes the contribution of roots and root multiplicities to the sums appearing in the main identity.
- `IsTranscendentalPi/SubsetSumPolynomial.lean`:

  Constructs the polynomial $T'$ whose roots are the nonzero subset sums $\alpha_1,\dots,\alpha_n$ of the roots of $B$. It also proves that $T' \in \mathbb{Q}[X]$, clears denominators to obtain $T \in \mathbb{Z}[X]$, and studies the monic rescaling whose roots are $c\alpha_1,\dots,c\alpha_n$.
- `IsTranscendentalPi/ScaledAuxiliaryPolynomial.lean`:

  Proves the integrality statement for the scaled sums involving $G_p(\alpha_j)$. It introduces the symmetric polynomials $R_{p,i}$ and shows that evaluating them at $(c\alpha_1,\dots,c\alpha_n)$ yields the terms $\frac{c^{np-1}}{p!}\sum_{j=1}^n F_p^{(i)}(\alpha_j)$, from which one deduces $c^{np-1}\sum_{j=1}^n G_p(\alpha_j)\in\mathbb{Z}$.
- `IsTranscendentalPi/AnalyticEstimates.lean`:

  Establishes the analytic upper and lower bounds that drive the contradiction. On the one hand, it shows that the scaled integral expression is eventually smaller than $(p-1)!$; on the other hand, it rewrites the same expression as $(p-1)!$ times a nonzero integer for sufficiently large primes.
- `IsTranscendentalPi/Main.lean`:

  Assembles the previous ingredients into the final contradiction argument. Starting from the assumption that $\pi$ is algebraic, it constructs the polynomial $B$, the nonzero subset sums $\alpha_i$, the auxiliary polynomial $T$, and finally combines the analytic and arithmetic estimates to prove that $\pi$ is transcendental.

## Build and Dependencies

This project uses:

- Lean 4
- mathlib

The exact toolchain is pinned in `lean-toolchain`. To build the project, run

```sh
lake build
```

## Authors, License, and Final Comments

James Huang and [Samuël Borza](https://samuelborza.github.io/).

This project is released under the Apache 2.0 license, matching mathlib's license; see `LICENSE`.

Comments, corrections, improvements, and pull requests are very welcome!

## References

[^Lindemann1882]: Ferdinand von Lindemann, *Über die Ludolph'sche Zahl*,
*Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften zu Berlin*,
vol. 2 (1882), pp. 679–682; and *Über die Zahl π*,
*Mathematische Annalen* **20**(2) (1882), pp. 213–225.

[^Niven1939]: Ivan Niven, "The transcendence of pi,"
*American Mathematical Monthly* **46**(8) (1939), pp. 469–471.

[^BernardEtAl2016]: Sylvie Bernard, Yves Bertot, Laurence Rideau, and Pierre-Yves Strub,
"Formal proofs of transcendence for e and pi as an application of multivariate and symmetric polynomials,"
in *Proceedings of the 5th ACM SIGPLAN Conference on Certified Programs and Proofs* (2016), pp. 76–87.

[^Eberl2018]: Manuel Eberl, "The Transcendence of π,"
*Archive of Formal Proofs* (September 2018),
\url{https://isa-afp.org/entries/Pi_Transcendental.html}.
