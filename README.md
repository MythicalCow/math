# Math

Two conjectured continued-fraction identities are formalized in Lean 4 with Mathlib. Both proofs use bounded moments to identify the limit of the convergents.

| Identity | Proof guide | Lean theorem |
| --- | --- | --- |
| **Ramanujan Machine `rm-z2-new8`** · $(3\pi^2+16)/(16-\pi^2)$ | [PDF](output/pdf/ramanujan-pcf.pdf) · [LaTeX](ramanujan-pcf.tex) | [`PCF.pcf_target`](PcfProof/PCF.lean) |
| **Catalan’s constant** · $1/(2G)$ | [PDF](output/pdf/catalan-pcf.pdf) · [LaTeX](catalan-pcf.tex) | [`CatalanPCF.catalan_pcf_target`](PcfProof/Catalan.lean) |

## The two proofs

A polynomial continued fraction has the form

$$
a_0+\cfrac{b_1}{a_1+\cfrac{b_2}{a_2+\ddots}}.
$$

Lean expresses each identity as convergence of the continuant ratios $P_n/Q_n$. The sequences $P_n$ and $Q_n$ both satisfy $Z_n=a_n Z_{n-1}+b_n Z_{n-2}$ for $n\geq 1$, with initial pairs $(P_{-1},P_0)=(1,a_0)$ and $(Q_{-1},Q_0)=(0,1)$.

- **The $\pi^2$ identity** uses $a_n=3n^2+9n+7$ and $b_n=-(2n^4+3n^3-3n^2-7n-3)$. A first-order recurrence for moments of $1-\cos x$ yields normalized numerator and denominator limits in terms of $\pi^2/8$.
- **The Catalan identity** uses $a_n=3n^2+3n+1$ and $b_n=-2n^4$, where $G=\sum_{k=0}^{\infty}(-1)^k/(2k+1)^2$. Elliptic moments satisfy the same recurrence as the factorial-normalized continuants. Their initial value is $2G$.

## Check the formal proofs

With Elan installed, run these commands from the project directory. The [toolchain file](lean-toolchain) pins Lean 4.36.0, and the [Lake configuration](lakefile.toml) pins Mathlib.

```sh
lake exe cache get
lake build
```

In a Lean buffer within the project, import the library and inspect the theorem dependencies.

```lean
import PcfProof

#print axioms PCF.pcf_target
#print axioms CatalanPCF.catalan_pcf_target
```

## Rebuild the proof guides

With Tectonic installed, run the following from the project directory.

```sh
mkdir -p output/pdf
tectonic --outdir output/pdf ramanujan-pcf.tex
tectonic --outdir output/pdf catalan-pcf.tex
```
