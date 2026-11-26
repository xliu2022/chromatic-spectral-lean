# The spectral radius of k-chromatic r-graphs in Lean

[中文说明](README_zh.md)

This project formalizes Theorems 1.3 and 1.4 and Corollary 1.5 of Xizhi Liu
and Junchi Luo. Let $r\ge4$, $k\ge2$, $n>(r-1)k$ and let $p\ge1$ be real.
Among all weakly $k$-colourable $r$-uniform hypergraphs on $n$ vertices, the
unique maximizer of the $p$-spectral radius, up to isomorphism, is the balanced
complete weakly $k$-colourable graph. Its edges are exactly the $r$-sets that
meet at least two colour classes. [Paper, arXiv:2605.14755v1](https://arxiv.org/abs/2605.14755v1)

Every such graph satisfies

$$
\lambda^{(p)}(G)\le r!\left(\binom nr-k\binom{n/k}{r}\right)n^{-r/p}.
$$

Equality holds exactly when $k$ divides $n$ and $G$ is isomorphic to the
balanced complete graph. A graph above this threshold has chromatic number
at least $k+1$.

| Result | Declaration in the `ChromaticSpectral` namespace |
|---|---|
| Theorem 1.3, including uniqueness | `RGraph.theorem_1_3` |
| Theorem 1.4, including strictness in the nondivisible case | `theorem_1_4` |
| Explicit bound for every weakly colourable graph | `chromatic_explicit_bound` |
| Equality criterion for the explicit bound | `chromatic_explicit_eq_iff` |
| Corollary 1.5, the spectral colouring criterion | `corollary_1_5` |
| Existence of the balanced complete reference graph | `exists_balanced_complete` |

## Build and check

The project pins Lean 4.35.0-rc2 and its Mathlib dependencies. With elan
installed, run the following commands from the repository root.

```sh
lake exe cache get
python3 scripts/verify.py
```

The script builds the proof library and both Palomar modules, compiles the
examples and checks the transitive axioms of all six results. To use the
results in Lean, import `ChromaticSpectral`. [Compiled examples](Examples.lean)

## Palomar verification

The Challenge gives the mathematical definitions and six statements using
Mathlib alone. The Solution exports the original proofs. The three permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`.
[Challenge](Challenge.lean) · [Solution](Solution.lean) · [Comparator configuration](comparator.json)

On Linux with bubblewrap installed, run `python3 scripts/verify.py --comparator`
to compare the declarations and replay the proofs with Lean and NanoDa.
The **Palomar full mechanical preflight** workflow runs Palomar's pinned
verifier against the chosen Git commit. Its downloadable report records the
outcome. [GitHub Actions](https://github.com/xliu2022/chromatic-spectral-lean/actions/workflows/palomar-preflight.yml)

Xizhi Liu is the formalization author and responsible maintainer. The project
uses the Apache-2.0 licence. The metadata describes the original paper, GPT
assistance, review and proof adaptations.
[Formalization metadata](formalization.yaml) · [Proof audit in Chinese](AUDIT.md) · [License](LICENSE)
