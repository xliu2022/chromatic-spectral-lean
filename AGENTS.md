# ChromaticSpectral
Author and responsible maintainer: Xizhi Liu.
Source: Liu–Luo, arXiv:2605.14755v1.
Use Lean 4.35.0-rc2 and pinned mathlib. Every source starts with `module` and uses public declarations as needed. Do not use sorry, custom axioms, native_decide, or conditional assumptions that conceal the target theorem in the proof development. Unproved targets are explicitly named propositions, not theorems. Do not claim a target proved until its complete dependency closure compiles and passes an axiom audit. Keep shared definitions in Basic.lean stable; coordinate additions. Use the finite-support p-sphere and finite r-uniform hypergraphs. The main results quantify over all real p >= 1 and include equality cases.
Use the toolchain selected by lean-toolchain. Local dependency caches are optional; lake-manifest.json pins portable dependencies.
