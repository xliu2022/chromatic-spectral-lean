# ChromaticSpectral：Liu–Luo 主定理的 Lean 形式化

[English](README.md)

本工程完成论文 **The spectral radius of k-chromatic r-graphs**（Xizhi Liu、Junchi Luo，arXiv:2605.14755v1）的 **Theorem 1.3、Theorem 1.4 及其全部等号条件**，并证明二者合并后的显式界和 Corollary 1.5。

作者及维护负责人：Xizhi Liu。许可：Apache 2.0。

论文：[摘要](https://arxiv.org/abs/2605.14755) · [固定版本全文](https://arxiv.org/html/2605.14755v1)

## 已完成的结论

令

\[
B_{r,k,n,p}=r!\left(\binom nr-k\binom{n/k}{r}\right)n^{-r/p}.
\]

所有主结果均覆盖 \(r\ge4\)、\(k\ge2\)、**任意实数** \(p\ge1\) 和严格条件 \(n>(r-1)k\)。

| Lean 入口（命名空间 `ChromaticSpectral`） | 结论 |
|---|---|
| `theorem_1_3`，原声明在 `RGraph.theorem_1_3` | 弱 \(k\) 可着色 \(G\) 满足 \(\lambda^{(p)}(G)\le\lambda^{(p)}(T)\)；等号当且仅当 \(G\cong T\)。\(T\) 可为任意同阶的平衡完整弱可着色图 |
| `theorem_1_4` | \(\lambda^{(p)}(T)\le B_{r,k,n,p}\)；等号当且仅当 \(k\mid n\) |
| `chromatic_explicit_bound` | 任意弱 \(k\) 可着色 \(G\) 的谱半径不超过 \(B_{r,k,n,p}\) |
| `chromatic_explicit_eq_iff` | 上一显式界取等号，当且仅当 \(k\mid n\) 且 \(G\cong T\) |
| `corollary_1_5` | 若 \(\lambda^{(p)}(G)>B_{r,k,n,p}\)，则 \(G\) 不可弱 \(k\) 着色 |
| `exists_balanced_complete` | 在主定理范围内，满足所需定义的平衡完整参考图确实存在 |

使用任意平衡完整参考图 \(T\)，等价于论文指定的 \(Q_k^r(n)\)：工程证明了任意两个同阶、同色数的这类图同构。主定理同时允许两个不同的有限顶点类型，不依赖具体顶点编号。

## Palomar 核验

`Challenge.lean` 仅导入 Mathlib，在文件中给出弱着色、平衡完整图、谱半径和显式界的定义，并独立陈述上表六项结论。`Solution.lean` 从证明库导出六项同名定理。`comparator.json` 指定核验目标和允许的公理。`formalization.yaml` 记录与原论文的对应关系、作者、GPT 的参与和已知的审查情况。

在安装了 bubblewrap 的 Linux 环境中，运行下列命令可同时检查构建、示例、公理依赖、声明一致性及 NanoDa 重放。

```sh
lake exe cache get
python3 scripts/verify.py --comparator
```

GitHub Actions 中的 **Palomar full mechanical preflight** 使用固定版本的 Palomar 官方核验程序。运行时选择待检查的提交及与维护者的关系，机器报告位于该次运行的 artifacts 中。正式登记使用公开仓库 `xliu2022/chromatic-spectral-lean`、该提交的完整 SHA 和项目根目录下的 `comparator.json`。

## 构建与验证

固定环境：

- Lean：`leanprover/lean4:v4.35.0-rc2`。
- mathlib：`065356127b1dc0016f66b7283ce0ce2c4055aa55`。
- 全部依赖由 `lake-manifest.json` 固定。

安装好 elan 后，在工程根目录执行：

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean Examples.lean
```

`lake exe cache get` 用于获取与固定依赖对应的 mathlib 编译缓存；首次下载依赖需要访问相应 Git 仓库。源码归档不包含开发时的编译缓存。

构建、示例与公理审计可通过下列命令一起运行。

```sh
python3 scripts/verify.py
```

它执行源码机制扫描、默认 `lake build`、六个最终目标的公理审计，以及 `Examples.lean` 的编译。它检查审计对象是否齐全，并在出现额外公理时返回失败。验证记录写入 `verification/`，其中：

- `build.log`：构建记录。
- `axioms.log`：完整定理类型和传递公理依赖。
- `examples.log`：应用示例的编译记录。
- `lean-version.log`：实际 Lean 版本。
- `summary.json`：验证状态、版本、源码统计和每个 Lean 文件的 SHA-256。

随附的 `verification/clean-rebuild.json` 记录了加入 Palomar 声明前 57 个 Lean 文件的干净重建、公理审计及示例检查。每个公开提交的构建与审计另由 GitHub Actions 运行。

六个最终目标的依赖均仅包含：

```text
[propext, Classical.choice, Quot.sound]
```

证明库和 Solution 中没有 `sorry`、`admit`、自定义公理或 `native_decide`。Challenge 的六个 `sorry` 标记分别对应 Comparator 要求 Solution 提供证明的六条声明。这里的可信性结论指最终证明项及其完整依赖闭包经 Lean 内核检查；源码关键词扫描只作为补充。构建中的未使用变量、简化建议等风格提示不改变证明检查结果。

## 如何应用

只需导入总入口：

```lean
import ChromaticSpectral
open ChromaticSpectral
```

在顶点集为 `Fin n` 时，主定理可直接这样调用：

```lean
example {n r k : ℕ} {p : ℝ} (G T : RGraph (Fin n) r)
    (hr : 4 ≤ r) (hk : 2 ≤ k) (hp : 1 ≤ p)
    (hn : (r - 1) * k < n)
    (hG : G.Colorable k) (hT : T.IsBalancedComplete k) :
    G.pSpectralRadius p ≤ T.pSpectralRadius p ∧
      (G.pSpectralRadius p = T.pSpectralRadius p ↔ G.IsIsomorphic T) := by
  exact theorem_1_3 hr hk hp (by simpa using hn) rfl G T hG hT
```

`Examples.lean` 包含这个实际通过编译的调用，以及任意可着色图的显式界、\(\lambda^{(1)}(Q_2^4(8))=51/128\) 的精确推导。

## 数学定义

- `RGraph V r`：边为 `Finset (Finset V)`，每条边的基数恰为 `r`。顶点类型中可以有孤立顶点。
- `Colorable G k`：存在 `V → Fin k`，每条边都含两个颜色不同的顶点，即不存在单色边。允许空颜色类，不要求染色数恰好等于 `k`。
- `completeOfColoring r c`：给定着色下全部非单色的 `r` 元子集。
- `polyform G x`：\(r!\sum_{e\in E(G)}\prod_{v\in e}x_v\)。
- `PWeights p x`：\(x_v\ge0\) 且 \(\sum_v x_v^p=1\)。工程证明最大点存在，逐坐标取绝对值不降低 polyform，因此这个优化定义对应原文的带绝对值单位球。
- `BalancedColoring c`：任意两个颜色类的大小相差至多一。
- `IsIsomorphic G H`：存在顶点类型间的等价，并双向保留边成员关系。
- `explicitBound`：\(B_{r,k,n,p}\)。广义二项式使用 `Ring.choose ((n : ℝ) / (k : ℝ)) r`，其中除法是实数除法。

`SemanticChecks.lean` 另外检查弱着色中允许 \(3+1\) 和 \(2+2\) 的四元边、排除单色四元边，并检查 \(r!\) 规范化及一个可整除实例的显式值。

## 证明结构

### Theorem 1.3

1. `SpectralBasic` 与 `Normalization` 证明有限维紧性、最大点存在、非负球上的齐次归一化与谱半径单调性。
2. `CompleteAveraging` 与 `Positivity` 证明完整图的所有最大向量在同色类上恒定且处处为正，并推出真子图的谱半径严格较小。这些论证统一适用于所有实数 \(p\ge1\)。
3. `ExtremalColoring` 与 `WeightedBinomial` 从移动单个顶点推导最小类大小和局部质量比例。
4. `OneSignChange`、`TruncatedMoments`、`LocalBoundary`、`LocalMass` 证明所需的局部严格不等式；`LocalVectorSmoothing` 实际构造保留 \(p\) 质量的有限向量。
5. `EsymmConvolution` 与 `GlobalBalancing` 将局部各层比较接到整个图的边多项式；`ExtremalBalanced` 因此排除任何大小相差至少二的色类。
6. `BalancedIsomorphism` 证明平衡完整图的唯一同构类型；`Theorem13` 完成一般可着色图的上界和同构等号条件。

### Theorem 1.4

1. `BalancedPartitions` 给出颜色类的商余数分类；`BinomialJensen` 给出边数显式上界及可整除等号条件。
2. `ClassStationarity`、`ClassOrder`、`ClassLocalization` 将 \(p=1\) 的最大点归约为两种权重，并证明所需比例区间。
3. `ChooseConvexity`、`Curvature`、`Endpoint` 证明实二项式严格凸性、曲率和端点估计；`SymmetricMean`、`Interpolation` 提供方差亏损与插值控制。
4. `BernsteinBound` 证明所有相关 Bernstein 系数的严格正性，推出非整除情形的严格 Lagrangian 上界。
5. `Holder` 与 `SpectralTransfer` 将 \(p=1\) 结果传递到任意实数 \(p\ge1\)；均匀向量下界给出可整除情形的等号。最终在 `ExplicitTheorem` 组装。

## 与原文证明的对应及范围

形式化保留主定理和等号条件，同时使用已证明的替代论证：有限凹插值代替反常积分，有限系数的符号比较代替 Descartes 法则，有限外向转移代替无限平均过程，正系数多项式证书处理部分曲率估计。令 \(\theta=1/p\in(0,1]\) 后，局部平滑直接涵盖 \(p=1\)，无需另行复制论文第 5 节的全部论证。

详细定义对照和可信性审查见 `AUDIT.md`。完整形式化的范围是两项主定理及其证明、合并显式界和 Corollary 1.5；不声称逐条复制论文所有旁支结论。例如论文 Proposition 6.2 额外的 \(r=3\) 分支不是主定理范围，本工程没有额外实现该分支。
