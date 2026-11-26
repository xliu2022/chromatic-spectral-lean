# 语义、证明路线与可信性审查

审查日期：2026-11-26。论文版本：[Liu–Luo, arXiv:2605.14755v1](https://arxiv.org/html/2605.14755v1)。

本文记录一次独立的规范审查与源码审查。它区分数学陈述是否对应原文、具体模块是否已经编译、最终定理的公理闭包是否已经检查；三者不能相互替代。

## 当前状态

- `RGraph.theorem_1_3` 与 `theorem_1_4` 的完整陈述已逐项审查，两个主定理均已实际编译通过。
- `ChromaticSpectral.lean` 导入 `Main` 和 `SemanticChecks`。总入口同时包含两个主定理、任意弱可着色图的显式界及其等号条件、Corollary 1.5、平衡参考图的存在性。实现负责人已经成功运行 `lake build ChromaticSpectral` 及默认 `lake build`。
- `Audit.lean` 已实际成功运行。六个公开最终目标的公理闭包均仅含 `propext`、`Classical.choice`、`Quot.sound`。
- 局部平滑链条另已完整编译并运行 `LocalAxiomAudit.lean`，六个局部关键结论具有相同的公理依赖。
- 独立审查时扫描覆盖 56 个第一方 Lean 源文件；最终自动验证另包含新增的 `Examples.lean`，详见 `verification/summary.json`。去除注释后，没有发现禁止的证明机制；每个文件的首个非空行均为 `module`。

## 1. 定义与主定理合同

以下核对以 `Basic.lean` 为基础，并检查相应的桥接定理。论文的定义和主定理见[第 1–2 节](https://arxiv.org/html/2605.14755v1#S1)。

| 对象 | 工程中的表达 | 审查结果 |
|---|---|---|
| 有限简单 $r$-一致超图 | `RGraph V r` 的边集是 `Finset (Finset V)`，`uniform` 要求每条边的基数恰为 `r` | 无序边、无重复边、无重复顶点；孤立顶点仍属于顶点类型 `V` |
| 阶数 | `Fintype.card V` | 始终计算全部顶点，没有改成非孤立顶点数 |
| 弱 $k$ 可着色 | `Colorable G k`：存在 `c : V → Fin k`，每条边包含两个颜色不同的顶点 | 正确表达“没有单色边”；并未要求每条边的顶点颜色两两不同，也未要求 $\chi(G)=k$ |
| 允许空颜色类 | 着色函数不要求满射 | 与通过非负类大小参数化的完全着色图一致；主定理所用极值图的非空性在后续证明中导出 |
| 完全弱着色图 | `completeOfColoring r c` 包含全部非单色的 `r` 元子集 | 与上述弱着色一致；不是每条边至多取每类一个顶点的另一种完全多部图 |
| 多项式规范化 | `polyform G x = (r.factorial : ℝ) * edgePolynomial G x` | 保留原文的 $r!$ 因子。内部一些比较使用未乘 $r!$ 的边多项式，再乘正因子返回谱量 |
| 谱参数 | 所有主接口中的 `p : ℝ` 和 `hp : 1 ≤ p` | 覆盖全部实数参数，包括 $p=1$，没有限制为自然数或有理数 |
| 单位约束 | `PWeights p x` 要求 `x ≥ 0` 且 `∑ v, (x v)^p = 1` | 使用实数幂。与带绝对值的原始优化问题之间的关系见下文 |
| 谱值 | `sSup (insert 0 {...})` | 在主定理的非空顶点范围内由紧性证明取到最大值；不是以“存在最大值”作为额外公理 |
| 平衡 | `BalancedColoring c := ∀ i j, classSize c i ≤ classSize c j + 1` | 同时对两个顺序量化，确实要求任意两个类大小相差至多一 |
| 完全平衡图 | `IsBalancedComplete G k` 存在一个平衡着色并要求 `G = completeOfColoring r c` | 作为同标号图上的中间谓词正确；主定理的最终等号使用显式同构关系 |
| 严格阈值 | `(r - 1) * k < Fintype.card V` | 保留严格不等号。这里 `r ≥ 4`，自然数减法没有截断歧义 |
| 广义二项式 | `Ring.choose ((n : ℝ) / (k : ℝ)) r` | 先转为实数再除法，确实是 $n/k$，没有误用自然数商 $\lfloor n/k\rfloor$ |
| 整数二项式 | `(n.choose r : ℝ)` | 自然数二项式再嵌入实数；与 `Ring.choose (n : ℝ) r` 的一致性由 `realChoose_natCast` 提供 |
| 谱界中的幂 | `(n : ℝ) ^ (-(r : ℝ) / p)` | 负号作用于实数，表达 $n^{-r/p}$；没有自然数负号或整数除法 |
| 同构 | 存在 `f : V ≃ W`，且对所有有限顶点子集双向保边 | 允许跨两个同阶有限顶点类型；不是单向同态或仅保正边的映射 |

### 非负优化与带符号优化

工程没有另外定义一个带符号版本的谱半径。它证明了 `polyform_le_abs`：逐坐标取绝对值不降低多项式，以及 `signed_polyform_le_pSpectralRadius`：任意满足原始绝对值约束的向量都不超过所定义的谱半径。另一方面，`exists_maximizer` 在非空有限顶点类型上构造非负最大点，该向量也满足原始绝对值约束。这两方面足以确定两个优化问题具有相同的最大值。

`spectralValues` 中额外放入的 `0` 用于使定义在空顶点类型等退化情形也总有非空取值集合。主定理假设推出顶点类型非空，非负可行集非空，且多项式在其上非负；因此这个额外元素不改变主定理所使用的最大值。`pWeights_isCompact`、`pWeights_nonempty`、`spectralValues_bddAbove` 和 `exists_maximizer` 分别处理这些事实。

### Theorem 1.3 的最终合同

`ChromaticSpectral.RGraph.theorem_1_3` 的假设恰包含：

- `4 ≤ r`、`2 ≤ k`、`p : ℝ`、`1 ≤ p`。
- `(r - 1) * k < Fintype.card V`。
- `G : RGraph V r` 弱 `k` 可着色。
- `T : RGraph W r` 是完全平衡弱着色图，且两个顶点类型同阶。

其结论同时给出

\[
\lambda^{(p)}(G)\leq\lambda^{(p)}(T),\qquad
\lambda^{(p)}(G)=\lambda^{(p)}(T)\iff G\cong T.
\]

参考图 `T` 可取任意完全平衡代表。`balanced_complete_isomorphic` 保证同阶的代表同构，`IsIsomorphic.pSpectralRadius_eq` 保证谱值与标号无关。`exists_extremal_balanced_coloring` 还在所需参数范围内提供平衡代表的存在性，因此主合同并非依赖一个可能不存在的参考对象而成立。

合同没有假设 `G` 已完全、已平衡、已极值、最大向量为正，或者目标谱不等式成立。所有这些中间性质均在证明内部获得。等号的正向证明先排除严格子图，再从极值性得到平衡，最后转成图同构。严格子图比较使用“每个非负最大向量均正”的结论，未用“存在一个正最大向量”代替它。

### Theorem 1.4 的最终合同

`ChromaticSpectral.theorem_1_4` 的对象假设是 `G.IsBalancedComplete k`，参数范围与 Theorem 1.3 一致。结论是

\[
\lambda^{(p)}(G)\leq
r!\left(\binom nr-k\binom{n/k}{r}\right)n^{-r/p},
\]

且等号当且仅当 `k ∣ Fintype.card V`。这是平衡完全图的评价界。对任意弱可着色图，工程另有合并显式界，其等号条件还包含与平衡完全图同构。

`Main.lean` 中的 `chromatic_explicit_eq_iff` 恰以“可除且同构”为等号条件；`corollary_1_5` 在相同参数范围内，从严格超过显式界推出 `¬ G.Colorable k`。这两个合同也已通过语义检查、最终编译和公理闭包检查。

## 2. 证明依赖与原文路线的替换

本工程形式化的是主结论及其完整证明链，不要求把原文所有中间命题逐字逐序重写。以下替换均以已经证明的有限或代数命题实现，不把替换后的结论当作新的假设。

| 证明任务 | 主要模块 | 实现方式 |
|---|---|---|
| 有限谱优化、绝对值归约、最大点存在 | `SpectralBasic`、`Normalization` | 有限维紧性、连续性、齐次归一化 |
| 完全着色图最大向量的类内常值性、严格正性与严格子图比较 | `TwoCoordinate`、`Averaging`、`CompleteAveraging`、`Positivity` | 两坐标平均与正系数的有限比较，完整证明所需结构结论 |
| 极值着色的类大小下界 | `ClassMove`、`ExtremalColoring`、`NonemptyComplete` | 移动一个顶点，直接计算增减边的贡献 |
| 局部质量不等式 | `WeightedBinomial` | 二项式与自然数幂的比较，再得到 $p$ 次质量的比较；Theorem 1.3 不需要完整的结构命题 3.1 |
| 完整局部层不降 | `TwoCoordinate`、`SymmetricMean` | 固定总和的有限两坐标转移；`endpoint_rpow_esymm_le` 不依赖一个未形式化的完整 majorization 理论 |
| 固定质量的单块比较 | `ConstantBlock` | 由归一化二项式的单调性得到任意次数的常值块比较 |
| 纯交叉层严格增加 | `TruncatedMoments` 至 `LocalMass` | 有限截断矩、显式正证书、一次符号变化与系数比单调性 |
| 局部向量到整张图 | `LocalVectorSmoothing`、`EsymmConvolution`、`GlobalBalancing` | 构造真实向量并证明质量守恒；通过生成多项式的系数卷积比较全图 |
| 极值图平衡与等号 | `ExtremalBalanced`、`BalancedPartitions`、`BalancedIsomorphism`、`Theorem13` | 局部改进矛盾、类大小纤维的有限等价、谱同构不变性 |
| 广义二项式的显式界 | `RealChoose`、`Curvature`、`ChooseConvexity`、`Endpoint`、`BernsteinBound` | 实二项式多项式、导数与有限系数证书 |
| 平衡图两权重归约与所有实数 $p$ 的传递 | `ClassStationarity`、`ClassOrder`、`LocalizationNumerics`、`ClassLocalization`、`ExplicitTheorem`、`SpectralTransfer` | 拉格朗日端点的一维局部变分和区间定位，再用有限 Hölder 不等式 |

### 2.1 用有限折线插值处理实数幂

`TruncatedMoments` 定义

\[
M(T)=\sum_i a_i\min\{T,x_i\}.
\]

在所有相关支撑值以及 $0$ 构成的有限结点集上，凹增函数由截断函数 `min T x` 的非负线性组合精确表示。把每个截断矩比较乘以相应系数后求和，即得到函数值的比较。这个证明只需要有限求和，不引入反常积分或端点的积分收敛论证。

对 $f(t)=t^\theta$，`rpow_sum_lt_of_truncatedMoment_le` 要求 $0<\theta\le1$，并由严格的总一阶矩比较得到严格性。它不依赖 $f$ 的严格凹性，因而自然包括 $\theta=1$。

### 2.2 只证明实际使用的边界范围

局部纯交叉证明使用 $3\le s\le c$。这正是主定理应用所需的范围：极值图的最小类大小至少为 $r-1$，取 $c=b+1$ 和 $s=r$ 即可。工程没有为证明主定理而额外实现所有较小类大小的分支。

令

\[
q=1-\frac1c,\qquad \beta=1-\frac1{c^2}.
\]

`LocalBinomial` 与 `LocalBalancing` 给出部分和、分部求和和损失项的显式恒等式。关键的正下界含有

\[
\frac{\binom{c-1}{s-2}}{s-1}
\left((c-1)q^{s-1}-(c-s+1)q^j\right)>0
\quad(1\le j<s).
\]

`LocalBoundary` 先在所有负侧支撑点证明截断矩差为正，再由 `TruncatedSupport` 延拓到所有非负截断值。Bernoulli 估计保留的余量为 $(s-2)/c>0$，因此端点 $\theta=1$ 的严格性没有丢失。

### 2.3 一次符号变化的直接传播

`OneSignChange` 和 `OrderedSign` 用有限项的逐项比较传播多项式正性。`LocalRatios` 验证二项式系数比的反单调性；`LocalCross` 据此从已验证的边界得到整个质量区间的严格不等式。这里不需要 Descartes 符号法则，也不需要证明某个特定首项系数为正后再数实根。

`LocalMass.lean` 中的 `pureCross_mass_lt` 的最终条件是

\[
3\le s\le c,\quad 0<\theta\le1,\quad A>0,\quad
B\ge\frac{c}{c+1}A.
\]

取 $\theta=1/p$ 即覆盖所有实数 $p\ge1$。因此 Theorem 1.3 的实现把 $p=1$ 与 $p>1$ 合并在同一条局部证明链中，不另行依赖原文第 5 节。

### 2.4 用卷积合并外部层

`LocalSmoothingWitness` 同时给出非负性、局部外坐标不变、$p$ 次质量守恒、全部完整局部层不降、缩小块的全部对称和不增，以及纯交叉层严格增加。

`GlobalBalancing` 通过不交并的对称和卷积将这些事实组合为完整边多项式的严格增加。外部坐标只要求非负，不要求外部颜色类上的权重恒定。这使得独立的一侧局部层总定理不再是主证明的依赖。

### 2.5 显式界保留其独立的分析内容

Theorem 1.4 仍需要平衡图最大向量的两权重归约、权重比区间定位、广义二项式的严格凸性、终端系数估计及 Bernstein 系数比较。相应模块使用真实多项式、导数、有限对称和与精确不等式。它没有用有限参数抽样或浮点计算代替全参数证明。

`Holder.lean` 中的 `RGraph.pSpectralRadius_holder` 包括 $p=1$，`SpectralTransfer` 把拉格朗日界和严格性传递到所有有限实数 $p\ge1$。可除情形再结合均匀向量给出的下界证明等号；不可除情形保留严格不等式。

## 3. 源码与可信计算审查

审查范围是项目根目录和 `ChromaticSpectral/` 中的全部第一方 `.lean` 文件；`.lake` 中的依赖源码与构建缓存不纳入关键词扫描。依赖版本由 `lake-manifest.json` 固定，实际被使用的外部证明依赖还应由最终定理的公理闭包检查覆盖。

实际递归扫描未发现以下机制：

- `sorry`、`admit`、`sorryAx` 或第一方 `axiom` 声明。
- `native_decide`、`ofReduceBool`、`ofReduceNat`。
- `unsafe`、`extern`、`implemented_by` 或跳过内核检查的选项。
- 自定义 `elab`、`macro`、`Lean.Meta`、`Lean.Elab` 或 `run_tac` 证明扩展。

所有已扫描 `.lean` 源文件的首个非空行均为 `module`。源码中的 `#print axioms` 是审计命令，不是公理声明；注释中出现单词 “axiom” 也不构成声明。

`noncomputable`、经典选择、`simp`、`ring`、`nlinarith`、`omega`、`norm_num` 等的存在不表示绕过证明检查。验收标准是最终生成的证明项由 Lean 内核接受，且公理依赖仅含约定的三项基础公理。源码扫描是补充证据，不能代替这一闭包检查。

### 已实际运行的局部公理审计

`lake env lean LocalAxiomAudit.lean` 已成功运行，输出如下六个目标均只依赖

```text
[propext, Classical.choice, Quot.sound]
```

审计目标为：

```lean
ChromaticSpectral.oneSignChange_pos_above
ChromaticSpectral.rpow_sum_lt_of_truncatedMoment_le
ChromaticSpectral.gap_boundary_rpow_lt
ChromaticSpectral.pureCross_mass_lt
ChromaticSpectral.constantBlock_reduce
ChromaticSpectral.exists_localSmoothingWitness
```

此结果认证相应证明实际使用的传递依赖，不声称认证所有已导入但未使用的 mathlib 声明。两个主定理和公开推论另有下面的最终公理审计。

## 4. 最终验证记录与复现

本次审查没有改动其他作者的 Lean 文件，也没有增加数值测试。最终验收以总入口构建、主定理公理闭包和源码扫描为依据。

1. 总入口已经导入完整主定理及公开推论，`lake build ChromaticSpectral` 和默认 `lake build` 成功。
2. `lake env lean Audit.lean` 成功。`RGraph.theorem_1_3`、`theorem_1_4`、`chromatic_explicit_bound`、`chromatic_explicit_eq_iff`、`corollary_1_5`、`exists_balanced_complete` 的 `#print axioms` 输出均只有三项约定的基础公理。
3. 最新源码扫描没有发现 `sorry`、自定义公理、原生计算公理或内核绕过机制。主定理合同没有加入隐藏的极值性、正性或目标结论假设。
4. 非负谱定义、同构关系、实数二项式及两项等号条件已分别完成语义核对。

已安装固定工具链和依赖缓存的环境可以用以下命令重现主要检查：

```sh
lake build
lake env lean Audit.lean
lake env lean LocalAxiomAudit.lean
```

环境约定为 Lean `4.35.0-rc2`、mathlib 提交 `065356127b1dc0016f66b7283ce0ce2c4055aa55`。此处记录的是可复现的证明环境；开发机器上的缓存路径不是数学证明的前提。

### 最终独立目录重建

已在不含本项目编译产物的新目录中运行 `scripts/verify.py`，从源码构建全部主定理依赖，并重新运行 `Audit.lean` 与 `Examples.lean`。全部通过。第三方依赖缓存的实际 mathlib 提交与固定版本一致，57 个交付 Lean 文件的 SHA-256 与本次重建逐项一致。验证记录见 `verification/summary.json` 和 `verification/clean-rebuild.json`。
