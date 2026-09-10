# 1-Y 数值展开与良序形式化

2026-09-10。此目录是核心工程的 `OneY` 库，已完成实际数值展开、父图复制、规范重建及其到良基性的组合证明。具体语义层也已供应有限反射和初始表示；[ActualWellOrdering.lean](../Concrete/OneYTruth/ActualWellOrdering.lean) 给出不再要求反射、表示、真值集或重建前提的最终四个定理。

结论包括全部合法起点的展开良基性与任意展开链终止性，以及标准生成集、任意固定起点后代集的字典序良序性。合法状态为空序列，或首项为 1 的有限正整数序列；标准种子为 `(1,m)`、`m≥2`。全部合法状态的字典序并不良基。

当前阅读入口是[实际展开与良序证明](../../research/1y-well-ordering-proof.md)、[通常数学意义的 ZFC 论证](../../research/1y-zfc-well-ordering-proof.md)和[具体语义模块说明](../Concrete/OneYTruth/README.md)。下面保留各组合模块的职责及局部输入；这些输入已在最终证明链中实际供应。

## 数值山脉与真实提取

- `Forest`、`ForestBridge`：左向森林，计算根和深度，连接既有 0-Y 祖先库。
- `Numeric`：零代表空格的稀疏行，继承祖先父项搜索、阶差递推、有限行预算、计算列高和顶值。
- `RootGeometry`、`NumericGeometry`：从具体数值定义构造计算根的山脉；顶点、轮廓边、参考边的行根刻画不再假设一个正确的根映射。
- `NumericRoots`：首项 1 的正整数序列满足无父项时值为 1 的初始不变量。
- `Pseudo`、`PseudoCollapse`、`PseudoSelection`：按真实腿路径计算伪父项；同高段收缩等于行根森林；在这两个森林上选顶值父项完全一致。
- `ExtractionGeometry`、`TopForestGeometry`：实际提取父项严格降低原层高度，并对应计算出的顶点和行根祖先。
- `Extraction`、`Build`：提取保持不变量；所有提取层有输入最大值给出的有限界；可执行构造停在第一个全 1 层。
- `BadRoot`、`RootSearch`：非后继列必有坏根，阶差 1 的位置唯一；可执行搜索的有根/无根情况与原列有无父项一致。
- `Examples`：内核直接核验继承祖先示例，包括提取值 `[1,2,1,2]` 的末项父项为第 1 列，而按数值重算会选第 3 列。

这一组模块负责单次山脉构造和坏根搜索的总性；任意多次展开的终止性由后文的图表示、实际有限反射与 `Dynamics` 接出。

## 父图复制与回填

- `Reconstruction`：按列良基递归计算回填值，证明正性、差分等式、存在唯一性及前缀依赖。
- `ReconstructionNumeric`：真实数值山脉经父图与顶值重建后逐格恢复。
- `CopyCoordinates`：坏部复制、原末列作为接缝、精确有限输出范围及父项平移坐标。
- `LowerCopy`、`LowerCopyNesting`：下层三段父图定义、父项合法性和相邻行细化；可构造回填使用的 `RowMountain`。
- `ActiveGeometry`：从真实活动父边在各下层推出根列锥与正提升高度，构造下层复制上下文。
- `LowerCopyRoots`：低行、提升段和填缝段的根列指标由具体父图计算并运输。
- `TerminalCopy`、`TerminalCopyNesting`、`TerminalCopyNumeric`：从数值坏根构造活动层复制图，核验接缝两侧的父项与细化。
- `OrdinaryCopyReconstruction`、`OrdinaryCopyNumeric`、`OrdinaryCopyPseudo`、`OrdinaryCopyExtraction`：普通复制与实际行搜索、拟父搜索和相邻层提取交换。
- `SparseComparison`、`TopComparison`：共候选链上，数值的比较等价于完整有限深度后缀与顶值的比较。
- `LowerCopyDominance`：以上层顶值支配为明确输入，证明按提升坐标运输后的下层回填支配源值。
- `TowerReconstruction`、`Expansion`：实际有限层列表的逐层回填、具体展开函数和输出合法性。
- `ExpansionProperties`：原前缀保持，复制零次等于删除末项。
- `ReconstructionCompute`、`ExpansionCompute`：结构递归求值版本与原定义的证明相等，可用于内核核验的展开例子。
- `Prefix`：全部真实数值行、拟父、提取层对右侧截断的局部性；没有把截断后父图不变作为假设。
- `LowerCopyBlocker`：有限行中父项位于好部的稀疏 NS 恢复，含 blocker 恰为原坏根的例外；旧证人直接从数值山脉生成。
- `LowerCopyDepths`：低行、锥外、提升及填缝各区域的实际森林深度公式。
- `TerminalCopySeam`：活动层第一个新接缝全部行的数值父项重建。
- `ForestFrame`、`ForestFrameMatrix`：任意继承父森林的有限 cutoff 框架，实际 BM4 父算法识别，及 DepthRegular；不据此声称任意稀疏顶值已可按根值 1 解码。

- `ReconstructionTop`、`LowerCopyTopBound`、`TerminalDecoratedRecovery`：顶行无父与其余行的最近较小父项恢复；所需顶值界和 blocker 条件由实际复制供应。
- `TerminalTowerRebuild`、`LowerTowerRebuild`：活动层及其上方的重建、下层的反向归纳，完整连接实际相邻提取层。
- `ExpansionCanonical`：独立重建真实有限输出，证明其各层各行恢复指定复制图，不以新图的 canonical 性为假设。
- `ExpansionOrder`、`Dynamics`：实际展开严格降低字典序，复制结果嵌套为前缀；由展开良基性推出标准生成集与固定后代集的字典序良序及任意链终止。

早期纸稿“尾部 C”的空父分支已修正，相关 blocker、拟父运输和跨层对接均已纳入上述完整重建证明。具体依赖见[完整多层重建说明](LowerTowerRebuild.md)。

## 根指标表示与语义

`RootIndexed/Representation` 已证明有限标签拼接和任意有限次迭代。`RootIndexed/ActualScheme` 进一步从实际 BadAt 和 copied mountains 构造完整 `BlockScheme`：每条新边分类、真实接缝 needs、原末列 templates、严格层级/根指标条件和逐块迭代均已证明。`copied_diagrams_bounded` 由原山脉表示构造所有指定复制图的有界表示。`FiniteReflection` 在核心库中保留为可复用的语义接口，其中没有把 1-Y 下降作为字段；具体实例现已在语义库中证明。`RootIndexed/Prefix` 将实际截断局部性接到表示的限制与保留，`ExpansionCanonical` 将指定复制图接回真实输出。

mathlib 语义子库位于 [Concrete/OneYTruth](../Concrete/OneYTruth/README.md)。实际混合真值塔、辅助统一 W、初始标签供应、较小 Lβ 内的规范 Σ₁ 证书及被量化域 U=L_a 的识别均已完成。[ActualFiniteReflection.lean](../Concrete/OneYTruth/ActualFiniteReflection.lean) 的 `RootSemantics.actual_finiteReflection` 证明具体反射；`ActualExpansion`、`ActualDynamics` 与 `ActualWellOrdering` 将其接到实际展开。

最终声明位于 `OneYTruth.WellOrdering`：`expansion_wellFounded`、`generated_strictWellOrder`、`descendants_strictWellOrder`、`expansion_chain_reaches_empty`。

## 构建与证明边界

在 `formalization` 目录运行：

```powershell
& '../.tools/lean-4.33.1-windows/bin/lake.exe' build
```

在 `formalization/Concrete` 目录运行：

```powershell
& '../../.tools/lean-4.33.1-windows/bin/lake.exe' build OneYTruth
& '../../.tools/lean-4.33.1-windows/bin/lake.exe' env lean OneYTruthAudit.lean
```

已通过声明的公理审计仅使用 Lean 标准公理 `propext`、`Classical.choice`、`Quot.sound`（部分定理用得更少）。未使用 `sorry`、自定义公理或原生判定公理。通常数学意义的 ZFC 证明由上述集合论论证给出；这项判断不单独依赖 Lean 公理打印，也不声称已生成一阶 ZFC 演算的机器可检验推导对象。
