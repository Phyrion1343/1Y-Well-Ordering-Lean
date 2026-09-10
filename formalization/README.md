# 0-Y / BMS 与 1-Y 形式化

1-Y 的数值算法与分层证明见 [OneY 说明](OneY/README.md)，最终无参数良序与终止定理见 [ActualWellOrdering.lean](Concrete/OneYTruth/ActualWellOrdering.lean)。完整模型需要在 `Concrete` 环境构建；复现步骤见 [具体工程说明](Concrete/README.md)，最新检查见 [验证记录](VALIDATION.md)。下文介绍 0-Y / BMS 部分。

本工程对应 [常规数学证明](../0Y-BMS-equivalence-proof.md)，包括任意非标准但合法的 0-Y 表达式。核心证明与具体构造宇宙模型均已通过 Lean 4.33.1 编译和公理依赖审计。

本工程以独立定义并证明的数学算法为规格；原 HTML 程序的正确性不是任何定理的前提。

## 已通过内核检查的主要结果

| 结论 | 实际声明 / 文件 |
| --- | --- |
| 所有合法式满足 F(D(s)) = s | `decode_encode`，[RoundTrip.lean](ZeroY/RoundTrip.lean) |
| 补零矩阵字典序与序列字典序精确对应 | `encode_lt_iff`，[OrderEmbedding.lean](ZeroY/OrderEmbedding.lean) |
| 往返可逆当且仅当满足纯矩阵条件 I、S | `roundTrip_iff_structural`，[Recognition.lean](ZeroY/Structural/Recognition.lean) |
| 同一充要条件对任意矩形原始表示成立，包括共同尾零行 | `roundTrip_iff_structural_of_rectangular`，[RawRecognition.lean](ZeroY/Structural/RawRecognition.lean) |
| 全部合法式与全部可逆规范矩阵序同构 | `reversibleOrderIso`，[Reversible.lean](ZeroY/Reversible.lean) |
| I、S 对任意参数的 BM4 展开保持 | `BMS.structural_expand`，[Structural/Expansion.lean](ZeroY/Structural/Expansion.lean) |
| 两个独立展开算法满足 D(Eₙ(s)) = Bₙ(D(s)) | `encode_expandY`，[Conjugacy.lean](ZeroY/Expansion/Conjugacy.lean) |
| 种子、任意前缀、有限展开路径精确对应 | [Seed.lean](ZeroY/Seed.lean)、[Prefix.lean](ZeroY/Expansion/Prefix.lean)、[Equivalence.lean](ZeroY/Dynamics/Equivalence.lean) |
| 两边标准生成集序同构 | `generatedOrderIso`，[Equivalence.lean](ZeroY/Dynamics/Equivalence.lean) |
| 任意固定起点的后代集序同构 | `descendantOrderIso`，[Equivalence.lean](ZeroY/Dynamics/Equivalence.lean) |
| 任意合法起点、任意指标选择的迭代最终为空 | `Concrete.y_trajectory_terminates`，[ZeroYConcrete.lean](Concrete/ZeroYConcrete.lean)，无需额外模型参数 |

上述往返、结构充要性、全域序同构和展开交换均没有标准生成性前提。条件 I、S 保留 [MatrixOrder.lean](ZeroY/MatrixOrder.lean) 中的原始定义；结构识别的充分性实际证明给定父图在反向求和后重新生成自身，没有假设这个结论。

`expandY` 的定义位于 [Expansion.lean](ZeroY/Expansion.lean)，直接实现完整坏部的山脉复制和求和。它没有通过 `decode ∘ BMS.expand ∘ encode` 定义。新块首列低行父项来自前一块的原末列；该边界规则在展开交换中单独验证。

## 良序结论的范围

- **全部合法式的全域字典序不良基**：`(1,2) > (1,1,2) > (1,1,1,2) > …`。`exprLt_not_wellFounded` 与 `reversibleLt_not_wellFounded` 已证明两侧反例。
- **全部合法式的非平凡展开关系良基**：`yStep_wellFounded`；实际任意参数迭代最终为空：`yTrajectory_terminates`。
- **每个固定合法起点的后代集按字典序良序**：`yDescendants_strictWellOrder`。
- **标准生成集按字典序良序**：`yGenerated_strictWellOrder`。

后三项核心定理使用 `RepresentationDescentSystem frame`。任意矩阵的初始有界表示已在 [AnyArray.lean](ZeroY/BMS/AnyArray.lean) 中构造，矩阵端不要求 I、S 或标准性。[ZeroYConcrete.lean](Concrete/ZeroYConcrete.lean) 已代入上游构造宇宙模型，提供不要求调用者另证模型存在性的最终定理；具体模型本身和全部 13 个最终定理均已编译、审计通过。详见 [具体模型说明](Concrete/README.md) 和 [验证记录](VALIDATION.md)。

Wiki 的有限端点约定与完整坏部约定不同。[Wiki.lean](ZeroY/Wiki.lean) 已证明两者标准集相同，更强地证明任意起点的可达闭包相同；[Wiki/Termination.lean](ZeroY/Wiki/Termination.lean) 给出任意指标迭代最终为空。

## 表示约定

- `Expr` 为空列，或首项为 1 且各项为正的有限自然数列。
- `ValidArray` 是矩形且已删除共同尾零行的列列表；这个名称不表示标准或可逆。
- 零行矩阵仍保留列数：`[]`、`[[]]`、`[[],[]]` 分别对应空式、`[1]`、`[1,1]`。
- `RoundTrip A` 固定为 `encodeRaw (decodeRaw A) = trimZeroRows A`。共同尾零行不影响父图、解码或可逆性。
- 比较列时补无限尾零；不能直接使用上游有限嵌套列表的比较函数。
- `YStep smaller larger` 排除空式的自环；`YExpansionPath` 包含零步及退化边。
- 标准种子取 `(1,h+1)`，包括 `h=0`；零高度种子本来就由正高度种子展开得到。

## 工具链与构建

Lean 固定为 `leanprover/lean4:v4.33.1`。便携运行时位于仓库的 `.tools/lean-4.33.1-windows`；初次准备依赖和登记 elan 工具链的步骤见 [根目录说明](../README.md)。

核心上游固定为提交 `bae7e3d741f24a56d80da9b99c1345562cd10c2d`；构建脚本检查版本和提交。核心只导入所需 BMS 模块，不需要 mathlib。

在工作区根目录运行：

```powershell
./formalization/build.ps1
```

在 `formalization` 目录运行公理审计：

```powershell
../.tools/lean-4.33.1-windows/bin/lake.exe env lean Audit.lean
```

核心总入口最新一次 `lake --wfail build` 通过 66 个任务；43 个关键声明的 `#print axioms` 检查退出 0，仅依赖 Lean 标准公理 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`、原生计算公理或自定义公理。完整输出保存在 [audit-output.txt](audit-output.txt)。

完整具体模型从锁定源码构建通过 1576 个任务，另有 14 项公理审计通过，依赖也仅为上述三个标准公理。在工作区根目录运行：

```powershell
./formalization/Concrete/build.ps1
```

在 VS Code 中检查最终具体模型，请打开文件夹 `formalization/Concrete`，再打开 `ZeroYConcrete.lean`。该独立工程包含构造宇宙和 mathlib 的依赖环境；两个上游证明脚本性能补丁及完整复现说明见 [Concrete/README.md](Concrete/README.md)。

若在新机器准备 Lean，可使用 `prepare-toolchain.ps1`；支持 `-Direct`。脚本核对官方 Windows 包 SHA-256，验证后才解压。便携运行时和所有 `.lake` 构建产物均被 Git 忽略。
