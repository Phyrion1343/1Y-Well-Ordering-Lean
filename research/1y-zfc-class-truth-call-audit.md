# 1-Y 最终证明中的全类 L 闭合调用审计

审计日期：2026-09-10。入口是 `OneYTruth.ActualWellOrdering` 的四个最终定理。本报告只检查全类 `L` 上的分离、替换及相邻封装；不将 Lean 的标准公理列表当作 ZFC 强度证明。

## 结论与范围

本轮源码追踪及最终声明闭包核对，未发现修订后的实际 1-Y 主线仍把任意输入公式直接交给全类 `L` 满意度来实施分离。原来最直接的一处已改成：输入公式先变成集合编码，在一个集合域 `D = Lδ` 中解释，再以**同一个固定公式**读取 `Sat(D)`。

整个塔和源集构造仍调用 `L` 中的分离、替换，但已追踪到固定公式的实例。公式代码、作用域长度、语言层数、序数阶段和候选赋值是集合参数；它们不改变这些实际分离／替换实例的公式文本。

需要保留的形式化边界是：库中那些对任意 `φ : FOFormula n` 量化的全类语义封装，不能原样视为 ZFC 内部关于全类真值的一个统一定理。ZFC 论证应使用下面列出的实际固定实例，或对有界语法采用集合编码的统一解释。两种追踪支持这一使用方式；它们自身不是一个机械生成的 ZFC 推导。

## 1. 已修复的任意辅助公式分离

相关代码为 [AuxiliarySeparation.lean](<../formalization/Concrete/OneYTruth/AuxiliarySeparation.lean>)、[AuxiliarySetTranslation.lean](<../formalization/Concrete/OneYTruth/AuxiliarySetTranslation.lean>)、[AuxiliaryFormulaCompilation.lean](<../formalization/Concrete/OneYTruth/AuxiliaryFormulaCompilation.lean>) 与 [PureSetSatisfaction.lean](<../formalization/Concrete/OneYTruth/PureSetSatisfaction.lean>)。

实际调用顺序为：

1. 取包含 `U,W` 的非零极限阶段 `D`。
2. `translate φ` 把辅助量词限制到 `U`，并将额外四元关系展开为 `W` 的成员关系；配对见证由 `D` 的有序对闭包供应。
3. `compile` 将两个参数搬到赋值的前两个位置，得到纯语言公式。
4. `PureSetSatisfaction.exists_separation` 将该公式存入 `packedCode`。它最终调用的是 `deltaSep_mem_L queryFormula`，其中 `queryFormula : Delta0Formula 5` 固定等于 `extendedHoldsAt 0 1 2 3 4`。

因此，最终分离实例中的可变对象是公式的**编码参数**，不是全类 `L` 上的公式语义。`Sat(D)` 的存在也由完整集合域满意度构造供应；这里没有假定任意候选满意度集合正确。

## 2. 满意度集合的存在没有把问题移回全类真值

`PureSetSatisfaction.satisfaction_mem_L` 使用 `ConstructibleDiagramSources.satisfactionSet_mem_L_of_relation_graphs`，后者通向下列固定构造。

| 构造 | 实际固定公式 | 可变集合参数 |
|---|---|---|
| 一步 Tarski 近似 | `ConstructibleEvaluationFamily.evaluationFilter : Delta0Formula 8` | 节点集、原子真值集、五类结构图、当前近似 |
| 所有有限近似的迭代族 | `uniformFiniteIterationFormula (filterGraph evaluationFilter 0).toFO` | 固定结构图、初始空集、自然数步骤 |
| 从节点中分离最终满意度 | `ConstructibleEvaluationFamily.eventualFormula : FOFormula 9` | 同一迭代的七个参数、ω、候选节点 |

`ConstructibleSatisfaction.filtered_range_FO_mem_L` 是接受任意 FO 公式的通用封装，但实际满意度定理只将固定的 `eventualFormula` 传给它。这个公式检查集合域语法图的有限 Tarski 迭代；它没有解释全类 `L` 的任意公式。其量词中出现 `LCarrier` 并不改变该实例的公式是固定的这一事实。

## 3. 完整语法、赋值与查询源

源码中的通用入口 `ConstructibleBoundedIteration.deltaSep_mem_L`、`family` 及 `filtered_range_mem_L` 均接受公式参数。实际源集使用的实例如下。

| 源集 | 实际规则／过滤公式 |
|---|---|
| 有限配对编码总界 | `ConstructibleCodeUniverse.pairStepFormula` |
| 有限列表与赋值编码 | `ConstructibleListCodes.listStepFormula`、`ConstructibleAssignmentCodes.sequenceCodeFormula`；另一条规范生成链使用 `AssignmentGrammar.ruleFormula` |
| 完整作用域语法 | `SyntaxGrammar.ruleFormula` |
| 完整 Δ₀ 语法 | `DeltaSyntaxGrammar.ruleFormula` |
| 完整 Σ₁ 语法 | `SigmaSyntaxGrammar.ruleFormula` |
| 赋值查表关系 | `AssignmentLookup.lookupFormula` |
| 语法与赋值匹配节点 | `matchingArityFormula` 及固定的原子／蕴含／量词／子节点检查式 |

特别检查了 `ConstructibleSyntaxStages.params`：语言层数 `k` 作为 `natLCarrier k` 放在一个固定的十一元参数组中。`grammarFamily` 使用同一个 `ruleFormula`，没有随 `k` 生成越来越长的全类语义分离式。Δ₀ 与 Σ₁ 的语法生成同样如此；量词复杂度条件由实际编码规则生成，而非从任意外部子类直接宣称构造性。

内部源供应的 `InternalBoundedIteration.allStages_mem` 等结论使用的是**集合域**上的 `HasSeparation`、`HasCollection`；其与全类 `L` 版本的等式只是识别已构造对象。不能把这些集合域模式调用误报为全类真值调用。通用有界公式参数若仍需在 ZFC 中统一处理，可用 Δ₀ 的集合编码及对传递域的绝对性；这不要求一般全类真值谓词。

## 4. 整个真值塔的超限递归

[ActualTowerConstructible.lean](<../formalization/Concrete/OneYTruth/ActualTowerConstructible.lean>) 的 `graph_mem_L` 明确传入：

```text
GraphStepMatrix.fixedParameters κ U
GraphStepMatrix.formula
```

其中 `GraphStepMatrix.formula : FOFormula 16` 是固定的：十三个参数，加阶段编码、前驱图及输出满意度集合。它的十八个存在见证通过同一个固定矩阵验证；`κ,U,k,η` 只影响赋值和被编码对象。

这一路实际实例化 [StageRecursionL.lean](<../formalization/Concrete/OneYTruth/StageRecursionL.lean>) 中的通用 `StageStepPresentation`：

- `classFormula` 与 `relationFormula` 来自固定的 `stageClassFormula`、`stageRelationFormula`。
- `stepFormula` 是上面固定 `GraphStepMatrix.formula` 的固定重编号。
- `collect_localGraphs` 调用 `exists_replacementLCarrier` 时使用 `localSolutionFormula` 对这三个固定公式的组合。
- `formulaRestrictionLCarrier` 使用的是上述固定阶段类／先后关系的限制式。
- `stageGraph_mem_L` 再次调用同一个 `collect_localGraphs`，将全部局部图收集成集合后取并集；此处没有额外变化的替换公式。
- 最后 `uniformSet_mem_L_of_graph` 通过固定 `uniformMemberFormula` 分离出统一编码。

所以，对全部自然数层与序数阶段的递归是对一个固定集合定义的递归，未逐阶段调用“该阶段所有公式在全类 L 中为真”的外部谓词。

## 5. 声明级闭包核对结果

以下名字本身不足以判为缺口：

- `exists_separationLCarrier`、`exists_replacementLCarrier`：需查最终实际传入的公式。
- `ParametricUniformOmegaFamilySpec.formula`、`StageStepPresentation.stepFormula`：字段在实际入口已由固定公式填入。
- `FullSkolemHull`、`FiniteFragmentSkolemHull`、`ZFModel`：文件被导入不等于其所有定理被使用。`CountableSetHull.exists_countable_elementary_hull` 的对象是一个实际集合域，使用 Mathlib 集合结构的 Skolem 闭包。

最终 [完整构建日志](<one-y-truth-zfc-build.log>) 确认 **1814 jobs 成功**，四个出口均重编通过。随后从这四个定理递归读取 Lean 常量的类型与证明体（`ConstantInfo.type`、`value? (allowOpaque := true)`），追踪其中的常量引用。共访问 **19333 个声明**；筛选出名称包含 separation／replacement／Skolem 的 **50 条边，去重后 44 条**。

实际进入声明闭包的全类闭合调用，可归为以下几组；其余筛选边是公式重编号、包装和普通环境集合替换。

| 实际调用者 | 全类接口 | 上文的实例分析 |
|---|---|---|
| `ConstructibleAssignmentCodes.sequenceCodes_mem_L` | `exists_separationLCarrier` | 固定 `sequenceCodeFormula` |
| `ConstructibleBoundedIteration.deltaSep_mem_L` | 同上 | 第 1、3 节的固定有界过滤式 |
| `ConstructibleDiagramSources.filtered_range_FO_mem_L` | 同上 | 固定 `eventualFormula` |
| `formulaRestrictionLCarrier._proof_1`、`mem_formulaRestrictionLCarrier_iff` | 同上 | 固定阶段类／先后关系 |
| `StageStepPresentation.collect_localGraphs` | `exists_replacementLCarrier` | 固定局部解公式 |
| `exists_parametricUniformOmegaFamilyData` 经函数图／值域包装 | `exists_replacementLCarrier` | 固定语法、查表、评价迭代的历史公式 |

以下名字经逐名检查**不在**这 19333 个声明中：

```text
Constructible.Model.exists_separationFormula
Constructible.Model.exists_replacementFormula
Constructible.Model.lCarrier_models_ZF
Constructible.Model.exists_uniformOmegaFamily
Constructible.Model.canonicalWitnessSelection
Constructible.Model.nullaryCanonicalWitnessSelection
Constructible.Model.positiveCanonicalWitnessSelection
```

同时，闭包中确实包含 `PureSetSatisfaction.queryFormula`、`AuxiliaryCode.realize_translate_stage`、`GraphStepMatrix.formula` 和集合域的 `CountableSetHull.exists_countable_elementary_hull`。这排除了“源码虽改动，但最终定理仍走旧辅助分离证明”的可能。

## 6. 不应混同的环境替换边界

探针还捕获了 `Constructible.replacementRangeZF`，由 `limitUnionZF` 及 `canonicalBareHistoryBelow` 等实际引用。它实现环境集合的替换像，并通过 `Classical.allZFSetDefinable` 为外部函数提供 Mathlib 所需的 `ZFSet.Definable₁` 实例。

这不是全类 `L` 真值调用。不过，`ZFSet.Definable₁` 在这里表示对 `PSet` 的提升条件，**不表示**该函数已经具有对象语言中的一阶定义；库的注释也明确指出这一点。不能因为 Lean 能对任意外部函数执行这个包装，就宣称 ZFC 对任意外部类函数都有替换。

已核对这一分支的实际用途：`canonicalBareHistoryBelow` 传入的族明确为 `ordinal ↦ pair ordinal.toZFSet (LStageZF ordinal)`；其余是规范构造阶段的 `limitUnionZF` 及相关成员关系引理。没有发现第三类未覆盖的 `Xs` 用途。

[ZFC 总论证](<1y-zfc-well-ordering-proof.md>) 第 3 节已用集合 `κ+1` 上的固定 Def／Sat 递归构造这些 `L` 阶段，第 5 节以固定一阶算子和完整局部解收集构造内部阶段历史。因此总论证采用的是这两个具体的 ZFC 集合递归，而没有移植“任意外部 `Xs` 都能替换”的通用 Lean 包装。这一注意点已被实际用途的重述覆盖，未构成新的缺口。

最终结论：本轮未发现另一处需要像旧辅助分离那样修复的实际全类真值调用。固定公式实例及具体集合递归的 ZFC 解释由总论证负责；本审计核对其实际调用范围，没有将这种解释替换成公理列表检查。
