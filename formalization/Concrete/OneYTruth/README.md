# 1-Y 良序与展开终止：Lean 形式化

2026-09-10 的集合论补充：[ZFC 证明](../../../research/1y-zfc-well-ordering-proof.md)给出通常数学意义的 ZFC 上界。`AuxiliarySeparation` 已用 `AuxiliarySetTranslation`、`AuxiliaryFormulaCompilation` 和 `PureSetSatisfaction` 将任意输入公式变为固定集合满意度查询的代码参数。本文下方保留各模块的说明；早先仅凭 Lean 公理审计不能判断 ZFC 上界的限制仍成立，现有上界依靠另行完成的集合论论证。没有一阶 ZFC 推导对象或最弱公理系统的认定。

这个目录已完成实际 1-Y 展开的良基性及标准生成序列良序性的 Lean 形式化。`ActualFiniteReflection.actual_finiteReflection`（命名空间 `RootSemantics`）已证明实际关系的有限反射，`ActualWellOrdering` 的最终四个出口无任何反射、真值集、表示或重建前提。所有最终定理的公理审计仅为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorry` 或自定义 `axiom`。

结论的范围是：每个合法有限序列（空序列，或首项为 1 且各项为正）的任意展开链最终到达空序列；从标准种子 `(1,m)`、`m≥2` 经实际 1-Y 展开得到的序列按字典序构成严格良序。任一固定起点的后代集也按字典序构成严格良序。这里没有声称全部首项为 1 的正序列在任意字典序下良序。

最终定理位于 `OneYTruth.WellOrdering`：`expansion_wellFounded`、`generated_strictWellOrder`、`descendants_strictWellOrder`、`expansion_chain_reaches_empty`。下方逐模块说明中的局部输入已由后续实际构造供应，不是这些最终出口的前提。
在 `formalization/Concrete` 中运行：

```powershell
& '../../.tools/lean-4.33.1-windows/bin/lake.exe' build OneYTruth
& '../../.tools/lean-4.33.1-windows/bin/lake.exe' env lean OneYTruthAudit.lean
```

## 已实现的具体对象

- `Language.lean`：真正的 Mathlib `FirstOrder.Language`。二元 `mem`，`k` 个三元 `diagonal j`，分别命名的二元 `named i`。`I` 可实例化为 `{ξ // ξ < η}`。同层没有可变索引的统一谓词。
- `Translation.lean`：实际公式递归 `S_i(e,s) ↦ U_k(c_i,e,s)`，旧 `U_j` 保持。新增 `c_i` 是自由参数。`realize_diagonalTranslate` 证明全部有限公式的语义正确性。
- `FiniteSupport.lean`：计算实际出现的有限命名符号集合；证明语义只依赖这些符号；构造有限子语言中的公式，并证明映回原语言后与原式**语法相等**。
- `Complexity.lean`：独立定义集合论有界量词与 Δ₀、有限存在前缀 Σ₁ 片段。这里不把 Mathlib 的 `BoundedFormula`（作用域变量有界）误认作 Δ₀。证明有界量词的预期语义及两种翻译的 Δ₀／Σ₁ 保持。
- `Weakening.lean`：`SigmaOneMap` 直接定义为公式 realization 的保持性质。证明同层命名语言 reduct 与跨层 diagonal reduct 保持它。单个公式只要求其有限支持上的索引参数交换。
- `LimitLanguage.lean`：每个极限阶段的有限公式可在某个严格较小阶段中表达，再由实际语言映射恢复。证明不需要把极限阶段本身作为一个参数。
- `Auxiliary.lean`：单独的固定有限语言，只有二元成员关系和四元 `W`。构造所有局部公式到它的翻译，并证明语义正确；`finiteTranslate` 使用严格有限的附加命名参数类型。这个辅助 `W` 没有加入任何控制语言。
- `FormulaCode.lean`：带作用域检查的原始语法解码器、公式和含元数公式的实际 `ZFSet` 编码；证明解码左逆、编码注入性、语言扩大时编码不变，以及各符号代码属于整个可构造宇宙 `L` 时公式代码也属于 `L`。这最后一点没有指定层高。
- `SmallSyntax.lean`：由命名符号的小性推出原始语法、作用域公式与所有有限元数公式的小性；序数开／闭初段的小性由到实际序数集合的注入得到。
- `SatisfactionSet.lean`：用 `ZFSet.range` 构造实际的外部满意度集合；`mem_satisfactionSet_iff` 验证每个实际公式与赋值代码的成员关系恰为其 realization。
- `ExternalTower.lean`：固定集合域 `U`、序数上界 `κ`，在 `Nat × {η ≤ κ}` 的已证良基字典序上递归，每步直接调用上述满意度构造。所有值和整个塔的 `graph` 都是实际 `ZFSet`；证明递归方程及 `mem_truth_iff`、`mem_graph_iff`。
- `TowerReducts.lean`：证明这个具体外部塔的同层命名限制、跨层统一谓词限制恰好是原先翻译定理中的 reduct。跨层索引代码须是域 `U` 中的实际参数。
- `UniformTruth.lean`：把所有有限块与所有 `ξ < κ` 阶段的真值对收集成一个实际 `ZFSet`，给固定有限辅助语言解释 `W`；证明带正确自然数／序数参数的辅助 reduct 等于规范解释。
- `TarskiCertificate.lean`：构造实际的合法公式／赋值对集合 `scopedPairs`，用无垃圾条件与五种精确语法递归条款刻画候选满意度集合；证明每个候选正确，规范集合满足条款且唯一。
- `TowerCertificate.lean`：对任意给定有界阶段族，证明若其各阶段满足上述局部证书，则整个族等于已经构造的规范塔；规范塔本身证明了此条件的存在性。
- `DeltaZeroBridge.lean`：实际编译 constructible 库的纯 Δ₀ 语法至混合语言，证明复杂度、语义及传递集合中的绝对性。
- `BoundedEvaluation.lean`：构造固定七参数的真正 Δ₀ 公式，检查一个候选集合是否解出给定的集合编码递归图；证明混合语言编译结果的 `IsDeltaZero` 与语义正确性。
- `SyntaxDiagram.lean`：从真实作用域公式和赋值构造六个递归图集合；原子真值表仅使用原子解释，没有通过完整满意度定义它；证明量词边精确表示全部单元素扩充赋值。
- `DiagramCertificate.lean`：证明该实际递归图的解条件等价于 `IsTarskiSet`，从而唯一刻画规范满意度；若七个实际集合参数属于一个传递 ambient 集合，则其中的 Δ₀ 公式精确识别较小固定域的完整满意度集合。
- `ConstructibleCodes.lean`：证明公式、赋值与节点的单个代码留在指定非零极限层 `LStageZF θ` 内。对所有代码或真值对的集合只推得 **subset**，没有将其冒充该层的成员。
- `LocalTruthQuery.lean`：构造肯定／否定两种局部真值查询的实际 Σ₁ 公式。它们存在量化一个解出递归图的集合；若实际图参数及规范满意度集合属于 ambient 传递集合，证明两种查询都精确。内部存在性在定理中作为明确待供应条件出现，没有被宣布已满足。
- `InternalClosure.lean`、`CollectionReplacement.lean`：明确写出混合公式的分离、收集与替代实例；通过实际构造的值域公式证明收集加分离推出替代，再证明内部筛选值域、函数像集合存在。没有使用 Power Set。
- `ScopedReindex.lean`：实现已作用域公式的变量重排及其精确语义，用于实际构造值域与后续证书公式。
- `InternalProducts.lean`：用两条具体纯 Δ₀ 替代实例、序偶闭合与并集闭合，构造并识别整个 Cartesian product；没有把外部乘积预设为模型成员。
- `CodedPaths.lean`、`PathEquality.lean`：用真正的有界存在量词读取 Kuratowski 代码字段，证明固定路径的成员、相等与两路径匹配语义。
- `AtomicCodeFormula.lean`、`QuantifiedCodeFormula.lean`：实际用 tag 字段判定原子／量词节点，通过分别指定的 Δ₀ 分离实例得到完整节点子集。
- `InternalNodes.lean`：完整 `scopedPairs` 恰为 `syntaxCodes × assignmentCodes` 上元数匹配的 Δ₀ 分离结果，证明其内部成员关系。完整两个源集合的成员关系是明确假设，逐码闭合不替代它们。
- `AssignmentFields.lean`：赋值改用倒序表存储，证明不同元数的编码区分、`Fin.snoc` 的表头递推及其逆向识别。原有注入与满意语义已随编码一起重验。
- `ImplicationCodeFormula.lean`、`ChildrenCodeFormula.lean`：以实际 Δ₀ 路径检查完整蕴含图与量词子项图，分别从合法节点的三次、二次乘积通过分离得到图集合。量词检查包括新赋值确实取自固定较小域 `U`。
- `EvaluationStep.lean`：给出六图上的实际有界求值单步、该步的集合图公式、从一条分离实例得到下一近似集，以及所有单个有限迭代的内部成员关系。尚未据此推断整个自然数迭代族内部存在，也未声称有限近似的并集就是满意集。
- `InternalDiagram.lean`：统一以上结果，从混合收集／分离、基本序偶／并集闭合以及两个完整源集，推出五个纯语法图属于指定模型；专门实例化到非零极限 `LStageZF θ`。原子真值表仍作为另一项必须供应的实际成员条件。
- `InternalFiniteRanges.lean`、`EvaluationHistory.lean`、`CanonicalEvaluationHistory.lean`：证明有限值域的内部闭合，给出真正 Δ₀ 历史证书，并通过自然数归纳证明任何获准历史值都是规范有限迭代；实际有限历史及其界容器均在模型内构造。
- `InternalEvaluationFamily.lean`：实际构造两存在量词的 Σ₁ 历史查询，由收集／分离推得对应替代实例，收集整个 `{iterate D n | n ∈ ω}` 为模型成员。没有全族存在字段。
- `EvaluationConvergence.lean`：证明六个规范图的求值单步恰为语法求值单步，且每个真实公式在 `formulaDepth + 1` 步后稳定为实际 realization；近似集不要求单调。
- `ScopedConnectives.lean`、`InternalSatisfaction.lean`：给出实际“最终真值”分离公式，并证明完整的较小固定域满意集属于模型。前提是六个真实图参数、`ω` 属于模型、基本 pair/union 闭合，以及两条明确分离实例；没有再假设满意集或满意度递归的内部存在。
- `InternalSatisfactionSources.lean`：把五图构造与满意集内部化连起来，得到指定非零极限 `Lθ` 中的定理。剩余成员前提集中为较小域、完整语法集合、完整赋值集合与实际原子真值表，连同真正的扩充分离／收集实例。
- `ConstructibleListCodes.lean`、`ConstructibleAssignmentCodes.lean`：从 `U∈L` 实际构造全部有限列表载荷、以统一迭代公式检查精确长度，再分离得到整个赋值编码集 `assignmentCodes U∈L`。此处构造的是全部集合，不仅是逐码闭合；指定较小层内的定位另需证明。
- `ConstructibleCodeUniverse.lean`：以实际有限迭代和内部自然数族并集构造一个 `L` 中的语法代码总界，含全部自然数、给定字母表并对序偶封闭；证明完整语法集合包含于此界，尚不把任意子集的可构造性当成已证。
- `AmbientSourceCodes.lean`：以实际可数性取得较小阶段界，再结合全集可构造性与凝缩子集定理，证明 `U∈Lω₁ → assignmentCodes U∈Lω₁`。
- `FiniteCodeFormula.lean`、`SyntaxConstructorFormula.lean`、`SyntaxGrammar.lean`：实际 Δ₀ 公式检查全部有限编码链、空尾、七个构造子、变量作用域及子公式的作用域匹配。
- `ConstructibleBoundedIteration.lean`：对任意显示的有界分离步给出真实图公式，并用库中已证有限迭代与 Replacement 收集其整个自然数族。
- `SyntaxGrammarSoundness.lean`、`ConstructibleSyntaxStages.lean`、`ConstructibleSyntaxCodes.lean`：证明规则的可靠性及按真实公式深度的完备性，识别内部自然数族并集恰为整个 `syntaxCodes`，从字母编码集属于 `L` 推出完整语法集合属于 `L`。
- `ConstructibleDiagramSources.lean`：从已经实际构造的语法／赋值集合，经具体 Δ₀ 分离和乘积得到五个纯语法图的整体可构造性。
- `ConstructibleEvaluationFamily.lean`、`ConstructibleEventualTruth.lean`、`ConstructibleSatisfaction.lean`：实际构造求值阶段族及纯 FO 最终真值公式，证明 `U`、字母编码全集和真实原子表属于 `L` 时，完整满意度集合属于 `L`。剩余的原子表条件与全塔构造没有被假定成立。
- `AssignmentLookup.lean`、`AssignmentLookupFormula.lean`、`ConstructibleAssignmentLookup.lean`：由实际赋值扩充的头尾关系建立 Δ₀ 查找迭代，以可靠性和按赋值长度的完备性识别整个查找图；从 `U∈L` 推出全部 `(assignment,index,value)` 查找记录组成的集合属于 `L`。
- `AtomicRelationGraphs.lean`：定义真实命名／对角原子解释的集合图并证明精确成员语义；`ConstructibleGraphInput.lean` 已从任意实际构造性输入图供应这些图的可构造性。
- `StageCoding.lean`、`StageOrderSet.lean`、`StageRecursionDomain.lean`：构造整个实际阶段集合、字典序边集合、全部前驱集合与局部递归域，证明它们属于 `L`、前驱关系良基且由固定 Δ₀ 公式识别。
- `StageRecursionL.lean`：实际良基归纳构造局部图；用一个固定局部解公式及其已证唯一性，经 `L` 的 Replacement 收集此前局部图、取并并添加新值，最终得到整张递归图属于 `L`。没有把任何递归图的可构造性作为输入。
- `GraphStepCorrect.lean`、`ActualTowerConstructible.lean`、`UniformFromGraph.lean`：完整一步 FO 公式的真实候选、可靠性和完备性已经供应，并接到实际外部塔递推。由此证明每个构造性域 U 的完整有界塔图属于 `L`，再经固定 Δ₀ 筛选得到实际统一 W 与 `ambientTruth_mem_L`。
- `GraphStepSyntaxCertificate.lean`、`GraphStepSigmaFormula.lean`、`GraphStepSigmaSoundness.lean`：同一个外层代码界服务所有较小阶段；完整一步查询是明确的 21 个存在量词接单个 Δ₀ 矩阵。任意传递 `V⊆L` 中的候选查询都只能给出真实规范结果，可靠性不要求 Collection 或 Separation。
- `InternalGraphInput.lean`、`GraphStepInternalWitnesses.lean`、`GraphStepSigmaComplete.lean`、`GraphStepSigmaFO.lean`、`InternalActualStep.lean`：在实际满足混合 Collection/Separation、序偶/并集闭合的传递较小域内，构造全部关系图、原子表、满意集以及 21 个证书见证；给出同一纯 FO 语法在该小域上的精确性。固定十三个源参数和单步输出都从 `U`、序数界、`ω` 的真实内部成员关系供应，没有内部 Sat、原子表或源集存在字段。
- `PureFOSchemas.lean`、`InternalStageDomain.lean`、`InternalRecursionEnvironment.lean`：从实际 Adequate 条件导出普通一阶 Separation、Replacement 及所需基本集合操作；对于 κ<β，证明实际 Stageκ、前驱集合与局部域属于 Lβ。没有假设 Lβ 满足全部 ZF，也没有声称任意 FO 公式跨层绝对。

- `InternalFormulaRestriction.lean`、`InternalStagePresentation.lean`、`InternalStageRecursion.lean`：从实际弱内部环境构造前驱限制图，由局部解唯一性、Replacement 和并集完成整张实际递归图；不假设任何递归图成员关系。
- `GraphStepSigmaFO.lean`、`InternalActualStep.lean`、`ActualInternalTower.lean`：真实 21 存在量词加 Δ₀ 的一步证书在较小模型中有完整规范见证；实际源和一步闭包均已供应。最终 `graph_mem_of_adequate` 仅以 `Adequate β`、`κ<β`、`U∈Lβ` 推出真实整图 `graph κ U∈Lβ`；`InternalUniformTower.uniformSet_mem_of_adequate` 再用固定 Δ₀ 筛选证明实际统一真值集也属于同一层。

- `OrdinalStageHistory.lean`、`OrdinalHistoryRaw.lean`、`OrdinalHistoryFormula.lean`：复用实际历史 `{〈i,L_i〉|i≤a}` 的 `L_(a+ω)` 界，证明局部 Def 递归条款唯一识别历史，并把全部条款实现成真正 Δ₀。
- `OrdinalHistoryWitnessBound.lean`、`OrdinalStageQuery.lean`、`ActualStageQuery.lean`：实际 Collection 为所有后继证书构造共同界；由四个存在见证加原生 Δ₀ 形成 `a,ω,∅,U` 查询。已完全实例化规范 Def 证书，最终 `realize_query_iff` 在 Adequate Lβ 中等价于 `U=L_a`，无 Def/source/Sat/history 成员字段。

解释数据 `Interpretation` 只记录任意关系。`diagonalReduct` 与辅助 `reduct` 从给定目标关系**定义**源解释，故翻译正确性没有预设任何真值公理。后续两个具体塔模块已证明所构造的外部塔确实满足这些 reduct 等式；它们没有提供反射或初等子模型存在性。

`SigmaOneMap` 当前测试实际语法中的“有限存在前缀 + 扩充 Δ₀ 矩阵”片段，允许外部参数赋值族；每个被测试公式仍然有限。尚未加入任意逻辑等价 Σ₁ 公式的正规化定理。纸面反射使用的存在证书公式应直接构造在此片段中，不能凭命名跳过复杂度证明。

`IsTarskiSet` 和 `IsTowerFamily` 不是未证的存在性公理：规范对象满足它们且满足者唯一。完整源集、原子表、一步满意度和整张塔在整个 `L` 及满足 Adequate 的较小 `Lβ` 中的构造已经接通。**整张塔、实际域、Adequate、内部 R 和端点 R 的规范 Σ₁ 查询及最终有限反射的实际参数适配均已完成**；被量化域 `U=L_a` 的实际规范查询已由 `ActualStageQuery` 完成；整个 `L` 上正确的任意 FO 公式不能直接当作较小层内的绝对公式。

## 与已有工程的关系

依赖为项目固定版本的 Mathlib 模型论语法与语义。现有 constructible 工程的 `CodedSatisfaction.lean` 为固定纯成员公式编译集合关系；它没有现成提供本目录所需的可变序数语言、完整混合满意度塔或统一内部证书。这里没有将其误作那些定理使用。

## 最终反射与良序出口

`ActualDiagramQueries` 将 `ActualAdequateQuery`、`ActualRelationQuery`、`ActualEndpointRelation` 按同一有限参数布局实例化。反射后先由序数检查及域条件供应关系查询的守卫，并由实际 admissibility 选择 named 或 diagonal 端点查询。所有元参数和原标签前缀共同固定。

`FiniteReflectionAssembly.reflect_representation_of_queries` 已实证联合量化、反射和全部标签解码。`ActualFiniteReflection.actual_finiteReflection` 再供应真实元参数和所有逐查询语义，最后由 `ActualWellOrdering` 从原先的条件定理消除 `FiniteReflection` 输入。详细组合审计见 `research/1y-finite-reflection-assembly.md`。
外部构造对固定 κ 使用已证小性的 `Nat × {η ≤ κ}`，整张图已经证明属于 `L`。相应集合长度递归的 ZFC 重述现见上方链接的独立论证，最弱集合论公理强度尚未确定。实际内部塔的存在与规范证书是分别证明的；最终有限反射在 `ActualFiniteReflection` 中完成。







