# 1-Y 当前 Lean 语义依赖审计

审计时间：2026-09-10。范围为 `RootSemantics`、完整真值塔可构造性、初始 club、变量 `L_a` 证书、内部两端及当前端点的 R 证书。此记录是源码依赖和接口审查，不是整个 1-Y 良基定理已经无条件完成的声明。

## 结论与明确边界

在本轮检查的链条中，没有发现以目标 `FiniteReflection` 为前提再证明其所需语义基础的循环；没有发现假定某个 `ZFSet` 是传递的完整 ZFC 模型；没有发现从外部逐点构造直接推断整个源集合属于小模型的步骤。下列依赖边解释这些结论。

`ActualRelationQuery.realize_query_iff` **显式**要求 `η ≤ a`、`a < b` 与小域非空。单独的查询体核验规范资料及真值一致，不核验严格端点次序。特别是 `a=b` 时相同 Sat 的一致检查会通过，而 `R` 本身要求严格。有限图装配必须另外核验序数列的严格次序、从 `Diagram.valid` 得到根指标不大于父标签，并从每点 Adequate 得到非空。根线程已确认采用这一装配顺序。这是公开接口限制，不是已编译定理的漏洞。

`ActualEndpointRelation` 的 sound 定理也显式保留小端为非零极限、`η≤a`、`a<b` 及许可的语言索引关系。其 complete 定理要求当前大端 Adequate。它没有把当前大端或大 Sat 当作内部集合参数。

## 非循环的核心依赖边

1. `ExternalTower` 先在 `Stage κ = Nat × {η | η≤κ}` 上定义真实外部递归。顺序是已证明良基的词典序；一个阶段仅读取更低块，或同块严格较小 η。`satisfactionSet` 给实际值，`Small (Stage κ)` 给外部整图的集合性。此处没有 Adequate、初始 club 或反射前提，也未宣称整图属于某个 `L_β`。

2. `GraphStepCorrect.formula_correct` 与实际一步闭合给出固定纯一阶的整输出定义。`StageRecursionL` 对真实阶段顺序归纳：先用 L 中的 Replacement 收集此前局部图，再取并并附加新值。`stageGraph_mem_L` 的整图成员性是结论；早期 `StageStepPresentation` 的一步接口已在 `ActualTowerConstructible.graph_mem_L` 全部实例化。实例定理只要求 `U∈L`，不要求 Adequate 或某个递归图存在。

3. `UniformFromGraph` 用规范图的分离/投影构造统一辅助谓词，得到 `uniformSet_mem_L`；取 `κ=ω₁`、`U=L_{ω₁}` 得 `ambientTruth_mem_L`。这里的 ω₁ 是外部第一不可数序数，无不可达基数参数，也不以它是 L 的第一不可数序数为前提。

4. `AuxiliarySkolem` 使用仅有成员与 W 两个符号的语言。`InitialStageBounds` 证明每个外部可数 `L_α` 的实际 Skolem hull 可被更高但仍小于外部 ω₁ 的阶段容纳。`InitialStageClosure` 交替迭代整个 `L_α` 与 hull，取 ω 次上确界，直接证明极限 `L_β` 满足 Tarski–Vaught。这条供应链允许任意辅助谓词，**不先要求 W∈L 或任何扩展集合论 schema**。

5. 初始 schemas 分别供应：`AmbientCollection.collection_bound` 选择可数个见证，用更小 L 阶段给出真实内部界；它不据此声称 Separation。`AuxiliarySeparation.exists_separation_L` 现已选取包含 U、W 的集合域 `L_δ`，用其满意度集和固定有界查询得到分离子集，输入公式只是代码参数。`ConstructibleSubsetBound` 再证明该构造子集属于 `L_{ω₁}`。其凝聚 hull 的种子包含整个足够小的传递 `L_γ` 以及子集本身，因此 collapse 确实固定子集；没有从“子集外部可数”推出内部成员性的捷径。

6. `TowerTrace.truth_trace` 独立按阶段词典序归纳，识别初等限制中的大真值与重新计算的小真值。关键对角步骤明确使用 `ξ.toZFSet∈L_α → ξ<α`。`InitialCanonicalSupply` 此后才把受限 schemas 识别为小域规范 schemas，并由前述 `ambientTruth_mem_L` 消掉 Separation 所需的 W 可构造性假设。

7. `InitialRepresentations` 保留 `hW` 的模块化版本，其调用方可使用已经证明的 `ambientTruth_mem_L`。文件头中“sole unresolved”一类旧文字已过时；定理类型没有因此引入未证公理。当前 `ActualDynamics` 仍显式以 `FiniteReflection` 为输入，故不能把它的标准公理审计误读为该输入已经实例化。

## 混合语言边界

`ExternalTower.stageInterpretation` 的同块关系是分开的谓词符号 `named ξ`，其类型要求 `ξ<η`；当前 η 不在自己的命名真值范围中。`diagonal` 只读取严格较小块，允许其索引作为变量。统一辅助 W 只用于外部初始构造及较高块语义，没有被当作同块截断 η 的统一谓词。

在 `η=α` 的端点，小模型的语言仍只含 `S_ξ (ξ<α)`。小域 `uniformSet` 不包含自己的 `(k,α)` 真值标签，因而没有把完整自满意度放入该模型。`TowerTrace` 覆盖 η=α，并不改变这一限制。

当前端点的 `namedComparison` 只使用一个固定符号 `η<θ`；`diagonalComparison` 使用固定 `k<K` 与参数 η。规范小 Sat、`L_a`、全 Σ₁ 节点源都通过真正的 Σ₁ 子查询存在绑定。内部存在来自已证明的 `ActualInternalTower`、`InternalActualTruth` 及源集合闭合；反射后的 sound 方向只使用有界证书绝对性及规范唯一性，不把任意纯一阶公式从 L 向 `L_β` 下传。

## 公理审计与对象理论 ZFC

后续更新：下文定位的可变辅助公式分离已经改成集合域 Sat 的固定查询；实际调用复核见[类 L 闭合调用审计](1y-zfc-class-truth-call-audit.md)。完整的[通常数学 ZFC 论证](1y-zfc-well-ordering-proof.md)也已写出。下面关于 Lean 公理打印不自动证明 ZFC 保守性，以及尚无一阶 ZFC 推导对象的区别仍须保留。

目前相关 theorem 的 `#print axioms` 输出仅有 `propext`、`Classical.choice`、`Quot.sound` 的子集；新整塔与当前端点模块也通过此检查。它排除了 `sorryAx` 与新增未证 Lean 公理，但**不会消掉显式 theorem 参数**，也不衡量对象理论证明强度。

本工程的对象是 Mathlib 的 `ZFSet.{u} : Type (u+1)`（预集合商）以及 Lean 中的类 L、序数与模型论语义。它不是已经构造出的一阶 ZFC 推导代码 `ZFC ⊢ WO(1-Y)`。Lean 宇宙层次与外部语义函数也不能仅凭“三个标准公理”宣称对 ZFC 的保守性。

一个具体翻译节点是：Lean 库能在统一的外部 `SatisfiesIn L φ` 语义中量化公式 φ，并陈述 `exists_separationFormula`、`exists_replacementLCarrier`。类 L 的全满意度不能原样变成一阶 ZFC 内的统一定义谓词。尤其要在初始供应中一次得到所有扩展公式的 schemas，适当的 ZFC 版本应以**集合域** `(U,W)` 的完整 Sat 的可构造性供应统一检查，再使用一个固定分离公式，或给出等效的集合域统一化证明；不能把外部类满意度悄然当成内部集合。这不否定现有 Lean 定理，也未显示必须增加大基数，而是对象理论翻译需明确处理的实际节点。

所审具体数学构造采用集合长度递归、集合域满意度、可数 Skolem 闭包、Replacement、Separation 与 L 的凝聚，未发现必须额外假定不可达基数或完整传递 ZFC 集合模型的步骤；这些给出纸面 ZFC 实现的具体路线。然而把整个 Lean 论证翻译为对象理论 ZFC 证明、证明翻译正确，并据此作精确 PTO 比较，是尚未完成的另一项工作。当前审计不声称已降至 Z₂/Z₃，也不从源码文件名中的 “ZFC” 得出这种结论。
