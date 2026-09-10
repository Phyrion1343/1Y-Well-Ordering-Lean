# 下一步内部化接口

当前局部结论有实际公式与实际集合：

`SyntaxDiagram.diagram indexCode M` 构造六个集合；`BoundedEvaluation.mixedSolutionFormula` 是明确 Δ₀ 语法；`DiagramCertificate.realize_certificate_iff_eq_satisfactionSet` 证明在传递 ambient 集合内，七个真实参数上的检查恰好表示候选集合等于完整满意度。`LocalTruthQuery` 再存在量化候选集合，给出两种符号的 Σ₁ 查询。

还不能消去的条件如下。

已补齐的具体中间步骤：`InternalDiagram.structural_sets_mem_LStageZF` 从指定非零极限层内的两个完整源集合、实际 mixed Collection/Separation 推出五个规范纯语法图属于该层；序偶和并集闭合来自已有 `LStageZF` 定理。`InternalNodes`、原子／量词节点判定以及蕴含／量词边判定都含实际 Δ₀ 公式和全体源代码上的精确语义。赋值倒序存储使量词边只读取有限固定字段。`EvaluationStep` 证明单个递归步骤与任意单个有限迭代属于模型。

进一步已完成：`InternalEvaluationFamily` 用实际 Σ₁ 有限历史证书收集整个自然数近似族；`EvaluationConvergence` 证明真实公式逐点最终稳定；`InternalSatisfaction.satisfactionSet_mem_of_diagram` 用实际最终真值分离公式构造完整较小域满意集。最后这条定理仅需两个真实分离实例和有限集合闭合，不用预设内部 Sat，也不把近似集并集当作 Sat。`InternalSatisfactionSources` 已把它接到上述五图构造：完整语法／赋值／原子真值表这三个源集合仍需由原始内部参数供应。

1. **语法和赋值的总集合。** `ConstructibleListCodes`、`ConstructibleAssignmentCodes` 已从 `U∈L` 实际构造整个赋值编码集合；`ConstructibleSyntaxCodes` 已从字母编码全集属于 `L` 构造完整语法集合，以实际构造子规则的可靠性、完备性识别整个迭代并集。`AmbientSourceCodes` 还将赋值全集定位到 `Lω₁`。`ConstructibleDiagramSources` 从它们供应五图的整体可构造性，`ConstructibleSatisfaction` 进一步证明给定真实原子表属于 `L` 时，完整满意集属于 `L`。仍须统一内部识别这些源集，并完成所需指定较小层定位；一般极限层的逐码封闭性不提供集合收集。
2. **原子表。** `trueAtomSet` 仅读取假、等号和关系原子的实际解释，不读取完整满意度。内部化它需要此前已经构造的低层／同层较早真值表作为实际集合参数，及统一的符号、赋值解码公式。任意外部 `Interpretation` 并不保证其原子表可构造。
3. **图的规范性。** 对六个任意集合存在量化并断言候选解出其图，不能得到满意度。五个纯语法图已有从真实完整源集生成的 Δ₀ 判定和内部成员定理；仍须内部验证源集本身的规范性，以及原子表来自指定关系。当前外部 `diagram` 加这些条件式内部化结果，还不是不带源集前提的完整统一证书。
4. **整个塔。** `ExternalTower.graph` 是实际外部集合，`TowerCertificate` 给出逐阶段证书的唯一性。仍需把有界阶段集、此前值查询、各阶段的规范图和全部局部满意度放入一个内部有界证书，证明它在目标层内存在。不能把已经构造的外部图自动视为该层内部的集合。
5. **端点区别。** `LocalTruthQuery` 假设较小固定域的规范满意度属于 ambient 集合；不能把域与 ambient 模型取成同一个并无条件供应此假设。到当前端点的反射接口，应沿混合语言的独立 `Sξ` 或低层 `Uj` 翻译进行。
6. **初始供应。** 独立初始模块已实际证明可数辅助语言的 Skolem 闭包、以及外部 `W` 的共尾初等 `Lβ` 供应。仍缺具体 `W∈L`／amenability、规范限制识别及 `D†` 的供应。外部 W 是集合或模型纯成员部分足够闭合，不单独供应扩充语言的 Separation。

建议先证明规范图的统一代码识别及内部收集，再把已证的 Δ₀ 解条件接入完整塔证书。这样每一步都使用已经定义的对象和可检查的公式，不需把整条缺失反射性质包装成一个新假设字段。
