# 1-Y 良基性形式化：证明结构与当前边界

工作区现已完成实际 1-Y 展开良基性及标准生成集良序在 Lean 4 类型论中的形式化证明，并通过内核核验。最终无参数定理见 `formalization/Concrete/OneYTruth/ActualWellOrdering.lean`，可读证明见 [1y-well-ordering-proof.md](1y-well-ordering-proof.md)。2026-09-10 又独立完成[通常数学意义的 ZFC 论证](1y-zfc-well-ordering-proof.md)：统一集合满意度、集合范围内的实际反射，以及可数序数值的下降秩。ZFC 上界由这份数学论证支持；相应证明向一阶 ZFC 演算的完整形式化迁移与机器核验尚未完成，Z₃ 上界也仍未确定。

## 展开对象

数值展开保留提取前继承的祖先关系。提取层的结构与山脉图的物理高度分别记录；复制时轮廓边抬高，不意味着提取层的标签改变。用户给出的 (1,3,3) → (1,3,2,5) 的提取层是 (1,2,2) → (1,2,1,2)，符合这一解释。旧版固定物理高度的 tail-C 引理错误，已不作为当前证明依据。

数值展开、规范重建、继承父关系与有限根索引图之间的对应已经形式化。`RootSemantics.actual_expansion_wellFounded` 保留的显式反射参数，现由无参数定理 `RootSemantics.actual_finiteReflection` 实例化。最终 `WellOrdering.expansion_wellFounded` 不再要求调用者提供反射、初始表示、真值集可构造性或良基性。

## 标签所表达的内容

图的每一列标上序数 a。对层号 k、根标签 η 和两端标签 a<b，关系 R(k,η,a,b) 表示规范结构 `(L_a,∈,较早真值谓词)` 到对应 `(L_b,∈,较早真值谓词)` 的实际 Σ₁ 保持。较早阶段按 `(k,η)` 的字典序定义：同层只能使用较小 η 的独立命名谓词；较低层可以使用带索引的对角谓词。

`Adequate(a)` 明确要求 a>ω、a 为非零极限以及全部这些规范扩展结构中的 Separation/Collection。它没有要求 L_a 是完整 ZFC 的传递集合模型。

每条图边要求一个实际 R 关系。初始表示由真实辅助真值结构上的可数 Skolem 闭包和 club 构造供应。其需要的实际统一真值集合属于 L 已通过内部递归、实际 FO 定义与 L 中的集合运算证明，现不再是额外前提。

## 为什么能将图的要求作为反射公式

对一个反射目标结构 L_α，候选的较小序数 a、规范域 L_a、完整语法/赋值/真值表都必须用内部集合表示。不能只宣称这些候选正确，也不能由它们是某个内部集合的子集就推断它们属于 L_α。

现已完成的检查包括：

- `ActualStageQuery`：用起始、后继 Def 和极限并集规则，规范识别 U=L_a。
- `ActualTowerQuery`、`ActualTruthQuery`：完整检查实际递归塔及其指定阶段真值，所有共享源与局部见证均在公式内核验。
- `ActualRelationQuery`：在严格列序、根≤父及非空域已经核验后，识别图内部两端的实际 R。
- `ActualEndpointRelation`：识别指向当前目标结构的 R；直接使用该结构允许的命名/对角谓词，不把当前结构自身的序数代码或完整真值集误当作内部参数。
- `ActualAdequateQuery`：仅以 a、ω、空集三个原始参数，内部核验实际 L_a、全部语法及真值、全部 schema 数据包与完整字段界，精确识别 Adequate(a)。

这些都是实际语法上的 Σ₁ 检查。完整集合的唯一性来自双向覆盖、无多余成员以及递归唯一性；反向所需的内部见证由真实 Collection/Separation 与有限集合运算供应。空域的 Def 步骤单独处理。

`ActualRelationQuery` 本身不负责严格次序护栏。例如两端相等时真值一致性可以成立，但 R 仍要求 a<b。有限图矩阵必须先检查并解码严格递增的序数元组，再从各顶点的 Adequate 条件和图的合法性推出该护栏。这一步在最终装配中显式保留。

## 有限反射如何完成下降

设切点标签为 α=f(cut)，大端标签为 β，已有 R(K,θ,α,β)。共同的 ω、零、有限层号及切点左侧标签作为 L_α 中固定参数。其余有限列标签及所有检查证书作为存在见证。

对指向顶端的需求，允许性条件恰保证所需谓词可用：层号小于 K，或同层根索引是切点左侧的固定索引且小于 θ。于是整个有限图要求可以在这一个语言中合成为一个 Σ₁ 公式。

大结构中的原图供应见证，Σ₁ 保持将整批见证反射到 L_α。解码后的新标签严格小于 α，固定前缀保持不变，所有内部边和顶端需求仍成立。数值展开对应的有限图拼接定理随后给出实际展开的下降和良基性。

`ActualQueryMetadata` 实际供应所需的有限固定参数，`ActualDiagramQueries` 供应全部局部公式及有护栏的双向语义；`FiniteReflectionAssembly` 把它们合成一次联合反射；`ActualFiniteReflection` 最终证明具体 `FiniteReflection`。该定理的 1623 项构建已通过。`ActualWellOrdering` 的四个无参数出口随后通过 1802 项构建，公理审计均只有 `propext`、`Classical.choice`、`Quot.sound`。

最终总入口 `lake build OneYTruth` 通过 1810 项构建；`lake env lean OneYTruthAudit.lean` 输出 148 项（147 个不同声明）的历史审计通过。日志保存在 [总构建记录](one-y-truth-final-build.log) 和 [公理审计记录](one-y-truth-final-audit.log)。

集合满意度替换后的最新完整验证为 1814 项构建与 153 个不同声明的发布审计，全部通过。见[最新构建](one-y-truth-zfc-build.log)、[最新审计](../formalization/Concrete/OneYTruth-audit-output.txt)及[类真理调用检查](1y-zfc-class-truth-call-audit.md)。

展开良基性及轨迹终止覆盖所有空序列或首项为 1 的正整数序列；字典序良序结论覆盖标准种子经实际展开生成的集合，以及任意固定起点的展开后继集合。没有声称所有首项为 1 的正整数序列在字典序下良序；该全域反而存在显式下降链。

Lean 的 `[propext, Classical.choice, Quot.sound]` 审计只说明没有 `sorry` 或额外声明公理混入对应定理。它本身不是对象理论 ZFC 中可形式化性的证明，更不自动判定最弱公理系统或精确证明论序数。
