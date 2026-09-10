# 非标准 BM4 形式化接口审计

初次审计：2026-09-09；最后更新：2026-09-10。审计对象是上游基线提交 `bae7e3d741f24a56d80da9b99c1345562cd10c2d` 与 `0Y-BMS-equivalence-proof.md` 第 7.1 节。初次报告来自源码审读；后续独立 `AnyArray.lean` 扩展和最终具体模型均已通过 Lean 编译及公理依赖审计，见 [验证记录](../formalization/VALIDATION.md)。具体模型构建使用两个本地证明性能补丁，通过分块证明、泛化语义桥与同步内核检查降低内存开销；保留原公开定理陈述、公式与假设，准确补丁和哈希见 [具体模型说明](../formalization/Concrete/README.md)。

## 结论

任意合法矩阵的展开良基性可以在上游现有接口上扩展。真正需要新增的是“任意矩阵拥有有界稳定表示”；降界和固定根的展开闭包可比性均已有不要求标准性的接口。建议沿 `Acc` 归纳，省去纸面最小序数上界 `ρ(A)` 的定义。

核心层只需 `import YesMetaZFC.BMS.WellFoundedness`。该模块传递导入了父项、祖先、规范数组、展开、生成关系、Lemma 2.5、稳定表示与展开可比性，且核心项目没有外部 Lake 包依赖。最终具体模型由独立的 `formalization/Concrete` 工程导入 `BMSConstructibleBridge.FinalAssembly`，并接入其构造宇宙和 mathlib 依赖。

## 已有精确接口

以下简称都位于 `YesMetaZFC.BMS`；稳定表示相关名称进一步位于 `StabilityFrame`。

| 接口 | 源文件 | 可复用的内容 |
| --- | --- | --- |
| `ValidArray` | `Array.lean` | `raw : List (List Nat)`，矩形、已去共同尾零行；不要求 `Generated`，也不要求深度正规 |
| `Step smaller larger` | `Generation.lean` | `ExpansionEdge larger smaller ∧ smaller ≠ larger`，其中边是 `∃ n, smaller = larger.expand n` |
| `ExpansionPath root target` | `Generation.lean` | 可含退化边、含零步的有限展开路径 |
| `StableRepresentation frame A` | `Stability.lean:142` | `label : Fin A.raw.length → Label`，标签按列严格增加，并保持每个布尔 `isAncestor` 真实例的 `frame.stableLt row` |
| `representation.BoundedBy bound` | `Stability.lean:156` | 每个列标签严格小于 `bound` |
| `RepresentationDescentSystem frame` | `WellFoundedness.lean:41` | 所有种子的有界表示存在，以及**任意** `ValidArray` 的每次非平凡展开降低表示上界 |
| `system.exists_bounded_of_generated hGenerated` | `WellFoundedness.lean:59` | 标准生成矩阵具有有界表示 |
| `system.accessible_of_bounded` | `WellFoundedness.lean:79` | 目前带 `Generated A` 参数；证明只用该参数传递生成性，并未用它获得任何下降事实 |
| `expansionPath_endpoints_comparable_of_accessible` | `ExpansionOrder.lean:426` | 从任意 `Acc Step root` 出发，两条 `ExpansionPath root` 的终点相等或互有 `StrictDescent`；没有标准性前提 |
| `WellOrderingModel.representationDescentSystem` | `BM4WellOrder.lean:42` | 完整反射模型到上述抽象系统 |
| `ConstructibleBridge.reflectionData_l` | `ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean:54` | 无额外数据参数的具体 `ReflectionWellOrderingData` |

因此最终实例可沿下式取得：

```lean
YesMetaZFC.BMS.ConstructibleBridge.reflectionData_l
  |>.wellOrderingModel
  |>.representationDescentSystem
```

这一接口已在 [ZeroYConcrete.lean](../formalization/Concrete/ZeroYConcrete.lean) 中实际实例化并编译；模型自身及全部最终包装定理也已通过公理依赖审计。

## 任意初始表示：不必展开证明整个阶梯矩阵

纸面使用 `U(h,m) = (0^h)(1^h)…((m−1)^h)`。形式化可稍换参数，取

```lean
let U := (validSeed (h + 1)).expand m
```

它有 `m+1` 列，保留前 `m` 个标签用于目标矩阵即可。这样 `m=0`、`m=1`、`h=0` 都统一处理，无须自然数截断减法分支，也无须先证明 `U.raw` 的全部坐标公式。

给定 `A : ValidArray`，先由

```lean
rectangular_iff_exists_uniformHeight.mp A.rectangular_eq
```

取高度 `h`，令 `m := A.raw.length`。为 `validSeed (h+1)` 显式构造

```lean
{ lastIndex := 1, maximalRow := h, parentColumn := 0, ... }
  : ExpansionContext (validSeed (h + 1))
```

三个证明字段分别由 `raw_validSeed`/`seed`、`maximalParentRow_seed_succ h`、`parent_seed_one_of_lt (row := h) (height := h+1)` 给出。这个上下文有 `blockLength = 1`、`copyPosition k 0 = k`。

随后直接复用：

1. `context.length_expand m`，给出 `U.raw.length = m+1`。
2. `context.first_copy_ancestor_of_lt`（`Lemma25.lean:678`），给出任何 `i < j ≤ m`、`r < h` 下 `isAncestor U.raw r i j = true`。这已经证明了需要的全祖先关系。
3. `Generated.expand (Generated.seed (h+1)) m` 和 `system.exists_bounded_of_generated`，取 `U` 的有界稳定表示。
4. 定义新标签为 `U` 表示在第 `i` 列的标签，索引从 `Fin m` 嵌入 `Fin (m+1)`。
5. 为验证 `A` 的祖先约束，从 `isAncestor_lt` 得 `i<j`；由 `ancestor_entries_lt` 取得对应行的有效条目，再由 `row_lt_uniformHeight_of_entry?_eq_some` 得 `r<h`。于是可调用第 2 项，并交给 `U` 的 `preservesAncestor`。

标签严格递增和有界性直接由源表示限制获得。这个论证完全不使用 `A` 的数值大小、深度正规性、条件 (S) 或标准性。

建议新增可复用的辅助定义 `StableRepresentation.restrictAlong`：输入列索引映射，要求它严格递增且把目标的祖先关系送到源祖先关系，输出目标稳定表示，并证明保持 `BoundedBy`。也可以先内联，待接口稳定后抽取。

## 已完成的 Lean 定理依赖

实际实现位于自己的桥接命名空间内，没有覆盖上游同名定理：

1. `accessible_of_bounded_any`：删除上游 `accessible_of_bounded` 的 `Generated` 参数；按 `Acc frame.lt bound` 归纳，使用 `system.expand_bounded` 获得更小上界，再调用归纳假设。
2. `exists_bounded_any`：实现上面的种子一次展开与标签限制构造。
3. `step_wellFounded_any : WellFounded Step`：对任意 `A`，取第 2 项见证，再给第 1 项输入 `frame.lt_wellFounded.apply bound`。
4. 任意起点的展开闭包可比性：对 `step_wellFounded_any.apply root` 直接调用 `expansionPath_endpoints_comparable_of_accessible`。
5. 有限严格展开的良基性：`WellFounded.transGen` 可以直接用于 `Relation.TransGen Step`。
6. 字典序桥接：另证每步严格下降，再把固定根上的可比性转为字典序良序；这一步不是上游 `compareArray` 的现成结论。
7. 最后从 0-Y 的展开交换定理和编码单射，把任意合法 0-Y 的 `Step` 送到矩阵 `Step`，用良基关系的逆像传输。

初次审计时这些均为待实现清单。随后已在独立模块 `formalization/ZeroY/BMS/AnyArray.lean` 写下第 1–5 项的完整证明项：`accessible_of_bounded_any`、`exists_bounded_any`、`step_wellFounded_any`、`transGen_step_wellFounded_any`、`descendants_comparable_any`。初始表示实际直接以复制块首列作索引，因此连种子展开长度的显式等式也省去了。

**第 1–7 项均已通过 Lean 4.33.1 编译。** 第 6 项位于 `ZeroY/BMS/PaddedDescent.lean`，第 7 项及具体展开同构位于 `ZeroY/Expansion/Conjugacy.lean`、`ZeroY/Dynamics/Equivalence.lean`；公理依赖均只包含 `propext`、`Classical.choice`、`Quot.sound`。核心降界定理保留显式模型参数；具体构造宇宙实例已在独立的 `formalization/Concrete` 工程中从锁定源码构建成功，共 1576 个任务通过。模型自身和 13 个无需额外模型参数的最终定理另经 14 项公理审计，全部仅依赖上述三个标准公理。实际输出见 [验证记录](../formalization/VALIDATION.md)。

## 易错点与纸面证明审查

- **关系方向不同。** `Step smaller larger` 使用良基关系方向；`ExpansionPath root target` 使用执行方向。上游 `StrictDescent smaller larger` 定义为 `Relation.TransGen (fun source target => Step target source) larger smaller`，不是逐字 `Relation.TransGen Step smaller larger`。可证明二者等价后传输，不能直接用 `rfl` 混同。
- **退化展开须排除。** 空矩阵可一直展开成自身，因此良基的是 `Step`，不是所有 `ExpansionEdge`。0-Y 一步关系也应显式要求两端不同，并用编码单射把该条件传到矩阵端。
- **上游有限列字典序不能直接借用。** `Reference.compareColumn` 把真有限前缀判小；本文是列内补无限尾零后比较。例如可逆矩阵 `A=(0,0)(1,1)` 和 `B=(0,0,0)(1,0,0)(2,1,1)`，上游首零列长度使 `compareArray A B = .lt`，但本文补零字典序有 `A > B`；它们分别编码 `(1,3)` 和 `(1,2,5)`。必须建立自己的补零矩阵序，或用共同填充长度的比较并证明填充不变性。
- **全域不是线性展开序。** `WellFounded Step` 与固定根闭包的全序，均不说明所有合法 0-Y 或所有可逆矩阵的全域字典序良序。下降族 `(1^k,2)` 必须保留在规格的反例部分。
- **表示降界范围已经在类型中处理。** 具体桥的标签是相应 `BoundedOrdinal σ`；复用实际模型保留这个限制，不要另造裸 `Ordinal` 标签后假定同一个有限支撑结论。
- 第 7.1 节的数学扩展未发现新的逻辑缺口。`U` 确实提供目标全部祖先约束的超集；用多留一列的方法仅简化退化情况。`Acc` 路线比“最小稳定上界”更贴合现有形式化，也避免在抽象 `StabilityFrame` 上额外假定标签序为全序。
- 0-Y 的山脉有限性、父图栈引理、精确往返、共链保序、条件 (S) 保持及独立算法的展开交换式，均已在本地 `ZeroY` 模块中完成。这些新增证明没有假定互译 HTML 程序准确，也没有将上游 BMS 良序性当作它们的替代。

上游 `AGENTS.md` 已阅读。与本任务相关的要求包括使用 `lake build` 验证、中文注释、不把测试枚举冒充通用定理、不新增未说明的 `sorry`/自定义公理。其关于源仓库公共 Library 回写的要求不涉及本任务的独立本地桥接工程。
