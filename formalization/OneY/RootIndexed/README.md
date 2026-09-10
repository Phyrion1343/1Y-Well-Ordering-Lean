# 根索引表示与实际展开下降

`Representation.lean` 只依赖 `Std`，采用任意标签类型 `α`、严格关系 `lt`、端点谓词 `D` 与根索引关系 `R k root parent child`。它不假定存在某种具体序数类型，也不把 1-Y 展开下降放进结构字段。

核心接口的具体语义实例已经完成。[ActualFiniteReflection.lean](../../Concrete/OneYTruth/ActualFiniteReflection.lean) 证明实际关系的有限反射，[ActualWellOrdering.lean](../../Concrete/OneYTruth/ActualWellOrdering.lean) 给出实际展开良基、标准生成集和固定后代集字典序良序、任意展开链终止四个最终定理，不再要求调用者提供反射或初始表示。当前数学入口是[实际展开证明](../../../research/1y-well-ordering-proof.md)与[ZFC 论证](../../../research/1y-zfc-well-ordering-proof.md)。

已经由 Lean 检查的内容：

1. 有限图原子、严格递增表示、严格序数界的抽象版本。
2. `spliceLabel`：反射旧末块后，在右侧重新使用该块原标签；证明列顺序、端点论域与整体界保持。
3. `representation_splice`：逐边证明旧图保存、原模板复制、参考边根指标降低、接缝需求转移。新图关系不是构造的假设。
4. `virtual_demands_from_templates`：从原末列模板关系与根指标降低，证明全部虚拟末端需求。
5. `exists_bounded_representation_splice`：将有限反射接口用于上述构造，得到新图表示及全部标签 `< beta`，并证明最后一块保留原标签与原关系储备。
6. `blockScheme_bounded_representations`：对任意有限块数归纳。`BlockScheme` 仅含图、列号映射和纯组合逐边分类；没有表示、稳定关系、反射或下降字段。归纳实际证明原模板储备与控制关系在下一末块重新成立。
7. 删除前缀的表示限制与末标签严格下降，以及从有界表示取得一个较小的末标签。
8. `wellFounded_of_lowerable_labels`：每一步可为目标选择较小有效标签即可得到良基性，不需选全局最小表示。

从抽象接口到实际 1-Y 的已完成连接：

* `FiniteReflection` 在 `Representation.lean` 中是显式语义接口，反射有限内部图与合法的到环境需求。具体混合真值结构的实例由 `RootSemantics.actual_finiteReflection` 实际证明。
* `ActualScheme.actualBlockScheme` 已从完整、无预算限制的 Lean 1-Y 山脉和展开定义构造 `SpliceGeometry` / `BlockScheme`，所有逐边分类均已证明。`ExpansionCanonical` 也已证明重新提取真实有限输出会恢复这些复制图。
* 根指标关系的严格性、弱化性、端点初始供应与标签序良基性均已由 `Concrete/OneYTruth` 的具体序数及真值模型供应。
* `ExpansionWellFounded.actual_expansion_wellFounded` 已把有界表示构造接到真实 `Numeric.expand` 的每个非平凡步骤，并单独处理空状态。这个可复用定理的前提为标签序良基且传递、根关系严格且可弱化、`FiniteReflection`、每个实际初始有限图有表示；不再保留数值重建、父图运输或几何分类假设。具体语义层供应全部前提后，`OneYTruth.WellOrdering.expansion_wellFounded` 是无这些外部输入的最终出口。

良序范围是标准种子 `(1,m)`、`m≥2` 的共同生成集，或任意固定合法起点的后代集。对全体合法起点证明的是展开关系良基，未声称全部首项为 1 的正整数序列整体按字典序良序。

`BlockScheme` 的模板关系不要求都是当前图的实际边。这是刻意保留的证明细节：轮廓提升后，最右块仍使用原标签，因此它保留原模板的较强关系储备；再次反射时，只需保存当前图的实际有限关系，随后新末块重新获得原储备。

核验命令（工作目录 `formalization`）：

```powershell
../.tools/lean-4.33.1-windows/bin/lake.exe env lean OneY/RootIndexed/Representation.lean
```

当前命令退出码为 0，无警告。四个核心拼接/迭代定理的 `#print axioms` 只含 `propext`、`Quot.sound`；良基传输定理不依赖任何公理。文件没有 `sorry`，没有自定义 `axiom`。

完整具体模型的核验命令（工作目录 `formalization/Concrete`）：

```powershell
../../.tools/lean-4.33.1-windows/bin/lake.exe build OneYTruth
../../.tools/lean-4.33.1-windows/bin/lake.exe env lean OneYTruthAudit.lean
```

最终声明的公理审计只包含 Lean 标准的 `propext`、`Classical.choice`、`Quot.sound`。上面的 ZFC 论证另行说明集合论中的证明，不把公理打印本身当作一阶 ZFC 形式化证明。
