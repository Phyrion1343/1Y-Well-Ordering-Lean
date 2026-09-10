# 回填计算与数值山脉往返

这两个模块已经通过 Lean 编译；它们不依赖根索引反射接口，也没有把展开后的 canonical 性放入假设。

`Reconstruction.lean` 的 `value M top r c` 按列号 `c` 作真实良基递归：

```text
r > H(c) 时为 0；
其余为 top(c) + Σ(u = r,...,H(c)-1) value u parent_u(c)。
```

每次递归调用的父列都严格小于 `c`。由此证明了：

* 顶值、空格值及实际父子加法递推；
* 正顶值下，每个实际格恰好为正，每条父边的父值严格较小，每下降一行数值严格增加；
* 同一父图和顶值的重建存在且唯一；唯一性先对列号归纳，再从有限顶高向下归纳；
* 只要某个前缀的高度、父项和顶值相同，该前缀所有重建值相同，右侧列不会影响它。

`ReconstructionNumeric.lean` 将此函数接到真正计算的 `Numeric.mountain`：

```lean
value (Numeric.mountain base hpos) (Numeric.topValue base)
  = fun r c => (Numeric.rows base r).value c
```

证明先从实际差分定义与 `Nat.sub_add_cancel` 取得加法递推，从 `live_iff_le_height` 取得空格值，再使用前述唯一性。包含有限正整数输入的底行往返，以及原数值山脉高行父项重新搜索后的恢复。

这里的往返是“原数值山脉 → 其父图和顶值 → 回填”。**复制展开后的新图 → 重新最近较小搜索**仍需要展开运输与 blocker 证明；本模块没有声称完成那一步。

核验命令（工作目录 `formalization`）：

```powershell
../.tools/lean-4.33.1-windows/bin/lake.exe build OneY.ReconstructionNumeric
```

当前命令成功完成全部 21 个任务。基础重建关键定理的 `#print axioms` 仅含 `propext`、`Quot.sound`；数值往返因既有 `Numeric` 依赖另含 `Classical.choice`。没有 `sorry` 或自定义 `axiom`。
