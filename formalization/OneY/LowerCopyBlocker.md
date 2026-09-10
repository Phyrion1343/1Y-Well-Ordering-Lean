# 下层好部父项的实际局部恢复

`LowerCopyBlocker.lean` 把上层 C、修正版尾部 C、复制路径及 sparse NS 恢复组成了一个局部定理。它覆盖有限行 `r=u+1≥1`、非根源列 `y<s<x`、旧实际父 `P_r(s)=p<y` 的情况；包括旧 blocker 恰为根 `z=y` 的特殊分支。

主要可用接口是 `restrictedParent_good_copy_numeric`。原山脉是实际 `Numeric.mountain base hBase`；原行的 NS 方程由已证数值重建往返推出，无须另假设。副本数值是实际 `Reconstruction.value C.toRowMountain newTop`。结论为：

```text
restrictedParent(new P_(r−1), reconstructed row r, copied s) = some p。
```

保留的精确前提为：

1. 新顶值为正，原前缀 `s<x` 的顶值不变。
2. `UpperFixed`：对非根坏部源，如果计算出的旧提取父项在好部或为空，则副本顶值等于源顶值。它只是上层固定值性质 C 的数值输入，不包含当前下层的 canonical 结论。
3. 当前列严格左侧的 sparse NS 已恢复，这是列号归纳的前提。

证明实际从旧 NS 产生 blocker，再分类运输：普通非根证人复制；好部证人固定；证人等于 y 时选择**原位置 y**，用已证低行跨接缝路径。非空好部父强制非根源在提升锥外，所需原物理行数值等式由尾部 C 给出；不存在把旧顶值放回错误物理行的步骤。

`SparseBlocker.lean` 独立给出 sparse 版本的 blocker 存在与恢复。证明只对有效父链使用足够大的空格哨兵，并实际证明所产生的 blocker 为正，因此没有错误地把值 0 的空格视为可用证人。

验证：`lake build OneY.LowerCopyBlocker` 共 50 个构建任务成功。关键声明无 `sorry` 或自定义公理。

后续 `LowerCopyCanonical`、`LowerCopyBottomRecovery` 已完成坏部父、顶项无额外父和继承森林 F 的底行恢复，消除了局部前缀假设。`LowerTowerInputs` 已从实际上层统一供应准确 B/C 及同高拟父顶值界，`LowerTowerRebuild` 和 `ExpansionCanonical` 已闭合实际有限输出的完整重新提取。详见 `LowerCopyRebuild.md`；完整多层良基性仍需语义下降的最终对接。
