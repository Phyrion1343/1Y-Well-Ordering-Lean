# 下层复制数值重建与 B/C 输出

已核验的构建目标为 `lake build OneY.LowerCopyRebuild`（82 个任务）。以下关键定理仅依赖 Lean 标准公理 `propext`、`Classical.choice`、`Quot.sound`。

- `FrameCopy` 定义保留旧末列接缝的继承候选森林，证明父向左与祖先运输。`LowerCopyBottom.zero_forest_eq_frameCopy` 证明实际下层新底父森林恰是旧底父森林的该复制。
- `LowerCopyBottomRecovery.restrictedParent_bottom_numeric`：从旧 `NS_F(value)=P₀`、旧根值为 1，以及有限行恢复所用的上层条件，推出实际回填底值的 `NS_(FrameCopy F)=newP₀`。好部、坏部非空父由实际旧 blocker 得出；空父为高度 0 的锥外列，其副本值实际等于 1。按新列强归纳消去全部当前层前缀假设。
- `LowerCopyTransport.value_copy_of_good_base_parent` 给出下一层可用的 C 输出；`value_copy_le_of_common_frame` 给出 B 输出，前提是原两列共继承候选父且较后值不大于较前值。后者先比较实际底父深度，首差严格保持；深度相等时父相同，再使用已证明的带顶值深度后缀比较与加法回填。
- `LowerCopyTopForest.topForest_eq_frameCopy` 不用新 canonical，直接从轮廓提升、锥外根公式证明严格降高度森林按普通接缝规则复制。
- `LowerCopyRebuild.copiedBase_mountain` 证明重算所有行与列高，`copiedBase_topValue` 证明重算顶值，`copiedBase_rootsOne` 保持根值 1。`copiedBase_rawExtract` 精确计算重新提取为 `select (FrameCopy oldTopForest) newTop`。

这些局部定理明确输入原前缀顶值保持、上层 `UpperFixed` / `UpperOrder`，以及新图同高拟父边的顶值界 `PseudoTopBound`。后续 `LowerTowerInputs` 已通过有限向下归纳，从实际活动层供应并逐层传递全部输入；它们不再是完整数值重建的外部假设。

`LowerCopyPseudo` 已证明新拟父相对普通复制拟父的唯一收缩类型，`SingleContraction` 和 `LowerCopyTopBound` 从真实上层选择方程证明收缩前后 NS 相等。`LowerCopyLayerTopBound` 据此供应同高拟父顶值界。`LowerTowerRebuild` 已证明实际组装值的所有重提取层都等于指定展开山脉，并恢复最底层的线性候选搜索。`ExpansionCanonical` 将它接到有限输出列表与实际坏根搜索。详见 `LowerTowerRebuild.md`。整体良基性仍需根索引语义反射及下降的最终对接，不能仅凭数值重建宣称完成。
