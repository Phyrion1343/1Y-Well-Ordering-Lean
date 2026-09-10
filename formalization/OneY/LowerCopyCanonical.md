# 下层有限行重建：已经核验的条件定理

`LowerCopyCanonical.restrictedParent_next_numeric` 已证明：给定实际原数值山脉及下列上层输入，按指定下层复制图回填的值，在每个有限行 `r≥1` 独立执行 sparse nearest-smaller，恢复指定父图。

必要输入分别是：

- 原 `[0,x)` 前缀的顶值保持；
- `UpperFixed`：原提取父在好部或不存在的非根源列，其副本顶值保持；
- `UpperOrder`：原共拟父的较后源列不大于较前源列时，副本顶值保持这个方向；
- `PseudoTopBound`：新拟父边两端同高时，子顶值不大于父顶值。

最后一项也可由 `ExtractedHeightDecrease` 推出：实际执行新拟父森林上的顶值 NS 后，每条真正父边严格降低列高。对应定理为 `restrictedParent_next_numeric_of_extracted`。这些局部输入现已由 `LowerTowerInputs` 的实际有限向下归纳统一供应，不再留作完整重建的外部条件。

本定理的内部推导不含待证明 canonical 字段：

1. `LowerCopyDepths` 计算低行、填缝、轮廓提升及锥外各段真实父链深度。
2. `LowerCopyComparison` 保持深度首个严格差或完整深度等号。全等时，原两列高度与拟父也相同，因此可使用上层 `UpperOrder` 比较最后的顶值坐标。
3. `ReconstructionComparisonPrefix` 把钥匙比较转回实际值比较，只要求已恢复的更高行在目标列及其左侧正确，不要求无限复制图在输出以外已经正确。
4. `LowerCopyBadBlocker` 实际运输旧 blocker 的位置、父链、父项和比较值，覆盖根行边界、末列接缝、任意复制块和轮廓提升。参考填缝行直接选中候选父。
5. 好部父分支由 `LowerCopyBlocker` 的正确非空尾部 C 与原根例外处理。
6. `ReconstructionTop` 处理正顶值的无父分支，读取同一行已经恢复的严格左前缀。对任意有效候选取当前行根 `a`，它也是当前列的拟父候选；若拟父是 `p`，则 `a≤p`。当 `a<p` 时，`p` 的前缀无父搜索给出 `value(p)≤value(a)`，再由根回填得到候选的下界。因此不需要预先证明新图 depth-NS 或先恢复所有新顶。
7. `restrictedParent_next_numeric` 对任意有限列前缀取有限高度上界，按剩余高度、列号归纳，消去全部“更高行正确”和“左前缀正确”的局部假设。

后续 `LowerCopyBottomRecovery.restrictedParent_bottom_numeric` 已接通底行：假设旧底行确为在继承候选森林 `F` 上选择的结果，并有实际序列保持的 `RootsOne`，独立恢复新值相对于 `FrameCopy F` 的底行父图。全部局部高行、左前缀假设已消去。`LowerCopyTransport` 进一步从这些条件推出本层的 B/C 数值输出。

`LowerCopyRebuild` 已证明实际重算的每行、列高、顶值与指定图一致，以及重新提取等于在 `FrameCopy oldTopForest` 上对新顶值执行 NS；严格高度森林的复制等式在 `LowerCopyTopForest` 中纯由几何推出。详见 `LowerCopyRebuild.md`。

后续 `LowerCopyPseudo`、`LowerCopyTopBound` 和 `LowerCopyLayerTopBound` 已完成新拟父的单类收缩、NS 运输和真实上层顶值界供应。`LowerTowerRebuild` 已闭合多层重新提取相容，`ExpansionCanonical` 接通实际有限输出。全局良基性仍需语义反射及下降接口最终实例化；数值重建完成本身不等于 1-Y 良序的完成形式化。
