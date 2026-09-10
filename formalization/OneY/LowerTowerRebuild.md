# 实际多层数值重建

`lake build OneY.LowerTowerRebuild` 已通过 154 个构建任务。关键声明只依赖 Lean 标准公理，无 `sorry` 或自定义公理。

`lowerTowerValues` 实际组装活动层以下的有限山脉；`lowerTowerRooted` 是从该组装值和已恢复底父森林构造的数值层。其定义没有 canonical 字段。

- `lowerTower_prefix_and_inputs` 对距离活动层的有限差作归纳。从无条件的活动层 B/C 和顶值界出发，向下供应每层的 `UpperFixed`、`UpperOrder`、`PseudoTopBound` 及前缀顶值保持。
- `lowerTowerBase_rawExtract_next` 证明重新提取当前实际层恰得下一实际层。
- `lowerTowerRooted_layers_mountain` 对所有自然数层号证明重新构图等于指定展开图，包括活动层以上重新提取产生的各层。
- `lowerTowerRooted_select_linear` 证明最底层确实由普通左邻候选森林上的数值搜索得到。
- `assemble_expanded_sequence_lower` 证明从原序列实际停止界生成的全部展开图，以顶值 1 回填，恰得该重建底值。

拟父运输只会把一种复制父边收缩回原根。`SingleContraction` 用真实上层的选择方程证明其 NS 不变；`LowerCopyLayerTopBound` 再由严格高度森林供应顶值界。因此向下归纳不依赖待证下层的 canonical 性。

`ExpansionCanonical` 将上述无限列函数限制为实际有限输出，并消去 `findBadRoot` 的计算分支。结果对任意复制次数、提取层、有限行及输出中每列成立。数值重建已无未实例化几何或层间比较前提。整体良基性尚需根索引语义反射与实际步骤下降的最终对接。
