# 实际展开与字典序良序的接口

`ExpansionOrder` 对实际 `Numeric.expand` 证明：

- 每个非空输入的展开在通常有限序列字典序下严格下降。
- 正复制次数的首接缝值恰为原末值减一。这先在活动行成立，再沿活动层低行及各个更低提取层传递。
- 当 `i≤j` 时，`E_i(s)` 是 `E_j(s)` 的前缀；零次展开恰为删尾。

`Dynamics` 据此证明固定起点后代的可达可比性。证明对实际一步关系的 accessibility 归纳；两个不同首步中，较长输出可通过删尾达到较短输出，从而在较长首步上使用归纳假设。因此通常字典序与后代之间的非空有限展开路径恰好一致。

已证明的最终组合接口为：

- `descendants_strictWellOrder hWF root`：任意固定起点全部有限后代的通常字典序良序。
- `generated_strictWellOrder hWF`：实际标准生成集的通常字典序良序。
- `expansion_chain_reaches_empty hWF chain hNext`：任意逐步选择自然数复制次数的无限记录，必有一项为空序列。

这些接口只要求实际 `Numeric.Step` 良基。种子链 `E₁(1,m+1)=(1,m)` 已由数值首接缝公式证明，没有作为假设。`generated_iff_nontrivial_seed` 证明标准集合恰是从 `(1,m)`、`m≥2` 生成的集合。

`RootIndexed.actual_expansion_wellFounded` 已从有限语义反射及初始标签表示推出所需 `hWF`，不再保留数值或几何条件。标签可在任意 `Type u` 中，因而适用于序数。实际语义反射实例仍在上层模块中完成；这里不将条件结论称为无条件总证明。
