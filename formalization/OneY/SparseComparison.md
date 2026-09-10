# 稀疏行与完整比较钥匙

`SparseComparison.lean` 和 `TopComparison.lean` 形式化了 `research/1y-canonical-rebuild.md` 第 2 节的共候选链比较。输入为实际候选森林 `F`、数值函数 `v`，实际父图始终由 `Numeric.select F v` 计算；没有假设复制后的新图 canonical。

## 跳过空格的实际搜索

`filledValue cap v` 把值 0 换成 `cap+1`。仅要求当前目标 `0<v(c)≤cap`，就有：

```text
restrictedParent(F,v,c) = nearestSmaller(F,filledValue(cap,v),c)。
```

不需要其余列的值也受 `cap` 限制。正目标的所有新祖先均正且更小，故在递归父链上始终满足同一界。按列强归纳证明整个计算深度也相等，再移植既有 0-Y 共链深度比较。

主要接口为 `select_common_chain_depth_compare`、`select_parent_eq_of_common_chain_depth_eq`，以及共候选父的 `select_common_parent_depth_compare`。

## 完整深度后缀与顶值

`TopComparison.lean` 的 `KeyLT` 首先比较所有行的计算深度；仅当全部相等时才比较 `Numeric.topValue`。`rows_depth_zero_of_bound` 保证这些深度有实际有限的零尾，因此没有把顶值插在每列各自的第一处零后面。

对两个正目标、共同候选祖先链，已证明：

```text
keyLT_iff_of_common_chain : KeyLT(select F v,left,right) ↔ v(left)<v(right)
keyEQ_iff_of_common_chain : KeyEQ(select F v,left,right) ↔ v(left)=v(right)
keyLE_iff_of_common_chain : KeyLE(select F v,left,right) ↔ v(left)≤v(right)
```

证明按左目标数值强归纳。当前深度不同就决定比较；深度相同则两父相同。父存在时减去相同的正父值并进入下一行；父不存在时两列同时到顶，后续深度全零，比较转为顶值。`height_eq_of_depthsEqual` 另证明完整深度相同的正列具有相同高度。

`keyLE_iff_of_common_parent` 和 `keyLE_next_iff_of_common_parent` 是方便实际逐行使用的接口。这里的正性仅要求两个比较目标；其他列允许空格。

核验命令（在 `formalization` 中）：

```powershell
../.tools/lean-4.33.1-windows/bin/lake.exe build OneY.TopComparison
```

36 个构建任务全部成功。关键定理只依赖标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorry` 或自定义公理。尚未由这些比较定理单独推出新复制图的 canonical 重建；几何复制下的比较保持与 blocker 运输仍需分别对接。
