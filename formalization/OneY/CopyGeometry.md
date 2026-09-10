# 已计算的复制坐标与下层父图

`CopyCoordinates.lean` 使用 `y<x` 的真实商余数坐标：

```text
L=x-y
width(N)=x+N L
source(c)=y+1+(c-y-1)%L
block(c)=(c-y-1)/L
```

对 `c>y` 已证明 `y<source(c)≤x`、`c=source(c)+block(c)L`，以及这一表示唯一。源列 `x` 表示接缝；原末列位置 `x` 的块号是 0。

有效范围的精确结论为：

```text
source+bL < width(N)
  iff b<N 或 (b=N 且 source<x)。
```

因此末尾不包含 `source=x, b=N` 的虚拟末列。父列在好部时固定，否则平移 `bL`；其严格向左性已证明。

`LowerCopy.lean` 的输入是实际 `RowMountain`、复制坐标、旧末列属于根顶行分量，以及 `H(y)<H(x)`。它直接定义原前缀保持、锥外普通运输、锥内插入参考行及提升轮廓行的 `height` 和 `parent`。没有把新图合法性或 canonical 性当成字段。

已证明：

* 普通源列和根副本的精确新高度；根副本高度为 `H(y)+b delta`。
* 高行父仍在同一锥内，运输后父高度的精确公式。
* 每条新父边严格向左，源格低于其新顶，父端点实际存在。
* 每个低于新顶的格都有父项，顶及以上恰无父项。
* 限制到输出宽度不会丢失任何保留列的父端点。

这些定义对任意自然列号给出一致的复制图；一次有限展开取 `c<width(N)` 的前缀。

`LowerCopyNesting.lean` 进一步证明了新相邻行森林的 `nested_succ`，并通过 `Context.toRowMountain` 把上述实际公式包装成完整 `RowMountain`。没有把行间嵌套性作为假设。

祖先运输的关键分为三种：

* 低于根顶行：好部固定，坏部平移。源路径到达根列后，新路径可经过之前的接缝；`root_good_ancestor` 按复制块号归纳证明仍到达原好部祖先，继而得到 `low_ancestor_copy`。
* 锥外高行：父祖先仍在锥外，`outside_ancestor_copy` 逐边保持普通运输。
* 锥内高行：`lifted_ancestor_copy` 保持整条同块祖先路径，物理行从 `u` 提升到 `u+b delta`。

填缝区域相邻行使用同一参考父图；在填缝末端，提升图的首行也恰是参考行。根顶行下方的边界则使用低行祖先运输。这些结论共同证明 `nested_succ`。

**数值回填后的最近较小 canonical 性仍待后续证明；这里证明的是指定复制父图本身构成山脉。**

`LowerCopyRoots.lean` 从计算得到的 `ParentForest.root` 进一步证明完整的根索引公式。设 `s` 在 `(y,x]`、`s` 在提升锥中、`h=H(y)`、`delta=H(x)-h`：

* 轮廓高段 `r≥h+b delta` 的根是 `oldRoot(r-b delta,s)+bL`（`rootAt_high`）。
* 填缝段 `h≤r<h+b delta`，令 `j=(r-h)/delta`、`t=h+(r-h)%delta`，根是 `oldRoot(t,x)+jL`（`rootAt_fill`）。
* 低于 `h` 时根是旧好部根，不随块改变（`rootAt_low_cone`）。
* 锥外任意行的根按普通 `parentCopy` 运输（`rootAt_outside`）。
* 原前缀的根保持不变（`rootAt_original`）；所有填缝根严格小于当前块根 `y+bL`（`rootAt_fill_lt_rootCopy`）。

填缝公式按块号归纳：参考父链先到当前根副本，再把此列视为前块的末列，重复直到到达商余数指定的块。根的无父性、可达性及唯一性全部实际证明，没有为这些公式新增接口假设。

核验命令（工作目录 `formalization`）：

```powershell
../.tools/lean-4.33.1-windows/bin/lake.exe build OneY.LowerCopyRoots
```

编译成功。关键定理只依赖 Lean 标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorry` 或自定义 `axiom`。
