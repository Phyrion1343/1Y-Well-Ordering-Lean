# 下层复制图的实际深度

`LowerCopyDepths.lean` 从 `LowerCopy.Context` 指定父图及已证明的嵌套性直接计算深度，不使用新图 canonical 假设，也不替换列顶值。

设 `h=H(y)`、`δ=H(x)−h`、`L=x−y`、`d_r(c)=depth(P_r,c)`。

- `depth_lifted`：锥内同步提升后，`d'_(u+bδ)(c+bL)=d_u(c)`，`u≥h`。
- `depth_fill`：锥内填缝行 `h≤r<h+bδ`，令 `j=(r−h)/δ`、`t=h+(r−h)%δ`，则 `d'_r(c+bL)=d_h(c)+(b−j−1)d_h(x)+d_t(x)`。
- `depth_low_of_root_ancestor`：`r<h` 且 `y=c` 或 `y` 是 `P_r` 祖先时，复制深度增加 `b(d_r(x)−d_r(y))`。
- `depth_low_of_no_root_ancestor`：`r<h` 且祖先链不经过 `y` 时深度不变。
- `depth_outside_high`：`r≥h` 的锥外列深度不变。

低行增量通过 `depth_low_ancestor` 保存同块两列之间的父链距离，再由 `y_(b+1)=x_b` 对块数归纳得到；填缝公式通过相同的参考行父链距离证明。所有等式都是计算所得父森林的深度等式。

这些结论只完成比较钥匙运输的几何坐标部分。恢复实际数值的 bad-parent blocker 仍需证明严格深度首差保持，并在深度全等时使用上层顶值比较；不能由这些深度公式直接声称新数值父图已恢复。
