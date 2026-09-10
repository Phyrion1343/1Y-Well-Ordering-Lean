# 1-Y 的展开终止性与生成序列良序：完整证明说明

**状态（2026 年 9 月 10 日）：下面的四个最终定理已经通过 Lean 内核检查。** 总入口构建成功（1814 项）；发布审计的 153 个不同声明均仅依赖 `[propext, Classical.choice, Quot.sound]`。四个最终出口均无有限反射、初始表示、真值集合、数值重建或良基性假设。

本文按数学依赖顺序说明这份已通过 Lean 4 内核核验的形式化证明，[proof-architecture](<1y-proof-architecture.md>) 提供补充结构概览。另行完成的[ZFC 论证](1y-zfc-well-ordering-proof.md)给出通常数学意义的 ZFC 上界，包括集合满意度替换与可数序数值的下降秩。相应证明向一阶 ZFC 演算的完整形式化迁移与机器核验尚未完成；Z₃ 上界、最弱证明系统与精确序型也仍未确定。

## 一、究竟证明了什么

令 

\[
\mathcal E=\{\varnothing\}\cup
\{(a_0,\ldots,a_{m-1}):m>0, a_0=1, a_i\in\mathbb N_{>0}\}.
\]

形式化沿用载体名 `ZeroY.Expr`，但本证明在其上使用的是 **1-Y 的实际展开函数** `OneY.Numeric.expand`，记为 \(E_N(s)\)。下标 \(N\in\mathbb N\) 表示追加的坏部复制数；特别地，\(N=0\) 删除末项。空序列的展开仍为空序列。

定义非平凡一步下降关系

\[
t\prec s\quad\Longleftrightarrow\quad
\exists N\in\mathbb N\ [t=E_N(s)]\quad\text{且 }t\ne s.
\]

已证明的结论是：

1. **全域展开良基性。** \(\prec\) 在全部 \(\mathcal E\) 上良基。
2. **任意展开策略终止。** 若 \(s_{n+1}=E_{N_n}(s_n)\)，其中每一步可任意选择有限的 \(N_n\)，则存在 \(n\) 使 \(s_n=\varnothing\)。不要求复制次数固定、单调或由可计算规则选择。
3. **单一起点的后代字典良序。** 对任意 \(s\in\mathcal E\)，所有经过有限次展开可从 \(s\) 到达的表达式，按“真前缀较小”的通常字典序构成严格良序。
4. **标准生成序列的字典良序。** 从种子 \((1,m)\)、\(m\ge2\)，经过有限次展开生成的全部表达式，按同一字典序构成严格良序。

第三项的载体是 `Descendant s`，第四项的载体是 `GeneratedExpr`。这一区分不能省略：**全部合法表达式的字典序并非良序**，因为

\[
(1,2)>_{\rm lex}(1,1,2)>_{\rm lex}(1,1,1,2)>_{\rm lex}\cdots.
\]

这些表达式各自仍满足第一项的展开终止性。展开关系的良基性与全域字典序的良基性是不同命题。

## 二、先把实际 1-Y 山脉和展开确定下来

对某一提取层，记第 \(r\) 行的数值为 \(v_r(c)\)，父森林为 \(P_r\)。每条父边严格向左。最底行的父项由原序列的最近较小项决定；之后每行只在上一行继承的祖先链上寻找最近的较小项。没有上方项的位置是空位；不能把 0-Y 中“第一项在每一行保持不变”的约定带入这里。

一列 \(c\) 的有限高度 \(H(c)\) 是该层中最高非空项的行号。提取取各列最高项

\[
U(c)=v_{H(c)}(c).
\]

**提取同时继承祖先结构，不只保留数值表。** 形式化从该层的真实父森林计算拟父森林 \(Q\)，然后对 \(U\) 沿 \(Q\) 选择最近较小项，得到下一提取层的父森林。具体地，当 \(H(c)>0\) 时，\(Q(c)\) 从第 \(H(c)-1\) 行的祖先链上，取最近的、列高为 \(H(c)\) 或 \(H(c)-1\) 的候选；\(H(c)=0\) 时没有拟父。这个几何公式及它与实际提取的关系均已证明。

每一次构造所需的行数和提取层数都是有限的。当某列的当前层底值大于 1 时，它的提取顶值严格小于该底值；值为 1 时保持为 1。因此，对有限输入 \(s\)，\(\max(1,\max s)\) 给出经过证明的统一提取层数界。超过该界的层全为 1，没有父边。这只是“一个输入的完整山脉能构造完”的证明，尚不是反复展开终止性的证明。

### 例子：\((1,3,3)\) 的第二层确实是 \((1,2,2)\)

在第一层中，两个 3 的原父项都为第一个 1，因此它们上方的值均为 2。每列的最高项为

\[
(1,2,2).
\]

对它作一次坏部复制后，上层数值成为 \((1,2,1,2)\)，实际底层展开为

\[
E_1(1,3,3)=(1,3,2,5).
\]

展开后第一层的实际非空项是：

| 第一层内的有限行号 | 第 1 列 | 第 2 列 | 第 3 列 | 第 4 列 |
|---|---:|---:|---:|---:|
| 2 | — | — | — | 2 |
| 1 | — | 2 | 1 | 3 |
| 0 | 1 | 3 | 2 | 5 |

各列最高项仍然是 \((1,2,1,2)\)。第四列的提取顶值 2 已经升到第一层的第 2 行；第 1 行的 3 是填入的参考部分。因而不能把“提取层中的对应位置”误读为“原山脉中固定物理高度的位置”。这些输出、列高及参考项有直接的 Lean 计算证明。

后文始终区分三个指标：

* \(k\)：第几次提取得到的层，原层记为 \(k=0\)；
* \(r\)：某一层山脉内部的有限行号；
* \(f(c)\)：证明中给第 \(c\) 列配置的序数标签。

抬高轮廓边改变的是有限行的位置；它不自动改变提取层号，也不把列的数值当作序数标签。

### 必须证明规范重建相容

给复制后的父图随意填入一组顶值，再逐层加回父值，未必能恢复原先指定的父关系。下一次按“最近较小祖先”重建时，父项可能改变。因此，只证明复制图的几何规则不够。

当前形式化对**真实上层展开产生的顶值**证明了各行所需的比较与阻挡条件，依次恢复活动层、下层和上层的最近较小父图。最终结论是：把实际输出序列重新完整构造山脉，得到的每一提取层、每一行父项和列高，都与展开构造指定的图一致。在有限输出宽度之外不要求不存在的额外相容性；冗余全 1 层也不贡献父边。

这一步由 `ExpansionCanonical` 的 `expandValues_layers_of_badRoot`、`expandValues_height_of_badRoot`、`expandValues_parent_of_badRoot` 及图前缀定理给出。它保证以下序数论证研究的是实际可反复执行的 1-Y 展开。

## 三、用每一行的分量根给父边标记

固定提取层 \(k\) 和有限行 \(r\)。沿父森林 \(P_{k,r}\) 从列 \(c\) 不断向左，最终到达无父项的列，记为

\[
q_{k,r}(c).
\]

这是该行父森林中 \(c\) 所在树的根。父项严格向左，所以根由有限良基递归直接计算，不是额外指定的资料。如果 \(P_{k,r}(c)=p\)，则

\[
q_{k,r}(c)=q_{k,r}(p)\le p<c.
\]

将这条真实父边记录为一个原子

\[
e=(k,q,p,c).
\]

有限表达式的全部提取层和有限行只给出有限多个这种原子，组成有限图 \(G(s)\)。**这里的分量根 \(q\) 与展开的坏根列 \(y\) 是两个概念。** 活动父边为 \(x\to y\) 时，控制这条边的分量根可以在 \(y\) 的左边。

我们给各列配置严格递增的序数

\[
f(0)<f(1)<\cdots<f(m-1),
\]

并要求每个标签满足条件 \(D\)，每个原子满足关系

\[
R\bigl(k,f(q),f(p),f(c)\bigr).
\]

这就是 \(G(s)\) 的一个**表示**。它使用整座山脉的所有父边；既不丢弃继承祖先信息，也不只观察数值上的最顶提取层。

根索引是关键：复制和参考填充引起物理行高变化时，相应分量根仍可追溯到原边的根，或者变成一个标签更小的根。关系 \(R\) 将允许后一种索引弱化。因此不必要求山脉的总物理高度、提取层数或某个朴素顶层序数在每一步都下降。

## 四、序数标签的实际含义

### 4.1 规范混合真值结构

对集合域 \(U\) 和序数界 \(\kappa\)，在指标

\[
(k,\eta)\in\mathbb N\times(\kappa+1)
\]

上，按先比较 \(k\)、再比较 \(\eta\) 的字典良序，递归构造完整的一阶满意度集合。

第 \((k,\eta)\) 个结构包含：

* 真实的成员关系 \(\in\)；
* 同一层中 \(\xi<\eta\) 的较早真值谓词，分别作为命名谓词；
* 每个 \(j<k\) 的较低层真值，通过一个同时接收序数代码的对角谓词访问。

每个阶段的真值只引用严格较早阶段，故递归良定义。`truth_eq_satisfactionSet` 与 `mem_truth_iff` 说明这些集合确实表达该结构中的完整公式真值。较大和较小界之间所需的相容性、语言约化与赋值代码相容性也在进入根关系前证明。

在域 \(L_a\) 上所得规范结构记为 \(\mathfrak M_{k,\eta}(L_a)\)。定义

\[
R(k,\eta,a,b)
\]

为以下条件的合取：\(\eta\le a<b\)，且自然包含映射

\[
\mathfrak M_{k,\eta}(L_a)\hookrightarrow
\mathfrak M_{k,\eta}(L_b)
\]

保持所有实际 \(\Sigma_1\) 公式的真值，包括任意有限赋值。这里“保持”给出两端真值的等价，因而也允许把在大结构中成立的存在断言反射回小结构。

由定义与语言约化证明：

\[
\begin{aligned}
R(k,\eta,a,b)&\Longrightarrow a<b,\\
\xi\le\eta, R(k,\eta,a,b)&\Longrightarrow R(k,\xi,a,b),\\
R(k,\eta,a,b), R(k,\eta,b,c)&\Longrightarrow R(k,\eta,a,c).
\end{aligned}
\]

此外，较高层关系可以通过对角谓词给出相应的较低层关系。以上是具体规范真值结构的定理，不是为获得下降而添加的关系公理。

### 4.2 Adequate 条件

置 \(D(a)=\operatorname{Adequate}(a)\)，其定义恰为：

\[
\omega<a,\qquad a\text{ 是非零极限序数},
\]

并且对每个有限 \(k\) 和每个 \(\eta\le a\)，真实结构 \(\mathfrak M_{k,\eta}(L_a)\) 满足展开语言中的 Separation 与 Collection 模式。

这个条件供应后续内部集合构造所需的闭包。它没有被定义为“\(L_a\) 是完整 ZFC 的传递集合模型”，也没有把未来所需的整个真值塔或数据包作为未证明的成员字段塞入定义。

## 五、每个有限图都有初始表示

在 \(L_{\omega_1}\) 上，把规范混合真值塔统一编码为一个真实辅助谓词。完整统一真值集合属于 \(L\) 已通过实际递归、语法定义及可构造集合运算证明。

对这个固定辅助结构，构造可数 Skolem 闭包，得到 \(\omega_1\) 以下无界的初等 \(L\) 阶段；在极限处通过初等子结构链的并证明闭性。选取这些阶段中大于 \(\omega\) 的成员，可以得到任意长的严格递增有限链

\[
\alpha_0<\alpha_1<\cdots<\alpha_{m-1}.
\]

辅助结构的初等性及其规范真值约化给出：

* 每个 \(\alpha_i\) 都是 Adequate；
* 当 \(q\le p<c<m\) 时，对任意有限 \(k\)，都有
  \(R(k,\alpha_q,\alpha_p,\alpha_c)\)。

因此任意有限合法原子图，尤其每个真实山脉图 \(G(s)\)，都有初始表示。`exists_initial_representation` 所曾使用的统一真值集合可构造性输入，已由 `ambientTruth_mem_L` 实际供应。

这一步解决“从哪里取得第一组标签”。它没有直接断言任何展开后的标签更小。

## 六、真正需要反射的是一条有限 \(\Sigma_1\) 公式

### 6.1 所有被量化的集合都必须完整且规范

为了在一个较大 \(L\) 阶段内部讨论候选标签 \(a\)，必须能在公式中核验：候选域确为 \(L_a\)，语法与赋值是全集，候选满意度确为规范真值。只检查某个任意子集内部自洽，不能证明这些事实。

当前形式化完成了以下实际 \(\Sigma_1\) 证书：

| 证书 | 核验的实际对象 |
|---|---|
| `ActualStageQuery` | 候选域正好是 \(L_a\)，包括初始、后继 Def、极限并集与历史完整性 |
| `AssignmentSourceCertificate`、语法证书 | 完整有限赋值、合法公式、\(\Delta_0\)/\(\Sigma_1\) 语法与对应节点集合 |
| `ActualTowerQuery`、`ActualTruthQuery` | 完整规范混合真值塔及指定阶段的满意度集合 |
| `ActualAdequateQuery` | 实际 \(\operatorname{Adequate}(a)\)，只以 \(a,\omega,\varnothing\) 为原始参数 |
| `ActualRelationQuery` | 在序数顺序护栏下，两内部端点间的实际 \(R\) 关系 |
| `ActualEndpointRelation` | 指向当前外部顶端的实际 \(R\) 需求 |

完整性来自双向覆盖、排除多余成员以及递归唯一性。其内部存在性来自实际 Separation、Collection、有限集合运算和显式的 \(\omega\) 迭代证书；没有从“外部看来是某个内部集合的子集”直接跳到“属于当前 \(L\) 阶段”。

尤其，Adequate 的检查遍历完整的阶段、公式和赋值集合。它把每阶段的语法、节点与满意度按同一阶段编码关联起来，再准确投影出模式检查使用的数据包和字段全集。一个共同内部集合界住全部局部有限见证，剩余量词均为有界量词；前面只剩有限个存在量词。故这是字面语法上的 \(\Sigma_1\) 公式。

这里没有把当前结构自己的完整真值集合假定为其内部元素。内部证书构造的是候选的更小域；指向当前顶端的关系使用现有语言允许的命名或对角谓词。

### 6.2 有限反射定理

设有限图 \(G\) 有表示 \(f\)，切点为 \(c\)，置

\[
\alpha=f(c).
\]

假设全部现有列标签小于一个 Adequate 的顶端 \(\beta\)，并且有控制关系

\[
R(K,\theta,\alpha,\beta).
\]

另有有限多个指向顶端的需求

\[
R(k,f(q),f(p),\beta).
\]

允许性要求每个需求满足下列两种情形之一：

1. \(k<K\)；
2. \(k=K\)，根列 \(q<c\)，且 \(f(q)<\theta\)。

第二种情形的根标签是切点左侧固定参数，确实能用作当前语言的命名索引；第一种使用较低层的对角谓词。内部图边的层号可以是任意有限数，不必小于 \(K\)：其关系通过内部完整真值证书表达，不需要调用不可用的顶端谓词。

把 \(\omega\)、空集、实际用到的有限层号以及切点左侧标签作为 \(L_\alpha\) 中的固定参数。对其余有限列标签和全部证书作存在量化，合成一条 \(\Sigma_1\) 公式，要求：

* 标签是严格递增的序数元组，固定前缀与参数相等；
* 所有列满足 Adequate；
* 全部内部父边满足实际 \(R\)；
* 所有允许的顶端需求成立。

原表示在 \(L_\beta\) 中提供见证。由控制关系的实际 \(\Sigma_1\) 保持，整条公式反射到 \(L_\alpha\)。解码后得到表示 \(g\)，满足

\[
g(i)=f(i)\quad(i<c),\qquad g(i)<\alpha\quad(i<|G|),
\]

而顶端需求变为

\[
R(k,g(q),g(p),\alpha).
\]

顺序护栏的检查先于关系解释：先解码严格递增序数元组，再从各列的 Adequate 条件及 \(q\le p<c\) 推出根关系所需的 \(\eta\le a<b\) 与非空域条件。因此没有用真值一致性冒充严格的 \(R\) 关系。

这就是 `RootSemantics.actual_finiteReflection`。它现为已证明、无额外反射假设的定理。

## 七、几何复制、反射和拼接怎样给出任意复制次数的下降

设原序列最后一列为 \(x\)，活动层为 \(K\)，活动行的父边为 \(x\to y\)，坏部长度 \(L=x-y>0\)。删除末项后，复制 \(b\) 个坏部的宽度为

\[
n_b=x+bL,
\]

最后一个可复制块的起点为 \(c_b=y+bL\)，故块长始终为 \(L\)。原末项的父关系仍作为接缝所需资料保留。

从真实三类山脉复制公式证明：每追加一块，所有新图边都属于以下三类之一。

1. **原图边。** 位于已存在的有限图中。
2. **复制边。** 父、子是某条已保存源边的列平移；根也按相同规则复制，或者改为更早的一个根。后一种情况由严格更小的根标签通过 \(R\) 的索引弱化处理。轮廓提升和参考填充的相关边都在这一步逐项归类。
3. **接缝边。** 子列是新块的第一列，父和根来自已存在部分；它正对应一个已证明允许的顶端需求。

活动层使用终端的 0-Y 式父关系复制，下层使用轮廓提升与参考填充，上层使用普通复制。三个区域的真实父图及每条边的分量根都已经计算并证明。关键边界是：同控制层的接缝需求，其根严格位于控制根左边；其他非平凡需求位于较低提取层。这正是上一节语言允许性的来源。

现设当前图宽度为 \(n\)、切点为 \(c\)，表示为 \(f\)，全部标签小于旧末标签 \(\beta\)。反射得到 \(g\)，其全部标签小于 \(\alpha=f(c)\)，并保留 \(c\) 左侧前缀。拼接新的标签：

\[
h(i)=
\begin{cases}
g(i),&i<n,\\
f(c+i-n),&n\le i<n+(n-c).
\end{cases}
\]

已反射部分严格位于 \(\alpha\) 以下，追加块从旧标签 \(f(c)=\alpha\) 开始，所以整个 \(h\) 仍严格递增。两部分也都严格小于 \(\beta\)。

三类边分别由 \(g\) 的表示性质、保存源边与索引弱化、反射后的顶端需求得到验证。故 \(h\) 是追加一块后的真实图表示。

为了再次复制，仅验证当前图边还不够：下一次可能需要比当前某条边更强的旧源关系。形式化同时保留 `facts` 中的源边关系，以及 `templates` 中指向旧虚拟顶端 \(\beta\) 的关系。新追加块沿用旧标签，因此这些关系也随列平移保留下来。控制根、切点、源边和模板全部满足下一步所需的归纳不变量。

于是对任意有限 \(N\)，反复应用一块拼接，得到复制后整个有限图的表示，且**所有新列标签都严格小于原末标签 \(\beta\)**。最后利用规范重建与有限图前缀定理，将它转为实际输出 \(E_N(s)\) 的表示。

若原末项没有父项，展开直接删除末项。真实重建图是旧图的适当前缀，严格递增的原标签立即给出更小的末标签；不需要复制反射。

## 八、用序数良基归纳证明全部表达式终止

记 \(\operatorname{LastRep}(s,\beta)\) 表示：\(s\) 非空，且存在一个山脉图表示，其最后一列标签为 \(\beta\)。上一节证明：

\[
\operatorname{LastRep}(s,\beta),\quad E_N(s)\ne\varnothing
\quad\Longrightarrow\quad
\exists\gamma<\beta\;\operatorname{LastRep}(E_N(s),\gamma).
\tag{*}
\]

对序数 \(\beta\) 作良基归纳，证明更强的陈述：

\[
\forall s\quad\operatorname{LastRep}(s,\beta)
\Longrightarrow \operatorname{Acc}_{\prec}(s).
\]

给定 \(s\) 的任何一步后继 \(t\prec s\)：若 \(t\) 为空，则它没有非平凡展开后继，立即可及；若 \(t\) 非空，则由 \((*)\) 获得 \(\gamma<\beta\) 和 \(t\) 的新表示，应用归纳假设即可。于是 \(s\) 可及。

第五节为每个非空 \(s\) 供应初始表示，序数顺序本身良基，因此每个 \(s\in\mathcal E\) 均可及。这证明 \(\prec\) 良基。若一条实际展开链永远非空，每一步都是非平凡下降，与其起点可及矛盾；故任意选择复制次数的链最终为空。

**表示无需唯一，也无需可计算。** 每次展开可以选择一组新的标签，只要新末标签严格小于已有表示的末标签，以上强化归纳就成立。证明没有预先计算一个显式函数 \(\operatorname{ord}(s)\)，也没有宣称已经求出 1-Y 的精确序数记号或序型。

## 九、从展开终止到标准字典良序

仅有展开良基性一般不能推出某个另行指定的字典序良基。因此还需要实际数值展开的两个性质。

第一，所有非空输入均满足

\[
E_N(s)<_{\rm lex}s.
\]

当 \(N=0\) 或末项无父时，这是删除末项所得的真前缀；其他情形保留末项以前的全部数值，在原末项位置出现的首接缝值恰为旧末值减 1。尾部再长也不影响首次差异处的字典比较。

第二，不同复制次数给出嵌套前缀：

\[
i\le j\quad\Longrightarrow\quad
E_i(s)=E_j(s)\upharpoonright |E_i(s)|.
\]

而任何有限前缀都可以反复取 \(E_0\) 到达。因此，\(E_j(s)\) 可以经过展开到达 \(E_i(s)\)。

利用已经证明的一步展开良基性，对共同起点的可及性归纳，可得它任意两个有限展开后代必定相等，或者一个经过非空有限展开到达另一个。由每一步的字典下降，在单一起点的后代集合上有精确等价：

\[
a<_{\rm lex}b
\quad\Longleftrightarrow\quad
a\text{ 是 }b\text{ 的非平凡有限展开后代}.
\]

右侧是良基关系的传递闭包，仍然良基，故 `Descendant s` 的字典序良基；传递性和三歧性来自有限序列字典序，得到严格良序。

对标准生成集合，形式化的种子为

\[
\operatorname{seed}(n)=(1,n+1).
\]

已证明 \(E_1(\operatorname{seed}(n+1))=\operatorname{seed}(n)\)。所以任意两个种子都能放到一个较大种子的后代集合中，任意两个标准生成序列也有共同的种子起点。上一段的等价因而适用于整个 `GeneratedExpr`，得到它的字典严格良序。加入退化种子 \((1,1)\) 不扩大集合，因为它已经由 \((1,2)\) 生成。

## 十、它与“由 0-Y 推出 1-Y”的直觉有什么关系

0-Y 式终端展开是数值与父图证明的重要基础：活动终端层按相同形式复制，再向下恢复数值。但是，仅凭“顶层按 0-Y 展开”还不能推出 1-Y 良基，因为提取必须带上继承祖先结构，下层会改变高度、加入参考部分，而且每一步的顶层投影可能发生变化。

完整证明把这种紧密联系用于活动层的局部展开，同时补上三个全局环节：

1. 真实下层回填与再次规范重建相容；
2. 每条父边使用其真实分量根的标签作为关系索引，覆盖轮廓提升和参考填充；
3. 通过实际有限 \(\Sigma_1\) 反射，为任意有限复制次数重新配置全部标签，并使末标签严格下降。

因此完成的论证不是把“0-Y 已良序”直接当作一句黑箱推论，而是给出了足以控制整个 1-Y 多层展开的表示与下降证明。

## 十一、Lean 出口与核验位置

最终文件为 [ActualWellOrdering.lean](<../formalization/Concrete/OneYTruth/ActualWellOrdering.lean>)。四个无条件出口是：

| Lean 定理 | 精确结论 |
|---|---|
| `OneYTruth.WellOrdering.expansion_wellFounded` | 全部 `ZeroY.Expr` 的实际非平凡 1-Y 一步展开良基 |
| `OneYTruth.WellOrdering.expansion_chain_reaches_empty` | 任意有限复制次数选择的实际展开链最终为空 |
| `OneYTruth.WellOrdering.descendants_strictWellOrder s` | 任一起点 `s` 的全部后代按字典序严格良序 |
| `OneYTruth.WellOrdering.generated_strictWellOrder` | 标准生成表达式的字典序严格良序 |

主要中间证明可按以下顺序核对：

| 环节 | 源文件 |
|---|---|
| 单次完整提取的有限性 | [Extraction.lean](<../formalization/OneY/Extraction.lean>)、[Build.lean](<../formalization/OneY/Build.lean>) |
| 实际数值展开与重新构造相容 | [ExpansionCanonical.lean](<../formalization/OneY/ExpansionCanonical.lean>) |
| 根索引图和表示 | [Diagram.lean](<../formalization/OneY/RootIndexed/Diagram.lean>)、[Representation.lean](<../formalization/OneY/RootIndexed/Representation.lean>) |
| 实际复制几何与块归纳 | [ActualScheme.lean](<../formalization/OneY/RootIndexed/ActualScheme.lean>) |
| 规范真值、R 与 Adequate | [ExternalTower.lean](<../formalization/Concrete/OneYTruth/ExternalTower.lean>)、[RootSemantics.lean](<../formalization/Concrete/OneYTruth/RootSemantics.lean>) |
| 初始表示供给 | [InitialRepresentations.lean](<../formalization/Concrete/OneYTruth/InitialRepresentations.lean>)、[ActualTowerConstructible.lean](<../formalization/Concrete/OneYTruth/ActualTowerConstructible.lean>) |
| 规范 Adequate 检查 | [ActualAdequateQuery.lean](<../formalization/Concrete/OneYTruth/ActualAdequateQuery.lean>) |
| 完整有限公式与实际反射 | [ActualDiagramQueries.lean](<../formalization/Concrete/OneYTruth/ActualDiagramQueries.lean>)、[ActualFiniteReflection.lean](<../formalization/Concrete/OneYTruth/ActualFiniteReflection.lean>) |
| 末标签下降与可及性归纳 | [RootIndexed/ExpansionWellFounded.lean](<../formalization/OneY/RootIndexed/ExpansionWellFounded.lean>) |
| 字典序与生成性桥接 | [ExpansionOrder.lean](<../formalization/OneY/ExpansionOrder.lean>)、[Dynamics.lean](<../formalization/OneY/Dynamics.lean>) |
| 本文所用实际计算例子 | [ExpansionExamples.lean](<../formalization/OneY/ExpansionExamples.lean>) |

最终核验记录为 [总入口构建日志](one-y-truth-zfc-build.log) 与 [153 个不同声明的公理审计](../formalization/Concrete/OneYTruth-audit-output.txt)。它们确认上述实际展开与良序定理已通过内核，且没有混入 `sorry` 或新声明的公理。
