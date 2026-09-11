# 具体良序模型

**1-Y 良序证明已完成 Lean 4 形式化，并通过其依赖类型论内核核验。** `OneYTruth/ActualWellOrdering.lean` 给出实际展开良基性、标准生成集良序、任一起点后代集良序及任意复制次数的轨迹终止定理。实际完整真值塔、初始表示和有限反射均由已证明的定理供应，最终出口没有这些未证前提。公理审计仅含 Lean 标准的 `propext`、`Classical.choice`、`Quot.sound`。实际展开证明见 [1-Y 证明说明](../../research/1y-well-ordering-proof.md)。

2026-09-10：另已写出[通常数学意义的 ZFC 证明](../../research/1y-zfc-well-ordering-proof.md)，将类语义改写为集合满意度，并把全部标签统一界在可数序数以下。代码中的辅助 Separation 已改用固定集合满意度查询。ZFC 结论依靠这份独立的集合论论证，不由 Lean 公理打印自动推出。

**尚未完成的是将完整证明迁移到一阶 ZFC 的形式化与机器核验。** 这需要将目标及其推导在一阶 ZFC 演算中完整编码和验证；当前已经完成的是 Lean 4 中的良序证明及内核核验。最弱理论或 Z₃ 上界仍未确定。

1-Y 的完整入口为 `OneYTruth.lean`；`./build.ps1 -Target OneYTruth` 同时运行其增量构建与公理白名单审计。脚本默认 `-Target All`，检查 0-Y 与 1-Y；下方最终定理表介绍 0-Y 部分，1-Y 四个出口见上方链接。

1-Y 早期最终入口通过 1810 项构建；当时审计输出 148 项，含一项重复打印，覆盖 147 个不同声明。历史记录见 [构建日志](../../research/one-y-truth-final-build.log) 与 [审计日志](../../research/one-y-truth-final-audit.log)。

集合满意度替换后的完整入口通过 1814 项构建，见[构建记录](../../research/one-y-truth-zfc-build.log)。发布审计清单已去重，并补入集合语义翻译定理；当前 153 个不同声明的结果见 [OneYTruth-audit-output.txt](OneYTruth-audit-output.txt)。

2026-09-12，自包含源码发布的联合目标 `ZeroYConcrete OneYTruth` 构建通过 2015 项任务，14 项与 153 项公理审计均通过。本次从无证明编译产物的目录开始，经过续建完成；默认单线程运行成功。完整过程和无 Git 的 ZIP 检查见 [验证记录](../VALIDATION.md)。

`ZeroYConcrete.lean` 把上游构造宇宙证明生成的
`reflectionData_l.wellOrderingModel.representationDescentSystem`
代入主工程的良序、无无限下降链及任意选指标轨迹终止定理。这里的最终定理不要求调用者提供降界系统。

## 工具链与依赖

实际编译统一使用 Lean **4.33.1**。上游 constructible-universe 与其锁定的
mathlib 源码声明的是 `4.33.0-rc1`；因此本目录使用所需依赖的源码构建，
不使用该候选版本的 `.olean` 缓存。`dependencies-lock.json` 保存各依赖的
准确提交、源码归档 SHA256、来源和本地路径。

完整依赖源码随仓库放在 `../../vendor/`，无需另外克隆 BMS 或任何其他源码仓库。`lakefile` 与 `lake-manifest.json` 的构建依赖全部使用仓库内相对路径；依赖自身的 Lake 配置也已改为本地路径，并取消 mathlib 自动下载缓存的更新钩子。源码中的 Lean 证明定义和定理没有因此改变。

`../prepare-dependencies.ps1` 现在只在本地核验 `vendor/source-manifest.json` 中的逐文件 SHA256，以及两个项目的本地路径清单。没有下载、解压、`git apply` 或独立 Git HEAD 要求；GitHub ZIP 解压目录同样适用。

桥接库基于 `bae7e3d741f24a56d80da9b99c1345562cd10c2d`，另附两个文件的
本地证明脚本性能补丁。`StageStableBetweenFormula.lean` 使用同步内核检查，
把原证明的两个方向分成独立的私有定理；删除两条递归 `simp only`，
对末尾赋值使用小元组等式的显式传输；载体与存在量词的语义转换先针对
任意公式证明，再用传递性装配公开结论。`StageStableToUniverseFormula.lean`
采用同样的同步检查、方向拆分和通用语义装配，保留其原有两个方向的证明体。
公开定理陈述、公式定义、前提及公理不变。
原始运行的单进程提交内存超过 18GB，超出本机物理内存而严重换页。
准确 diff 及改动前后 SHA256 保存在 `patches/`，
`dependencies-lock.json` 也记录了此补丁；原始源码可由基线提交恢复。
本机的原文件字节备份不发布。修改后的证明须由本机 Lean 重新检查。
随附 BMS 源码已应用这两份补丁，文件哈希纳入本地源码清单；构建时不再应用补丁。补丁文件及其基线记录仍保留供复核。
同步诊断确认两个方向通过内核后，原公开包装仍会消耗大量内存；
把该包装改为通用公式上的语义引理后，完整源文件正常退出。
这不是逐战术性能剖析；最终结果以完整 Lake 构建和下面的公理审计为准。

## 编译与审计

下载或克隆后，先按 [仓库根目录说明](../../README.md) 安装 Lean 4.33.1。全部锁定依赖源码已随仓库提交，构建脚本会自动进行本地核验。也可在本目录单独运行 `../prepare-dependencies.ps1 -CheckOnly`。

在本目录的 PowerShell 终端执行：

```powershell
./build.ps1
```

脚本默认增量构建 `ZeroYConcrete` 和 `OneYTruth`，再分别运行 `Audit.lean` 的 14 项审计与 `OneYTruthAudit.lean` 的 153 项审计。逐项核对名称、数量、重复项及公理白名单；只允许 `propext`、`Classical.choice`、`Quot.sound`。两份输出分别保存在 `audit-output.txt` 和 `OneYTruth-audit-output.txt`。

可用 `-Target ZeroYConcrete` 或 `-Target OneYTruth` 单独选择；`-AuditOnly` 跳过构建只执行所选审计。`--no-cache` 禁用外部构建缓存，不会删除当前本地 `.olean`，也不意味着每次从零编译。

在 VS Code 中检查这组具体模型定理时，使用“打开文件夹”打开本目录
`formalization/Concrete`，再打开 `OneYTruth/ActualWellOrdering.lean` 或 `ZeroYConcrete.lean`。
这样 Lean 扩展会使用本目录的工具链声明、Lake 配置与完整依赖路径。
仅打开上一层 `formalization` 时，主工程的依赖环境不包含构造宇宙桥接库。

`LEAN_NUM_THREADS` 只控制当前进程及子进程的并行度，避免源码构建占用过多资源。
脚本支持 `-LeanBin` 指定编译器，也可使用便携工具链或 PATH 中的 Lean 4.33.1。脚本默认使用 1 个线程：本机约 16GB 内存，末段两个大型反射模块同时编译会造成
严重换页；串行编译更稳妥。内存足够的机器可显式传入 `-Threads 6`。
本机构建日志按目标保存在 `.lake/build-source.log`、`.lake/OneYTruth-build-source.log` 或 `.lake/all-build-source.log`，不提交到仓库。`Audit.lean` 检查具体模型本身和
13 个最终定理的实际公理依赖；应在总构建成功后运行。

## 最终定理

所有名称位于 `ZeroY.Concrete` 命名空间：

| 对象 | 定理 |
| --- | --- |
| 任意合法 BMS 的展开关系 | `bms_step_wellFounded` |
| 任意 BMS 根的后代字典序 | `bms_descendants_strictWellOrder` |
| BMS 标准生成集字典序 | `bms_generated_strictWellOrder` |
| 独立 0-Y 展开关系 | `y_step_wellFounded` |
| 0-Y 标准生成集字典序 | `y_generated_strictWellOrder` |
| 任意合法 0-Y 根的后代字典序 | `y_descendants_strictWellOrder` |
| 0-Y 无无限展开链 | `no_infinite_y_step_chain` |
| 0-Y 任意选指标轨迹终止于空式 | `y_trajectory_terminates` |
| Wiki 0-Y 展开关系 | `wiki_step_wellFounded` |
| Wiki 标准生成集字典序 | `wiki_generated_strictWellOrder` |
| 任意合法 Wiki 根的后代字典序 | `wiki_descendants_strictWellOrder` |
| Wiki 无无限展开链 | `no_infinite_wiki_step_chain` |
| Wiki 任意选指标轨迹终止于空式 | `wiki_trajectory_terminates` |

“任意根的后代”允许根本身不是标准式；良序断言的范围是固定该根以后由有限次展开
产生的表达式集合，并不把所有合法有限序列的通常字典序误称为良序。

## 实际验证记录

2026 年 9 月 10 日，使用本工程 Lean **4.33.1** 从锁定源码完成构建：
`Build completed successfully (1576 jobs).` 具体模型 `reflectionData_l` 和
`ZeroYConcrete.lean` 中的全部 13 个最终定理均已实际编译通过。

随后 `./build.ps1 -AuditOnly` 正常退出。**14 项公理审计全部通过**，
每项依赖恰为 `propext`、`Classical.choice`、`Quot.sound`，无额外公理。
完整输出见 `audit-output.txt`；没有使用跳过内核检查、`sorry` 或伪造缓存。

实际构建日志记录：两个经性能优化的公式模块分别用时 **15 秒、14 秒**，
`ConstructibleStabilityFormulaData` 与 `FinalAssembly` 各 **14 秒**，
`ZeroYConcrete` **21 秒**。上游原有的未使用变量和战术风格警告保留，构建无错误。
本机累计日志保留早期失败、诊断与最终成功，应以最后一次结果为准；仓库公开保留最终审计输出和依赖锁中的验证记录。
