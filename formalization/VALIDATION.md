# 验证记录

以下路径均相对于本仓库。

## 2026-09-12：自包含源码发布验证

完整构建所需的 11 个依赖源码仓库现已直接随附在 `vendor/`，对应 12 个外部 Lake 包；无需子模块、额外克隆或独立依赖仓库的 Git 元数据。必要构建清单中的 44 条依赖均指向仓库内部。依赖来源、固定版本、许可证与配置改动见 [vendor 说明](../vendor/README.md)。

### 从源码开始的完整构建

在 Windows、Lean 4.33.1 下，使用独立的源码目录运行当前构建脚本。开始时项目与依赖中的证明 `.olean` 数量为 **0**，只使用已安装的官方编译器；没有复制旧工程的证明编译产物，也没有下载外部构建缓存。Lake 配置文件产生的元数据不计为证明产物。

构建中途为调整并发度而停止、续建，沿用的产物全部由该目录本次编译生成。这不是一次不间断的单进程构建。8 线程阶段曾有四个模块报告读取 `.olean` 或 `.olean.private` 失败；相应文件均存在且可读取，未修改源码，以默认单线程续建后四个模块及其后续目标全部通过。未据此认定具体底层错误原因，发布脚本保留单线程默认值。

最终执行 `./formalization/Concrete/build.ps1 -LeanBin <Lean-4.33.1/bin>`，结果为：

```text
Build completed successfully (2015 jobs).
ZeroYConcrete: all 14 declarations passed the axiom whitelist audit.
OneYTruth: all 153 declarations passed the axiom whitelist audit.
```

脚本退出码为 0，构建包含 `ZeroYConcrete` 和 `OneYTruth`。公理审计逐项核对声明名称、数量、唯一性及白名单，只允许 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义公理。此次依赖打包没有修改主项目的证明定义或定理；BMS 随附源码保留之前已记录的两份性能补丁。

完成后又实际运行核心构建脚本，通过 191 项任务，并核对核心 `Audit.lean` 的 43 个不同声明及同一公理白名单。随后再次运行具体工程的默认构建，2015 项任务及 14 / 153 项审计再次通过；这次为复用本次产物的增量验证，确认生成缓存存在时可以重复运行。上述补充检查合计约 198 秒，不是完整源码重建的总耗时。

本次生成的审计输出与此前公开输出逐字节相同：

| 输出 | SHA256 |
| --- | --- |
| [0-Y 具体模型审计](Concrete/audit-output.txt) | `5f0b7cd4a11bb47037df253aa0fd7d22ded1b3f05c22454180d3b0fb2106c889` |
| [1-Y 审计](Concrete/OneYTruth-audit-output.txt) | `26ab1b830725b8e73c9cac3eccb5211e92ef0d44fae56d866845741e61466fe9` |

### 源码核验与 ZIP 检查

- 全部 **11,363 个依赖文件的 SHA256** 核验通过；缺失、篡改、未登记源码及越界路径的检查也已验证。源码清单自身 SHA256 为 `cbdbbdc3758ce97f0258303891f93ab881d4b166f614bd190435420e11c44c54`。
- 实际构建发现 ProofWidgets 会生成 `widget/package-lock.json.hash`。核验脚本已允许这一准确路径的生成缓存，同时继续核验原有 `.trace` 文件并拒绝其他未登记源码；重复核验无需删除生成缓存。
- 将暂存的发布文件导出为约 41 MB 的 ZIP，解包得到 11,870 个文件，无 `.git`、`.lake`、子模块或符号链接；11,363 个依赖哈希再次全部通过。
- 在该解包目录中清空 `LEAN_PATH`，让 `PATH` 只含官方 Lean 的 `bin`，确认 Git 不可用后，离线依赖核验及 `lake --keep-toolchain --no-cache env lean --version` 均成功，报告 Lean 4.33.1。ZIP 中的构建配置与证明源码与上述完整构建相同；此后只更新说明和验证记录。**ZIP 检查是依赖加载测试，没有在解包目录再进行第二轮完整编译。**

验证平台为 Windows。其他操作系统的完整源码构建尚未实际验证。以下保留先前版本的历史记录，旧版依赖恢复流程不再是当前发布方式。

## 2026-09-10：1-Y 与发布验证（历史记录）

**1-Y 良序证明已完成 Lean 4 形式化，并通过其依赖类型论内核核验。** 最终入口 [OneYTruth/ActualWellOrdering.lean](Concrete/OneYTruth/ActualWellOrdering.lean) 包含实际展开良基性、标准生成集字典序良序、固定起点后代集字典序良序及任意复制次数轨迹终止。最终定理不要求调用者另外提供有限反射、初始表示或数值重建假设。

另已有[通常数学意义的 ZFC 证明](../research/1y-zfc-well-ordering-proof.md)。**尚未完成的是将完整证明迁移到一阶 ZFC 的形式化与机器核验**，包括目标及整条推导在一阶 ZFC 演算中的编码与验证。以下记录核验的是已经完成的 Lean 4 证明；ZFC 数学论证和后续形式化迁移的状态与之分别说明。

集合满意度替换后的 `lake build OneYTruth` 通过 1814 项任务，记录见 [构建日志](../research/one-y-truth-zfc-build.log)。发布准备随后实际运行当前两个构建脚本：

```powershell
./formalization/build.ps1
./formalization/Concrete/build.ps1
```

- 核心脚本通过 191 项构建任务，约 1.6 秒。
- 具体工程的默认 `All` 目标同时构建 `ZeroYConcrete` 和 `OneYTruth`，通过 2015 项任务。没有重新编译证明模块；日志记录 0 条 `Built`、295 条 `Replayed`，其余任务同样复用现有产物。
- 随后自动审计 0-Y 的 14 个不同声明与 1-Y 的 153 个不同声明，退出码均为 0。逐项检查名称、数量、重复项及公理白名单，只允许 `propext`、`Classical.choice`、`Quot.sound`。
- 默认具体工程构建加两套审计合计约 93 秒。输出见 [发布增量构建](../research/one-y-release-build.log)、[0-Y 审计](Concrete/audit-output.txt)、[1-Y 审计](Concrete/OneYTruth-audit-output.txt)。仅验证 1-Y 可用 `./formalization/Concrete/build.ps1 -Target OneYTruth`。

早期 1-Y 审计日志的 148 项、153 项是打印次数，分别包含 147、152 个不同声明；重复项是 `assignmentCode_injective`。当前清单将第二次打印替换为集合语义翻译定理 `AuxiliaryCode.realize_translate_set`，并已核对 153 个名称互异。历史输出保留原样，当前结果以以上发布审计为准。

本次为增量验证，没有删除缓存、重新下载全部依赖或从零构建。全部公开 Markdown 文件的本地链接均已检查，目标均纳入发布清单；项目内 Lean 导入未发现缺失源码。下文保留 0-Y 的先前构建及依赖恢复记录。

## 编译环境

```text
Lean (version 4.33.1, x86_64-w64-windows-gnu,
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

上游 BMS 基线提交：`bae7e3d741f24a56d80da9b99c1345562cd10c2d`。核心没有新增外部库依赖。具体模型接入另有两个证明脚本性能补丁：[StageStableBetweenFormula](Concrete/patches/stage-stable-between-performance.patch) 和 [StageStableToUniverseFormula](Concrete/patches/stage-stable-to-universe-performance.patch)。两者将证明方向拆为独立辅助定理，先对任意公式证明外层语义桥，再用等价传递装配公开定理，并同步执行内核检查；第一个文件还删除两条递归化简，使用小元组等式作显式传输。这些改动避免比较大型语义表达式时的内存膨胀。公开定理陈述、公式定义和假设均未改变，没有关闭或跳过任何验证。准确补丁、基线提交和改动前后 SHA256 见 [具体模型说明](Concrete/README.md)；原始源码可从基线提交恢复。

## 已实际完成的核心合并检查

工作区根目录运行：

```powershell
./formalization/build.ps1
```

结果：`Build completed successfully (66 jobs).`，无错误、无警告。入口已合并完整往返、原始及规范矩阵可逆充要条件、全域序同构、I/S 展开保持、独立算法展开交换、标准生成集及任意固定起点后代集对应，以及全部 Wiki 桥接和终止定理。

`ZeroY.Dynamics.Termination` 和 `ZeroY.Wiki.Termination` 提供任意合法起点、任意指标序列的实际迭代最终到达空式。核心保留显式的 `RepresentationDescentSystem frame` 参数；下述具体工程已实际构造并代入该系统，完成无需额外模型参数的结论。

## 实际公理依赖审计

在 `formalization` 中运行 `lake env lean Audit.lean`，退出码 0，检查 43 个指定声明。可复现清单位于 [Audit.lean](Audit.lean)，实际输出见 [audit-output.txt](audit-output.txt)。

其中包括：

```text
ZeroY.decode_encode
ZeroY.encode_lt_iff
ZeroY.roundTrip_iff_structural
ZeroY.reversibleOrderIso
ZeroY.BMS.structural_expand
ZeroY.encode_expandY
ZeroY.decode_expand
ZeroY.encode_seed
ZeroY.generatedOrderIso
ZeroY.descendantOrderIso
ZeroY.yStep_wellFounded
ZeroY.no_infinite_yStep_chain
ZeroY.yGenerated_strictWellOrder
ZeroY.yDescendants_strictWellOrder
```

这些声明的实际依赖均为 `propext`、`Classical.choice`、`Quot.sound`。其余基础声明只依赖这个集合的子集；两个通用传输声明没有公理依赖。全部 43 项均无 `sorryAx`、原生计算公理或自定义公理。

静态搜索 `formalization/ZeroY/**/*.lean` 的 `sorry`、`admit`、`axiom` 也未发现声明或占位。静态搜索本身不能代替上面的内核编译及公理依赖检查。

## 已实际完成的具体模型接入

在 `formalization/Concrete` 中运行：

```powershell
./build.ps1
```

完整源码构建的实际结果为 `Build completed successfully (1576 jobs).`。[Concrete/ZeroYConcrete.lean](Concrete/ZeroYConcrete.lean) 的 13 个最终定理均已编译通过，包括 BMS 与 0-Y 的展开良基性、标准集及任意固定起点后代集的字典序良序性，以及两种 0-Y 约定下任意指标轨迹到达空式的终止性。它们不要求调用者提供降界系统。上游原有的未使用变量和战术风格警告保留，构建无错误。

随后实际运行 `./build.ps1 -AuditOnly`，退出码 0。脚本核对 [Concrete/Audit.lean](Concrete/Audit.lean) 的 14 项名称，无缺漏或重复，并逐项检查公理白名单。具体模型 `reflectionData_l` 自身及上述 13 个最终定理的依赖均恰为 `propext`、`Classical.choice`、`Quot.sound`。实际输出保存在 [Concrete/audit-output.txt](Concrete/audit-output.txt)，SHA256 为 `5f0b7cd4a11bb47037df253aa0fd7d22ded1b3f05c22454180d3b0fb2106c889`。

核心与具体工程合计 **57 项关键声明公理审计通过**，无 `sorryAx`、原生计算公理或自定义公理。最终模型已实际构造和检查，不再遗留模型存在性假设。

构造宇宙依赖固定于 `7f5a7d03d63d9769172f17350bbe8303996e5b53`，mathlib 固定于 `eba3d887fc52c98627f4b81507c0efc3096e91b9`。后两者原始工具链是 `4.33.0-rc1`；本次所需 Lean 证明源码全部使用 `4.33.1` 重建，没有复用其他版本的 `.olean`。完整依赖锁定、两个性能补丁的哈希与构建记录见 [dependencies-lock.json](Concrete/dependencies-lock.json)。

## 辅助样例（非证明前提）

[Examples.lean](Examples.lean) 的 `by decide` 检查覆盖空式、零指标、跨块边界、不可逆反例和共同尾零行。交付规格是独立定义的数学算法；这些样例和外部程序均不是全称定理的前提。

## 2026-09-10：旧版发布与恢复脚本检查（历史记录）

本节描述旧版发布方式。当前版本已将依赖源码直接放入 `vendor/`，`prepare-dependencies.ps1` 已改为离线逐文件核验；以下恢复脚本测试不代表当前脚本的行为。

发布文件包括数学稿、Lean 源码、Lake 配置、锁定记录、构建与恢复脚本、两份性能补丁及最终公理审计输出。依赖源码、运行时、构建缓存、论文副本和本机诊断材料不随仓库提交。`.gitattributes` 保留补丁和审计输出的原始字节，避免 Git 换行转换改变其 SHA256。

2026-09-10，在 Windows / PowerShell 7 下实际检查 [prepare-dependencies.ps1](prepare-dependencies.ps1)：

- 全量 `-CheckOnly` 通过：11 项依赖、两个 Lake 路径清单、三个真实 Git 提交、八份缓存源码归档的 SHA256 及两份补丁对应的源码哈希。
- 在已有正确依赖上执行默认恢复模式通过，验证重复执行无需重新下载或改写已应用的补丁。
- 在隔离目录使用锁定的 LeanSearchClient 缓存归档，实际经过归档列表核验、解包、移动和临时目录清理，随后 `-CheckOnly` 通过。
- 从本地真实 Git 对象克隆干净 BMS 基线并检出固定提交，实际重新应用两份补丁；改动后源码哈希和随后 `-CheckOnly` 均通过。

这组测试验证恢复脚本的本地检查、解包与补丁路径；没有重新进行一轮“全新网络获取全部依赖后完整构建”的测试。前文的 1576 项源码构建与 57 项审计是已实际完成的数学证明验证。恢复脚本检查提交、配置、缓存归档和指定补丁的身份，不逐字验证所有已经解包的依赖文件。
