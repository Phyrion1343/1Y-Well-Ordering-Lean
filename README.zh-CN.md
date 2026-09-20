# 0-Y / BMS 与 1-Y：展开、良序性及 Lean 形式化

[English](README.md) | **简体中文**

本项目包含 0-Y 与 BM4（Bashicu Matrix System）的对应、良序性证明，以及实际 1-Y 展开的良基性与标准生成集良序证明。Lean 工具链固定为 4.33.1；展开算法独立定义，HTML 展开器用于展示和实验。

## 1-Y 的已证明结论

- 任意首项为 1 的有限正整数序列，无论逐步选择什么有限复制次数，实际 1-Y 展开最终到达空序列。
- 从标准种子 `(1,m)`、`m≥2` 生成的序列集合按字典序良序；任意固定起点的后代集也按字典序良序。
- 提取保留祖先关系；形式化包括轮廓提升、参考填充及完整数值重建。

**1-Y 的实际展开良基性与标准生成集良序性已在 Lean 4 类型论中完成形式化证明，并通过内核核验。** 仓库另附通常数学意义的 ZFC 论证；相应证明向一阶 ZFC 演算的完整形式化迁移与机器核验尚未完成。

最终四个无参数 Lean 定理位于 [ActualWellOrdering.lean](formalization/Concrete/OneYTruth/ActualWellOrdering.lean)。[实际展开证明](research/1y-well-ordering-proof.md)解释形式化结构，[ZFC 数学论证](research/1y-zfc-well-ordering-proof.md)给出集合论证明。

2026-09-12，使用随附依赖源码的 0-Y 与 1-Y 联合构建通过 2015 项任务；0-Y 的 14 项及 1-Y 的 153 项公理审计均通过，仅使用 `propext`、`Classical.choice`、`Quot.sound` 的子集。见[验证记录](formalization/VALIDATION.md)及[1-Y 审计输出](formalization/Concrete/OneYTruth-audit-output.txt)。本次从没有证明编译产物的目录开始，经过续建完成；具体过程与 ZIP 检查分别记录在验证说明中。

[离线 1-Y 展开器](1-Y展开器.html)可直接用浏览器打开；[算法与界面说明](y1/README.md)记录规则、计算预算和测试方法。

## 0-Y / BMS 的已证明结论

- 对所有合法 0-Y 表达式，先编码再解码恢复原式。
- BMS 矩阵可逆，当且仅当满足深度正规性与阻挡条件 S。矩阵的共同尾零行视为同一表示。
- 全部合法 0-Y 式与全部可逆 BMS 矩阵序同构，包括非标准式；编码还保持并反映展开路径。
- 标准生成集以及任意固定合法起点的展开后代集按字典序良序。
- 从任意合法起点出发，无论逐步如何选择自然数指标，展开最终到达空式。
- 完整坏部与 Wiki 有限端点两种展开约定的可达闭包相同；两者都有上述良序性和终止性。

**全体合法表达式的字典序不良基。** 例如 `(1,2) > (1,1,2) > (1,1,1,2) > …`。这一反例也已形式化；良序结论的范围是标准生成集或固定起点的后代集。

## 0-Y / BMS 阅读入口

- [完整数学证明](0Y-BMS-equivalence-proof.md)：定义、可逆充要条件及普通数学论证。
- [形式化说明](formalization/README.md)：各结论对应的 Lean 声明。
- [最终具体模型定理](formalization/Concrete/ZeroYConcrete.lean)：13 个最终定理，使用已构造的模型，无需调用者额外提供降界系统。
- [实际验证记录](formalization/VALIDATION.md)：构建结果、公理审计和依赖说明。
- [上游接口与非标准推广审计](research/formalization-bms-interface-audit.md)。

2026-09-10，核心构建通过 66 个任务，包含具体模型的完整构建通过 1576 个任务；合计 57 项关键声明的公理依赖审计通过，仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或自定义公理。57 项包含具体模型和辅助定义，不是 57 个独立数学定理。

## 构建：无需另外克隆依赖仓库

本仓库的 `vendor/` 已直接包含完整构建所需的 **11 个依赖源码仓库**，包括 BMS 良序形式化、构造宇宙库、mathlib 及其传递依赖。它们是普通文件，不是 Git 子模块；使用 **Download ZIP** 解压也可以构建。源码版本仍按 [依赖锁](formalization/Concrete/dependencies-lock.json) 固定，逐文件 SHA256 见 [源码清单](vendor/source-manifest.json)。

仍需安装 **Lean 4.33.1** 编译器。已有该版本的 Lean / elan 时，可以直接使用下面的构建命令；Windows 用户也可先在仓库根目录运行官方便携工具链安装脚本（此安装步骤需要联网，以及 `curl.exe`、`tar.exe`）：

```powershell
./formalization/prepare-toolchain.ps1
```

在仓库根目录的 PowerShell 终端执行：

```powershell
./formalization/Concrete/build.ps1
```

该命令先在本地核验随附源码，再构建 0-Y 与 1-Y 的具体证明，最后分别执行 14 项、153 项公理白名单审计。**依赖验证和源码构建不需要联网，也不要求任何依赖目录带有 `.git`。** 只验证 1-Y 可用：

```powershell
./formalization/Concrete/build.ps1 -Target OneYTruth
```

脚本可使用仓库内的便携 Lean、PATH 中的 Lean，或用 `-LeanBin "你的 Lean 4.33.1/bin 路径"` 明确指定。默认单线程；首次从源码构建需要较多时间和内存，后续构建会复用本地产物。

只核验依赖源码、构建核心库或检查核心 0-Y 的 43 项公理审计时：

```powershell
./formalization/prepare-dependencies.ps1 -CheckOnly
./formalization/build.ps1
# 在 formalization 目录中，用 Lean 4.33.1 的 lake 执行：
lake --keep-toolchain --no-cache env lean Audit.lean
```

不使用 PowerShell 时，安装 Lean 4.33.1 后可在 `formalization/Concrete` 目录直接执行：

```sh
lake --keep-toolchain --no-cache build ZeroYConcrete OneYTruth
lake --keep-toolchain env lean Audit.lean
lake --keep-toolchain env lean OneYTruthAudit.lean
```

这组命令会输出公理依赖；PowerShell 构建脚本另外自动检查名称、数量和公理白名单。当前完整构建验证平台为 Windows；其他系统的完整构建尚未验证。

在 VS Code 中打开 `formalization/Concrete` 文件夹，再打开 `OneYTruth/ActualWellOrdering.lean` 或 `ZeroYConcrete.lean`。使用便携运行时和 elan 的 Windows 用户，可在仓库根目录登记工具链：

```powershell
elan toolchain link leanprover/lean4:v4.33.1 ./.tools/lean-4.33.1-windows
```

依赖已经固定，无需运行 `lake update`。具体构建与核验记录见 [VALIDATION.md](formalization/VALIDATION.md)。第三方来源、许可证和本地构建配置改动见 [vendor/README.md](vendor/README.md)。

## 上游工作

良序模型复用 [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) 的构造宇宙桥接，固定于 `bae7e3d741f24a56d80da9b99c1345562cd10c2d`，并附有两个证明性能补丁。具体模型的其他依赖包括 constructible-universe 与 mathlib；源码随附在 `vendor/`，准确来源和提交均见锁定记录。

数学背景参见 Rachel Hunter 的 [Well-Orderedness of the Bashicu Matrix System](https://arxiv.org/abs/2307.04606) 以及 [Googology Wiki 的 0-Y 定义](https://wiki.googology.top/index.php/0-Y)。外部参考 HTML、依赖编译缓存和本机诊断材料不包含在发布文件中。

本项目自身保留既有的 [Apache-2.0 许可证](LICENSE)；`vendor/` 内第三方文件按其各自的许可与来源说明提供，详见 [第三方说明](vendor/THIRD-PARTY-NOTICES.md)。
