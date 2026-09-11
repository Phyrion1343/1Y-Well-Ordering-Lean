# 随附源码依赖

这里包含主项目完整构建需要的 11 个源码仓库（12 个外部 Lake 包）。BMS 仓库同时提供 YesMetaZFC 与 ConstructibleBridge。下载本仓库即可取得这些文件，无需子模块或额外克隆。

- [第三方来源与许可](THIRD-PARTY-NOTICES.md)
- [上游版本与构建配置差异](source-provenance.json)
- [逐文件 SHA256](source-manifest.json)
- [主工程依赖锁与两份原有 BMS 补丁记录](../formalization/Concrete/dependencies-lock.json)

Lean 编译器不是本目录的一部分。安装 Lean 4.33.1 后，源码构建只使用本仓库的文件和该工具链。依赖原来的 `lean-toolchain` 文件保留其历史版本；主工程统一用 4.33.1 编译，不使用 rc1 的编译缓存。

相对于锁定上游，依赖的 Lake 配置和 manifest 改为仓库内相对路径，mathlib 自动下载缓存的更新钩子已取消。BMS 保留之前通过检查的两份证明性能补丁。其余 Lean 证明源码未改写。上游归档中的辅助脚本符号链接以其目标文件内容随附，适配 Windows ZIP 解压；这些辅助脚本不参与本项目的证明构建。

各上游原有文档、测试或辅助工具也一并保留，其中独立开发工具可能描述其他依赖；它们不是主工程的构建目标。主工程所需的完整依赖闭包由 `formalization/Concrete/lake-manifest.json` 固定。

ProofWidgets 原包自带的 23 个 JavaScript 文件、`widget/js/lake.trace` 及其源码输入保留，用于满足上游 Lake 构建规则。这些网页部件不是 Lean 证明产物；本仓库不包含 `.olean` 或 `.lake` 编译缓存。

在根目录运行 `./formalization/prepare-dependencies.ps1 -CheckOnly` 可离线核验文件。该清单用于检测意外缺失或改动，不是第三方签名。若有意修改依赖，应重新审查来源、更新清单并重新构建。

构建生成的 `.lake/` 目录及 ProofWidgets 的 `widget/package-lock.json.hash` 不属于随附源码，核验脚本允许它们存在，重复构建无需删除这些缓存。
