# Stacks Project 的 Lean 形式化

[English](README.md) | 简体中文

我们将 [Stacks Project](https://stacks.math.columbia.edu/) 中的数学内容整理为
**可复用的 Lean 4 数学库**。在 mathlib 的基础上，我们把共享的数学定义、构造和
辅助引理提取到 `ReasLib`，并在 `stacks_project` 中保留按章节组织的声明及其来源对应关系。

这项工作的核心是数学库的组织：让依赖相同数学基础的结果使用共同的 API，让后续
形式化工作能够直接导入相关模块，复用已有的定义和构造。我们正在持续补全证明、
完善数学接口，并审查形式化声明与原始数学内容之间的对应关系。

## 可复用的数学库

我们围绕三个相互衔接的部分组织形式化内容：

- **共享数学基础。** `ReasLib` 按数学主题组织定义、构造和辅助引理，覆盖代数、
  范畴论、拓扑和代数几何等领域。
- **模块化接口。** 将相关概念和结果整理到 Lean 命名空间及可导入模块中，
  为章节结果和后续数学库开发提供共同基础。
- **数学来源对应。** `stacks_project` 保留章节结构和已有的 Stacks tag，
  方便读者对照形式化声明与原始数学内容。

例如，环化 site 和 topos 的可复用基础位于
[`ReasLib/AlgebraicGeometry/RingedSite/`](ReasLib/AlgebraicGeometry/RingedSite/)，
章节中的具体结果则位于 [`stacks_project/`](stacks_project/)。
声明上的 `@[stacks 0DPK]` 等属性可以对应到
[Stacks Project 的 Tag 0DPK](https://stacks.math.columbia.edu/tag/0DPK)。

## 仓库结构

| 路径 | 内容 |
| --- | --- |
| [`ReasLib/`](ReasLib/) | 可复用的数学定义、构造和引理 |
| [`ReasLib.lean`](ReasLib.lean) | 数学库入口 |
| [`stacks_project/`](stacks_project/) | 按章节组织的形式化内容及来源对应关系 |
| [`lean-toolchain`](lean-toolchain) | 项目使用的 Lean 版本 |
| [`lakefile.toml`](lakefile.toml)、[`lake-manifest.json`](lake-manifest.json) | 数学库目标与依赖配置 |

项目使用 **Lean 4.32.0** 和 mathlib。参与开发时，请使用仓库中的工具链与 Lake 配置。
环境准备可参考 [Lean 安装指南](https://leanprover-community.github.io/get_started.html)
和[贡献者环境说明](CONTRIBUTING.md#contributor-setup-and-validation)。

## 项目状态

本项目已将 Stacks Project 的数学内容整理为按章节组织的 Lean 形式化源码和
可复用的数学库 `ReasLib`，包括第 1–26 章及后续章节的内容。
目前正在持续补全证明、完善共享数学接口，并审查形式化结果与原文的对应关系。

| 项目 | 数量 |
| --- | --- |
| 章节源码中的不同 Stacks tag | 17,350 |
| Lean 源码文件 | 41,072 |
| 数学声明（含定义、结构、实例和定理等） | 219,381 |
| 共享库 `ReasLib` 中的数学声明 | 144,213 |
| 证明条目 | 122,179 |
| 无显式占位符的证明条目 | 9,351 |
| 含显式占位符的待补证明条目 | 112,828 |

证明条目按 `theorem`、`lemma` 和 `example` 统计；无显式 `sorry` 或 `admit`
不等于证明及其依赖已完成验证。

### 章节覆盖

| 章节 | Lean 文件 | 不同 Stacks tag |
| --- | --- | --- |
| 1–26 | 6,178 | 5,824 |
| 27–34 | 1,800 | 1,761 |
| 35–111 | 14,441 | 9,766 |

分章数量统计的是章节目录中的源码，不包含共享库。不同章节可能引用同一个 tag。
完整的[逐章统计表](docs/chapter-statistics.tsv)和[统计说明](docs/formalization-statistics.json)
可供查阅。

## 形式化作者

- **Statement 形式化：** ReasBook team
- **证明形式化：** ReasBook team

作者信息记录在代码文件头中，并随贡献持续完善。来源与许可说明见
[ATTRIBUTION.md](ATTRIBUTION.md)。

## 参与贡献

**欢迎所有人通过 GitHub Pull Request 提交 Lean 证明。**
你可以补全一个引理、证明共享的辅助结果、改进数学库接口，或修正声明与原文之间的
对应关系。小而集中的贡献同样有价值。

数学库中仍有以 `sorry` 标记的待完成证明。你可以浏览
[`ReasLib/`](ReasLib/) 和 [`stacks_project/`](stacks_project/)，也可以从
[待补证明清单](docs/proof-debt.tsv) 中寻找切入点。清单记录的是显式占位符；
没有占位符并不代表某个结果及其依赖已经得到完整验证。

1. 选择一个声明，阅读其对应的原始数学内容。
2. 在自己的 fork 中创建分支，补全证明或改进模块。
3. 保留来源 tag 和原命题的数学含义，将可共享的辅助引理整理到数学库中。
4. 提交 **Pull Request**，注明文件、声明名称、Stacks tag 或来源章节，
   并简要说明证明思路及验证结果。

详细流程见 [CONTRIBUTING.md](CONTRIBUTING.md)。较大的工作可以先通过 issue 与其他
贡献者协调。审查会关注数学来源对应关系和证明依赖；新增公理或削弱命题不能代替证明。

## 许可证与致谢

项目代码采用 [Apache-2.0](LICENSE)。第三方材料保留原有许可，Stacks Project 的
原始文本仍遵循 GNU Free Documentation License。详见 [ATTRIBUTION.md](ATTRIBUTION.md)。

感谢 Stacks Project 的作者与贡献者、Lean 和 mathlib 社区，以及参与这项形式化工作的
所有贡献者。本项目是一项独立的形式化工作。
