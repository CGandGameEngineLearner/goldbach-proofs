---
name: goldbach-research-tasks
description: 为哥德巴赫研究台及其并列问题设计或调整研究路线，拆解开放命题，编写中英文 Lean 任务清单，验证领取流程并发布。适用于维护者更新任务台；参与者领取已有引理时使用站点参与指南。
---

# 研究路线与命题发布

## 逐题拆解与批量发布接口 v1

所有问题共用[变更集 JSON Schema](../../../research/schema/change-set.v1.json)；每次拆解选择一个研究台、一条父命题。参照[次弧拆解示例](../../../research/schema/example-minor-split.json)，示例供校验，不加入任务队列。

1. **读取**：从研究台快照取得父题 ID、冻结声明和基线 Git SHA。对原声明 UTF-8 字节计算 SHA-256。读取父题、已完成输入和在途任务，先查重。
2. **拆解**：将数学家的意图写入 `motivation`。每条子题给出独立 Lean 声明、显式前提、中英文解释、证明提示、所属路线、来源和依赖 ID。用 `links` 指向下游：`input` 提供必要步骤或可复用输入，`exploration` 是探索，`sufficient_reduction` 要列全输入并提供组合引理 `bridge`。检查组合引理的类型确实把这些输入推到父题。证明状态始终读取权威流水线裁决。
3. **校验**：先用 Draft 2020-12 验证 JSON 结构，再验证父题哈希、ID 唯一性、引用在本台存在、路线存在、依赖无环和双语语义。服务端从 ID 派生固定文件名与模块名；v1 新题使用 Mathlib 并遵循该台的 program/role 规则。新路线或新增允许导入项需要扩展协议；v1 的 `route_note` 更新父题对应路线的双语说明。仅调整说明时允许空任务列表。最后运行仓库目录测试和固定版本 Lean。
4. **交付变更 PR**：将变更集落实到对应目录，在功能分支提交并推送。用 PR 正文记录父题、数学动机、新增命题、依赖关系、声明变化和待解决输入。把 PR 链接交给 lifesize 审核；不代替管理员合并。网站部署器读取 GitHub 的合并身份和 main 上对应 SHA 的 CI 结果。变更集是 skill 的逐题交换格式；发布入口是 GitHub PR。

## 定位缺口

从仓库根目录运行命令。用 `git fetch origin main` 核对研究基线，保留其他维护者的工作树改动。查询主站 `/api/status` 或分站 `/problems/<slug>/api/status`，按 `gaps[].proved` 查看已证与开放命题。结合 `desk.assignments` 查看在途任务。记录取样时间、目标 ID、冻结声明和已经可复用的结果。用户只要方案时，到路线建议为止。

读父命题的 Lean 原文，逐项核对量词、参数范围、显式假设和最终结论。给每个子题说明它向下一步提供哪个估计、恒等式或构造。把容易并行的输入、组合输入的归约、仍然困难的目标分别标明。几个估计需要同时成立时，统一尺度、权重、阈值和误差预算。例如可将二次素因子中段质量分为两个互斥带，证明分割恒等式，分别研究一个最终一致上界和一个无界多尺度上界，最后证明它们可以在同一尺度合并。

调整方向时在路线里记录目前最缺的输入。借用论文或上游 Lean 工程时，给出原文或固定提交中的具体声明，并区分直接可调用的结论和借用的证明方法。涉及 RH、GRH 或其他猜想时，把前提写入正式命题。若发布参数族，报告族数、实例数、参数选择和共用的一般引理；拆解核心难题时优先寻找实质不同的中间步骤。

## 编辑研究台

- 哥德巴赫主站使用 [gaps.json](../../../research/gaps.json) 中的 `gaps`、`tracks` 和 `feeds`。每道新题关联有效的 `track`、`program` 和适当的 `role`。主线数学方向改变时更新 [ROADMAP.md](../../../research/ROADMAP.md)，并核对中英文首页的路线摘要。
- 分站使用 [problems.json](../../../research/problems.json) 对应 slug 下的 `gaps` 与 `roadmap`。在阶段的 `tasks` 中引用同一分站的题目 ID，并为阶段和任务填写中英文文本。只改阶段顺序、说明或引用时，可保留原有题目。
- 遵循同分支相邻记录的字段和 [目录测试](../../../research/test_catalogue.py)。例如 `L-goldbach-example` 对应模块 `PEqualNP.Outside.L_goldbach_example`、文件 `lean/PEqualNP/Outside/L_goldbach_example.lean`。全站 ID、模块名和文件路径须唯一。填写完整 `statement`、两种语言的 `plain_statement` 与 `brief`、可核对的 `source`，按实际情况设置 `parallel`。使用项目允许的导入。
- 既有领取记录绑定声明字节的 SHA-256。扩充目录时对比基线，核对旧题 ID 和声明。修正改变数学含义的已发布命题时使用新 ID，在路线中解释替代关系并处理旧任务的在途领取和历史记录。仅重写路线说明不需要换 ID。

## 验证、发布与回读

1. 运行 `python -B -m unittest research.test_catalogue deploy.test_landau` 和 `git diff --check`。人工核对中英文描述与 Lean 类型是否一致，尤其是自然数减法、整除、求和括号和存在量词。若实际需要导入其他已证引理，核对它已存在于受信基线，提交者能够按导入规则使用。
2. 参照 [Desk 测试](../../../deploy/test_desk.py)，用临时 SQLite 初始化各受影响的 Desk，调用 `/api/desk/claim`，逐一验证新增 ID 返回 201 且领取对应题目。验证过程使用隔离租约。
3. 创建 PR 后核对目录 CI，修正在预检中发现的问题。管理员审核后用项目所有者的 GitHub 账号合并到 main。
4. 合并后查看该 SHA 的 push 目录 CI 和网站 `research-changes`，检查生产快照里的新增 ID 和冻结声明。需要诊断发布时参见[自动发布运维](../../../deploy/catalogue-release.md)。不要把 PR 检查通过或合并动作单独报告为已上线。
5. 给出 PR、CI、受影响研究台与任务链接。区分声明通过类型检查与提交的证明通过权威核验。
