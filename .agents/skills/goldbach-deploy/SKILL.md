---
name: goldbach-deploy
description: Deploy or update the Goldbach Open Conjecture Platform, verify the deployed version, or roll back a release. Use for website and task-catalogue updates, GitHub Actions or webhook changes, and service or nginx configuration updates. Read the deployment plan without changing production when asked only for advice.
---

# Goldbach 项目部署

先确定目标环境、Git 提交和授权范围。GitHub 的 `main`、服务器上的 Git 工作副本、正在运行的 `/opt/goldbach-web` 是三个可以独立变化的位置。推送 Git 不会自动发布网站。服务器工作副本的 HEAD 也不足以证明某文件已经上线。发布前核对实际服务文件和本次改动路径。

从仓库根目录运行命令。部署步骤和按变更类型选择的检查见 [发布与回滚](references/release.md)。服务配置、依赖、凭据文件位置和双入口架构见仓库的 [部署文档](../../../deploy/README.md)。

- **网站更新**：只发布本次涉及的 `deploy/` 运行文件及其依赖。新增 JS、CSS 或图片还要检查应用资源路由和两种入口下的路径。替换文件后用线上请求确认效果。仅当应用加载方式或变更内容要求时重启 `goldbach-web`。
- **任务清单**：对照 `research/gaps.json` 和 `research/problems.json`，确认新增 ID 唯一，已发布命题及其哈希按预期保留。先核验 GitHub Actions 中的 Lean 命题检查，再部署相应清单并重启服务。逐个核对受影响研究台的公开任务。
- **工作流、代理或凭据**：GitHub Actions 工作流从仓库发布。nginx 改动仅涉及项目专属虚拟主机或子路径，配置通过 `nginx -t` 后平滑重载。systemd 单元或 drop-in 修改后执行 `daemon-reload`。现有业务、生产数据库和站点凭据都在发布文件清单之外。

使用开发者自己的授权账号与服务器权限。只有获准更新生产时才运行生产命令。凭据通过 systemd、GitHub Actions Secrets 或各自的凭据存储提供。Git、提交描述、日志、截图和命令输出只记录必要的版本与验证结果。部署完成时给出提交 SHA、实际更新文件、线上验证结果和适用的回滚备份位置。
