# 研究清单自动发布

AI 从最新 main 开分支，为目录变更提交 PR。项目所有者或授权的数学任务发布者在 GitHub 审核并合并。ECS 定时器每五分钟按 main 第一父链顺序检查变更，要求每个目录提交对应由获授权账号合并的 PR，并有该 SHA 的 catalogue.yml push 成功记录。建议用 squash merge。目录通过直接推送或多 PR 打包时若无法对应单一合并提交，发布停下供人工核对。服务器只从 Git 读取两个目录数据文件。服务代码及工作流的运维更新仍走部署技能。

在 `goldbach-catalogue.service` 的服务器 drop-in 中设置 `GOLDBACH_CATALOGUE_MERGER_IDS`，填入以空格分隔的 GitHub 数字用户 ID，随后执行 `systemctl daemon-reload`。项目所有者默认有权限。该名单独立于网站发布名单。

## 首次启用

在此功能 PR 合并之后，按部署技能从已审提交发布 server.py、zh.html、en.html、publish_catalogue.py。核对线上基线：选择已经在生产处理过的最后一个目录提交，或之后尚未引入目录变化的 main 提交。用完整 SHA 初始化。初始化会复制现网两份 JSON；历史页面从首次自动发布开始计数。

```sh
install -d -m 0755 /opt/goldbach-catalogues
python3 /opt/goldbach-web/publish_catalogue.py --bootstrap "$LIVE_BASE_SHA"
install -m 0644 deploy/goldbach-catalogue.service deploy/goldbach-catalogue.timer /etc/systemd/system/
systemctl daemon-reload
systemctl enable --now goldbach-catalogue.timer
```

加载器一次解析 current 指向的不可变版本。新版本目录完整落盘后，发布器原子切换链接、仅重启 goldbach-web，并从生产 health 核对 catalogue_revision；失败时切回原版本。若线上清单与 Git 基线不同，三方合并保留现网差异；有冲突时在切换前退出。核验 API 和服务记录无需部署令牌。对批量发布检查各台 api/status 和新题详情；公开变更记录入口为 research-changes?lang=zh。

## 故障处理

查看 journalctl -u goldbach-catalogue.service，区分身份不符、CI 待完成、清单合并冲突和重载失败。网络错误由下一轮定时器重试。需要人工回滚时先停止 timer 和发布服务，核对旧版本后原子切回 current，重启 goldbach-web 并核对 health。恢复 timer 前在 Git 上创建并审核修复 PR；若队列头仍是有冲突或未获授权的提交，须由管理员明确核对并协调基线。历史记录属于正在提供服务的快照。
