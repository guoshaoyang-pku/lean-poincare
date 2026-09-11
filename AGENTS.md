# Publication repository agent rules

遵守 workspace 根目录 `AGENTS.md`，并遵循以下更严格规则：

- `main` 只接收经过 compile gate 的批量合并；实验性调度修改放在 `codex/*` 分支。
- 不提交密钥、credential 文件、远程日志、共享 `.lake` 缓存或未审计生成物。
- 所有新 Lean 声明必须记录编译命令、toolchain/mathlib pin、source hash、axiom evidence 和语义分类。
- 任何 blocker closure 都必须有构造者和下游 checked use；接口或假设字段不算 closure。
- 修改 dispatcher、queue schema 或 worker prompt 时，先备份运行配置并保留回滚路径。
- leader/worker 只能修改自己的 worktree；integrator 负责跨任务合并和冲突解决。
- 结果卡片必须准确反映当前状态；不得用 `TASK_DONE` 掩盖 gate failure、transport failure 或未完成审计。
