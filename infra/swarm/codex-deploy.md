# Codex leader deployment

The leader runtime may use the host's installed Codex CLI and existing credential reference. This repository never copies provider keys or auth databases.

## Preflight

```sh
codex --version
codex doctor
```

The model must be an explicit, host-supported identifier. `gpt-6-astra` is not assumed to exist on the remote host merely because the supervising local environment uses a model with that internal name. If the host administrator enables it, pass the exact supported ID with `codex exec --model <id>`. Otherwise use the configured `deepseek-flash` dsh route.

## Leader process contract

Each leader receives `TASK_ID`, `LEADER_ID`, `WORKTREE`, `CHECKPOINT`, `COMMS_DIR` and `MODEL` through environment variables. It writes only inside its workspace, checkpoints every 30 minutes and emits child task JSON into `comms/outbox/`. The dispatcher remains the only process that launches children.

Never put credentials in environment snapshots, prompts, logs, Git, or command arguments. Use the provider's existing credential reference mechanism.
