
## 2026-09-11 — active execution model switch

The active Poincare execution fleet is standardized on `deepseek-flash` (DeepSeek v4.1 Flash). Existing worktrees, checkpoints, heartbeats, result cards, and historical logs are preserved. The switch applies to the active queue, worker default heartbeat metadata, and task prompts; historical result artifacts retain their original model labels for auditability. Workers pick up the model at the next invocation boundary; no worktree is reset or deleted. If transport or authentication fails, resume from the existing checkpoint rather than recreating the task.
