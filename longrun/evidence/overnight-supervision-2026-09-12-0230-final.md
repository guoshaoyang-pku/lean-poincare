# Live supervision checkpoint — 2026-09-12 02:30 +0800

A delayed recheck on ophis-gpu is unchanged: 141 task records (`verified` 92, `queued` 40, `paused` 7, `blocked` 2), with `ADMISSION_PAUSED` present. The previously observed process list still has one actual `python3 bin/dispatch_loop.py` worker (PID 3924237) plus its launcher shell; inspection commands that contain the pattern are excluded from the dispatcher count.

The five registered leader workspaces and checkpoints remain present. The three L1 recovery worktrees/prompts/checkpoints prepared at 02:15 remain isolated and have not been admitted. No new provider call, queue mutation, task reset, or artifact promotion occurred during this interval.

360-1 and 360-2 continue to return SSH `Connection closed` and are left untouched. Quota/API exhaustion remains the external blocker.
