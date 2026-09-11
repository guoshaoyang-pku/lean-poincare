# Transport resume control fix — 2026-09-12 03:00 +0800

The publication `bin/resume_transport.py` was hardened and syntax-checked, then deployed to ophis-gpu after preserving the prior remote copy as `bin/resume_transport.py.bak-20260912-0300`.

The fix refuses to proceed when `dispatcher.lock` is held, refuses to start a second dispatcher when an existing `dispatch_loop.py` is detected, and preserves the queue's configured model instead of silently switching models during recovery. Remote syntax check passed; new script SHA256 is `92523732ca648c671bea4a548f1be533f6598dde988d88c08387803becdec993`.

The recovery helper itself was not run. Queue counts, admission pause, credentials, worktrees and task states were untouched.
