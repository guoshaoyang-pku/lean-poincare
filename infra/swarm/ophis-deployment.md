# ophis-gpu unified deployment

All leaders, executors, dispatcher state, event log and communication directories live under one host root. Remote 360 queues remain recovery mirrors until transport is stable.

Deploy by copying code and non-secret configuration, backing up the active queue, validating Python syntax, then restarting exactly one dispatcher under its lock. Never copy credentials.

The initial pressure-test policy is adaptive target 96 with hard cap 128. Monitor API errors, heartbeat age, load, compile latency and useful artifacts before increasing further.
