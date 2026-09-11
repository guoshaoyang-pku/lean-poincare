# Resume-control safety finding - 2026-09-12 02:45 +0800

Inspection of the host-side `bin/resume_transport.py` found two unsafe defaults for the current deployment: it unconditionally writes `queue.json[model] = deepseek-v4-pro`, despite the current host configuration being deepseek-flash, and it unconditionally starts a new dispatch_loop process. Calling it while PID 3924237 is alive would risk model drift and a duplicate dispatcher.

I did not execute this helper. The fleet remains under the existing single dispatcher, current model configuration, ADMISSION_PAUSED, min/target=1 and hard_cap=128. This is a control-plane finding only; no task or credential state was changed.