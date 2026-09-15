# CambridgeHPC admission and migration checkpoint

Date: 2026-09-15 (Asia/Shanghai)

## Authentication probe

Target alias: `CambridgeHPC` → `hw681@login-cpu.hpc.cam.ac.uk:22`

The server accepted the configured public key `~/.ssh/id_ed25519` with **partial success**, then required `keyboard-interactive` or `hostbased` authentication. Batch mode therefore ended with:

`Permission denied (keyboard-interactive,hostbased)`

This is an external MFA/second-factor gate. It is not evidence of a bad hostname, wrong user, failed network route, or unavailable cluster capacity. No password, OTP, private key, provider key, or credential file was read, copied, logged, or written.

## Migration safety decision

No Cambridge session, Slurm job, dispatcher, worktree copy, or queue mutation was started because the login session is not authenticated. The existing ophis fleet remains independent and untouched; its single-dispatcher invariant and checkpoints must be preserved. Cambridge must receive a fresh isolated control root at `/rds/user/hw681/hpc-work/poincare`, never an in-place overwrite of ophis state.

## Ready actions after authentication

1. Run a read-only preflight on Cambridge: hostname, disk quota, `sbatch`/`squeue`/`srun`, partition names, CPU/GPU availability, Singularity/Apptainer or container runtime, Python, Git, and the pinned Lean toolchain.
2. Create `/rds/user/hw681/hpc-work/poincare/{control,worktrees,state,logs,results}` and copy only the publication control sources and selected task inputs. Do not copy `.dsh` credentials or provider secrets.
3. Use a Cambridge-specific Slurm array executor with explicit array-size and CPU/memory limits. The array must run workers only; the existing ophis dispatcher remains the sole dispatcher until a separately locked Cambridge controller is deliberately installed and audited.
4. Start with a canary array of one task, verify heartbeat/checkpoint/compile evidence, then scale in bounded waves. Do not assume an Astra model alias exists; record the model identifier returned by the authorized runtime.
5. Migrate only tasks from preserved checkpoints, prioritizing L1/L2/L3/L4/L5 child rows with valid prompts, dependencies, worktrees, and acceptance commands.

## Current Poincare baseline

The Cambridge pool is not yet counted in fleet totals or ETA. Until its preflight and canary succeed, ophis remains the only live compute host in this control view. Existing semantic and mathematical claim ceilings remain unchanged.
