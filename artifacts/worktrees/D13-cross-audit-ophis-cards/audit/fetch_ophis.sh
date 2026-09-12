#!/usr/bin/env bash
set -u
MUX="$HOME/.ssh/relay-mux-10022"
SSH_OPT="-p 10022 -o StrictHostKeyChecking=no -o BatchMode=yes -o ConnectTimeout=20 -o ControlMaster=auto -o ControlPath=$MUX -o ControlPersist=900"
REMOTE=guoshaoyang@127.0.0.1
RW=workdir/lean_poincare/longrun/worktrees
W=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards/audit/ophis
TASKS="D13-integrated-kernel-audit D13-critical-path-review D13-upstream-adapter-audit D13-morgan-tian-adapter-plan D13-topping-ricci-adapter-plan D13-manifold-ibp-volume-form D13-deturck-shorttime-producer D13-vankampen-recognition D13-heatkernel-bridge-d10-d7 D13-cross-audit-360-cards"
for t in $TASKS; do
  echo "=== FETCH $t $(date -Is)"
  mkdir -p "$W/$t"
  rsync -a --timeout=600 --exclude='.lake/' --exclude='.git/' --exclude='third_party/' --exclude='tmp/' \
    -e "ssh $SSH_OPT" \
    "$REMOTE:$RW/$t/longrun/" "$W/$t/longrun/" 2>&1 | tail -3
  for f in checkpoint.json README.md LONG_PLAN.json; do
    rsync -a --timeout=300 -e "ssh $SSH_OPT" "$REMOTE:$RW/$t/$f" "$W/$t/" 2>/dev/null
  done
  for d in manifest tools negcontrol docs audit-evidence input; do
    rsync -a --timeout=600 -e "ssh $SSH_OPT" "$REMOTE:$RW/$t/$d" "$W/$t/" 2>/dev/null
  done
  mkdir -p "$W/$t/release"
  rsync -a --timeout=900 --exclude='.lake/' -e "ssh $SSH_OPT" \
    "$REMOTE:$RW/$t/release/" "$W/$t/release/" 2>&1 | tail -3
  echo "=== DONE $t $(date -Is) size=$(du -sh "$W/$t" | cut -f1)"
done
echo "ALL FETCH DONE $(date -Is)"
