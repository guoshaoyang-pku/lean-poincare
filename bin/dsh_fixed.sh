#!/bin/bash
# Thin wrapper that pins the DeepSeek API key for headless worker runs.
# The key is read from the host's dsh credential file so that swapping
# providers/keys is a single-file edit per host (~/.dsh/.credentials.yaml).
# The PATH line may need per-host adjustment (node + local dsh package).
export PATH="$HOME/.local/node/bin:$HOME/workdir/lean_poincare/.dshpkg/node_modules/.bin:$PATH"
export DEEPSEEK_API_KEY="$(python3 -c "import re;t=open('$HOME/.dsh/.credentials.yaml').read();m=re.findall(r'sk-[A-Za-z0-9]+',t);print(m[0] if m else '')")"
exec dsh "$@"
