#!/usr/bin/env python3
"""Stage and generate the audit probes for a late-arriving card.

The card lists are hard-coded in the round-1..10 tooling; this driver reuses
those modules with the card list overridden to exactly one card, so no existing
package directory is touched (prepare.copy_sources wipes the destination).

Usage:
  python3 r11/stage_card8.py stage   <card>   # copy sources, A3Probe.lean, A3Meta.json
  python3 r11/stage_card8.py genfull <card>   # A3FullAudit.lean (needs a build)
  python3 r11/stage_card8.py genkind <card>   # A3KindAudit.lean
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
AUD = os.path.dirname(HERE)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    mode, card = sys.argv[1], sys.argv[2]
    if mode == "stage":
        m = load("prepare", os.path.join(AUD, "prepare.py"))
        m.CARDS = [card]
        m.main()
    elif mode == "genfull":
        m = load("gen_full", os.path.join(AUD, "gen_full_audit.py"))
        m.CARDS = [card]
        m.main()
    elif mode == "genkind":
        m = load("gen_kind", os.path.join(AUD, "gen_kind_audit.py"))
        m.CARDS = [card]
        m.main()
    else:
        raise SystemExit("unknown mode " + mode)


if __name__ == "__main__":
    main()
