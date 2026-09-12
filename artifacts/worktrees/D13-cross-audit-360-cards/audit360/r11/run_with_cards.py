#!/usr/bin/env python3
"""Run an existing round-1..10 audit script with its CARDS list (and optionally
LOG directory) overridden to one card, without editing the original script.

Usage: python3 r11/run_with_cards.py <script.py> <card> [LOG=dir] [CARDS_FMT=tuple]
CARDS_FMT=tuple builds [(card, "360-2")] for scripts whose CARDS are (id, host).
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
AUD = os.path.dirname(HERE)


def main():
    script, card = sys.argv[1], sys.argv[2]
    opts = dict(a.split("=", 1) for a in sys.argv[3:] if "=" in a)
    spec = importlib.util.spec_from_file_location("m_" + os.path.basename(script)[:-3],
                                                  os.path.join(AUD, script))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    if getattr(mod, "CARDS", None) is not None:
        if opts.get("CARDS_FMT") == "tuple":
            mod.CARDS = [(card, "360-2")]
        else:
            mod.CARDS = [card]
    if "LOG" in opts and hasattr(mod, "LOG"):
        mod.LOG = os.path.join(AUD, opts["LOG"])
    mod.main()


if __name__ == "__main__":
    main()
