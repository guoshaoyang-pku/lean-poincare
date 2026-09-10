#!/usr/bin/env python3
import os
import socket

os.environ.setdefault("DSH_HOST", "360-1" if socket.gethostname().startswith("gpu01") else "360-2")

from dispatch_loop import main

if __name__ == "__main__":
    main()
