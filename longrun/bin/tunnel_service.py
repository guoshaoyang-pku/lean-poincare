#!/usr/bin/env python3
import asyncio
import contextlib
import os
from pathlib import Path
import signal

PROXY_PORT = int(os.environ.get("POINCARE_HTTP_PROXY_PORT", "7897"))
SSH_CONFIG = Path.home() / ".ssh/tunnel_360.conf"
PROCESSES = set()


def log(message):
    print(message, flush=True)


async def copy_stream(reader, writer):
    while data := await reader.read(65536):
        writer.write(data)
        await writer.drain()


async def relay(reader, writer):
    upstream = None
    pumps = []
    try:
        proxy_reader, upstream = await asyncio.wait_for(asyncio.open_connection("127.0.0.1", PROXY_PORT), 15)
        upstream.write(b"CONNECT api.deepseek.com:443 HTTP/1.1\r\nHost: api.deepseek.com:443\r\n\r\n")
        await upstream.drain()
        response = await asyncio.wait_for(proxy_reader.readuntil(b"\r\n\r\n"), 20)
        if response.split(b"\r\n", 1)[0].split()[1] != b"200":
            raise ConnectionError("HTTP proxy rejected CONNECT")
        pumps = [asyncio.create_task(copy_stream(reader, upstream)), asyncio.create_task(copy_stream(proxy_reader, writer))]
        completed, pending = await asyncio.wait(pumps, return_when=asyncio.FIRST_COMPLETED)
        for task in completed:
            task.result()
    except (OSError, ConnectionError, asyncio.TimeoutError, asyncio.IncompleteReadError) as error:
        log(f"RELAY_ERROR {type(error).__name__}")
    finally:
        for task in pumps:
            task.cancel()
        if pumps:
            await asyncio.gather(*pumps, return_exceptions=True)
        for stream in (writer, upstream):
            if stream:
                stream.close()
                with contextlib.suppress(OSError):
                    await stream.wait_closed()


async def tunnel(host, port):
    while True:
        process = None
        try:
            process = await asyncio.create_subprocess_exec(
                "/usr/bin/ssh", "-N", "-T", "-F", str(SSH_CONFIG),
                "-o", "BatchMode=yes", "-o", "ConnectTimeout=15",
                "-o", "ServerAliveInterval=20", "-o", "ServerAliveCountMax=3",
                "-o", "ExitOnForwardFailure=yes", "-o", "ControlMaster=no", "-o", "ControlPath=none",
                "-R", f"127.0.0.1:8443:127.0.0.1:{port}",
                "-R", "127.0.0.1:10022:223.167.85.180:50002",
                "-R", "127.0.0.1:1080", host,
                stdin=asyncio.subprocess.DEVNULL,
            )
            PROCESSES.add(process)
            log(f"SSH_START {host} pid={process.pid}")
            code = await process.wait()
            log(f"SSH_EXIT {host} code={code}")
        finally:
            if process:
                if process.returncode is None:
                    process.terminate()
                    with contextlib.suppress(asyncio.TimeoutError):
                        await asyncio.wait_for(process.wait(), 5)
                    if process.returncode is None:
                        process.kill()
                        await process.wait()
                PROCESSES.discard(process)
        await asyncio.sleep(15)


async def main():
    stopped = asyncio.Event()
    loop = asyncio.get_running_loop()
    for signum in (signal.SIGTERM, signal.SIGINT):
        loop.add_signal_handler(signum, stopped.set)
    server = await asyncio.start_server(relay, "127.0.0.1", 0)
    port = server.sockets[0].getsockname()[1]
    log(f"RELAY_READY loopback_port={port} http_proxy_port={PROXY_PORT}")
    workers = [asyncio.create_task(tunnel(host, port)) for host in ("360-1", "360-2")]
    async with server:
        await stopped.wait()
    for worker in workers:
        worker.cancel()
    await asyncio.gather(*workers, return_exceptions=True)


if __name__ == "__main__":
    asyncio.run(main())
