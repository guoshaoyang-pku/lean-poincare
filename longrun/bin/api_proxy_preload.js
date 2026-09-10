const path = require("node:path");
const tls = require("node:tls");
const { Agent, setGlobalDispatcher } = require(path.join(process.env.HOME, "proxyhelper/node_modules/undici6"));

function connect(options, callback) {
  let settled = false;
  const finish = (error, socket) => {
    if (settled) return;
    settled = true;
    callback(error, socket);
  };
  const startTls = (socketOptions) => {
    const socket = tls.connect({ ...socketOptions, servername: options.servername || options.hostname });
    socket.setTimeout(20000, () => socket.destroy(new Error("API TLS connect timeout")));
    socket.once("secureConnect", () => {
      socket.setTimeout(0);
      finish(null, socket);
    });
    socket.once("error", (error) => finish(error, null));
  };
  if (options.hostname === "api.deepseek.com") {
    startTls({ host: "127.0.0.1", port: Number(process.env.DSH_API_TUNNEL_PORT || 8443) });
    return;
  }
  const { SocksClient } = require(path.join(process.env.HOME, "proxyhelper/node_modules/socks"));
  SocksClient.createConnection({
    proxy: { host: "127.0.0.1", port: 1080, type: 5 },
    command: "connect",
    destination: { host: options.hostname, port: Number(options.port) || 443 },
    timeout: 20000,
  }, (error, info) => {
    if (error) finish(error, null);
    else startTls({ socket: info.socket });
  });
}

setGlobalDispatcher(new Agent({ connect }));
