import json
import os
import subprocess
import sys
import threading
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

HERE = os.path.dirname(os.path.abspath(__file__))
PORT = 8000
LOCK = threading.Lock()  # one command at a time through the engine pipe


def find_engine():
    for name in ("engine.exe", "engine"):
        path = os.path.join(HERE, name)
        if os.path.exists(path):
            return path
    sys.exit("engine.exe not found next to server.py (compile: gcc -std=c99 engine.c -o engine.exe)")


ENGINE = subprocess.Popen(
    [find_engine()],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.DEVNULL,
    text=True,
    bufsize=1,
    cwd=HERE,
)


def run_command(cmd):
    with LOCK:
        if ENGINE.poll() is not None:
            return {"ok": False, "error": "engine.exe has exited"}
        ENGINE.stdin.write(cmd.replace("\r", " ").replace("\n", " ") + "\n")
        ENGINE.stdin.flush()
        line = ENGINE.stdout.readline()
    if not line:
        return {"ok": False, "error": "engine.exe closed its output"}
    try:
        return json.loads(line)
    except json.JSONDecodeError:
        return {"ok": False, "error": "engine returned invalid JSON", "raw": line.strip()}


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, body, ctype):
        data = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        url = urlparse(self.path)
        if url.path in ("/", "/index.html"):
            try:
                with open(os.path.join(HERE, "index.html"), "rb") as f:
                    self._send(200, f.read(), "text/html; charset=utf-8")
            except OSError:
                self._send(404, "index.html not found", "text/plain")
        elif url.path == "/run":
            cmd = parse_qs(url.query).get("cmd", [""])[0].strip()
            if not cmd:
                result = {"ok": False, "error": "empty command"}
            else:
                result = run_command(cmd)
            self._send(200, json.dumps(result), "application/json")
        else:
            self._send(404, "not found", "text/plain")

    def log_message(self, fmt, *args):
        pass


def main():
    server = ThreadingHTTPServer(("localhost", PORT), Handler)
    url = f"http://localhost:{PORT}"
    print(f"Serving {url}  (Ctrl+C to stop)")
    threading.Timer(0.5, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        try:
            ENGINE.stdin.close()
            ENGINE.terminate()
        except Exception:
            pass


if __name__ == "__main__":
    main()
