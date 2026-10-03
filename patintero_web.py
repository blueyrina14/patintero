"""
PATINTERO WEB - 2 players in the browser (phones welcome). Two modes, picked by whoever creates the game:
    CO-OP    both players run together against 3 AI guards and share one team score.
    VERSUS   Runners vs Guards: Jack en poy decides the teams, roles swap every round.

    python patintero_web.py            (default port 8000; or: python patintero_web.py 9000)

Needs nothing but Python 3.7+. It serves the game page AND the game server.
Player 1 opens the page, taps CO-OP or VERSUS, then sends the invite link (email / share / copy).
Player 2 taps the link (or types the 4-letter code) and is in. In VERSUS, a JACK EN POY match
picks the teams: the winner's team RUNS first, the loser's team GUARDS first (taya).

Same Wi-Fi:   http://<your-computer-ip>:8000
Other Wi-Fi:  put a tunnel in front, e.g.  cloudflared tunnel --url http://localhost:8000
              (or ngrok http 8000) and share the https link it prints.
"""
import asyncio
import base64
import hashlib
import json
import math
import random
import socket
import sys
import time
from urllib.parse import parse_qs, urlparse

PORT = 8000
TICK = 1 / 30
WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

COURT_LEFT, COURT_RIGHT = 190, 810
COURT_TOP, COURT_BOTTOM = 70, 550
LINE_1, LINE_2, MIDDLE_X = 220, 385, 500
START_Y = COURT_BOTTOM - 35
START_X = (440, 560)
PLAYER_SPEED = 250              # pixels per second
GUARD_SPEED = 280               # AI guards
HUMAN_GUARD_SPEED = 240
HIT_DISTANCE = 46
ROUNDS = 4                      # roles swap every round
ROUND_TIME = 20
TAG_POINTS = 30
RPS_TIME = 10                   # seconds to pick rock/paper/scissors
SHAKE_TIME = 1.6                # JACK...EN...POY! bump animation before the reveal
REVEAL_TIME = 3.0
READY_TIME = 3.0
RESULT_TIME = 2.5
HURT_TIME = 1.2                 # co-op: frozen (blinking) after being tagged
SERVER_PORT = PORT

ROOMS = {}


# ============================================================
# WEBSOCKET (just enough of RFC 6455, standard library only)
# ============================================================

def ws_accept(key):
    return base64.b64encode(hashlib.sha1((key + WS_GUID).encode()).digest()).decode()


def ws_frame(op, payload):
    n = len(payload)
    if n < 126:
        head = bytes([0x80 | op, n])
    elif n < 65536:
        head = bytes([0x80 | op, 126]) + n.to_bytes(2, "big")
    else:
        head = bytes([0x80 | op, 127]) + n.to_bytes(8, "big")
    return head + payload


async def read_frame(reader):
    b1, b2 = await reader.readexactly(2)
    op, n = b1 & 0x0F, b2 & 0x7F
    if n == 126:
        n = int.from_bytes(await reader.readexactly(2), "big")
    elif n == 127:
        n = int.from_bytes(await reader.readexactly(8), "big")
    if n > 65536:
        raise ValueError("frame too big")
    mask = await reader.readexactly(4) if b2 & 0x80 else None
    data = await reader.readexactly(n)
    if mask:
        data = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
    return op, data


class Conn:
    def __init__(self, writer):
        self.writer = writer

    def write(self, frame):
        try:
            if not self.writer.is_closing():
                self.writer.write(frame)
        except Exception:
            pass

    def send(self, obj):
        self.write(ws_frame(1, json.dumps(obj, separators=(",", ":")).encode()))


# ============================================================
# GAME ROOM (server-authoritative)
# ============================================================

class Room:
    def __init__(self, code, mode="coop"):
        self.code = code
        self.mode = mode                 # "coop" or "versus"
        self.conns = [None, None]
        self.first = 0                   # who RUNS in round 1 (the Jack en poy winner)
        self.rr = 0                      # bumps whenever the RPS screen must reset
        self.alive = True
        self.reset()

    # ---------- state ----------
    def reset(self):
        if not all(self.conns):
            self.phase, self.timer = "lobby", RPS_TIME
        elif self.mode == "versus":              # Jack en poy decides the teams
            self.phase, self.timer = "rps", RPS_TIME
        else:                                    # co-op: no teams, straight to the game
            self.phase, self.timer = "ready", READY_TIME
        self.rr += 1
        self.choices = [None, None]
        self.rc, self.rw = None, -1
        self.rs = [0, 0]
        self.score = 0
        self.round = 1
        self.msg = ""
        self.again = set()
        self.events = []
        self.setup_round()

    def setup_round(self):
        self.runner = (self.first + self.round - 1) % 2
        self.round_timer = ROUND_TIME
        self.guards = [
            {"x": 350, "y": LINE_1, "dx": GUARD_SPEED, "moving": True},
            {"x": MIDDLE_X, "y": 300, "dx": 0, "moving": False},
        ]
        if self.mode == "versus":                # bottom guard is played by a human
            self.guards.append({"x": MIDDLE_X, "y": LINE_2, "dx": 0, "moving": False})
        else:                                    # co-op: an AI guard
            self.guards.append({"x": 650, "y": LINE_2, "dx": -GUARD_SPEED, "moving": True})
        self.players = [{"x": START_X[i], "y": START_Y, "dx": 0, "dy": 0, "crossed": [False, False],
                         "pts": 0, "done": False, "hurt": 0.0} for i in (0, 1)]

    def revealed(self):
        """True once the outcome is allowed to reach the browser: not before the
        shake animation has actually finished playing, so nobody can peek early."""
        return self.phase not in ("lobby", "rps", "rpsshake")

    def snapshot(self):
        return {
            "t": "s", "ph": self.phase, "tm": round(max(0, self.timer), 2),
            "on": [c is not None for c in self.conns],
            "mode": self.mode, "sc": self.score,
            "rn": self.runner, "rd": self.round, "tot": ROUNDS,
            "rt": round(max(0, self.round_timer), 1), "rs": self.rs, "msg": self.msg,
            "rr": self.rr, "ch": [c is not None for c in self.choices],
            "rc": self.rc if self.revealed() else None, "rw": self.rw if self.revealed() else -1,
            "g": [[round(g["x"], 1), g["y"], int(g["moving"])] for g in self.guards],
            "p": [[round(p["x"], 1), round(p["y"], 1), int(p["done"]), round(p["hurt"], 2)]
                  for p in self.players],
            "ev": self.events,
        }

    # ---------- players coming and going ----------
    def join(self, conn):
        for i in (0, 1):
            if self.conns[i] is None:
                self.conns[i] = conn
                if all(self.conns):
                    self.reset()                      # both here -> Jack en poy
                return i
        return None

    def leave(self, conn):
        if conn in self.conns:
            self.conns[self.conns.index(conn)] = None
            if not any(self.conns):
                self.alive = False
                ROOMS.pop(self.code, None)
            else:
                self.reset()                          # back to the lobby

    def on_message(self, pid, m):
        t = m.get("t")
        if t == "in":
            p = self.players[pid]
            p["dx"] = max(-1, min(1, int(m.get("dx", 0))))
            p["dy"] = max(-1, min(1, int(m.get("dy", 0))))
        elif t == "rps" and self.phase == "rps" and self.choices[pid] is None:
            c = int(m.get("c", -1))
            if c in (0, 1, 2):
                self.choices[pid] = c
        elif t == "again" and self.phase == "done":
            self.again.add(pid)
            if len(self.again) == 2:
                self.reset()

    # ---------- simulation ----------
    def step(self, dt):
        for g in self.guards:
            if g["moving"]:
                g["x"] += g["dx"] * dt
                if g["x"] <= COURT_LEFT + 30:
                    g["x"], g["dx"] = COURT_LEFT + 30, abs(g["dx"])
                elif g["x"] >= COURT_RIGHT - 30:
                    g["x"], g["dx"] = COURT_RIGHT - 30, -abs(g["dx"])

        ph = self.phase
        if ph == "rps":
            self.timer -= dt
            if self.timer <= 0:                                   # too slow: random pick
                self.choices = [c if c is not None else random.randrange(3) for c in self.choices]
            if None not in self.choices:
                a, b = self.choices
                self.rw = 0 if (a - b) % 3 == 1 else 1 if (b - a) % 3 == 1 else -1
                self.rc = list(self.choices)
                self.phase, self.timer = "rpsshake", SHAKE_TIME
        elif ph == "rpsshake":
            self.timer -= dt
            if self.timer <= 0:
                self.phase, self.timer = "rpsr", REVEAL_TIME
        elif ph == "rpsr":
            self.timer -= dt
            if self.timer <= 0:
                if self.rw < 0:                                   # tie: throw again
                    self.phase, self.timer, self.choices, self.rc = "rps", RPS_TIME, [None, None], None
                    self.rr += 1
                else:
                    self.first = self.rw                          # winner's team runs first
                    self.setup_round()
                    self.phase, self.timer = "ready", READY_TIME
        elif ph == "ready":
            self.timer -= dt
            if self.timer <= 0:
                self.phase = "play"
        elif ph == "result":
            self.timer -= dt
            if self.timer <= 0:
                self.next_round()
        if self.phase == "play":
            if self.mode == "versus":
                self.step_play(dt)
            else:
                self.step_coop(dt)

    def step_coop(self, dt):
        for pid, p in enumerate(self.players):
            if p["done"]:
                continue
            if p["hurt"] > 0:
                p["hurt"] -= dt
                continue
            dx, dy = p["dx"], p["dy"]
            if dx or dy:
                k = PLAYER_SPEED * dt / (1.414 if dx and dy else 1)
                p["x"] = max(COURT_LEFT + 30, min(COURT_RIGHT - 30, p["x"] + dx * k))
                p["y"] = max(COURT_TOP + 30, min(COURT_BOTTOM - 40, p["y"] + dy * k))
            if any(math.hypot(p["x"] - g["x"], p["y"] - g["y"]) < HIT_DISTANCE for g in self.guards):
                self.score -= p["pts"]                          # tagged: lose this try's points
                self.events.append(["caught", pid, p["pts"]])
                p.update(x=START_X[pid], y=START_Y, pts=0, crossed=[False, False],
                         hurt=HURT_TIME, dx=0, dy=0)
                continue
            for i, line_y in enumerate((LINE_2, LINE_1)):
                if p["y"] <= line_y and not p["crossed"][i]:
                    p["crossed"][i] = True
                    p["pts"] += 10
                    self.score += 10
                    self.events.append(["+10", pid])
            if p["y"] <= COURT_TOP + 30:
                p["done"], p["pts"] = True, 0
                self.score += 30
                self.events.append(["+30", pid])
        if all(p["done"] for p in self.players):
            self.score += 50                                     # team bonus
            self.events.append(["+50", -1])
            self.phase = "done"

    def step_play(self, dt):
        r = self.runner
        p, gp, hg = self.players[r], self.players[1 - r], self.guards[2]
        hg["x"] = max(COURT_LEFT + 30, min(COURT_RIGHT - 30,
                                           hg["x"] + gp["dx"] * HUMAN_GUARD_SPEED * dt))
        self.round_timer -= dt

        dx, dy = p["dx"], p["dy"]
        if dx or dy:
            k = PLAYER_SPEED * dt / (1.414 if dx and dy else 1)
            p["x"] = max(COURT_LEFT + 30, min(COURT_RIGHT - 30, p["x"] + dx * k))
            p["y"] = max(COURT_TOP + 30, min(COURT_BOTTOM - 40, p["y"] + dy * k))

        if any(math.hypot(p["x"] - g["x"], p["y"] - g["y"]) < HIT_DISTANCE for g in self.guards):
            self.end_round("tag", 1 - r, TAG_POINTS, f"Player {2 - r} tagged Player {r + 1}!", r)
            return
        for i, line_y in enumerate((LINE_2, LINE_1)):
            if p["y"] <= line_y and not p["crossed"][i]:
                p["crossed"][i] = True
                self.rs[r] += 10
                self.events.append(["+10", r])
        if p["y"] <= COURT_TOP + 30:
            self.end_round("+30", r, 30, f"Player {r + 1} made it across the finish!")
        elif self.round_timer <= 0:
            self.end_round("time", 1 - r, TAG_POINTS, "Time's up! The guards win the round.")

    def end_round(self, kind, winner, pts, msg, extra=0):
        self.rs[winner] += pts
        self.events.append([kind, winner, pts, extra])
        self.msg = f"{msg}   +{pts}"
        self.phase, self.timer = "result", RESULT_TIME

    def next_round(self):
        self.round += 1
        if self.round > ROUNDS:
            self.phase = "done"
            return
        self.setup_round()
        self.phase, self.timer = "ready", 2.0

    async def run(self):
        last = time.perf_counter()
        while self.alive:
            await asyncio.sleep(TICK)
            now = time.perf_counter()
            dt, last = min(now - last, .1), now
            self.step(dt)
            frame = ws_frame(1, json.dumps(self.snapshot(), separators=(",", ":")).encode())
            self.events = []
            for c in self.conns:
                if c:
                    c.write(frame)


def new_code():
    while True:
        code = "".join(random.choice("ABCDEFGHJKMNPQRSTUVWXYZ") for _ in range(4))
        if code not in ROOMS:
            return code


# ============================================================
# HTTP + WEBSOCKET CONNECTION HANDLER
# ============================================================

async def handle(reader, writer):
    try:
        head = await asyncio.wait_for(reader.readuntil(b"\r\n\r\n"), 10)
        lines = head.decode("latin1").split("\r\n")
        _, target, _ = lines[0].split(" ", 2)
        headers = {k.lower(): v for k, v in (l.split(": ", 1) for l in lines[1:] if ": " in l)}
        url = urlparse(target)
        qs = parse_qs(url.query)

        if url.path == "/ws" and headers.get("upgrade", "").lower() == "websocket":
            await ws_session(reader, writer, headers, qs)
            return
        if url.path in ("/", "/index.html"):
            body, status, ctype = INDEX_HTML.encode(), "200 OK", "text/html; charset=utf-8"
        else:
            body, status, ctype = b"Not found", "404 Not Found", "text/plain"
        writer.write((f"HTTP/1.1 {status}\r\nContent-Type: {ctype}\r\nContent-Length: {len(body)}\r\n"
                      "Cache-Control: no-cache\r\nConnection: close\r\n\r\n").encode() + body)
        await writer.drain()
    except Exception:
        pass
    finally:
        try:
            writer.close()
        except Exception:
            pass


async def ws_session(reader, writer, headers, qs):
    writer.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                  f"Sec-WebSocket-Accept: {ws_accept(headers.get('sec-websocket-key', ''))}\r\n\r\n").encode())
    conn = Conn(writer)

    if "create" in qs:
        mode = "versus" if qs.get("mode", [""])[0] == "versus" else "coop"
        room = Room(new_code(), mode)
        ROOMS[room.code] = room
        asyncio.get_running_loop().create_task(room.run())
    else:
        room = ROOMS.get(qs.get("room", [""])[0].upper())
    if room is None:
        conn.send({"t": "error", "msg": "No game with that code"})
        return
    pid = room.join(conn)
    if pid is None:
        conn.send({"t": "error", "msg": "That game already has 2 players"})
        return
    ips = local_ips()
    conn.send({"t": "welcome", "id": pid, "room": room.code, "mode": room.mode,
               "lan": f"http://{ips[0]}:{SERVER_PORT}",
               "lanAll": [f"http://{ip}:{SERVER_PORT}" for ip in ips[:4]]})

    try:
        while True:
            op, data = await read_frame(reader)
            if op == 8:
                break
            if op == 9:
                conn.write(ws_frame(10, data))
            elif op == 1:
                try:
                    room.on_message(pid, json.loads(data))
                except (ValueError, TypeError, AttributeError):
                    pass
    except (asyncio.IncompleteReadError, ConnectionError, ValueError, OSError):
        pass
    finally:
        room.leave(conn)


def local_ips():
    """Best-effort list of this machine's LAN IPv4 addresses, most likely one first.
    A machine with a VPN, virtual switch, or multiple adapters can have several; trying
    to guess a single 'right' one is fragile, so we rank candidates and offer the rest
    as fallbacks the host can share if the first guess isn't reachable."""
    candidates = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))          # no packet is actually sent
        candidates.append(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    try:
        for ip in socket.gethostbyname_ex(socket.gethostname())[2]:
            if ip not in candidates:
                candidates.append(ip)
    except OSError:
        pass

    def rank(ip):
        parts = ip.split(".")
        if ip.startswith("127.") or ip.startswith("169.254."):
            return 9                              # loopback / link-local: last resort
        if ip.startswith("192.168."):
            return 0                              # most common home/school Wi-Fi range
        if ip.startswith("10."):
            return 1
        if len(parts) == 4 and parts[0] == "172" and parts[1].isdigit() and 16 <= int(parts[1]) <= 31:
            return 2
        return 3

    candidates.sort(key=rank)
    return candidates or ["127.0.0.1"]


def local_ip():
    return local_ips()[0]


async def main(port):
    global SERVER_PORT
    SERVER_PORT = port
    server = await asyncio.start_server(handle, "0.0.0.0", port)
    print(f"\n  PATINTERO is running!\n"
          f"  Same Wi-Fi:   http://{local_ip()}:{port}\n"
          f"  Other Wi-Fi:  cloudflared tunnel --url http://localhost:{port}   (or: ngrok http {port})\n"
          f"  Ctrl+C to stop.\n")
    async with server:
        await server.serve_forever()


# ============================================================
# THE GAME PAGE (HTML + CSS + JavaScript, served at "/")
# ============================================================

INDEX_HTML = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover">
<title>Patintero</title>
<style>
:root{--padsz:0px}
*{box-sizing:border-box}
html,body{margin:0;height:100%;overflow:hidden;background:#8BDCF7;font-family:"Arial Rounded MT Bold","Trebuchet MS",Verdana,sans-serif;touch-action:none;-webkit-user-select:none;user-select:none;-webkit-tap-highlight-color:transparent}
#app{height:100vh;height:100dvh;display:flex;align-items:center;justify-content:center;gap:2vmin}
#stage{position:relative;flex:0 1 auto;aspect-ratio:1000/720;width:min(100vw - var(--padsz) - 2vmin, calc(100dvh*1000/720));--u:7px}
canvas{width:100%;height:100%;display:block}
#ui{position:absolute;inset:0;display:none;align-items:center;justify-content:center;font-size:calc(var(--u)*2.4);color:#173B72}
.card{background:#fff;border:calc(var(--u)*.45) solid #173B72;border-radius:calc(var(--u)*2.4);box-shadow:calc(var(--u)*.8) calc(var(--u)*.8) 0 #6BBFDC;padding:calc(var(--u)*2.4) calc(var(--u)*4);text-align:center;max-width:92%;max-height:96%;overflow:auto}
.card h1{margin:0;font-size:calc(var(--u)*7.5);letter-spacing:.05em}
.sub{font-size:calc(var(--u)*2.6);margin-bottom:calc(var(--u)*1.4)}
.big{font-size:calc(var(--u)*3.6);margin:calc(var(--u)*.8) 0}
.code{font-size:calc(var(--u)*9);letter-spacing:.25em;color:#F4A340;margin:calc(var(--u)*.4) 0 calc(var(--u)*1)}
.score{font-size:calc(var(--u)*5);color:#F4A340;margin:calc(var(--u)*1) 0}
.small{font-size:calc(var(--u)*1.7);opacity:.85;margin-top:calc(var(--u)*.8)}
.or{margin:calc(var(--u)*1) 0;font-size:calc(var(--u)*1.9)}
.status{min-height:1.4em;color:#C94444;margin-top:calc(var(--u)*.6)}
.win{color:#2e9e57}.lose{color:#C94444}
.btn{font:inherit;font-weight:bold;font-size:calc(var(--u)*2.7);border:0;border-radius:calc(var(--u)*1.6);padding:calc(var(--u)*1.3) calc(var(--u)*3.2);cursor:pointer;color:#fff;background:#438FD1;margin:calc(var(--u)*.5);touch-action:manipulation}
.btn.y{background:#FFD84D;color:#173B72}
a.btn{display:inline-block;text-decoration:none}
.btn:active{transform:scale(.96)} .btn:disabled{opacity:.55}
.rpsrow{display:flex;gap:calc(var(--u)*1.4);justify-content:center;margin:calc(var(--u)*1) 0}
.btn.rps{font-size:calc(var(--u)*8);line-height:1;padding:calc(var(--u)*1.4) calc(var(--u)*2.4);background:#FFD84D;color:#173B72}
.btn.rps small{display:block;font-size:calc(var(--u)*1.7);margin-top:calc(var(--u)*.6)}
.btn.rps.sel{background:#55B879;color:#fff;transform:scale(1.08)}
.reveal{display:flex;align-items:center;justify-content:center;gap:calc(var(--u)*4);margin:calc(var(--u)*1)}
.hand{font-size:calc(var(--u)*11)} .vs{font-size:calc(var(--u)*3.4);color:#F4A340}
input{font:inherit;font-size:calc(var(--u)*3);width:calc(var(--u)*15);text-align:center;text-transform:uppercase;border:calc(var(--u)*.35) solid #173B72;border-radius:calc(var(--u)*1.4);padding:calc(var(--u)*1) 0;color:#173B72;-webkit-user-select:text;user-select:text}
#leave{position:absolute;top:1%;right:1%;display:none;width:calc(var(--u)*5);height:calc(var(--u)*5);border-radius:50%;border:0;background:#fff;color:#173B72;font-size:calc(var(--u)*2.6);font-weight:bold;opacity:.9;cursor:pointer}
#pad{display:none;position:relative;flex:none;width:var(--padsz);height:var(--padsz);border-radius:50%;background:rgba(23,59,114,.28);border:3px solid rgba(255,255,255,.75)}
#pad i{position:absolute;font-style:normal;color:#fff;font-size:calc(var(--padsz)*.15);transform:translate(-50%,-50%);pointer-events:none}
#knob{position:absolute;left:50%;top:50%;width:36%;height:36%;margin:-18% 0 0 -18%;border-radius:50%;background:#fff;opacity:.9;pointer-events:none}
@media (pointer:coarse){:root{--padsz:min(34vmin,220px)} #pad{display:block}}
@media (orientation:portrait){#app{flex-direction:column;justify-content:flex-start;padding-top:2vh} #stage{width:100vw} :root{--padsz:min(46vw,260px)}}
</style></head>
<body>
<div id="app">
  <div id="stage">
    <canvas id="cv" width="1000" height="720"></canvas>
    <div id="ui"></div>
    <button id="leave" onclick="toMenu('')">&#10005;</button>
  </div>
  <div id="pad"><i style="left:50%;top:12%">&#9650;</i><i style="left:50%;top:88%">&#9660;</i><i style="left:12%;top:50%">&#9664;</i><i style="left:88%;top:50%">&#9654;</i><div id="knob"></div></div>
</div>
<script>
"use strict";
const $=id=>document.getElementById(id);
const cv=$('cv'), ui=$('ui'), stage=$('stage'), pad=$('pad'), knob=$('knob');
let ctx=cv.getContext('2d');
const FONT='"Arial Rounded MT Bold","Trebuchet MS",Verdana,sans-serif';
const C={sky:'#8BDCF7',grass:'#78C968',grassL:'#82D072',grassD:'#55A84B',court:'#DDB77A',courtAlt:'#D5AD6E',line:'#FFF8E8',white:'#FFFFFF',black:'#292929',navy:'#173B72',blue:'#438FD1',blueD:'#2869A3',red:'#F05B5B',redD:'#C94444',yellow:'#FFD84D',orange:'#F4A340',skin:'#FFD0A6',hair:'#35251F'};
const PCOL=[C.red,C.yellow];
const CL=190,CR=810,CT=70,CB=550,L1=220,L2=385,MX=500,HUD=65;
const RPS=['\u270A','\u270B','\u270C\uFE0F'], RPSN=['Rock','Paper','Scissors'];

let ws=null, me=0, room='', lan='', lanAll=[], st=null, disp=null, view='menu', anim=0, last=0, goUntil=0, myChoice=null, connectTimer=null;
let offline=false, localSim=null;
const LSTART_X=[440,560], LSTART_Y=CB-35, LSPD=250, LGSPD=280, LHGSPD=240, LHIT=46, LROUNDS=4, LRT=20, LTAG=30, LREADY=3.0, LRESULT=2.5, LHURT=1.2;
let popups=[], lastSend=0, lastDx=9, lastDy=9, gotError=false, courtImg=null;
let mv=[false,false], gmv=[false,false,false];
const keys=new Set(), padState={left:false,right:false,up:false,down:false};

/* ---------- drawing primitives ---------- */
function ell(x,y,rx,ry,f,s,lw){ctx.beginPath();ctx.ellipse(x,y,Math.abs(rx),Math.abs(ry),0,0,6.2832);if(f){ctx.fillStyle=f;ctx.fill();}if(s){ctx.lineWidth=lw||2;ctx.strokeStyle=s;ctx.stroke();}}
function box(x,y,w,h,f,s,lw){if(f){ctx.fillStyle=f;ctx.fillRect(x,y,w,h);}if(s){ctx.lineWidth=lw||2;ctx.strokeStyle=s;ctx.strokeRect(x,y,w,h);}}
function ln(x1,y1,x2,y2,c,w){ctx.beginPath();ctx.moveTo(x1,y1);ctx.lineTo(x2,y2);ctx.strokeStyle=c;ctx.lineWidth=w;ctx.lineCap='round';ctx.stroke();}
function txt(t,x,y,size,f,sh,al){ctx.font='bold '+size+'px '+FONT;ctx.textAlign=al||'center';ctx.textBaseline='middle';if(sh){ctx.fillStyle=sh;ctx.fillText(t,x+3,y+4);}ctx.fillStyle=f;ctx.fillText(t,x,y);}
function cardBox(x1,y1,x2,y2){box(x1+8,y1+8,x2-x1,y2-y1,'#6BBFDC');box(x1,y1,x2-x1,y2-y1,C.white,C.navy,4);}
function cloud(x,y,s){[[0,15,65,48],[20,0,75,48],[48,12,105,48]].forEach(([a,b,c,d])=>ell(x+(a+c)/2*s,y+(b+d)/2*s,(c-a)/2*s,(d-b)/2*s,C.white));}
function tree(x,y,s){box(x-12*s,y,24*s,75*s,'#9A6237','#74421F',2);[[-55,-50,5,25],[-5,-70,55,20],[-40,-85,35,-5]].forEach(([a,b,c,d])=>ell(x+(a+c)/2*s,y+(b+d)/2*s,(c-a)/2*s,(d-b)/2*s,C.grassD));}
function marker(x,y){const b=Math.sin(anim*.5)*3;ctx.beginPath();ctx.moveTo(x-8,y-46+b);ctx.lineTo(x+8,y-46+b);ctx.lineTo(x,y-34+b);ctx.closePath();ctx.fillStyle=C.yellow;ctx.fill();ctx.lineWidth=2;ctx.strokeStyle=C.black;ctx.stroke();}

function person(x,y,shirt,s,phase,amp){
  s=s||1;phase=phase||0;amp=amp===undefined?7:amp;
  const sn=Math.sin(phase),sw=sn*amp,ll=amp?4*Math.max(0,sn):0,rl=amp?4*Math.max(0,-sn):0,ow=Math.max(1,2*s),lw=Math.max(3,6*s);
  const O=(x1,y1,x2,y2,f,o,w)=>ell(x+(x1+x2)/2*s,y+(y1+y2)/2*s,(x2-x1)/2*s,(y2-y1)/2*s,f,o||C.black,w||ow);
  const R=(x1,y1,x2,y2,f)=>box(x+x1*s,y+y1*s,(x2-x1)*s,(y2-y1)*s,f,C.black,ow);
  const L=(x1,y1,x2,y2)=>ln(x+x1*s,y+y1*s,x+x2*s,y+y2*s,C.skin,lw);
  ctx.globalAlpha=.25;ell(x,y+88*s,20*s,5*s,'#000');ctx.globalAlpha=1;
  O(-16,-16,16,16,C.skin);O(-16,-21,16,2,C.hair,C.hair,1);O(-8,-3,-5,0,C.black,C.black,1);O(5,-3,8,0,C.black,C.black,1);
  R(-16,15,16,48,shirt);L(-14,20,-26+sw,38);L(14,20,26-sw,38);
  R(-14,48,14,66,C.navy);const lx=-10+sw,rx=10-sw;
  L(-7,65,lx,83-ll);L(7,65,rx,83-rl);O(lx-8,78-ll,lx+8,88-ll,C.white);O(rx-8,78-rl,rx+8,88-rl,C.white);
}

function buildCourt(){
  const o=document.createElement('canvas');o.width=1000;o.height=655;const main=ctx;ctx=o.getContext('2d');
  for(let i=0;i<655;i+=55)box(0,i,1000,55,(i/55)%2?C.grassL:C.grass);
  cloud(30,20,.7);cloud(800,30,.7);tree(70,300,.65);tree(930,300,.65);
  [[CT,L1],[L1,L2],[L2,CB]].forEach(([a,b],i)=>box(CL,a,CR-CL,b-a,i%2?C.courtAlt:C.court));
  for(let k=0;k<31;k++)for(let r=0;r<2;r++)box(CL+k*20,CT+r*10,20,10,(k+r)%2?C.white:C.black);
  box(CL,CT,CR-CL,CB-CT,null,C.line,8);
  [L1,L2].forEach(y=>ln(CL,y,CR,y,C.line,7));ln(MX,CT,MX,CB,C.line,7);
  txt('FINISH',500,40,18,C.navy);txt('START',500,575,18,C.navy);
  ctx=main;courtImg=o;
}

function drawMenu(t){
  box(0,0,1000,720,C.sky);ell(890,65,40,40,C.yellow);box(0,520,1000,200,C.grass);
  cloud(((t*20)%1300)-150,70,.9);cloud(((t*14+500)%1300)-150,120,.8);
  tree(75,440,.9);tree(925,440,.9);
  for(let i=0;i<4;i++){const x=((t*60+i*300)%1300)-150;person(x,585+Math.sin(t*3+i)*3,i%2?C.yellow:C.red,.7,t*9+i*2,7);}
}

/* ---------- world ---------- */
function smooth(dt){
  const k=1-Math.exp(-dt*20);
  st.p.forEach((p,i)=>{const d=disp.p[i];if(Math.abs(p[0]-d[0])>150||Math.abs(p[1]-d[1])>150){d[0]=p[0];d[1]=p[1];}
    mv[i]=Math.abs(p[0]-d[0])+Math.abs(p[1]-d[1])>2;d[0]+=(p[0]-d[0])*k;d[1]+=(p[1]-d[1])*k;});
  st.g.forEach((g,i)=>{const d=disp.g[i];gmv[i]=Math.abs(g[0]-d[0])+Math.abs(g[1]-d[1])>2;d[0]+=(g[0]-d[0])*k;d[1]+=(g[1]-d[1])*k;});
  popups.forEach(p=>{p.y-=45*dt;p.life-=dt;});popups=popups.filter(p=>p.life>0);
}

function drawWorld(){
  const vs=st.mode==='versus',runner=st.rn,guard=1-runner,ents=[];
  st.g.forEach((g,i)=>ents.push({y:disp.g[i][1],k:'g',i}));
  if(vs){if(st.on[runner])ents.push({y:disp.p[runner][1],k:'p',i:runner});}
  else st.p.forEach((p,i)=>{if(st.on[i])ents.push({y:disp.p[i][1],k:'p',i});});
  ents.sort((a,b)=>a.y-b.y);
  for(const e of ents){
    if(e.k==='g'){
      const x=disp.g[e.i][0],y=disp.g[e.i][1];
      if(vs&&e.i===2){person(x,y,PCOL[guard],.75,gmv[2]?anim:0,gmv[2]?7:0);
        if(guard===me)marker(x,y);else txt('P'+(guard+1),x,y-38,14,C.navy);}
      else if(st.g[e.i][2])person(x,y,C.blue,.75,anim);
      else person(x,y,C.blueD,.75,anim*.2,3);
    }else{
      const x=disp.p[e.i][0],y=disp.p[e.i][1],done=st.p[e.i][2],hurt=st.p[e.i][3],m=mv[e.i]&&!done;
      if(hurt>0&&Math.floor(anim*.35)%2===0)continue;
      if(e.i===me)ell(x,y+76,30,6,null,C.yellow,4);
      person(x,y-(m?Math.abs(Math.sin(anim))*3:0),PCOL[e.i],.85,m?anim:0,m?7:0);
      if(done)txt('SAFE \u2713',x,y-38,14,C.navy);
      else if(e.i===me)marker(x,y);else txt('P'+(e.i+1),x,y-38,14,C.navy);
    }
  }
  for(const p of popups)txt(p.t,p.x,p.y,24,p.c,C.navy);
}

function drawOverlay(){
  const ph=st.ph,run=st.rn===me;
  if(ph==='ready'){
    if(st.mode==='versus'){
      txt('ROUND '+st.rd+' OF '+st.tot,500,170,34,C.white,C.navy);
      txt(run?'YOU RUN!  Cross both lines and reach the FINISH':'YOU GUARD!  Slide \u2190 \u2192 on the bottom line and TAG the runner',500,225,22,C.white,C.navy);
    }else{
      txt('GET READY!',500,170,34,C.white,C.navy);
      txt('Both of you run!  Dodge the guards and reach the FINISH',500,225,22,C.white,C.navy);
    }
    txt(String(Math.max(1,Math.ceil(st.tm))),500,320,80,C.yellow,C.navy);
  }else if(ph==='play'&&performance.now()<goUntil){txt('GO!',500,300,70,C.white,C.navy);}
  else if(ph==='result'){cardBox(220,200,780,370);txt(st.msg,500,258,20,C.navy);txt('P1: '+st.rs[0]+'     P2: '+st.rs[1],500,318,28,C.orange);}
  else if(ph==='rpsshake'){
    const total=1.6,elapsed=total-st.tm,seg=total/3,idx=Math.max(0,Math.min(2,Math.floor(elapsed/seg)));
    const words=['JACK','EN','POY!'],localT=Math.max(0,Math.min(1,(elapsed%seg)/seg)),bounce=Math.sin(localT*Math.PI)*55;
    txt(words[idx],500,150,54,C.yellow,C.navy);
    txt('\u270A',350,300-bounce,90,C.white,C.navy);txt('\u270A',650,300-bounce,90,C.white,C.navy);
    txt('PLAYER 1',350,395,18,C.white,C.navy);txt('PLAYER 2',650,395,18,C.white,C.navy);
  }
}

function drawHud(){
  box(0,0,1000,HUD,C.sky);
  txt('PATINTERO',25,33,27,C.white,C.navy,'left');
  if(!st)return;
  const vs=st.mode==='versus';
  txt(vs?'\u2B50 P1: '+st.rs[0]+'   P2: '+st.rs[1]:'\u2B50 TEAM SCORE: '+st.sc,vs?400:420,33,23,C.navy);
  if(!vs){txt('SAFE: '+st.p.filter(p=>p[2]).length+' / 2',900,33,22,C.navy,null,'right');return;}
  const inRound=['ready','play','result'].includes(st.ph);
  if(inRound){
    if(offline)txt('P'+(st.rn+1)+' RUNS  \u00B7  P'+(2-st.rn)+' GUARDS',630,33,19,C.navy);
    else txt(st.rn===me?'YOU: RUNNER':'YOU: GUARD',630,33,22,st.rn===me?C.redD:C.blueD);
  }
  if(inRound)txt('R'+Math.min(st.rd,st.tot)+'/'+st.tot+(st.ph==='play'?'  \u23F1'+Math.ceil(st.rt):''),900,33,22,C.navy,null,'right');
}

/* ---------- offline (same device, no server) ---------- */
function newLocalGuards(mode){
  const g=[{x:350,y:L1,dx:LGSPD,moving:true},{x:MX,y:300,dx:0,moving:false}];
  g.push(mode==='versus'?{x:MX,y:L2,dx:0,moving:false}:{x:650,y:L2,dx:-LGSPD,moving:true});
  return g;
}
function rpsBeat(a,b){return((a-b+3)%3)===1?0:(((b-a+3)%3)===1?1:-1);}
function LocalRoom(mode){
  return {
    mode, first:0, round:1, rs:[0,0], sc:0, msg:'', phase:'ready', timer:LREADY, ev:[], runner:0, roundTimer:LRT,
    rc:[null,null], rw:-1,
    guards:null, players:null,
    setupRound(){
      this.runner=(this.first+this.round-1)%2; this.roundTimer=LRT;
      this.guards=newLocalGuards(this.mode);
      this.players=[0,1].map(i=>({x:LSTART_X[i],y:LSTART_Y,dx:0,dy:0,crossed:[false,false],pts:0,done:false,hurt:0}));
    },
    step(dt){
      for(const g of this.guards){if(g.moving){g.x+=g.dx*dt;
        if(g.x<=CL+30){g.x=CL+30;g.dx=Math.abs(g.dx);}else if(g.x>=CR-30){g.x=CR-30;g.dx=-Math.abs(g.dx);}}}
      if(this.phase==='rpsshake'){
        this.timer-=dt;
        if(this.timer<=0){this.rw=rpsBeat(this.rc[0],this.rc[1]);this.phase='rpsreveal';this.timer=LRESULT;}
      }else if(this.phase==='rpsreveal'){
        this.timer-=dt;
        if(this.timer<=0){
          if(this.rw<0){this.rc=[null,null];this.phase='rps1';}
          else{this.first=this.rw;this.round=1;this.setupRound();this.phase='ready';this.timer=LREADY;}
        }
      }else if(this.phase==='ready'){this.timer-=dt;if(this.timer<=0)this.phase='play';}
      else if(this.phase==='result'){this.timer-=dt;if(this.timer<=0)this.nextRound();}
      this.ev=[];
      if(this.phase==='play'){this.mode==='versus'?this.stepPlay(dt):this.stepCoop(dt);}
    },
    stepPlay(dt){
      const r=this.runner,p=this.players[r],gp=this.players[1-r],hg=this.guards[2];
      hg.x=Math.max(CL+30,Math.min(CR-30,hg.x+gp.dx*LHGSPD*dt));
      this.roundTimer-=dt;
      const dx=p.dx,dy=p.dy;
      if(dx||dy){const k=LSPD*dt/((dx&&dy)?1.414:1);
        p.x=Math.max(CL+30,Math.min(CR-30,p.x+dx*k));p.y=Math.max(CT+30,Math.min(CB-40,p.y+dy*k));}
      if(this.guards.some(g=>Math.hypot(p.x-g.x,p.y-g.y)<LHIT)){
        this.endRound('tag',1-r,LTAG,'Player '+(2-r)+' tagged Player '+(r+1)+'!',r);return;}
      [L2,L1].forEach((ly,i)=>{if(p.y<=ly&&!p.crossed[i]){p.crossed[i]=true;this.rs[r]+=10;this.ev.push(['+10',r]);}});
      if(p.y<=CT+30)this.endRound('+30',r,30,'Player '+(r+1)+' made it across the finish!');
      else if(this.roundTimer<=0)this.endRound('time',1-r,LTAG,"Time's up! The guards win the round.");
    },
    stepCoop(dt){
      this.players.forEach((p,pid)=>{
        if(p.done)return;
        if(p.hurt>0){p.hurt-=dt;return;}
        const dx=p.dx,dy=p.dy;
        if(dx||dy){const k=LSPD*dt/((dx&&dy)?1.414:1);
          p.x=Math.max(CL+30,Math.min(CR-30,p.x+dx*k));p.y=Math.max(CT+30,Math.min(CB-40,p.y+dy*k));}
        if(this.guards.some(g=>Math.hypot(p.x-g.x,p.y-g.y)<LHIT)){
          this.sc-=p.pts;this.ev.push(['caught',pid,p.pts]);
          Object.assign(p,{x:LSTART_X[pid],y:LSTART_Y,pts:0,crossed:[false,false],hurt:LHURT,dx:0,dy:0});return;}
        [L2,L1].forEach((ly,i)=>{if(p.y<=ly&&!p.crossed[i]){p.crossed[i]=true;p.pts+=10;this.sc+=10;this.ev.push(['+10',pid]);}});
        if(p.y<=CT+30){p.done=true;p.pts=0;this.sc+=30;this.ev.push(['+30',pid]);}
      });
      if(this.players.every(p=>p.done)){this.sc+=50;this.ev.push(['+50',-1]);this.phase='done';}
    },
    endRound(kind,winner,pts,msg,extra){this.rs[winner]+=pts;this.ev.push([kind,winner,pts,extra||0]);this.msg=msg+'   +'+pts;this.phase='result';this.timer=LRESULT;},
    nextRound(){this.round++;if(this.round>LROUNDS){this.phase='done';return;}this.setupRound();this.phase='ready';this.timer=2.0;},
    snapshot(){return{t:'s',ph:this.phase,tm:Math.max(0,this.timer),on:[true,true],rn:this.runner,rd:this.round,tot:LROUNDS,
      rc:this.rc,rw:this.rw,
      rt:Math.max(0,this.roundTimer),rs:this.rs,msg:this.msg,mode:this.mode,sc:this.sc,
      g:this.guards.map(g=>[g.x,g.y,g.moving?1:0]),p:this.players.map(p=>[p.x,p.y,p.done?1:0,p.hurt]),ev:this.ev};}
  };
}
function localPick(i){
  if(!offline||!localSim)return;
  if(localSim.phase==='rps1'){localSim.rc[0]=i;localSim.phase='rps2';}
  else if(localSim.phase==='rps2'){localSim.rc[1]=i;localSim.phase='rpsshake';localSim.timer=1.6;}
}
function localDirP1(){const k=keys;return[((k.has('d')?1:0)-(k.has('a')?1:0)),((k.has('s')?1:0)-(k.has('w')?1:0))];}
function localDirP2(){const k=keys;return[((k.has('arrowright')?1:0)-(k.has('arrowleft')?1:0)),((k.has('arrowdown')?1:0)-(k.has('arrowup')?1:0))];}
function startOffline(mode){
  if(ws){try{ws.close();}catch(e){}ws=null;}
  offline=true;me=-1;view='game';st=null;disp=null;popups=[];pad.style.display='none';
  localSim=LocalRoom(mode);localSim.setupRound();
  if(mode==='versus'){localSim.rc=[null,null];localSim.rw=-1;localSim.phase='rps1';localSim.timer=0;}
  else{localSim.phase='ready';localSim.timer=LREADY;}
  setUI('');$('leave').style.display='block';
}
function stepOffline(dt){
  const[dx1,dy1]=localDirP1(),[dx2,dy2]=localDirP2();
  localSim.players[0].dx=dx1;localSim.players[0].dy=dy1;
  localSim.players[1].dx=dx2;localSim.players[1].dy=dy2;
  localSim.step(dt);
  const snap=localSim.snapshot(),prevPh=st?st.ph:null;
  for(const ev of snap.ev){const k=ev[0];
    if(k==='tag')pop(snap.p[ev[3]],'TAGGED!  +'+ev[2],C.red);
    else if(k==='time')pop([500,300],"TIME'S UP!",C.red);
    else if(k==='+10')pop(snap.p[ev[1]],'+10',C.yellow);
    else if(k==='+30')pop(snap.p[ev[1]],'+30 FINISH!',C.orange);
    else if(k==='caught')pop(snap.p[ev[1]],ev[2]?'CAUGHT!  -'+ev[2]:'CAUGHT!',C.red);
    else if(k==='+50')pop([500,300],'+50 TEAM BONUS!',C.yellow);}
  st=snap;disp={p:snap.p.map(x=>[x[0],x[1]]),g:snap.g.map(x=>[x[0],x[1]])};
  mv=[dx1!==0||dy1!==0,dx2!==0||dy2!==0];
  gmv=[snap.g[0][2]===1,false,localSim.mode==='versus'?(localSim.players[1-localSim.runner].dx!==0):(snap.g[2][2]===1)];
  popups.forEach(x=>{x.y-=45*dt;x.life-=dt;});popups=popups.filter(x=>x.life>0);
  if(prevPh!==snap.ph)phaseUI();
}

/* ---------- input ---------- */
function dir(){
  const k=keys;
  const dx=((k.has('arrowright')||k.has('d')||padState.right)?1:0)-((k.has('arrowleft')||k.has('a')||padState.left)?1:0);
  const dy=((k.has('arrowdown')||k.has('s')||padState.down)?1:0)-((k.has('arrowup')||k.has('w')||padState.up)?1:0);
  return [dx,dy];
}
function sendInput(now){
  const [dx,dy]=dir();
  if(dx!==lastDx||dy!==lastDy||now-lastSend>100){send({t:'in',dx,dy});lastDx=dx;lastDy=dy;lastSend=now;}
}
addEventListener('keydown',e=>{
  const k=e.key.toLowerCase();
  if(e.target.tagName==='INPUT'){if(k==='enter')joinGame();return;}
  if(k.startsWith('arrow')||k===' ')e.preventDefault();
  if(k==='escape'&&view==='game'){toMenu('');return;}
  keys.add(k);
});
addEventListener('keyup',e=>keys.delete(e.key.toLowerCase()));
addEventListener('blur',()=>keys.clear());

let padOn=false;
function padUpdate(e){
  const r=pad.getBoundingClientRect();
  const x=Math.max(-1,Math.min(1,(e.clientX-r.left)/r.width*2-1)),y=Math.max(-1,Math.min(1,(e.clientY-r.top)/r.height*2-1));
  padState.left=x<-.28;padState.right=x>.28;padState.up=y<-.28;padState.down=y>.28;
  knob.style.transform='translate('+(x*45)+'%,'+(y*45)+'%)';
}
function padOff(){padOn=false;padState.left=padState.right=padState.up=padState.down=false;knob.style.transform='none';}
pad.addEventListener('pointerdown',e=>{e.preventDefault();padOn=true;pad.setPointerCapture(e.pointerId);padUpdate(e);});
pad.addEventListener('pointermove',e=>{if(padOn)padUpdate(e);});
['pointerup','pointercancel'].forEach(ev=>pad.addEventListener(ev,padOff));

/* ---------- networking ---------- */
function send(o){if(ws&&ws.readyState===1)ws.send(JSON.stringify(o));}
function setStatus(t){const s=$('status');if(s)s.textContent=t;}
function connect(q){
  if(ws)return;gotError=false;setStatus('Connecting\u2026');
  let sock;
  try{sock=ws=new WebSocket((location.protocol==='https:'?'wss':'ws')+'://'+location.host+'/ws?'+q);}
  catch(e){setStatus('Could not start the connection. Check the address and try again.');return;}
  clearTimeout(connectTimer);
  connectTimer=setTimeout(()=>{
    if(sock!==ws)return;
    gotError=true;ws=null;try{sock.close();}catch(e){}
    setStatus('Could not reach the game server. Make sure you\'re on the same Wi-Fi as the host, or ask them to check their firewall.');
  },8000);
  sock.onmessage=e=>{if(sock===ws)onMsg(JSON.parse(e.data));};
  sock.onclose=()=>{if(sock!==ws)return;clearTimeout(connectTimer);ws=null;
    if(view==='game')toMenu('Disconnected from the game');else if(!gotError)setStatus('Could not connect to the game server');};
}
function createGame(mode){connect('create=1&mode='+mode);}
function joinGame(){const c=($('code').value||'').trim().toUpperCase();if(c.length!==4){setStatus('Enter the 4-letter code');return;}connect('room='+encodeURIComponent(c));}
function toMenu(msg){const s=ws;ws=null;if(s)try{s.close();}catch(e){}offline=false;localSim=null;me=0;pad.style.display='';
  view='menu';st=null;disp=null;popups=[];$('leave').style.display='none';menuUI(msg);}
function onMsg(m){
  clearTimeout(connectTimer);
  if(m.t==='welcome'){me=m.id;room=m.room;lan=m.lan||'';lanAll=m.lanAll||(lan?[lan]:[]);view='game';st=null;disp=null;popups=[];myChoice=null;setUI('');$('leave').style.display='block';}
  else if(m.t==='error'){gotError=true;const s=ws;ws=null;if(s)try{s.close();}catch(e){}setStatus(m.msg);}
  else if(m.t==='s')applyState(m);
}
function pop(p,t,c){popups.push({x:p[0],y:p[1]-50,t,c,life:.9});}
function applyState(m){
  const prev=st;st=m;
  if(!disp)disp={p:m.p.map(p=>[p[0],p[1]]),g:m.g.map(g=>[g[0],g[1]])};
  if(prev&&prev.ph==='ready'&&m.ph==='play')goUntil=performance.now()+800;
  for(const ev of m.ev){const k=ev[0];
    if(k==='tag')pop(disp.p[ev[3]],'TAGGED!  +'+ev[2],C.red);
    else if(k==='time')pop([500,300],"TIME'S UP!",C.red);
    else if(k==='+10')pop(disp.p[ev[1]],'+10',C.yellow);
    else if(k==='+30')pop(disp.p[ev[1]],'+30 FINISH!',C.orange);
    else if(k==='caught')pop(disp.p[ev[1]],ev[2]?'CAUGHT!  -'+ev[2]:'CAUGHT!',C.red);
    else if(k==='+50')pop([500,300],'+50 TEAM BONUS!',C.yellow);}
  if(!prev||prev.ph!==m.ph||prev.rr!==m.rr){if(m.ph==='rps')myChoice=null;phaseUI();}
  if(m.ph==='rps'){const t=$('tm');if(t)t.textContent=Math.ceil(m.tm);const o=$('opp');if(o)o.textContent=m.ch[1-me]?'Opponent is ready \u2713':'Opponent is choosing\u2026';}
}

/* ---------- DOM screens ---------- */
function setUI(h){ui.innerHTML=h;ui.style.display=h?'flex':'none';}
function menuUI(msg){
  const pre=(new URLSearchParams(location.search).get('room')||'').replace(/[^A-Za-z]/g,'').slice(0,4);
  setUI('<div class="card"><h1>PATINTERO</h1><div class="sub">Takbo \u2022 Iwas \u2022 Pumasa</div>'+
   '<div class="or">create a game</div>'+
   '<div><button class="btn y" onclick="createGame(\'coop\')">\uD83E\uDD1D CO-OP</button><button class="btn y" onclick="createGame(\'versus\')">\u2694\uFE0F VERSUS</button></div>'+
   '<div class="small">CO-OP: both run past the guards \u2022 VERSUS: runners vs guards</div>'+
   '<div class="or">\u2014 or join a friend \u2014</div>'+
   '<div><input id="code" maxlength="4" placeholder="CODE" value="'+pre+'" autocapitalize="characters" autocomplete="off"><button class="btn" onclick="joinGame()">\uD83C\uDF10 JOIN</button></div>'+
   '<div id="status" class="status">'+(msg||'')+'</div>'+
   '<div class="or">\u2014 or play offline on this device (optional) \u2014</div>'+
   '<div><button class="btn" onclick="startOffline(\'coop\')">\uD83E\uDD1D CO-OP</button><button class="btn" onclick="startOffline(\'versus\')">\u2694\uFE0F VERSUS</button></div>'+
   '<div class="small">No internet or Wi-Fi needed. Share one keyboard \u2014 P1: WASD, P2: Arrow keys.</div>'+
   '<div class="small">2 players \u2022 in VERSUS, <b>Jack en poy</b> picks the team</div></div>');
}
function phaseUI(){
  const ph=st.ph;
  if(ph==='lobby')setUI('<div class="card"><div class="big">WAITING FOR PLAYER 2\u2026</div><div class="small">'+(st.mode==='versus'?'\u2694\uFE0F VERSUS':'\uD83E\uDD1D CO-OP')+'</div><div>Game code</div><div class="code">'+room+'</div>'+
    '<a class="btn y" href="'+mailto()+'">\uD83D\uDCE7 EMAIL INVITE</a><button class="btn" onclick="invite()">'+(navigator.share?'\uD83D\uDCE4 SHARE':'\uD83D\uDCCB COPY LINK')+'</button>'+
    '<div class="small">'+inviteUrl()+'</div><div class="small">'+(location.protocol==='https:'?'Works from anywhere \u2713':'Same Wi-Fi only \u2014 for another network, open this game through your tunnel link first')+'</div>'+
    (lanAll.length>1?'<div class="small">Link not working? Ask them to try: '+lanAll.map(a=>a+'/?room='+room).join('  \u2022  ')+'</div>':'')+
    '<div id="note" class="small"></div></div>');
  else if(ph==='rps')setUI('<div class="card"><div class="big">JACK EN POY!</div>'+
    '<div class="small">Winner\'s team <b>RUNS</b> first \u2022 the loser\'s team <b>guards</b> (taya)</div><div class="rpsrow">'+
    RPS.map((e,i)=>'<button class="btn rps" id="r'+i+'" onclick="pick('+i+')">'+e+'<small>'+RPSN[i]+'</small></button>').join('')+
    '</div><div>Time: <b id="tm">'+Math.ceil(st.tm)+'</b></div><div id="opp" class="small"></div></div>');
  else if(ph==='rpsr'){
    const w=st.rw,mine=st.rc[me],theirs=st.rc[1-me];
    const res=w<0?"IT'S A TIE! Throw again\u2026":(w===me?'YOU WIN! Your team RUNS first \uD83C\uDFC3':'You lost. Your team GUARDS first \uD83D\uDEE1');
    setUI('<div class="card"><div class="big">JACK EN POY!</div><div class="reveal"><div><span class="hand">'+RPS[mine]+'</span><br>YOU</div><div class="vs">VS</div><div><span class="hand">'+RPS[theirs]+'</span><br>THEM</div></div>'+
      '<div class="big '+(w<0?'':w===me?'win':'lose')+'">'+res+'</div></div>');
  }else if(ph==='rps1'||ph==='rps2'){
    const p1=ph==='rps1';
    setUI('<div class="card"><div class="big">'+(p1?'PLAYER 1':'PLAYER 2')+': CHOOSE!</div>'+
      '<div class="small">'+(p1?'Player 2, don\'t peek! \uD83D\uDE49':'Your turn now \u2014 pick your throw')+'</div><div class="rpsrow">'+
      RPS.map((e,i)=>'<button class="btn rps" onclick="localPick('+i+')">'+e+'<small>'+RPSN[i]+'</small></button>').join('')+
      '</div></div>');
  }else if(ph==='rpsshake'){setUI('');
  }else if(ph==='rpsreveal'){
    const w=st.rw,a=st.rc[0],b=st.rc[1];
    const res=w<0?"IT'S A TIE! Throw again\u2026":('PLAYER '+(w+1)+' WINS! Their team RUNS first \uD83C\uDFC3 \u2014 the other team guards (taya)');
    setUI('<div class="card"><div class="big">JACK EN POY!</div><div class="reveal"><div><span class="hand">'+RPS[a]+'</span><br>PLAYER 1</div><div class="vs">VS</div><div><span class="hand">'+RPS[b]+'</span><br>PLAYER 2</div></div>'+
      '<div class="big '+(w<0?'':'win')+'">'+res+'</div></div>');
  }else if(ph==='done'){
    const vs=st.mode==='versus',a=st.rs[0],b=st.rs[1];
    let t;
    if(!vs)t='TEAM VICTORY! \uD83C\uDFC6';
    else if(a===b)t="IT'S A DRAW!";
    else if(offline)t=(a>b?'PLAYER 1':'PLAYER 2')+' WINS! \uD83C\uDFC6';
    else t=(a>b)===(me===0)?'YOU WIN! \uD83C\uDFC6':'YOU LOST \u2014 GG!';
    setUI('<div class="card"><div class="big">'+t+'</div><div>'+(vs?'Final score':'Both players passed!')+'</div><div class="score">'+(vs?'P1 '+a+' \u2014 '+b+' P2':'\u2B50 '+st.sc)+'</div>'+
      '<button class="btn y" id="again" onclick="playAgain()">\u21BB PLAY AGAIN</button><button class="btn" onclick="toMenu(\'\')">\u2302 LEAVE</button></div>');
  }else setUI('');
}
function pick(i){
  if(myChoice!==null||!st||st.ph!=='rps')return;
  myChoice=i;send({t:'rps',c:i});
  for(let j=0;j<3;j++){const b=$('r'+j);if(b){b.disabled=true;b.classList.toggle('sel',j===i);}}
}
function playAgain(){
  if(offline){localSim.round=1;localSim.rs=[0,0];localSim.sc=0;localSim.msg='';localSim.setupRound();
    if(localSim.mode==='versus'){localSim.rc=[null,null];localSim.rw=-1;localSim.phase='rps1';localSim.timer=0;}
    else{localSim.phase='ready';localSim.timer=LREADY;}
    return;}
  send({t:'again'});const b=$('again');if(b){b.disabled=true;b.textContent='Waiting for partner\u2026';}
}
function inviteUrl(){
  const h=location.hostname,local=h==='localhost'||h==='127.0.0.1'||h==='[::1]'||h==='::1';
  return (local&&lan?lan:location.origin)+'/?room='+room;      // never hand out a "localhost" link
}
function mailto(){
  return 'mailto:?subject='+encodeURIComponent('Play Patintero with me!')+
    '&body='+encodeURIComponent('Join my Patintero game ('+(st.mode==='versus'?'Versus':'Co-op')+'):\n'+inviteUrl()+'\n\nGame code: '+room);
}
function copyText(t){
  try{if(navigator.clipboard&&window.isSecureContext){navigator.clipboard.writeText(t);return;}}catch(e){}
  const a=document.createElement('textarea');a.value=t;document.body.appendChild(a);a.select();
  try{document.execCommand('copy');}catch(e){}document.body.removeChild(a);
}
function invite(){
  const url=inviteUrl(),n=$('note');
  if(navigator.share)navigator.share({title:'Patintero',text:'Join my Patintero game!',url}).catch(()=>{});
  else{copyText(url);if(n)n.textContent='Link copied! Paste it into a message or email.';}
}
function fit(){stage.style.setProperty('--u',Math.max(stage.clientWidth/100,5.2)+'px');}
addEventListener('resize',fit);addEventListener('orientationchange',()=>setTimeout(fit,250));

/* ---------- main loop ---------- */
function frame(now){
  requestAnimationFrame(frame);
  const dt=Math.min((now-last)/1000,.05);last=now;anim+=dt*14;
  ctx.clearRect(0,0,1000,720);
  if(view==='menu'){drawMenu(now/1000);return;}
  box(0,0,1000,720,C.sky);ctx.drawImage(courtImg,0,HUD);
  if(offline){stepOffline(dt);ctx.save();ctx.translate(0,HUD);drawWorld();drawOverlay();ctx.restore();drawHud();return;}
  if(!st){txt('Connecting\u2026',500,360,30,C.white,C.navy);drawHud();return;}
  smooth(dt);
  ctx.save();ctx.translate(0,HUD);drawWorld();drawOverlay();ctx.restore();
  drawHud();sendInput(now);
}
buildCourt();fit();menuUI('');
{const pre=(new URLSearchParams(location.search).get('room')||'').replace(/[^A-Za-z]/g,'');if(pre.length===4)connect('room='+pre);}
requestAnimationFrame(frame);
</script></body></html>
"""

if __name__ == "__main__":
    import os
    # command-line arg > $PORT (set automatically by hosts like Render/Railway) > default
    chosen_port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", PORT))
    try:
        asyncio.run(main(chosen_port))
    except KeyboardInterrupt:
        print("\nStopped.")
