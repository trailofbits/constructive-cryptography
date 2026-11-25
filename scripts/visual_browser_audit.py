#!/usr/bin/env python3
"""
Rapid Multi-State Browser Visual & Prose Audit for ETH CADMO Informalization HTML.

Uses local Google Chrome (`--headless=new` + DevTools Protocol over Python stdlib
WebSockets — zero third-party packages required) to audit rendered HTML pages across
multiple interactive states:
  1. `collapsed` — initial Paper-mode view
  2. `partial`   — first few `⊕` toggles expanded + first inner diagram opened
  3. `expanded`  — `Expand proofs` clicked + all diagram disclosures opened

Checks real browser geometry (diagram left/right clipping, box-vs-label overlaps,
excessive height, raw multi-line ASCII equations inside diagrams) AND rendered
expanded `innerText` prose quality (missing spaces like `ThenSecure`, double
punctuation `.,`, bare `be a function`, broken grammar, raw Lean identifiers).

Usage:
  python3 scripts/visual_browser_audit.py \
    --base-url http://127.0.0.1:8765 \
    --screenshots-dir /tmp/visual_audit_shots \
    cc-validation/aead.html cc-validation/verbose_cc.html
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import socket
import struct
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


CHROME_CANDIDATES = [
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "google-chrome",
    "chromium",
    "chromium-browser",
]


def find_chrome() -> str:
    for cand in CHROME_CANDIDATES:
        if os.path.isabs(cand):
            if os.path.exists(cand):
                return cand
        else:
            from shutil import which
            found = which(cand)
            if found:
                return found
    raise RuntimeError("Google Chrome / Chromium binary not found")


class SimpleCDPClient:
    """Minimal stdlib-only RFC 6455 WebSocket client for Chrome DevTools Protocol."""

    def __init__(self, ws_url: str, timeout: float = 30.0) -> None:
        m = re.match(r"^ws://([^:/]+):(\d+)(/.*)$", ws_url)
        if not m:
            raise ValueError(f"Unsupported ws url: {ws_url}")
        host, port_s, path = m.group(1), m.group(2), m.group(3)
        self.sock = socket.create_connection((host, int(port_s)), timeout=timeout)
        key = base64.b64encode(os.urandom(16)).decode("ascii")
        req = (
            f"GET {path} HTTP/1.1\r\n"
            f"Host: {host}:{port_s}\r\n"
            f"Upgrade: websocket\r\n"
            f"Connection: Upgrade\r\n"
            f"Sec-WebSocket-Key: {key}\r\n"
            f"Sec-WebSocket-Version: 13\r\n\r\n"
        )
        self.sock.sendall(req.encode("ascii"))
        resp = b""
        while b"\r\n\r\n" not in resp:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise RuntimeError("WebSocket handshake failed")
            resp += chunk
        if b"101" not in resp.split(b"\r\n", 1)[0]:
            raise RuntimeError(f"WebSocket upgrade rejected: {resp[:200]!r}")
        self._buf = resp.split(b"\r\n\r\n", 1)[1]
        self._msg_id = 0
        self.events: List[Dict[str, Any]] = []

    def close(self) -> None:
        try:
            self.sock.close()
        except Exception:
            pass

    def _recv_exact(self, n: int) -> bytes:
        while len(self._buf) < n:
            chunk = self.sock.recv(65536)
            if not chunk:
                raise EOFError("WebSocket closed")
            self._buf += chunk
        out = self._buf[:n]
        self._buf = self._buf[n:]
        return out

    def _send_text(self, text: str) -> None:
        payload = text.encode("utf-8")
        mask = os.urandom(4)
        header = bytearray([0x81])
        ln = len(payload)
        if ln < 126:
            header.append(0x80 | ln)
        elif ln < 65536:
            header.append(0x80 | 126)
            header.extend(struct.pack("!H", ln))
        else:
            header.append(0x80 | 127)
            header.extend(struct.pack("!Q", ln))
        header.extend(mask)
        masked = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
        self.sock.sendall(bytes(header) + masked)

    def _recv_frame(self) -> Tuple[int, bytes]:
        b1, b2 = self._recv_exact(2)
        opcode = b1 & 0x0F
        masked = (b2 & 0x80) != 0
        ln = b2 & 0x7F
        if ln == 126:
            ln = struct.unpack("!H", self._recv_exact(2))[0]
        elif ln == 127:
            ln = struct.unpack("!Q", self._recv_exact(8))[0]
        mask = self._recv_exact(4) if masked else b""
        data = self._recv_exact(ln)
        if masked:
            data = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
        return opcode, data

    def _recv_message(self) -> str:
        chunks: List[bytes] = []
        while True:
            opcode, data = self._recv_frame()
            if opcode == 0x8:
                raise EOFError("WebSocket close frame")
            if opcode == 0x9:  # ping -> pong
                continue
            if opcode == 0xA:  # pong
                continue
            chunks.append(data)
            if opcode in (0x1, 0x2) or opcode == 0x0:
                return b"".join(chunks).decode("utf-8", errors="replace")

    def call(self, method: str, params: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        self._msg_id += 1
        cid = self._msg_id
        self._send_text(json.dumps({"id": cid, "method": method, "params": params or {}}))
        while True:
            raw = self._recv_message()
            msg = json.loads(raw)
            if msg.get("id") == cid:
                if "error" in msg:
                    raise RuntimeError(f"CDP error on {method}: {msg['error']}")
                return msg.get("result", {})
            self.events.append(msg)

    def eval_js(self, expr: str) -> Any:
        res = self.call("Runtime.evaluate", {
            "expression": expr,
            "returnByValue": True,
            "awaitPromise": True,
        })
        if "exceptionDetails" in res:
            raise RuntimeError(f"JS exception: {res['exceptionDetails']}")
        return res.get("result", {}).get("value")


AUDIT_JS = r"""
(() => {
  const docOverflow = Math.max(0, Math.round(document.documentElement.scrollWidth - document.documentElement.clientWidth));
  const katexErrors = document.querySelectorAll('.katex-error').length;

  // 1. Audit every visible .cadmo-diagram for clipping, physical overlap, excess height, raw ASCII blocks
  const diagramIssues = [];
  const diagrams = Array.from(document.querySelectorAll('.cadmo-diagram'));
  let visibleDiagCount = 0;

  for (let i = 0; i < diagrams.length; i++) {
    const card = diagrams[i];
    if (card.tagName === 'DETAILS' && !card.open) continue;
    const cr = card.getBoundingClientRect();
    if (cr.width < 10 || cr.height < 10) continue;
    const det = card.querySelector('details.ccw');
    if (det && !det.open) continue;
    visibleDiagCount++;

    // Find closest entry title for context
    const entryEl = card.closest('.cadmo-entry');
    const entryTitle = entryEl
      ? (entryEl.querySelector('.cadmo-entry-heading')?.innerText || '').trim().slice(0, 70)
      : 'document';

    // Check clipping against card box (excluding hidden popovers and <summary>)
    let leftClip = 0, rightClip = 0, maxChildW = 0;
    const checkEls = Array.from(card.querySelectorAll('.cc-node, .cc-interface-label, .cc-wire-label, .cc-literal, .cc-error, .cc-system, .cc-comparison'));
    for (const el of checkEls) {
      if (el.closest('.cc-inspector-body') || el.closest('.cc-source')) continue;
      const r = el.getBoundingClientRect();
      if (r.width === 0 || r.height === 0) continue;
      maxChildW = Math.max(maxChildW, Math.round(r.width));
      if (r.left < cr.left - 2) leftClip = Math.max(leftClip, Math.round(cr.left - r.left));
      if (r.right > cr.right + 2) rightClip = Math.max(rightClip, Math.round(r.right - cr.right));
    }

    // Check pairwise physical overlaps between .cc-node and .cc-wire-label / .cc-interface-label / sibling .cc-node
    const boxes = [];
    for (const el of card.querySelectorAll('.cc-node, .cc-wire-label, .cc-interface-label')) {
      if (el.closest('.cc-inspector-body') || el.closest('.cc-source')) continue;
      const r = el.getBoundingClientRect();
      if (r.width < 2 || r.height < 2) continue;
      boxes.push({
        el,
        cls: el.className,
        text: (el.innerText || '').replace(/\s+/g, ' ').trim().slice(0, 45),
        r
      });
    }
    const overlaps = [];
    for (let a = 0; a < boxes.length; a++) {
      for (let b = a + 1; b < boxes.length; b++) {
        const A = boxes[a], B = boxes[b];
        if (A.el.contains(B.el) || B.el.contains(A.el)) continue;
        const ox = Math.min(A.r.right, B.r.right) - Math.max(A.r.left, B.r.left);
        const oy = Math.min(A.r.bottom, B.r.bottom) - Math.max(A.r.top, B.r.top);
        if (ox > 4 && oy > 4) {
          overlaps.push(`${A.text} ∩ ${B.text} (${Math.round(ox)}x${Math.round(oy)}px)`);
        }
      }
    }

    // Check raw multi-line ASCII equation inside diagram
    let rawAsciiBlock = null;
    for (const lit of card.querySelectorAll('.cc-literal, .cc-error')) {
      if (lit.closest('.cc-inspector-body') || lit.closest('.cc-source')) continue;
      const t = (lit.innerText || '').trim();
      const lines = t.split('\n').filter(Boolean).length;
      if (lines >= 2 || t.length > 75 || t.includes('•') && t.length > 40) {
        rawAsciiBlock = t.replace(/\s+/g, ' ').slice(0, 90);
        break;
      }
    }

    const tall = Math.round(cr.height) > 420;
    if (leftClip > 0 || rightClip > 0 || overlaps.length > 0 || tall || rawAsciiBlock) {
      diagramIssues.push({
        index: i,
        entry: entryTitle,
        size: `${Math.round(cr.width)}x${Math.round(cr.height)}`,
        maxChildW,
        leftClip,
        rightClip,
        overlaps: overlaps.slice(0, 4),
        tall,
        rawAsciiBlock,
      });
    }
  }

  // 2. Collect rendered visible prose text (excluding hidden Lean disclosures, inspector drawers, buttons)
  const mainEl = document.querySelector('.cadmo-main') || document.body;
  const clone = mainEl.cloneNode(true);
  clone.querySelectorAll('.cc-source, .cc-inspector-body, .cadmo-diagram, .cadmo-axiom-link, .cadmo-goal-btn, .cadmo-toggle, .cadmo-origin-tag, script, style').forEach(el => el.remove());
  const proseText = (clone.textContent || '').replace(/[ \t]+/g, ' ');

  const prosePatterns = [
    ['missing-space-Then', /\bThen(?=[A-Z|0-9ΔΣΠ\[])/g],
    ['missing-space-WeHave', /\bWe have(?=[0-9A-ZΔΣΠ|\[])/g],
    ['double-punct', /(?<!i\.e)(?<!e\.g)\.,|,\./g],
    ['bare-be-a-function', /\bbe a function\b|\bbe functions\b/gi],
    ['raw-TypedDistinguisher', /\bTypedDistinguisher\b/g],
    ['broken-yields-grammar', /yields the resource [^.\n]{1,120} can be substituted/g],
    ['dup-distinguisher', /\bdistinguisher distinguisher\b/gi],
    ['clunky-calc-opener', /To prove the claim, proceeding through/g],
    ['raw-of-distance', /by substitution \(of distance\)/g],
    ['raw-lemma-names', /\b(?:hybrid ideal distance le|advantage le distance|edist smul le|collision win le|distance attach le|solvers winner)\b/gi],
    ['raw-DDE-kernelMass', /\b(?:kernelMass|revealMass|kernelLaw|isProbDist|QueryBounded|inputDomain)\b/g],
    ['tautological-eq', /\b([A-Za-z][A-Za-z0-9_]{1,12})\s*=\s*\1(?![A-Za-z0-9_'])/g],
    ['literal-dollar-math', /\$[A-Za-z0-9_\\]+\$/g],
    ['offline-tex-leak', /\b(?:leftarrow|rightarrow|hat[a-z]|tilde[a-z]|mathtt[A-Za-z0-9]|mathbin|begincases|endcases)\b/g],
  ];

  const proseIssues = [];
  for (const [name, re] of prosePatterns) {
    const matches = [];
    let m;
    while ((m = re.exec(proseText)) !== null && matches.length < 5) {
      if (name === 'tautological-eq') {
        const sym = m[1];
        if (['n', 'm', 'k', 'q', 'r', 'c', 'x', 'y', 'z', 'i', 'j', 'b', 'p', 't', 's', 'a', 'd'].includes(sym)) continue;
      }
      const start = Math.max(0, m.index - 25);
      const end = Math.min(proseText.length, m.index + m[0].length + 35);
      matches.push(proseText.slice(start, end).replace(/\s+/g, ' ').trim());
    }
    if (matches.length > 0) {
      proseIssues.push({ rule: name, count: matches.length, samples: matches });
    }
  }

  // Also check `by reflexivity` attached to ≈ (two different systems)
  const calcReflIssues = [];
  for (const row of document.querySelectorAll('.cadmo-calc-row, tr')) {
    const t = (row.innerText || '').replace(/\s+/g, ' ').trim();
    if (t.includes('by reflexivity') && t.includes('≈')) {
      calcReflIssues.push(t.slice(0, 110));
    }
  }
  if (calcReflIssues.length > 0) {
    proseIssues.push({ rule: 'misleading-by-reflexivity-on-approx', count: calcReflIssues.length, samples: calcReflIssues.slice(0, 3) });
  }

  return {
    docOverflow,
    katexErrors,
    totalDiagrams: diagrams.length,
    visibleDiagrams: visibleDiagCount,
    diagramIssues,
    proseIssues,
  };
})()
"""


def audit_pages(
    base_url: str,
    rel_paths: List[str],
    screenshots_dir: Optional[Path] = None,
    width: int = 1280,
    height: int = 900,
) -> Dict[str, Any]:
    chrome = find_chrome()
    user_data_dir = tempfile.mkdtemp(prefix="cadmo_visual_audit_")
    proc = subprocess.Popen(
        [
            chrome,
            "--headless=new",
            "--disable-gpu",
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--remote-debugging-port=0",
            f"--user-data-dir={user_data_dir}",
            f"--window-size={width},{height}",
            "about:blank",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    ws_url = None
    deadline = time.time() + 15.0
    stderr_lines: List[str] = []
    assert proc.stderr is not None
    while time.time() < deadline:
        line = proc.stderr.readline()
        if not line:
            if proc.poll() is not None:
                break
            time.sleep(0.05)
            continue
        stderr_lines.append(line)
        m = re.search(r"DevTools listening on (ws://\S+)", line)
        if m:
            # Fetch page target via /json
            port_m = re.search(r":(\d+)/", m.group(1))
            if port_m:
                port = port_m.group(1)
                targets = json.loads(urllib.request.urlopen(f"http://127.0.0.1:{port}/json").read())
                for t in targets:
                    if t.get("type") == "page" and t.get("webSocketDebuggerUrl"):
                        ws_url = t["webSocketDebuggerUrl"]
                        break
            break

    if not ws_url:
        proc.terminate()
        raise RuntimeError(f"Could not connect to Chrome CDP: {''.join(stderr_lines[-10:])}")

    client = SimpleCDPClient(ws_url, timeout=30.0)
    results: Dict[str, Any] = {}
    if screenshots_dir:
        screenshots_dir.mkdir(parents=True, exist_ok=True)

    try:
        client.call("Page.enable")
        client.call("Runtime.enable")
        client.call("Emulation.setDeviceMetricsOverride", {
            "width": width,
            "height": height,
            "deviceScaleFactor": 1,
            "mobile": False,
        })

        for rel in rel_paths:
            url = base_url.rstrip("/") + "/" + rel.lstrip("/")
            slug = re.sub(r"[^a-zA-Z0-9_-]+", "_", rel).strip("_")
            client.events.clear()
            client.call("Page.navigate", {"url": url})
            # Wait for document ready + CADMO mount
            for _ in range(60):
                ready = client.eval_js(
                    "document.readyState === 'complete' && document.querySelectorAll('.cadmo-entry').length > 0"
                )
                if ready:
                    break
                time.sleep(0.1)
            time.sleep(0.25)

            console_errors = [
                ev.get("params", {})
                for ev in client.events
                if ev.get("method") == "Runtime.exceptionThrown"
            ]

            page_report: Dict[str, Any] = {
                "url": url,
                "consoleErrors": len(console_errors),
                "states": {},
            }

            # State 1: collapsed
            page_report["states"]["collapsed"] = client.eval_js(AUDIT_JS)
            if screenshots_dir:
                shot = client.call("Page.captureScreenshot", {"format": "png"})
                (screenshots_dir / f"{slug}_collapsed.png").write_bytes(base64.b64decode(shot["data"]))

            # State 2: partial expand (click first 4 ⊕ toggles + open first inner diagram)
            client.eval_js("""
            (() => {
              const btns = Array.from(document.querySelectorAll('.cadmo-inline-toggle[aria-expanded="false"], .cadmo-toggle[aria-expanded="false"]')).slice(0, 4);
              btns.forEach(b => b.click());
              const firstInnerDiag = document.querySelector('details.cadmo-step-diagram, details.cadmo-calc-diagram');
              if (firstInnerDiag) firstInnerDiag.open = true;
              return btns.length;
            })()
            """)
            time.sleep(0.25)
            page_report["states"]["partial"] = client.eval_js(AUDIT_JS)

            # State 3: full expand (`Expand proofs` + open all diagram disclosures)
            client.eval_js("""
            (() => {
              for (const b of document.querySelectorAll('button')) {
                if ((b.textContent || '').trim() === 'Expand proofs') { b.click(); break; }
              }
              document.querySelectorAll('details.cadmo-diagram, .cadmo-diagram details.ccw').forEach(d => { d.open = true; });
              return true;
            })()
            """)
            time.sleep(0.35)
            page_report["states"]["expanded"] = client.eval_js(AUDIT_JS)
            if screenshots_dir:
                # Scroll to first diagram so screenshots actually display diagrams + theorem prose
                client.eval_js("""
                (() => {
                  const target = document.querySelector('.cadmo-entry-diagram') || document.querySelector('.cadmo-diagram');
                  if (target) target.scrollIntoView({ block: 'center' });
                })()
                """)
                time.sleep(0.15)
                shot = client.call("Page.captureScreenshot", {"format": "png"})
                (screenshots_dir / f"{slug}_expanded.png").write_bytes(base64.b64decode(shot["data"]))

            results[rel] = page_report
    finally:
        client.close()
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except Exception:
            proc.kill()
        import shutil
        shutil.rmtree(user_data_dir, ignore_errors=True)

    return results


def main() -> int:
    ap = argparse.ArgumentParser(description="Multi-state Chrome visual & prose audit for CADMO pages")
    ap.add_argument("--base-url", default="http://127.0.0.1:8765")
    ap.add_argument("--screenshots-dir", type=Path, default=None)
    ap.add_argument("--json-out", type=Path, default=None)
    ap.add_argument("--strict", action="store_true", help="Exit 1 if any diagram or prose issue is found")
    ap.add_argument("pages", nargs="+")
    args = ap.parse_args()

    report = audit_pages(args.base_url, args.pages, args.screenshots_dir)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2))

    total_diag_issues = 0
    total_prose_issues = 0
    for rel, pr in report.items():
        print(f"\n=== {rel} (consoleErr={pr['consoleErrors']}) ===")
        for st_name in ("collapsed", "partial", "expanded"):
            st = pr["states"][st_name]
            di = st["diagramIssues"]
            pi = st["proseIssues"]
            if st_name == "expanded":
                total_diag_issues += len(di)
                total_prose_issues += len(pi)
            print(f"  [{st_name:9s}] overflow={st['docOverflow']}px katexErr={st['katexErrors']} "
                  f"visDiag={st['visibleDiagrams']}/{st['totalDiagrams']} diagIssues={len(di)} proseIssues={len(pi)}")
            if st_name in ("collapsed", "expanded"):
                for d in di[:6]:
                    print(f"    DIAG[{d['index']}] {d['entry'][:42]} ({d['size']}, childW={d['maxChildW']}): "
                          f"clip=L{d['leftClip']}/R{d['rightClip']} ov={len(d['overlaps'])} tall={d['tall']} "
                          f"ascii={bool(d['rawAsciiBlock'])}")
                    for ov in d["overlaps"][:2]:
                        print(f"      OVERLAP: {ov}")
                if st_name == "expanded":
                    for p in pi:
                        print(f"    PROSE[{p['rule']}] x{p['count']}: {p['samples'][0]!r}")

    print(f"\nSUMMARY (expanded): total_diag_issues={total_diag_issues}, total_prose_issues={total_prose_issues}")
    if args.strict and (total_diag_issues > 0 or total_prose_issues > 0):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
