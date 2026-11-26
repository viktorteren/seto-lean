#!/usr/bin/env python3
"""
seto-lean: Extract a Transition System from a Lean 4 proof, decompose it into
interacting State Machines with Seto 2.0, and render an interactive HTML/SVG view.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


@dataclass
class TacticStep:
    line_no: int
    indent: int
    text: str
    kind: str  # "branch" | "tactic"


@dataclass
class ParsedProof:
    name: str
    start_line: int
    steps: list[TacticStep]


def parse_lean_proofs(lean_src: str) -> list[ParsedProof]:
    """Extract theorem/lemma tactic blocks from Lean 4 source."""
    lines = lean_src.splitlines()
    proofs: list[ParsedProof] = []
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:theorem|lemma|def|instance)\s+([A-Za-z0-9_'.]+)"
    )

    i = 0
    while i < len(lines):
        m = decl_re.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group(1)
        start_line = i + 1
        decl_indent = len(lines[i]) - len(lines[i].lstrip(" "))
        # Scan until ':= by' or next declaration
        j = i
        found_by = False
        while j < len(lines):
            if ":=" in lines[j] and re.search(r"\bby\b\s*(?:--.*)?$", lines[j]):
                found_by = True
                break
            if j > i and decl_re.match(lines[j]):
                break
            j += 1

        if not found_by:
            i += 1
            continue

        steps: list[TacticStep] = []
        k = j + 1
        while k < len(lines):
            raw = lines[k]
            stripped = raw.strip()
            if not stripped or stripped.startswith("--"):
                k += 1
                continue
            indent = len(raw) - len(raw.lstrip(" "))
            if indent <= decl_indent:
                break

            is_branch = stripped.startswith(("|", "·", "case ")) or ":=" in stripped and stripped.endswith("by")
            clean = stripped.lstrip("·.").strip()
            if clean:
                steps.append(TacticStep(
                    line_no=k + 1,
                    indent=indent,
                    text=clean,
                    kind="branch" if is_branch else "tactic",
                ))
            k += 1

        if steps:
            proofs.append(ParsedProof(name=name, start_line=start_line, steps=steps))
        i = k

    return proofs


def proof_to_ts_g(proof: ParsedProof, out_g: Path) -> tuple[dict[str, dict], int, int]:
    """
    Build a Transition System (.g) capturing sequential steps and case/have branches.
    Each branch under a branching tactic splits from the branch root state and
    converges to a join state so Seto can discover concurrent/independent proof lanes.
    """
    label_meta: dict[str, dict] = {}
    label_to_id: dict[str, str] = {}
    edges: list[tuple[str, str, str]] = []

    def get_eid(step: TacticStep) -> str:
        key = step.text
        if key not in label_to_id:
            eid = f"e{len(label_to_id)}"
            label_to_id[key] = eid
            label_meta[eid] = {
                "label": step.text,
                "line": step.line_no,
                "kind": step.kind,
            }
        return label_to_id[key]

    state_counter = 0

    def new_state() -> str:
        nonlocal state_counter
        s = f"s{state_counter}"
        state_counter += 1
        return s

    init_state = new_state()
    cur_state = init_state

    # Group steps by branch markers ('| ... =>', '·', 'case ...', 'have ... := by')
    idx = 0
    steps = proof.steps
    while idx < len(steps):
        st = steps[idx]
        if st.kind == "branch" and (st.text.startswith("|") or st.text.startswith("case ") or st.text.endswith("by")):
            branch_indent = st.indent
            branch_root = cur_state
            join_state = new_state()
            # Collect sibling branches at the same indentation
            while idx < len(steps):
                cur_step = steps[idx]
                if cur_step.indent < branch_indent:
                    break
                if cur_step.indent == branch_indent and cur_step.kind == "branch":
                    eid = get_eid(cur_step)
                    b_state = new_state()
                    edges.append((branch_root, eid, b_state))
                    idx += 1
                    # Inner steps of this branch
                    while idx < len(steps) and steps[idx].indent > branch_indent:
                        inner = steps[idx]
                        ieid = get_eid(inner)
                        nxt = new_state()
                        edges.append((b_state, ieid, nxt))
                        b_state = nxt
                        idx += 1
                    # Connect branch end to join_state via a close/qed step
                    done_step = TacticStep(cur_step.line_no, branch_indent, f"qed:{cur_step.text[:24]}", "tactic")
                    deid = get_eid(done_step)
                    edges.append((b_state, deid, join_state))
                else:
                    break
            cur_state = join_state
        else:
            eid = get_eid(st)
            nxt = new_state()
            edges.append((cur_state, eid, nxt))
            cur_state = nxt
            idx += 1

    # Close loop back to init_state so regions/SMs form clean cyclic/ergodic components if needed
    # (Optional: keep DAG-like TS; Seto handles both, and .g requires .inputs + .state graph + .marking)
    lines = [
        f".model {re.sub(r'[^A-Za-z0-9_]', '_', proof.name)}",
        f".inputs {' '.join(label_meta.keys())}",
        ".state graph",
    ]
    for src, eid, dst in edges:
        lines.append(f"{src} {eid} {dst}")
    lines.append(f".marking {{{init_state}}}")
    lines.append(".end")
    out_g.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return label_meta, state_counter, len(edges)


def find_seto_bin(explicit: Path | None) -> Path:
    if explicit and explicit.exists():
        return explicit.resolve()
    here = Path(__file__).resolve().parent
    candidates = [
        here / "deps" / "Seto" / "build_perf" / "Seto.exe",
        here / "deps" / "Seto" / "build" / "Seto.exe",
        here / "deps" / "Seto" / "build" / "Seto",
        here.parent / "Seto" / "build_perf" / "Seto.exe",
        here.parent / "Seto" / "build" / "Seto.exe",
    ]
    for c in candidates:
        if c.exists():
            return c.resolve()
    raise FileNotFoundError("Seto executable not found. Pass --seto-bin <path> or build deps/Seto.")


def parse_dot_sm(dot_text: str, label_meta: dict[str, dict]) -> dict:
    """Parse a Seto *_SM_*.dot file into nodes, edges, and initial place."""
    nodes: dict[str, dict] = {}
    edges: list[dict] = []
    initial_nodes: set[str] = set()
    in_initial = False
    in_transitions = False

    for raw in dot_text.splitlines():
        line = raw.strip()
        if line.startswith("subgraph initial_place"):
            in_initial = True
            in_transitions = False
            continue
        if line.startswith("subgraph place"):
            in_initial = False
            in_transitions = False
            continue
        if line.startswith("subgraph transitions"):
            in_initial = False
            in_transitions = True
            continue
        if line == "}":
            in_initial = False
            in_transitions = False
            continue

        nm = re.match(r'^([A-Za-z0-9_]+)\s*\[label\s*=\s*"([^"]+)"\];$', line)
        if nm:
            nid, lbl = nm.group(1), nm.group(2)
            if in_transitions:
                base_eid = lbl.split("/")[0]
                meta = label_meta.get(base_eid, {})
                nodes[nid] = {
                    "id": nid,
                    "kind": "tactic",
                    "eid": base_eid,
                    "label": meta.get("label", lbl),
                    "line": meta.get("line", 0),
                }
            else:
                nodes[nid] = {"id": nid, "kind": "place", "label": lbl, "initial": in_initial}
                if in_initial:
                    initial_nodes.add(nid)
            continue

        em = re.match(r'^([A-Za-z0-9_]+)\s*->\s*([A-Za-z0-9_]+);$', line)
        if em:
            edges.append({"src": em.group(1), "dst": em.group(2)})

    return {"nodes": nodes, "edges": edges, "initial": sorted(initial_nodes)}


def render_html(proof: ParsedProof, lean_src: str, sms: list[dict], num_states: int, num_edges: int, out_html: Path) -> None:
    # Compute shared tactics across >1 SM
    tactic_sm_count: dict[str, set[int]] = {}
    for idx, sm in enumerate(sms):
        for n in sm["nodes"].values():
            if n["kind"] == "tactic":
                tactic_sm_count.setdefault(n["eid"], set()).add(idx)

    shared_eids = {eid for eid, s in tactic_sm_count.items() if len(s) > 1}

    lean_lines_html = "\n".join(
        f'<div class="code-line" id="L{idx+1}"><span class="ln">{idx+1:>3}</span><span>{html.escape(line)}</span></div>'
        for idx, line in enumerate(lean_src.splitlines())
    )

    payload = {
        "proof_name": proof.name,
        "num_states": num_states,
        "num_edges": num_edges,
        "shared_eids": sorted(shared_eids),
        "sms": sms,
    }

    html_doc = f"""<!doctype html>
<html lang="it">
<head>
  <meta charset="utf-8" />
  <title>Seto-Lean — {html.escape(proof.name)}</title>
  <style>
    :root {{
      --bg: #0f172a; --panel: #1e293b; --border: #334155;
      --text: #e2e8f0; --muted: #94a3b8;
      --local: #38bdf8; --shared: #f59e0b; --place: #22c55e;
    }}
    * {{ box-sizing: border-box; }}
    body {{ margin: 0; font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: var(--bg); color: var(--text); }}
    header {{ padding: 16px 24px; border-bottom: 1px solid var(--border); display: flex; flex-wrap: wrap; gap: 16px; align-items: center; justify-content: space-between; }}
    header h1 {{ margin: 0; font-size: 18px; }}
    .stats {{ display: flex; gap: 12px; flex-wrap: wrap; }}
    .badge {{ background: var(--panel); border: 1px solid var(--border); border-radius: 999px; padding: 4px 12px; font-size: 13px; color: var(--muted); }}
    .badge b {{ color: var(--text); }}
    .layout {{ display: grid; grid-template-columns: 1.55fr 1fr; height: calc(100vh - 64px); }}
    .sm-pane {{ overflow-y: auto; padding: 16px; display: grid; grid-template-columns: repeat(auto-fit, minmax(340px, 1fr)); gap: 16px; align-content: start; }}
    .sm-pane.stacked {{ grid-template-columns: 1fr; }}
    .code-pane {{ overflow-y: auto; border-left: 1px solid var(--border); background: #0b1220; padding: 16px; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 13px; line-height: 1.55; }}
    .card {{ background: var(--panel); border: 1px solid var(--border); border-radius: 12px; padding: 14px; display: flex; flex-direction: column; }}
    .card-head {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; font-size: 14px; font-weight: 600; gap: 8px; flex-wrap: wrap; }}
    .card-tools {{ display: flex; gap: 6px; align-items: center; }}
    .btn {{ background: #0f172a; color: var(--text); border: 1px solid var(--border); border-radius: 6px; padding: 3px 9px; font-size: 12px; cursor: pointer; }}
    .btn:hover, .btn.active {{ border-color: var(--local); color: var(--local); }}
    .svg-wrap {{ width: 100%; height: 520px; overflow: hidden; border: 1px solid #263244; border-radius: 8px; background: #0b1220; cursor: grab; position: relative; }}
    .svg-wrap.grabbing {{ cursor: grabbing; }}
    .card.expanded .svg-wrap {{ height: 78vh; }}
    .legend {{ display: flex; gap: 16px; font-size: 12px; color: var(--muted); align-items: center; }}
    .dot {{ width: 10px; height: 10px; border-radius: 50%; display: inline-block; margin-right: 5px; }}
    .code-line {{ display: flex; gap: 12px; padding: 1px 6px; border-radius: 4px; white-space: pre; }}
    .code-line.active {{ background: rgba(56, 189, 248, 0.22); outline: 1px solid var(--local); }}
    .ln {{ color: #64748b; user-select: none; }}
    svg {{ width: 100%; height: 100%; display: block; }}
    .tactic-node {{ cursor: pointer; }}
    .tactic-node:hover rect {{ filter: brightness(1.2); }}
    .tactic-node.sync-selected rect {{ stroke: #fde047 !important; stroke-width: 3px !important; filter: drop-shadow(0 0 8px rgba(250, 204, 21, 0.75)); }}
    .tactic-node.dimmed {{ opacity: 0.35; }}
    .sync-banner {{ padding: 8px 16px; background: #1e293b; border-bottom: 1px solid var(--border); font-size: 13px; display: none; align-items: center; justify-content: space-between; gap: 12px; }}
    .sync-banner.visible {{ display: flex; }}
    @media (max-width: 960px) {{ .layout {{ grid-template-columns: 1fr; height: auto; }} }}
  </style>
</head>
<body>
<header>
  <div>
    <h1>Seto-Lean: <code>{html.escape(proof.name)}</code></h1>
  </div>
  <div class="legend">
    <span><i class="dot" style="background:var(--place)"></i>Stato di prova</span>
    <span><i class="dot" style="background:var(--local)"></i>Tattica locale (parallela)</span>
    <span><i class="dot" style="background:var(--shared)"></i>Sincronizzazione tra SM</span>
  </div>
  <div class="stats">
    <span class="badge">Stati TS: <b>{num_states}</b></span>
    <span class="badge">Transizioni: <b>{num_edges}</b></span>
    <span class="badge">State Machines: <b>{len(sms)}</b></span>
    <span class="badge">Sincronizzazioni: <b>{len(shared_eids)}</b></span>
    <button class="btn active" id="btn-cols" onclick="setCols(true)">Colonne affiancate</button>
    <button class="btn" id="btn-stack" onclick="setCols(false)">Impilate</button>
  </div>
</header>

<div class="sync-banner" id="sync-banner">
  <span id="sync-banner-text"></span>
  <button class="btn" onclick="clearSyncHighlight()">Deseleziona</button>
</div>

<div class="layout">
  <div class="sm-pane" id="sm-pane"></div>
  <div class="code-pane" id="code-pane">{lean_lines_html}</div>
</div>

<script>
const DATA = {json.dumps(payload)};
const sharedSet = new Set(DATA.shared_eids);

function highlightLine(ln) {{
  document.querySelectorAll('.code-line.active').forEach(el => el.classList.remove('active'));
  if (!ln) return;
  const el = document.getElementById('L' + ln);
  if (el) {{
    el.classList.add('active');
    el.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
  }}
}}

function clearSyncHighlight() {{
  document.querySelectorAll('.tactic-node.sync-selected').forEach(el => el.classList.remove('sync-selected'));
  document.querySelectorAll('.tactic-node.dimmed').forEach(el => el.classList.remove('dimmed'));
  document.getElementById('sync-banner').classList.remove('visible');
}}

function selectEidAcrossSMs(eid, label, line) {{
  highlightLine(line);
  const allNodes = document.querySelectorAll('.tactic-node');
  if (!eid) {{ clearSyncHighlight(); return; }}

  const matchingSMs = new Set();
  allNodes.forEach(el => {{
    const eids = (el.dataset.eids || '').split(',').filter(Boolean);
    const match = eids.includes(eid);
    el.classList.toggle('sync-selected', match);
    el.classList.toggle('dimmed', !match);
    if (match && el.dataset.smIdx !== undefined) {{
      matchingSMs.add(Number(el.dataset.smIdx) + 1);
    }}
  }});

  const banner = document.getElementById('sync-banner');
  const text = document.getElementById('sync-banner-text');
  const smList = Array.from(matchingSMs).sort((a, b) => a - b).map(i => `SM #${{i}}`).join(', ');
  const isShared = sharedSet.has(eid);
  text.innerHTML = `${{isShared ? '<b>Sincronizzazione</b>' : 'Tattica'}}: <code>${{label}}</code> (Riga ${{line}}) → presente in <b>${{matchingSMs.size}}</b> grafi (${{smList}})`;
  banner.classList.add('visible');
}}

function setCols(cols) {{
  const p = document.getElementById('sm-pane');
  p.classList.toggle('stacked', !cols);
  document.getElementById('btn-cols').classList.toggle('active', cols);
  document.getElementById('btn-stack').classList.toggle('active', !cols);
}}

/**
 * 1) Contract 1-in/1-out intermediate places so consecutive tactics connect directly.
 * 2) Merge consecutive linear non-branching tactics (with same shared/local status)
 *    into vertical blocks so long proofs stay compact and readable top-down.
 */
function compactSM(sm) {{
  const nodes = {{}};
  Object.entries(sm.nodes).forEach(([k, v]) => {{
    nodes[k] = {{ ...v, items: v.kind === 'tactic' ? [{{ label: v.label, line: v.line, eid: v.eid }}] : [] }};
  }});
  let edges = sm.edges.map(e => ({{ ...e }}));

  const buildAdj = () => {{
    const out = {{}}, inc = {{}};
    Object.keys(nodes).forEach(k => {{ out[k] = []; inc[k] = []; }});
    edges.forEach(e => {{
      if (nodes[e.src] && nodes[e.dst]) {{
        out[e.src].push(e.dst);
        inc[e.dst].push(e.src);
      }}
    }});
    return {{ out, inc }};
  }};

  // Step 1: bypass non-initial places with 1 in and 1 out
  let changed = true;
  while (changed) {{
    changed = false;
    const {{ out, inc }} = buildAdj();
    for (const id of Object.keys(nodes)) {{
      const n = nodes[id];
      if (n.kind === 'place' && !n.initial && inc[id].length === 1 && out[id].length === 1) {{
        const u = inc[id][0], v = out[id][0];
        if (u !== id && v !== id) {{
          edges = edges.filter(e => e.src !== id && e.dst !== id);
          edges.push({{ src: u, dst: v }});
          delete nodes[id];
          changed = true;
          break;
        }}
      }}
    }}
  }}

  // Step 2: merge consecutive linear tactics of the same kind (local vs shared)
  const isSpecial = (n) => {{
    const lbl = n.items[0]?.label || '';
    return lbl.startsWith('|') || lbl.startsWith('case ') || lbl.startsWith('qed:') || lbl.endsWith('by');
  }};
  changed = true;
  while (changed) {{
    changed = false;
    const {{ out, inc }} = buildAdj();
    for (const u of Object.keys(nodes)) {{
      const nu = nodes[u];
      if (nu.kind !== 'tactic' || out[u].length !== 1) continue;
      const v = out[u][0];
      const nv = nodes[v];
      if (!nv || nv.kind !== 'tactic' || inc[v].length !== 1 || u === v) continue;
      if (isSpecial(nu) || isSpecial(nv)) continue;
      const su = sharedSet.has(nu.eid), sv = sharedSet.has(nv.eid);
      if (su !== sv) continue;

      // Merge v into u
      nu.items.push(...nv.items);
      edges = edges.filter(e => !(e.src === u && e.dst === v));
      edges.forEach(e => {{ if (e.src === v) e.src = u; if (e.dst === v) e.dst = u; }});
      delete nodes[v];
      changed = true;
      break;
    }}
  }}

  // Deduplicate edges
  const seenE = new Set();
  edges = edges.filter(e => {{
    const k = e.src + '->' + e.dst;
    if (seenE.has(k) || e.src === e.dst) return false;
    seenE.add(k);
    return true;
  }});

  return {{ nodes, edges, initial: sm.initial.filter(id => nodes[id]) }};
}}

function nodeSize(n) {{
  if (n.kind === 'place') return {{ w: 32, h: 32 }};
  const count = n.items.length;
  const shown = count <= 4 ? n.items : [...n.items.slice(0, 3), {{ label: `… +${{count - 3}} altre tattiche`, line: n.items[0].line }}];
  const maxLen = Math.max(14, ...shown.map(it => Math.min(34, it.label.length)));
  const w = Math.min(280, Math.max(150, maxLen * 6.8 + 26));
  const h = 24 + shown.length * 16;
  return {{ w, h, shown }};
}}

function layoutSMVertical(sm) {{
  const adj = {{}};
  Object.keys(sm.nodes).forEach(k => adj[k] = []);
  sm.edges.forEach(e => {{ if (adj[e.src]) adj[e.src].push(e.dst); }});

  const roots = sm.initial.length ? sm.initial : [Object.keys(sm.nodes)[0]];
  const level = {{}};
  const q = [];
  roots.forEach(r => {{ if (r) {{ level[r] = 0; q.push(r); }} }});
  while (q.length) {{
    const u = q.shift();
    for (const v of (adj[u] || [])) {{
      if (level[v] === undefined) {{
        level[v] = level[u] + 1;
        q.push(v);
      }}
    }}
  }}
  Object.keys(sm.nodes).forEach(k => {{ if (level[k] === undefined) level[k] = 0; }});

  const byLevel = {{}};
  Object.entries(level).forEach(([id, lv]) => {{
    byLevel[lv] = byLevel[lv] || [];
    byLevel[lv].push(id);
  }});

  const sizes = {{}};
  Object.entries(sm.nodes).forEach(([id, n]) => {{ sizes[id] = nodeSize(n); }});

  const pos = {{}};
  let curY = 28;
  let maxW = 360;
  const maxLv = Math.max(0, ...Object.keys(byLevel).map(Number));
  for (let lv = 0; lv <= maxLv; lv++) {{
    const ids = byLevel[lv] || [];
    if (!ids.length) continue;
    const rowMaxH = Math.max(...ids.map(id => sizes[id].h));
    const totalRowW = ids.reduce((s, id) => s + sizes[id].w, 0) + Math.max(0, ids.length - 1) * 28;
    maxW = Math.max(maxW, totalRowW + 60);
    let curX = 30;
    ids.forEach(id => {{
      const sz = sizes[id];
      pos[id] = {{ x: curX + sz.w / 2, y: curY + rowMaxH / 2, w: sz.w, h: sz.h }};
      curX += sz.w + 28;
    }});
    curY += rowMaxH + 34;
  }}
  // Center rows horizontally
  for (let lv = 0; lv <= maxLv; lv++) {{
    const ids = byLevel[lv] || [];
    if (!ids.length) continue;
    const minX = Math.min(...ids.map(id => pos[id].x - pos[id].w / 2));
    const maxX = Math.max(...ids.map(id => pos[id].x + pos[id].w / 2));
    const shift = (maxW - (maxX - minX)) / 2 - minX;
    ids.forEach(id => {{ pos[id].x += shift; }});
  }}

  return {{ pos, sizes, width: maxW, height: Math.max(180, curY + 20) }};
}}

const pane = document.getElementById('sm-pane');
DATA.sms.forEach((rawSm, idx) => {{
  const sm = compactSM(rawSm);
  const card = document.createElement('div');
  card.className = 'card';
  const tacticCount = Object.values(rawSm.nodes).filter(n => n.kind === 'tactic').length;
  const blockCount = Object.values(sm.nodes).filter(n => n.kind === 'tactic').length;

  const head = document.createElement('div');
  head.className = 'card-head';
  head.innerHTML = `<span>State Machine #${{idx + 1}} <span class="badge">${{tacticCount}} tattiche · ${{blockCount}} blocchi</span></span>`;
  const tools = document.createElement('div');
  tools.className = 'card-tools';
  tools.innerHTML = `
    <button class="btn" data-act="in" title="Zoom in">+</button>
    <button class="btn" data-act="out" title="Zoom out">−</button>
    <button class="btn" data-act="fit" title="Adatta alla vista">Fit</button>
    <button class="btn" data-act="reset" title="Scala 1:1">100%</button>
    <button class="btn" data-act="expand" title="Espandi">⛶</button>
  `;
  head.appendChild(tools);
  card.appendChild(head);

  const wrap = document.createElement('div');
  wrap.className = 'svg-wrap';

  const {{ pos, sizes, width, height }} = layoutSMVertical(sm);
  const svgNS = 'http://www.w3.org/2000/svg';
  const svg = document.createElementNS(svgNS, 'svg');
  const vp = document.createElementNS(svgNS, 'g');

  const defs = document.createElementNS(svgNS, 'defs');
  defs.innerHTML = `<marker id="arrow-${{idx}}" markerWidth="8" markerHeight="8" refX="7" refY="3" orient="auto"><path d="M0,0 L0,6 L7,3 z" fill="#64748b"/></marker>`;
  svg.appendChild(defs);
  svg.appendChild(vp);

  sm.edges.forEach(e => {{
    const a = pos[e.src], b = pos[e.dst];
    if (!a || !b) return;
    const x1 = a.x, y1 = a.y + a.h / 2;
    const x2 = b.x, y2 = b.y - b.h / 2;
    const my = (y1 + y2) / 2;
    const line = document.createElementNS(svgNS, 'path');
    line.setAttribute('d', `M ${{x1}} ${{y1}} C ${{x1}} ${{my}}, ${{x2}} ${{my}}, ${{x2}} ${{y2}}`);
    line.setAttribute('fill', 'none');
    line.setAttribute('stroke', '#64748b');
    line.setAttribute('stroke-width', '1.6');
    line.setAttribute('marker-end', `url(#arrow-${{idx}})`);
    vp.appendChild(line);
  }});

  Object.values(sm.nodes).forEach(n => {{
    const p = pos[n.id];
    const sz = sizes[n.id];
    if (!p) return;
    if (n.kind === 'place') {{
      const g = document.createElementNS(svgNS, 'g');
      const c = document.createElementNS(svgNS, 'circle');
      c.setAttribute('cx', p.x); c.setAttribute('cy', p.y); c.setAttribute('r', 15);
      c.setAttribute('fill', n.initial ? '#14532d' : '#0f172a');
      c.setAttribute('stroke', '#22c55e'); c.setAttribute('stroke-width', n.initial ? '3' : '2');
      g.appendChild(c);
      const t = document.createElementNS(svgNS, 'text');
      t.setAttribute('x', p.x); t.setAttribute('y', p.y + 4);
      t.setAttribute('text-anchor', 'middle'); t.setAttribute('fill', '#e2e8f0');
      t.setAttribute('font-size', '10'); t.textContent = n.initial ? 'Start' : n.label;
      g.appendChild(t);
      vp.appendChild(g);
    }} else {{
      const isShared = sharedSet.has(n.eid);
      const firstLine = n.items[0]?.line || 0;
      const lastLine = n.items[n.items.length - 1]?.line || firstLine;
      const g = document.createElementNS(svgNS, 'g');
      g.setAttribute('class', 'tactic-node');
      g.dataset.eids = n.items.map(it => it.eid).filter(Boolean).join(',');
      g.dataset.smIdx = String(idx);
      g.addEventListener('click', ev => {{
        ev.stopPropagation();
        selectEidAcrossSMs(n.items[0]?.eid || n.eid, n.items[0]?.label || '', firstLine);
      }});

      const rect = document.createElementNS(svgNS, 'rect');
      rect.setAttribute('x', p.x - sz.w / 2); rect.setAttribute('y', p.y - sz.h / 2);
      rect.setAttribute('width', sz.w); rect.setAttribute('height', sz.h);
      rect.setAttribute('rx', 8);
      rect.setAttribute('fill', isShared ? '#451a03' : '#0c4a6e');
      rect.setAttribute('stroke', isShared ? '#f59e0b' : '#38bdf8');
      rect.setAttribute('stroke-width', '1.6');
      g.appendChild(rect);

      const title = document.createElementNS(svgNS, 'title');
      title.textContent = n.items.map(it => `L${{it.line}}: ${{it.label}}`).join('\\n');
      g.appendChild(title);

      // Header line range inside block
      const hdr = document.createElementNS(svgNS, 'text');
      hdr.setAttribute('x', p.x - sz.w / 2 + 10);
      hdr.setAttribute('y', p.y - sz.h / 2 + 14);
      hdr.setAttribute('fill', isShared ? '#fbbf24' : '#7dd3fc');
      hdr.setAttribute('font-size', '10');
      hdr.setAttribute('font-weight', '600');
      hdr.textContent = n.items.length > 1 ? `L${{firstLine}}–${{lastLine}} · ${{n.items.length}} passi` : `L${{firstLine}}`;
      g.appendChild(hdr);

      sz.shown.forEach((it, k) => {{
        const t = document.createElementNS(svgNS, 'text');
        t.setAttribute('x', p.x - sz.w / 2 + 10);
        t.setAttribute('y', p.y - sz.h / 2 + 30 + k * 16);
        t.setAttribute('fill', '#f8fafc');
        t.setAttribute('font-size', '11');
        t.setAttribute('font-family', 'ui-monospace, Consolas, monospace');
        const txt = it.label.length > 34 ? it.label.slice(0, 33) + '…' : it.label;
        t.textContent = txt;
        t.addEventListener('click', ev => {{
          ev.stopPropagation();
          selectEidAcrossSMs(it.eid, it.label, it.line);
        }});
        g.appendChild(t);
      }});
      vp.appendChild(g);
    }}
  }});

  wrap.appendChild(svg);
  card.appendChild(wrap);
  pane.appendChild(card);

  // Pan & Zoom state
  let scale = 1, tx = 16, ty = 16;
  const apply = () => vp.setAttribute('transform', `translate(${{tx}},${{ty}}) scale(${{scale}})`);
  const fitView = () => {{
    const r = wrap.getBoundingClientRect();
    const sx = (r.width - 24) / width;
    const sy = (r.height - 24) / height;
    scale = Math.max(0.08, Math.min(1.2, Math.min(sx, sy)));
    tx = 12;
    ty = Math.max(12, (r.height - height * scale) / 2);
    apply();
  }};
  requestAnimationFrame(fitView);

  wrap.addEventListener('wheel', e => {{
    e.preventDefault();
    const r = wrap.getBoundingClientRect();
    const mx = e.clientX - r.left;
    const my = e.clientY - r.top;
    const factor = e.deltaY < 0 ? 1.15 : 1 / 1.15;
    const next = Math.max(0.05, Math.min(6, scale * factor));
    tx = mx - (mx - tx) * (next / scale);
    ty = my - (my - ty) * (next / scale);
    scale = next;
    apply();
  }}, {{ passive: false }});

  let dragging = false, lx = 0, ly = 0;
  wrap.addEventListener('mousedown', e => {{
    dragging = true; lx = e.clientX; ly = e.clientY;
    wrap.classList.add('grabbing');
  }});
  window.addEventListener('mousemove', e => {{
    if (!dragging) return;
    tx += e.clientX - lx; ty += e.clientY - ly;
    lx = e.clientX; ly = e.clientY;
    apply();
  }});
  window.addEventListener('mouseup', () => {{
    if (dragging) {{ dragging = false; wrap.classList.remove('grabbing'); }}
  }});

  tools.addEventListener('click', e => {{
    const act = e.target?.dataset?.act;
    if (!act) return;
    const r = wrap.getBoundingClientRect();
    const cx = r.width / 2, cy = r.height / 2;
    if (act === 'in' || act === 'out') {{
      const factor = act === 'in' ? 1.25 : 0.8;
      const next = Math.max(0.05, Math.min(6, scale * factor));
      tx = cx - (cx - tx) * (next / scale);
      ty = cy - (cy - ty) * (next / scale);
      scale = next;
      apply();
    }} else if (act === 'fit') {{
      fitView();
    }} else if (act === 'reset') {{
      scale = 1; tx = 16; ty = 16; apply();
    }} else if (act === 'expand') {{
      card.classList.toggle('expanded');
      requestAnimationFrame(fitView);
    }}
  }});
}});
</script>
</body>
</html>
"""
    out_html.write_text(html_doc, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Visualize Lean 4 proofs as Seto State Machines")
    parser.add_argument("lean_file", type=Path, help="Input .lean file")
    parser.add_argument("--theorem", type=str, default=None, help="Specific theorem/lemma name")
    parser.add_argument("--seto-bin", type=Path, default=None, help="Path to Seto executable")
    parser.add_argument("--out", type=Path, default=Path("output/proof_sm.html"), help="Output HTML file")
    args = parser.parse_args()

    lean_src = args.lean_file.read_text(encoding="utf-8")
    proofs = parse_lean_proofs(lean_src)
    if not proofs:
        raise RuntimeError(f"No `:= by` proofs found in {args.lean_file}")

    proof = proofs[0]
    if args.theorem:
        matches = [p for p in proofs if p.name == args.theorem]
        if not matches:
            raise ValueError(f"Theorem '{args.theorem}' not found. Available: {[p.name for p in proofs]}")
        proof = matches[0]

    seto_bin = find_seto_bin(args.seto_bin)
    args.out.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="seto_lean_") as tmp_str:
        tmp_dir = Path(tmp_str)
        ts_path = tmp_dir / "proof.g"
        label_meta, num_states, num_edges = proof_to_ts_g(proof, ts_path)

        proc = subprocess.run(
            [str(seto_bin), str(ts_path), "SM", "O", f"--work-dir={tmp_dir}"],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            print(proc.stdout)
            print(proc.stderr)
            return proc.returncode

        dot_files = sorted(tmp_dir.glob("*_SM_*.dot"))
        if not dot_files:
            raise RuntimeError("Seto did not produce any *_SM_*.dot files")

        sms = [parse_dot_sm(df.read_text(encoding="utf-8", errors="replace"), label_meta) for df in dot_files]

    render_html(proof, lean_src, sms, num_states, num_edges, args.out)
    print(f"Generated {args.out} ({len(sms)} SMs from {num_states} states, {num_edges} transitions)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
