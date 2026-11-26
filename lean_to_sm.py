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
    .layout {{ display: grid; grid-template-columns: 1.5fr 1fr; height: calc(100vh - 64px); }}
    .sm-pane {{ overflow-y: auto; padding: 20px; display: flex; flex-direction: column; gap: 16px; }}
    .code-pane {{ overflow-y: auto; border-left: 1px solid var(--border); background: #0b1220; padding: 16px; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 13px; line-height: 1.55; }}
    .card {{ background: var(--panel); border: 1px solid var(--border); border-radius: 12px; padding: 14px; }}
    .card-head {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; font-size: 14px; font-weight: 600; }}
    .legend {{ display: flex; gap: 16px; font-size: 12px; color: var(--muted); align-items: center; }}
    .dot {{ width: 10px; height: 10px; border-radius: 50%; display: inline-block; margin-right: 5px; }}
    .code-line {{ display: flex; gap: 12px; padding: 1px 6px; border-radius: 4px; white-space: pre; }}
    .code-line.active {{ background: rgba(56, 189, 248, 0.22); outline: 1px solid var(--local); }}
    .ln {{ color: #64748b; user-select: none; }}
    svg {{ width: 100%; overflow: visible; }}
    .tactic-node {{ cursor: pointer; }}
    .tactic-node:hover rect {{ filter: brightness(1.2); }}
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
  </div>
</header>

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

function layoutSM(sm) {{
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

  const pos = {{}};
  const colW = 190, rowH = 74;
  let maxRow = 1;
  Object.entries(byLevel).forEach(([lv, ids]) => {{
    maxRow = Math.max(maxRow, ids.length);
    ids.forEach((id, idx) => {{
      pos[id] = {{ x: 60 + Number(lv) * colW, y: 46 + idx * rowH }};
    }});
  }});

  const maxLv = Math.max(0, ...Object.keys(byLevel).map(Number));
  return {{ pos, width: Math.max(520, (maxLv + 1) * colW + 80), height: Math.max(120, maxRow * rowH + 30) }};
}}

const pane = document.getElementById('sm-pane');
DATA.sms.forEach((sm, idx) => {{
  const card = document.createElement('div');
  card.className = 'card';
  const tacticCount = Object.values(sm.nodes).filter(n => n.kind === 'tactic').length;
  card.innerHTML = `<div class="card-head"><span>State Machine #${{idx + 1}}</span><span class="badge">${{tacticCount}} tattiche</span></div>`;

  const {{ pos, width, height }} = layoutSM(sm);
  const svgNS = 'http://www.w3.org/2000/svg';
  const svg = document.createElementNS(svgNS, 'svg');
  svg.setAttribute('viewBox', `0 0 ${{width}} ${{height}}`);
  svg.setAttribute('height', height);

  const defs = document.createElementNS(svgNS, 'defs');
  defs.innerHTML = `<marker id="arrow-${{idx}}" markerWidth="8" markerHeight="8" refX="7" refY="3" orient="auto"><path d="M0,0 L0,6 L7,3 z" fill="#64748b"/></marker>`;
  svg.appendChild(defs);

  sm.edges.forEach(e => {{
    const a = pos[e.src], b = pos[e.dst];
    if (!a || !b) return;
    const line = document.createElementNS(svgNS, 'path');
    const mx = (a.x + b.x) / 2;
    line.setAttribute('d', `M ${{a.x}} ${{a.y}} C ${{mx}} ${{a.y}}, ${{mx}} ${{b.y}}, ${{b.x}} ${{b.y}}`);
    line.setAttribute('fill', 'none');
    line.setAttribute('stroke', '#64748b');
    line.setAttribute('stroke-width', '1.6');
    line.setAttribute('marker-end', `url(#arrow-${{idx}})`);
    svg.appendChild(line);
  }});

  Object.values(sm.nodes).forEach(n => {{
    const p = pos[n.id];
    if (!p) return;
    if (n.kind === 'place') {{
      const g = document.createElementNS(svgNS, 'g');
      const c = document.createElementNS(svgNS, 'circle');
      c.setAttribute('cx', p.x); c.setAttribute('cy', p.y); c.setAttribute('r', 14);
      c.setAttribute('fill', n.initial ? '#14532d' : '#0f172a');
      c.setAttribute('stroke', '#22c55e'); c.setAttribute('stroke-width', n.initial ? '3' : '2');
      g.appendChild(c);
      const t = document.createElementNS(svgNS, 'text');
      t.setAttribute('x', p.x); t.setAttribute('y', p.y + 4);
      t.setAttribute('text-anchor', 'middle'); t.setAttribute('fill', '#e2e8f0');
      t.setAttribute('font-size', '10'); t.textContent = n.label;
      g.appendChild(t);
      svg.appendChild(g);
    }} else {{
      const isShared = sharedSet.has(n.eid);
      const g = document.createElementNS(svgNS, 'g');
      g.setAttribute('class', 'tactic-node');
      g.onclick = () => highlightLine(n.line);

      const textLabel = n.label.length > 22 ? n.label.slice(0, 21) + '…' : n.label;
      const boxW = Math.max(96, textLabel.length * 6.8 + 16);
      const rect = document.createElementNS(svgNS, 'rect');
      rect.setAttribute('x', p.x - boxW / 2); rect.setAttribute('y', p.y - 14);
      rect.setAttribute('width', boxW); rect.setAttribute('height', 28);
      rect.setAttribute('rx', 6);
      rect.setAttribute('fill', isShared ? '#451a03' : '#0c4a6e');
      rect.setAttribute('stroke', isShared ? '#f59e0b' : '#38bdf8');
      rect.setAttribute('stroke-width', '1.6');
      g.appendChild(rect);

      const title = document.createElementNS(svgNS, 'title');
      title.textContent = `Riga ${{n.line}}: ${{n.label}}`;
      g.appendChild(title);

      const t = document.createElementNS(svgNS, 'text');
      t.setAttribute('x', p.x); t.setAttribute('y', p.y + 4);
      t.setAttribute('text-anchor', 'middle'); t.setAttribute('fill', '#f8fafc');
      t.setAttribute('font-size', '11'); t.textContent = textLabel;
      g.appendChild(t);
      svg.appendChild(g);
    }}
  }});

  card.appendChild(svg);
  pane.appendChild(card);
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
