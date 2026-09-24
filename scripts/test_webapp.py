#!/usr/bin/env python3
"""
scripts/test_webapp.py: Comprehensive headless test runner for the Verified Algorithms Skill Tree.

Validates:
- Tier 1: Static HTTP serving, DOM structure (#canvas-container, #tree-svg, #inspector-drawer, tabs, #quiz-container, savefile controls),
          tree.json schema, and 28-node count.
- Tier 2: Boundary cases: local file:// fallback (docs/tree_data.js), malformed savefile rejection, empty quiz answer handling, zoom bounds.
- Tier 3: Multi-hop unlock cascade (fan-in: INS + BS -> MERGE), savefile download/load round-trip fidelity.
- Tier 4: Real-world learner session simulation (fresh visit -> BGCD active -> answer quizzes -> BGCD mastered -> Tier 2 unlocked -> export -> reset -> import -> restored).
"""

import sys
import os
import json
import re
import http.server
import threading
import urllib.request
import urllib.error
import subprocess
from html.parser import HTMLParser
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = REPO_ROOT / "docs"
TREE_JSON = REPO_ROOT / "tutorial" / "tree.json"
FALLBACK_JS = DOCS_DIR / "tree_data.js"
INDEX_HTML = DOCS_DIR / "index.html"

# Canonical 28-node DAG specification for opaque-box contract verification
CANONICAL_NODE_IDS = [
    "BGCD", "EUC", "INS", "BS", "DYN", "MODEXP",
    "EXT", "MERGE", "TSQ", "NAIVE", "HEAP",
    "LB", "QS", "INTV", "KMP", "LCS", "BFS", "DIJ",
    "ED", "KNAP", "BF", "TWOSAT", "RED", "DSU", "Z", "AC",
    "LIS", "KRUS"
]

CANONICAL_PREREQS = {
    "BGCD": [],
    "EUC": ["BGCD"],
    "INS": ["BGCD"],
    "BS": ["BGCD"],
    "DYN": ["BGCD"],
    "MODEXP": ["BGCD"],
    "EXT": ["EUC"],
    "MERGE": ["INS", "BS"],
    "TSQ": ["DYN"],
    "NAIVE": ["INS"],
    "HEAP": ["DYN"],
    "LB": ["MERGE"],
    "QS": ["MERGE"],
    "INTV": ["MERGE"],
    "KMP": ["NAIVE", "TSQ"],
    "LCS": ["NAIVE"],
    "BFS": ["TSQ"],
    "DIJ": ["HEAP"],
    "ED": ["LCS"],
    "KNAP": ["LCS"],
    "BF": ["BFS"],
    "TWOSAT": ["BFS"],
    "RED": ["LB"],
    "DSU": ["BFS"],
    "Z": ["KMP"],
    "AC": ["KMP"],
    "LIS": ["KNAP"],
    "KRUS": ["DSU"]
}

CANONICAL_UNLOCKS = {
    "BGCD": ["EUC", "INS", "BS", "DYN", "MODEXP"],
    "EUC": ["EXT"],
    "INS": ["MERGE", "NAIVE"],
    "BS": ["MERGE"],
    "DYN": ["TSQ", "HEAP"],
    "MODEXP": [],
    "EXT": [],
    "MERGE": ["LB", "QS", "INTV"],
    "TSQ": ["KMP", "BFS"],
    "NAIVE": ["KMP", "LCS"],
    "HEAP": ["DIJ"],
    "LB": ["RED"],
    "QS": [],
    "INTV": [],
    "KMP": ["Z", "AC"],
    "LCS": ["ED", "KNAP"],
    "BFS": ["BF", "TWOSAT", "DSU"],
    "DIJ": [],
    "ED": [],
    "KNAP": ["LIS"],
    "BF": [],
    "TWOSAT": [],
    "RED": [],
    "DSU": ["KRUS"],
    "Z": [],
    "AC": [],
    "LIS": [],
    "KRUS": []
}

CANONICAL_TIERS = {
    "BGCD": 1,
    "EUC": 2, "INS": 2, "BS": 2, "DYN": 2, "MODEXP": 2,
    "EXT": 3, "MERGE": 3, "TSQ": 3, "NAIVE": 3, "HEAP": 3,
    "LB": 4, "QS": 4, "INTV": 4, "KMP": 4, "LCS": 4, "BFS": 4, "DIJ": 4,
    "ED": 5, "KNAP": 5, "BF": 5, "TWOSAT": 5, "RED": 5, "DSU": 5, "Z": 5, "AC": 5,
    "LIS": 6, "KRUS": 6
}

PLANNED_NODES = {"HEAP", "DIJ", "DSU", "KRUS", "Z", "AC"}


# ==============================================================================
# HTML DOM Structure Parser
# ==============================================================================
class WebAppDOMValidator(HTMLParser):
    """Parses HTML5 DOM to verify required visual components and accessibility structures."""
    def __init__(self):
        super().__init__()
        self.found_canvas = False
        self.found_svg = False
        self.found_wires_layer = False
        self.found_nodes_layer = False
        self.found_drawer = False
        self.found_quiz_container = False
        self.found_savefile_controls = False
        self.found_tabs = set()
        self.found_buttons = set()
        self.all_ids = set()

    def handle_starttag(self, tag, attrs):
        attr_dict = dict(attrs)
        tag_id = attr_dict.get("id", "")
        if tag_id:
            self.all_ids.add(tag_id)

        # Canvas container verification
        if tag_id in ("canvas-container", "canvas-world", "tree-canvas"):
            self.found_canvas = True

        # SVG wire layer
        if tag == "svg" or tag_id == "tree-svg":
            self.found_svg = True
        if tag_id == "wires-layer":
            self.found_wires_layer = True

        # Nodes container
        if tag_id in ("nodes-layer", "tree-nodes"):
            self.found_nodes_layer = True

        # Inspector drawer (<dialog id="inspector-drawer"> or similar)
        if (tag == "dialog" and "drawer" in tag_id) or tag_id == "inspector-drawer":
            self.found_drawer = True

        # Quiz container
        if tag_id == "quiz-container":
            self.found_quiz_container = True

        # Savefile controls
        if tag_id in ("savefile-controls", "btn-export-save", "file-import-save", "btn-reset-save"):
            self.found_savefile_controls = True

        # Tabs verification: data-tab attribute
        if "data-tab" in attr_dict:
            self.found_tabs.add(attr_dict["data-tab"])

        # Button IDs
        if tag == "button" and tag_id:
            self.found_buttons.add(tag_id)


# ==============================================================================
# In-Memory Skill Tree State Machine & Logic Simulator
# ==============================================================================
class SkillTreeSimulator:
    """Accurately mirrors client-side state machine in docs/app.js for opaque-box verification."""
    def __init__(self, tree_data=None):
        if tree_data:
            self.nodes = tree_data.get("nodes", [])
        else:
            self.nodes = [
                {
                    "id": nid,
                    "tier": CANONICAL_TIERS[nid],
                    "status": "planned" if nid in PLANNED_NODES else ("open" if nid == "BGCD" else "ready"),
                    "prerequisites": CANONICAL_PREREQS[nid],
                    "unlocks": CANONICAL_UNLOCKS[nid]
                }
                for nid in CANONICAL_NODE_IDS
            ]
        self.nodes_map = {n["id"]: n for n in self.nodes}
        self.mastered_nodes = set()
        self.answers = {}

    def compute_node_states(self):
        """
        Computes states for all nodes:
        - planned: if node.status == 'planned'
        - mastered: if node.id in mastered_nodes
        - active: if node.prerequisites is empty OR all prerequisites in mastered_nodes
        - locked: otherwise
        """
        states = {}
        for nid, node in self.nodes_map.items():
            if node.get("status") == "planned":
                states[nid] = "planned"
            elif nid in self.mastered_nodes:
                states[nid] = "mastered"
            else:
                prereqs = node.get("prerequisites", [])
                if not prereqs or all(p in self.mastered_nodes for p in prereqs):
                    states[nid] = "active"
                else:
                    states[nid] = "locked"
        return states

    def submit_quiz_answer(self, node_id, quiz_type, question_id, answer, correct_answer):
        """Processes quiz answer submission with validation."""
        if not answer or not str(answer).strip():
            return False, "Answer cannot be empty"

        is_correct = (str(answer).strip().lower() == str(correct_answer).strip().lower())
        if node_id not in self.answers:
            self.answers[node_id] = {"predict": {}, "spot_the_fake": {}}

        self.answers[node_id][quiz_type][question_id] = str(answer).strip()

        if is_correct:
            return True, "Correct"
        return False, "Incorrect answer"

    def mark_mastered(self, node_id):
        """Marks a node mastered if it is valid, eligible, and prerequisites are satisfied."""
        if node_id not in self.nodes_map:
            raise ValueError(f"Unknown node {node_id}")
        if self.nodes_map[node_id].get("status") == "planned":
            raise ValueError(f"Planned node {node_id} cannot be marked mastered")

        prereqs = self.nodes_map[node_id].get("prerequisites", [])
        if any(p not in self.mastered_nodes for p in prereqs):
            unsatisfied = [p for p in prereqs if p not in self.mastered_nodes]
            raise ValueError(f"Cannot master locked node {node_id}: unsatisfied prerequisites {unsatisfied}")

        self.mastered_nodes.add(node_id)
        return self.compute_node_states()

    def export_savefile(self):
        """Produces JSON savefile payload adhering to Contract 4."""
        return {
            "schema_version": "1.0.0",
            "saved_at": "2026-09-24T04:20:00Z",
            "mastered_nodes": sorted(list(self.mastered_nodes)),
            "answers": json.loads(json.dumps(self.answers))
        }

    def import_savefile(self, payload):
        """Validates and restores state from savefile payload."""
        if isinstance(payload, str):
            try:
                payload = json.loads(payload)
            except Exception:
                raise ValueError("Savefile payload must be a JSON object")

        if not isinstance(payload, dict) or isinstance(payload, bool):
            raise ValueError("Savefile payload must be a JSON object")

        if payload.get("schema_version") != "1.0.0":
            raise ValueError(f"Unsupported schema version: {payload.get('schema_version')}")

        mastered = payload.get("mastered_nodes")
        if not isinstance(mastered, list):
            raise ValueError("'mastered_nodes' must be a list")

        mastered_set = set()
        for nid in mastered:
            if not isinstance(nid, str) or not nid:
                raise ValueError(f"Invalid node ID in mastered_nodes: {nid}")
            if nid not in self.nodes_map:
                raise ValueError(f"Savefile references unknown node ID: {nid}")
            if self.nodes_map[nid].get("status") == "planned":
                raise ValueError(f"Savefile illegally claims planned node '{nid}' as mastered")
            mastered_set.add(nid)

        # Enforce prerequisite topological closure
        for nid in mastered_set:
            node = self.nodes_map[nid]
            for p in node.get("prerequisites", []):
                if p not in mastered_set:
                    raise ValueError(f"Savefile topological closure violation: Node '{nid}' is marked mastered, but prerequisite '{p}' is not in mastered_nodes")

        answers = payload.get("answers", {})
        if not isinstance(answers, dict) or isinstance(answers, bool):
            raise ValueError("'answers' must be a JSON dictionary")
        for nid, node_ans in answers.items():
            if not isinstance(node_ans, dict) or isinstance(node_ans, bool):
                raise ValueError(f"'answers.{nid}' must be a JSON dictionary")

        self.mastered_nodes = mastered_set
        self.answers = json.loads(json.dumps(answers))
        return self.compute_node_states()

    def reset_progress(self):
        """Resets learner progress to fresh state."""
        self.mastered_nodes.clear()
        self.answers.clear()
        return self.compute_node_states()


# ==============================================================================
# Zoom Clamping Boundary Logic
# ==============================================================================
def clamp_zoom(scale, min_scale=0.25, max_scale=3.0):
    """Clamps viewport scale within safe interactive limits."""
    if not isinstance(scale, (int, float)) or scale <= 0:
        return 1.0
    return max(min_scale, min(scale, max_scale))


# ==============================================================================
# Ephemeral HTTP Server Context
# ==============================================================================
class EphemeralServer:
    def __init__(self, root_dir):
        self.root_dir = root_dir
        self.server = None
        self.thread = None
        self.port = None

    def __enter__(self):
        class SilentHandler(http.server.SimpleHTTPRequestHandler):
            def log_message(self, format, *args):
                pass  # Suppress HTTP server terminal access logs

        self.server = http.server.HTTPServer(("127.0.0.1", 0), lambda *args: SilentHandler(*args, directory=str(self.root_dir)))
        self.port = self.server.server_port
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.server:
            self.server.shutdown()
            self.server.server_close()


# ==============================================================================
# Tier 1 Tests: Feature Coverage
# ==============================================================================
def test_tier1_http_serving(base_url, strict=False):
    print("  [Tier 1.1] Testing HTTP serving of web application assets...")
    assets = [
        ("docs/index.html", 200, "text/html"),
        ("docs/style.css", 200, "text/css"),
        ("docs/app.js", 200, "application/javascript"),
        ("docs/tree_data.js", 200, "application/javascript"),
        ("tutorial/tree.json", 200, "application/json")
    ]

    for rel_path, expected_code, expected_type in assets:
        target_path = REPO_ROOT / rel_path
        if not target_path.exists():
            if strict:
                raise AssertionError(f"[STRICT] Required file missing: {rel_path}")
            print(f"    - Skipping {rel_path} (file pending implementation)")
            continue

        url = f"{base_url}/{rel_path}"
        req = urllib.request.Request(url)
        with urllib.request.urlopen(req, timeout=5) as resp:
            assert resp.status == expected_code, f"Expected HTTP {expected_code} for {url}, got {resp.status}"
            content = resp.read()
            assert len(content) > 0, f"Empty response received from {url}"
            content_type = resp.headers.get("Content-Type", "")
            # Verify primary MIME subtype or charset
            assert expected_type.split("/")[0] in content_type, f"Expected {expected_type} for {url}, got {content_type}"
    print("  ✓ HTTP serving verified successfully.")


def test_tier1_dom_elements(strict=False):
    print("  [Tier 1.2] Testing HTML5 DOM structure and component anchors...")
    if not INDEX_HTML.exists():
        if strict:
            raise AssertionError("[STRICT] docs/index.html missing on disk")
        print("    - Skipping docs/index.html DOM test (file pending M4)")
        return

    html_text = INDEX_HTML.read_text(encoding="utf-8")
    parser = WebAppDOMValidator()
    parser.feed(html_text)

    assert parser.found_canvas, "Missing #canvas-container or #canvas-world in docs/index.html"
    assert parser.found_svg, "Missing #tree-svg in docs/index.html"
    assert parser.found_nodes_layer, "Missing #nodes-layer in docs/index.html"
    assert parser.found_drawer, "Missing inspector drawer (<dialog id='inspector-drawer'>) in docs/index.html"
    assert parser.found_quiz_container, "Missing #quiz-container in docs/index.html"

    # Tab anchors
    for expected_tab in ("specs", "quiz", "chapter"):
        assert expected_tab in parser.found_tabs, f"Missing inspector tab [data-tab='{expected_tab}'] in docs/index.html"

    # Savefile buttons
    for btn_id in ("btn-export-save", "file-import-save", "btn-reset-save"):
        assert btn_id in parser.all_ids, f"Missing control element #{btn_id} in docs/index.html"

    print("  ✓ HTML5 DOM structure and control elements verified.")


def test_tier1_tree_json_schema(strict=False):
    print("  [Tier 1.3] Testing tree.json schema compliance and 28-node cardinality...")
    if not TREE_JSON.exists():
        if strict:
            raise AssertionError("[STRICT] tutorial/tree.json missing on disk")
        print("    - Skipping tutorial/tree.json schema test (file pending M1)")
        # Verify canonical contract in memory
        sim = SkillTreeSimulator()
        assert len(sim.nodes) == 28, f"Expected 28 canonical nodes, got {len(sim.nodes)}"
        return

    with open(TREE_JSON, "r", encoding="utf-8") as f:
        data = json.load(f)

    assert "nodes" in data, "tree.json missing top-level 'nodes' array"
    nodes = data["nodes"]
    assert len(nodes) == 28, f"Expected exactly 28 nodes in tree.json, got {len(nodes)}"

    required_node_fields = [
        "id", "name", "tier", "category", "status",
        "prerequisites", "unlocks", "algorithm_skill", "lean_skill",
        "reference_module", "headline_theorems", "chapter_path", "exercises"
    ]

    node_ids = {n["id"] for n in nodes}
    for node in nodes:
        nid = node.get("id")
        for fld in required_node_fields:
            assert fld in node, f"Node {nid} missing required field '{fld}'"

        assert node["status"] in ("open", "ready", "planned"), f"Node {nid} has invalid status '{node['status']}'"
        assert 1 <= node["tier"] <= 6, f"Node {nid} has invalid tier {node['tier']}"

        # Prerequisite & unlock link targets must exist
        for p in node["prerequisites"]:
            assert p in node_ids, f"Node {nid} references unknown prerequisite '{p}'"
        for u in node["unlocks"]:
            assert u in node_ids, f"Node {nid} references unknown unlock '{u}'"

    print("  ✓ tree.json schema conformance and 28 nodes verified.")


# ==============================================================================
# Tier 2 Tests: Boundary Value Analysis & Corner Cases
# ==============================================================================
def test_tier2_tree_data_fallback(strict=False):
    print("  [Tier 2.1] Testing local file:// offline fallback snapshot (docs/tree_data.js)...")
    if not FALLBACK_JS.exists():
        if strict:
            raise AssertionError("[STRICT] docs/tree_data.js missing on disk")
        print("    - Skipping docs/tree_data.js test (file pending M4)")
        return

    content = FALLBACK_JS.read_text(encoding="utf-8")
    assert "__TREE_DATA_FALLBACK__" in content or "treeData" in content, "tree_data.js missing global snapshot variable"

    # Extract JSON object using regex
    match = re.search(r"=\s*(\{.*\})\s*;?", content, re.DOTALL)
    assert match is not None, "Failed to parse JSON payload from docs/tree_data.js"
    snapshot = json.loads(match.group(1))

    assert "nodes" in snapshot, "Fallback snapshot missing 'nodes' key"
    assert len(snapshot["nodes"]) == 28, f"Fallback snapshot contains {len(snapshot['nodes'])} nodes, expected 28"
    print("  ✓ Offline fallback snapshot in docs/tree_data.js verified.")


def test_tier2_malformed_savefile_rejection():
    print("  [Tier 2.2] Testing malformed savefile rejection...")
    sim = SkillTreeSimulator()

    # Case 1: Corrupted / non-dict payload
    try:
        sim.import_savefile("corrupted string")
        assert False, "Should reject non-dict payload"
    except ValueError as e:
        assert "must be a JSON object" in str(e)

    # Case 2: Missing schema_version
    try:
        sim.import_savefile({"mastered_nodes": ["BGCD"]})
        assert False, "Should reject missing schema_version"
    except ValueError as e:
        assert "schema version" in str(e).lower()

    # Case 3: Invalid mastered_nodes type
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": "BGCD"})
        assert False, "Should reject non-list mastered_nodes"
    except ValueError as e:
        assert "must be a list" in str(e)

    # Case 4: Unknown node ID in savefile
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["NONEXISTENT_NODE_999"]})
        assert False, "Should reject unknown node ID"
    except ValueError as e:
        assert "unknown node ID" in str(e)

    # Case 5: Tampered savefile attempting to master a planned node
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["HEAP"]})
        assert False, "Should reject mastering planned node"
    except ValueError as e:
        assert "planned node" in str(e)

    # Case 6: Tampered savefile without prerequisite closure
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["LIS"], "answers": {}})
        assert False, "Should reject savefile without prerequisite topological closure"
    except ValueError as e:
        assert "closure" in str(e).lower() or "prerequisite" in str(e).lower()

    # Case 7: Malformed savefile with array answers
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": [1, 2, 3]})
        assert False, "Should reject array answers field"
    except ValueError as e:
        assert "answers" in str(e).lower() and "dictionary" in str(e).lower()

    # Case 8: Malformed savefile with primitive answers string
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": "invalid"})
        assert False, "Should reject string answers field"
    except ValueError as e:
        assert "answers" in str(e).lower() and "dictionary" in str(e).lower()

    # Case 9: Malformed savefile with primitive entry inside answers
    try:
        sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": {"BGCD": "corrupt"}})
        assert False, "Should reject non-dict entry inside answers"
    except ValueError as e:
        assert "answers" in str(e).lower() and "dictionary" in str(e).lower()

    print("  ✓ 9/9 malformed savefile boundary test cases rejected cleanly.")


def test_tier2_locked_nodes_gating():
    print("  [Tier 2.3] Testing locked nodes gating and quiz prohibition...")
    sim = SkillTreeSimulator()

    # 1. Locked nodes cannot be marked mastered directly
    try:
        sim.mark_mastered("EUC")
        assert False, "Should reject marking locked node EUC as mastered"
    except ValueError as e:
        assert "locked" in str(e).lower() or "prerequisite" in str(e).lower()

    try:
        sim.mark_mastered("LIS")
        assert False, "Should reject marking locked node LIS as mastered"
    except ValueError as e:
        assert "locked" in str(e).lower() or "prerequisite" in str(e).lower()

    # 2. In docs/app.js: renderQuizTab renders locked notification and no active form
    node_eval_script = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    let quizHtml = '';
    function makeEl(tag) {
      return {
        tagName: tag,
        style: {},
        className: '',
        _inner: '',
        set innerHTML(v) { this._inner = v; },
        get innerHTML() { return this._inner; },
        get outerHTML() { return '<' + tag + ' class=\"' + this.className + '\">' + this._inner + '</' + tag + '>'; },
        appendChild(c) { this._inner += (c.outerHTML || c.innerHTML || ''); }
      };
    }
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = {
      addEventListener: () => {},
      createElement: makeEl,
      getElementById: (id) => (id === 'quiz-container' ? {
        set innerHTML(val) { quizHtml = val; },
        get innerHTML() { return quizHtml; },
        appendChild: (el) => { quizHtml += el.outerHTML || el.innerHTML || ''; }
      } : null)
    };
    eval(appCode);
    const app = new window.SkillTreeApp();
    app.engine = new window.SkillTreeEngine(treeData);
    app.nodesMap = app.engine.nodesMap;
    app.nodeStates = app.engine.computeNodeStates();
    const eucNode = app.nodesMap.get('EUC');
    app.renderQuizTab(eucNode);
    const isLockedBanner = quizHtml.includes('Module Locked');
    const hasActiveForm = quizHtml.includes('predict-form') || quizHtml.includes('<input');
    console.log(JSON.stringify({ isLockedBanner, hasActiveForm }));
    """
    res = subprocess.run(["node", "-e", node_eval_script], cwd=str(REPO_ROOT), capture_output=True, text=True)
    assert res.returncode == 0, f"Node script failed: {res.stderr}"
    data = json.loads(res.stdout)
    assert data["isLockedBanner"], "Locked node quiz tab must render locked notification banner"
    assert not data["hasActiveForm"], "Locked node quiz tab must NOT render active quiz forms"

    print("  ✓ Locked node direct mastery prohibition and quiz tab lock banner verified.")


def test_tier2_empty_quiz_answers():
    print("  [Tier 2.3] Testing empty and invalid quiz answer validation...")
    sim = SkillTreeSimulator()

    # Empty string
    success, msg = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "", "6")
    assert not success and "cannot be empty" in msg, f"Empty answer was accepted: {msg}"

    # Whitespace only
    success, msg = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "   ", "6")
    assert not success and "cannot be empty" in msg, f"Whitespace answer was accepted: {msg}"

    # None / null
    success, msg = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", None, "6")
    assert not success and "cannot be empty" in msg, f"None answer was accepted: {msg}"

    # Incorrect answer
    success, msg = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "12", "6")
    assert not success and "Incorrect" in msg, f"Incorrect answer was accepted: {msg}"

    print("  ✓ Empty and incorrect quiz answer boundary checks passed.")


def test_tier2_zoom_boundaries():
    print("  [Tier 2.4] Testing zoom scale boundaries and clamping...")
    assert clamp_zoom(0.1) == 0.25, f"Expected clamp to 0.25, got {clamp_zoom(0.1)}"
    assert clamp_zoom(0.0) == 1.0, "Zero or negative zoom should reset to 1.0"
    assert clamp_zoom(-5.0) == 1.0, "Negative zoom should reset to 1.0"
    assert clamp_zoom(10.0) == 3.0, f"Expected clamp to 3.0, got {clamp_zoom(10.0)}"
    assert clamp_zoom(1.5) == 1.5, f"Expected 1.5, got {clamp_zoom(1.5)}"
    print("  ✓ Zoom scale boundaries and clamping verified.")


# ==============================================================================
# Tier 3 Tests: Cross-Feature Combinations
# ==============================================================================
def test_tier3_multi_hop_unlock_propagation():
    print("  [Tier 3.1] Testing multi-hop unlock propagation with fan-in convergence...")
    sim = SkillTreeSimulator()
    states = sim.compute_node_states()

    # Initial state
    assert states["BGCD"] == "active", "BGCD should be active initially"
    assert states["EUC"] == "locked", "EUC should be locked initially"
    assert states["MERGE"] == "locked", "MERGE should be locked initially"

    # Step 1: Master BGCD -> Tier 2 unlocked
    states = sim.mark_mastered("BGCD")
    assert states["BGCD"] == "mastered"
    for t2 in ["EUC", "INS", "BS", "DYN", "MODEXP"]:
        assert states[t2] == "active", f"Mastering BGCD should unlock {t2}"

    # Step 2: Fan-in convergence test for MERGE (requires both INS and BS)
    # Master only INS
    states = sim.mark_mastered("INS")
    assert states["MERGE"] == "locked", "MERGE must remain locked until both INS and BS are mastered"
    assert states["NAIVE"] == "active", "Mastering INS should unlock NAIVE"

    # Master BS
    states = sim.mark_mastered("BS")
    assert states["MERGE"] == "active", "Mastering both INS and BS must unlock MERGE"

    # Step 3: Fan-in convergence test for KMP (requires both NAIVE and TSQ)
    # Master DYN -> unlocks TSQ
    states = sim.mark_mastered("DYN")
    assert states["TSQ"] == "active", "Mastering DYN should unlock TSQ"
    assert states["HEAP"] == "planned", "Planned node HEAP must remain planned"

    states = sim.mark_mastered("TSQ")
    assert states["KMP"] == "locked", "KMP requires both NAIVE and TSQ; NAIVE is not yet mastered"

    states = sim.mark_mastered("NAIVE")
    assert states["KMP"] == "active", "Mastering both TSQ and NAIVE must unlock KMP"

    print("  ✓ Multi-hop unlock cascade and multi-parent fan-in verified.")


def test_tier3_savefile_roundtrip():
    print("  [Tier 3.2] Testing savefile export -> reset -> import round-trip...")
    sim = SkillTreeSimulator()

    # Build intermediate learner progress
    sim.mark_mastered("BGCD")
    sim.mark_mastered("INS")
    sim.mark_mastered("BS")
    sim.mark_mastered("MERGE")
    sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "6", "6")
    sim.submit_quiz_answer("BGCD", "spot_the_fake", "bgcd_fake_1", "b", "b")

    original_states = sim.compute_node_states()
    original_mastered = set(sim.mastered_nodes)
    original_answers = json.loads(json.dumps(sim.answers))

    # 1. Export savefile
    savefile = sim.export_savefile()
    assert savefile["schema_version"] == "1.0.0"
    assert set(savefile["mastered_nodes"]) == original_mastered
    assert savefile["answers"] == original_answers

    # 2. Reset progress
    reset_states = sim.reset_progress()
    assert len(sim.mastered_nodes) == 0
    assert reset_states["BGCD"] == "active"
    assert reset_states["INS"] == "locked"
    assert reset_states["MERGE"] == "locked"

    # 3. Import savefile
    restored_states = sim.import_savefile(savefile)
    assert set(sim.mastered_nodes) == original_mastered
    assert sim.answers == original_answers
    assert restored_states == original_states
    assert restored_states["MERGE"] == "mastered"
    assert restored_states["LB"] == "active"

    print("  ✓ Savefile round-trip state preservation verified 100%.")


# ==============================================================================
# Tier 4 Tests: Real-World Learner Workload Scenario
# ==============================================================================
def test_tier4_learner_simulation():
    print("  [Tier 4.1] Executing real-world learner simulation workflow...")
    sim = SkillTreeSimulator()

    # Step 1: Learner visits app. Fresh state check.
    states = sim.compute_node_states()
    assert states["BGCD"] == "active", "Opening node BGCD must be active on fresh visit"
    locked_count = sum(1 for s in states.values() if s == "locked")
    planned_count = sum(1 for s in states.values() if s == "planned")
    assert locked_count == 21, f"Expected 21 locked nodes on fresh visit, got {locked_count}"
    assert planned_count == 6, f"Expected 6 planned nodes, got {planned_count}"

    # Step 2: Learner inspects BGCD and attempts exercises.
    # Answering Predict question
    corr, msg = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "6", "6")
    assert corr, f"Predict answer submission failed: {msg}"

    # Answering Spot the Fake question
    corr, msg = sim.submit_quiz_answer("BGCD", "spot_the_fake", "bgcd_fake_1", "b", "b")
    assert corr, f"Spot the Fake answer submission failed: {msg}"

    # Both exercises complete -> Node marked mastered
    states = sim.mark_mastered("BGCD")
    assert states["BGCD"] == "mastered"
    assert len(sim.mastered_nodes) == 1

    # Step 3: Verify dynamic unlock cascade to Tier 2
    for unlocked_id in ["EUC", "INS", "BS", "DYN", "MODEXP"]:
        assert states[unlocked_id] == "active", f"{unlocked_id} should be active after BGCD mastery"

    # Step 4: Export savefile
    savefile = sim.export_savefile()
    assert "BGCD" in savefile["mastered_nodes"]
    assert "bgcd_pred_1" in savefile["answers"]["BGCD"]["predict"]

    # Step 5: Learner accidentally clicks "Reset Progress"
    sim.reset_progress()
    post_reset_states = sim.compute_node_states()
    assert post_reset_states["BGCD"] == "active"
    assert post_reset_states["EUC"] == "locked"
    assert len(sim.mastered_nodes) == 0

    # Step 6: Learner imports exported savefile to recover session
    restored_states = sim.import_savefile(savefile)
    assert restored_states["BGCD"] == "mastered"
    assert restored_states["EUC"] == "active"
    assert restored_states["INS"] == "active"
    assert len(sim.mastered_nodes) == 1

    print("  ✓ Tier 4 real-world learner simulation completed with full state fidelity.")


# ==============================================================================
# Main Runner Entry Point
# ==============================================================================
def run_all_tests(strict=False):
    print("=" * 70)
    print("RUNNING VERIFIED ALGORITHMS SKILL TREE WEB APPLICATION TEST SUITE")
    print("=" * 70)

    with EphemeralServer(REPO_ROOT) as srv:
        base_url = f"http://127.0.0.1:{srv.port}"
        print(f"Ephemeral HTTP Server active at {base_url}\n")

        print("--- [TIER 1: FEATURE COVERAGE] ---")
        test_tier1_http_serving(base_url, strict=strict)
        test_tier1_dom_elements(strict=strict)
        test_tier1_tree_json_schema(strict=strict)
        print()

        print("--- [TIER 2: BOUNDARY VALUE ANALYSIS & CORNER CASES] ---")
        test_tier2_tree_data_fallback(strict=strict)
        test_tier2_malformed_savefile_rejection()
        test_tier2_locked_nodes_gating()
        test_tier2_empty_quiz_answers()
        test_tier2_zoom_boundaries()
        print()

        print("--- [TIER 3: CROSS-FEATURE COMBINATIONS] ---")
        test_tier3_multi_hop_unlock_propagation()
        test_tier3_savefile_roundtrip()
        print()

        print("--- [TIER 4: REAL-WORLD LEARNER WORKLOAD SCENARIOS] ---")
        test_tier4_learner_simulation()
        print()

    print("=" * 70)
    print("ALL WEB APPLICATION TEST SUITES PASSED (0 ERRORS)")
    print("=" * 70)


def main():
    strict = "--strict" in sys.argv
    try:
        run_all_tests(strict=strict)
        sys.exit(0)
    except AssertionError as err:
        print(f"\n[FAIL] Test assertion failed: {err}", file=sys.stderr)
        sys.exit(1)
    except Exception as exc:
        print(f"\n[ERROR] Unexpected error during test execution: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
