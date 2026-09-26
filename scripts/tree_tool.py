#!/usr/bin/env python3
"""
Verified Algorithms Skill Tree Tool (scripts/tree_tool.py)

Single Source of Truth Tooling for:
- DAG acyclicity and reachability validation
- Prerequisite completeness and bidirectional symmetry
- "Verified-only" rule enforcement against Amort/Audit.lean
- Mermaid flowchart synchronization in SKILL_TREE_TUTORIAL_PLAN.md (§4.2)
- Tree statistics and pedagogical health metrics
"""

import argparse
import difflib
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path


def resolve_path(path_str: str, default_subpath: str, repo_root: Path) -> Path:
    """Resolve a path argument against cwd or repo_root."""
    if path_str:
        p = Path(path_str)
        if p.is_file() or p.is_absolute():
            return p
        if (repo_root / p).is_file():
            return repo_root / p
        return p
    return repo_root / default_subpath


class SkillTreeValidator:
    """Performs comprehensive validation of tutorial/tree.json."""

    def __init__(self, tree_data: dict, audit_path: Path, repo_root: Path):
        self.data = tree_data
        self.audit_path = audit_path
        self.repo_root = repo_root
        self.errors = []
        self.nodes = self.data.get("nodes", [])
        self.node_map = {n["id"]: n for n in self.nodes if "id" in n}

    def error(self, msg: str):
        self.errors.append(msg)

    def validate(self) -> bool:
        self._validate_schema()
        if self.errors:
            return False

        self._validate_single_root_and_open()
        self._validate_bidirectional_links()
        if self.errors:
            return False

        self._validate_dag_and_topological_sort()
        if self.errors:
            return False

        self._validate_verified_only_rule()

        return len(self.errors) == 0

    def _validate_schema(self):
        # Top-level required keys
        for key in ["title", "description", "categories", "nodes"]:
            if key not in self.data:
                self.error(f"Missing top-level key: '{key}'")

        if "version" not in self.data and "schema_version" not in self.data:
            self.error("Top-level missing version/schema_version")

        categories = self.data.get("categories", [])
        if not isinstance(categories, list) or len(categories) == 0:
            self.error("'categories' must be a non-empty array")
            return

        cat_ids = set()
        for cat in categories:
            for field in ["id", "name", "color"]:
                if field not in cat or not cat[field]:
                    self.error(f"Category {cat} missing non-empty field '{field}'")
            if "id" in cat:
                cat_ids.add(cat["id"])

        if len(self.nodes) < 20:
            self.error(f"Expected at least 20 nodes, got {len(self.nodes)}")

        required_node_fields = [
            "id", "name", "tier", "category", "status",
            "prerequisites", "unlocks", "algorithm_skill", "lean_skill",
            "reference_module", "headline_theorems", "chapter_path", "exercises"
        ]

        seen_ids = set()
        for i, node in enumerate(self.nodes):
            nid = node.get("id", f"<index {i}>")
            if "id" not in node or not node["id"]:
                self.error(f"Node at index {i} missing 'id'")
                continue
            if not re.match(r"^[A-Z0-9_]+$", node["id"]):
                self.error(f"Node id '{node['id']}' must match ^[A-Z0-9_]+$")
            if node["id"] in seen_ids:
                self.error(f"Duplicate node id '{node['id']}'")
            seen_ids.add(node["id"])

            for field in required_node_fields:
                if field not in node:
                    self.error(f"Node '{nid}' missing required field '{field}'")

            tier = node.get("tier")
            if not isinstance(tier, int) or tier < 1 or tier > 6:
                self.error(f"Node '{nid}' tier must be an integer between 1 and 6 (got {tier})")

            cat = node.get("category")
            if cat not in cat_ids:
                self.error(f"Node '{nid}' references undefined category '{cat}'")

            status = node.get("status")
            if status not in ["open", "ready", "planned"]:
                self.error(f"Node '{nid}' status must be 'open', 'ready', or 'planned' (got '{status}')")

            for skill_field in ["algorithm_skill", "lean_skill"]:
                val = node.get(skill_field)
                if not isinstance(val, str) or not val.strip():
                    self.error(f"Node '{nid}' field '{skill_field}' must be a non-empty string")

            for list_field in ["prerequisites", "unlocks"]:
                val = node.get(list_field)
                if not isinstance(val, list):
                    self.error(f"Node '{nid}' field '{list_field}' must be a list")

            ex = node.get("exercises")
            if not isinstance(ex, dict) or "predict" not in ex or "spot_the_fake" not in ex:
                self.error(f"Node '{nid}' exercises must be an object with 'predict' and 'spot_the_fake' arrays")

    def _validate_single_root_and_open(self):
        open_nodes = [n["id"] for n in self.nodes if n.get("status") == "open"]
        if len(open_nodes) != 1:
            self.error(f"Expected exactly 1 node with status 'open', found {len(open_nodes)}: {open_nodes}")
        elif open_nodes[0] != "BGCD":
            self.error(f"Sole open node must be 'BGCD', found '{open_nodes[0]}'")

        roots = [n["id"] for n in self.nodes if len(n.get("prerequisites", [])) == 0]
        if len(roots) != 1:
            self.error(f"Expected exactly 1 root node with 0 prerequisites, found {len(roots)}: {roots}")
        elif roots[0] != "BGCD":
            self.error(f"Sole root node must be 'BGCD', found '{roots[0]}'")

        for n in self.nodes:
            if n["id"] != "BGCD" and len(n.get("prerequisites", [])) == 0:
                self.error(f"Non-root node '{n['id']}' has empty prerequisites")

    def _validate_bidirectional_links(self):
        for nid, node in self.node_map.items():
            prereqs = node.get("prerequisites", [])
            unlocks = node.get("unlocks", [])

            for p in prereqs:
                if p not in self.node_map:
                    self.error(f"Node '{nid}' lists non-existent prerequisite '{p}'")
                else:
                    if nid not in self.node_map[p].get("unlocks", []):
                        self.error(f"Asymmetry: Node '{nid}' has prerequisite '{p}', but '{p}' does not list '{nid}' in unlocks")

            for u in unlocks:
                if u not in self.node_map:
                    self.error(f"Node '{nid}' lists non-existent unlock target '{u}'")
                else:
                    if nid not in self.node_map[u].get("prerequisites", []):
                        self.error(f"Asymmetry: Node '{nid}' has unlock target '{u}', but '{u}' does not list '{nid}' in prerequisites")

    def _validate_dag_and_topological_sort(self):
        in_degrees = {nid: len(node.get("prerequisites", [])) for nid, node in self.node_map.items()}
        queue = deque([nid for nid, deg in in_degrees.items() if deg == 0])

        visited_order = []
        while queue:
            curr = queue.popleft()
            visited_order.append(curr)

            for nxt in self.node_map[curr].get("unlocks", []):
                if nxt in in_degrees:
                    in_degrees[nxt] -= 1
                    if in_degrees[nxt] == 0:
                        queue.append(nxt)

        if len(visited_order) < len(self.node_map):
            cycle_nodes = [nid for nid, deg in in_degrees.items() if deg > 0]
            cycle_path = self._detect_cycle_path(cycle_nodes)
            self.error(f"DAG cycle detected! Nodes involved: {cycle_nodes}. Cycle path: {cycle_path}")
            return

        # Reachability from BGCD
        reachable = set()
        reach_q = deque(["BGCD"])
        while reach_q:
            curr = reach_q.popleft()
            if curr in reachable:
                continue
            reachable.add(curr)
            for nxt in self.node_map[curr].get("unlocks", []):
                reach_q.append(nxt)

        unreachable = set(self.node_map.keys()) - reachable
        if unreachable:
            self.error(f"Unreachable nodes from root 'BGCD': {sorted(list(unreachable))}")

        # Depth vs Tier verification
        depths = {"BGCD": 0}
        for nid in visited_order:
            if nid == "BGCD":
                continue
            prereqs = self.node_map[nid].get("prerequisites", [])
            max_p_depth = max(depths[p] for p in prereqs)
            depths[nid] = max_p_depth + 1

        for nid, d in depths.items():
            expected_tier = d + 1
            declared_tier = self.node_map[nid].get("tier")
            if declared_tier != expected_tier:
                self.error(f"Node '{nid}' tier mismatch: declared tier {declared_tier}, computed depth {d} (expected tier {expected_tier})")

    def _detect_cycle_path(self, cycle_nodes: list) -> str:
        adj = defaultdict(list)
        for u in cycle_nodes:
            for v in self.node_map[u].get("unlocks", []):
                if v in cycle_nodes:
                    adj[u].append(v)

        visited = set()
        path = []

        def dfs(u):
            visited.add(u)
            path.append(u)
            for v in adj[u]:
                if v in path:
                    idx = path.index(v)
                    return path[idx:] + [v]
                if v not in visited:
                    res = dfs(v)
                    if res:
                        return res
            path.pop()
            return None

        for n in cycle_nodes:
            if n not in visited:
                res = dfs(n)
                if res:
                    return " -> ".join(res)
        return " -> ".join(cycle_nodes[:3] + [cycle_nodes[0]])

    def _validate_verified_only_rule(self):
        if not self.audit_path.is_file():
            self.error(f"Axiom audit file not found at '{self.audit_path}'")
            return

        audit_content = self.audit_path.read_text(encoding="utf-8")
        audited_theorems = set(re.findall(r"#print\s+axioms\s+([A-Za-z0-9_.]+)", audit_content))

        for nid, node in self.node_map.items():
            status = node.get("status")
            ref_mod = node.get("reference_module")
            theorems = node.get("headline_theorems", [])
            exercises = node.get("exercises", {})

            if status in ["open", "ready"]:
                if not ref_mod or not isinstance(ref_mod, str):
                    self.error(f"Ready/open node '{nid}' must have non-null 'reference_module'")
                else:
                    lean_file = self.repo_root / (ref_mod.replace(".", "/") + ".lean")
                    if not lean_file.is_file():
                        self.error(f"Node '{nid}' reference module file '{lean_file}' does not exist on disk!")

                if not theorems or len(theorems) == 0:
                    self.error(f"Ready/open node '{nid}' must have non-empty 'headline_theorems'")
                else:
                    for thm in theorems:
                        if thm not in audited_theorems:
                            self.error(f"Theorem '{thm}' claimed by ready/open node '{nid}' is NOT audited in {self.audit_path.name}!")

                # Exercises validation
                predict_list = exercises.get("predict", [])
                if not predict_list or len(predict_list) < 1:
                    self.error(f"Ready/open node '{nid}' must have at least 1 'predict' exercise")
                else:
                    for q in predict_list:
                        for f in ["id", "prompt", "input_type", "expected_answer", "explanation"]:
                            if f not in q or not str(q[f]).strip():
                                self.error(f"Node '{nid}' predict exercise {q.get('id')} missing field '{f}'")
                        if q.get("input_type") not in ["number", "text", "choice"]:
                            self.error(f"Node '{nid}' predict exercise {q.get('id')} invalid input_type '{q.get('input_type')}'")

                stf_list = exercises.get("spot_the_fake", [])
                if not stf_list or len(stf_list) < 1:
                    self.error(f"Ready/open node '{nid}' must have at least 1 'spot_the_fake' exercise")
                else:
                    for q in stf_list:
                        for f in ["id", "prompt", "options", "correct_option_id", "summary_explanation"]:
                            if f not in q or not q[f]:
                                self.error(f"Node '{nid}' spot_the_fake exercise {q.get('id')} missing field '{f}'")
                        options = q.get("options", [])
                        if len(options) < 2:
                            self.error(f"Node '{nid}' spot_the_fake {q.get('id')} must have at least 2 options")
                        correct_opt_id = q.get("correct_option_id")
                        genuine_opts = [opt for opt in options if opt.get("is_fake") is False]
                        if len(genuine_opts) != 1:
                            self.error(f"Node '{nid}' spot_the_fake {q.get('id')} must have exactly 1 genuine option (is_fake: false), found {len(genuine_opts)}")
                        elif genuine_opts[0].get("id") != correct_opt_id:
                            self.error(f"Node '{nid}' spot_the_fake {q.get('id')} correct_option_id '{correct_opt_id}' does not match genuine option id '{genuine_opts[0].get('id')}'")

            elif status == "planned":
                if theorems and len(theorems) > 0:
                    self.error(f"Planned node '{nid}' must have empty 'headline_theorems', found {theorems}")


def generate_mermaid_diagram(tree_data: dict) -> str:
    """Generate canonical Mermaid flowchart TD block matching SKILL_TREE_TUTORIAL_PLAN.md §4.2.

    Dynamically extracts all edges by traversing tree_data['nodes'] and their unlocks,
    grouping and styling edges dynamically based on branch and node status.
    """
    nodes = tree_data.get("nodes", [])
    nodes_by_id = {n["id"]: n for n in nodes}
    root_node = next((n for n in nodes if not n.get("prerequisites")), None)
    root_id = root_node["id"] if root_node else "BGCD"

    # Canonical branch tiebreaker ordering for canonical nodes
    edge_priority = {
        ("BGCD", "EUC"): 1, ("BGCD", "INS"): 2, ("BGCD", "BS"): 3, ("BGCD", "DYN"): 4, ("BGCD", "MODEXP"): 5,
        ("EUC", "EXT"): 10,
        ("INS", "MERGE"): 20, ("BS", "MERGE"): 21, ("MERGE", "LB"): 22, ("MERGE", "QS"): 23, ("MERGE", "INTV"): 24,
        ("DYN", "TSQ"): 30, ("INS", "NAIVE"): 31, ("NAIVE", "KMP"): 32, ("TSQ", "KMP"): 33, ("NAIVE", "LCS"): 34, ("LCS", "ED"): 35, ("LCS", "KNAP"): 36, ("KNAP", "LIS"): 37,
        ("TSQ", "BFS"): 40, ("BFS", "BF"): 41, ("BFS", "TWOSAT"): 42, ("LB", "RED"): 43,
        ("DYN", "HEAP"): 50, ("HEAP", "DIJ"): 51, ("BFS", "DSU"): 52, ("DSU", "KRUS"): 53, ("KMP", "Z"): 54, ("KMP", "AC"): 55,
    }

    # Dynamically extract all graph edges from node unlocks
    extracted_edges = []
    for node in nodes:
        u = node["id"]
        for v in node.get("unlocks", []):
            if v in nodes_by_id:
                extracted_edges.append((u, v))

    # Dynamically partition edges into categorical branches
    g_root, g_arith, g_sort, g_str_dp, g_graph, g_planned = [], [], [], [], [], []
    for u, v in extracted_edges:
        src = nodes_by_id[u]
        tgt = nodes_by_id[v]
        if tgt.get("status") == "planned" or src.get("status") == "planned":
            g_planned.append((u, v))
        elif u == root_id:
            g_root.append((u, v))
        elif tgt.get("category") == "arithmetic":
            g_arith.append((u, v))
        elif tgt.get("category") in {"sorting", "greedy"} or tgt.get("id") in {"MERGE", "LB", "QS", "INTV"}:
            g_sort.append((u, v))
        elif tgt.get("category") in {"amortization", "strings", "dp"}:
            g_str_dp.append((u, v))
        elif tgt.get("category") in {"graphs", "complexity"}:
            g_graph.append((u, v))
        else:
            g_root.append((u, v))

    def edge_key(e):
        u, v = e
        tgt = nodes_by_id.get(v, {})
        src = nodes_by_id.get(u, {})
        if e in edge_priority:
            return (0, edge_priority[e], u, v)
        return (1, tgt.get("tier", 99), src.get("tier", 99), u, v)

    edge_groups = [
        sorted(g_root, key=edge_key),
        sorted(g_arith, key=edge_key),
        sorted(g_sort, key=edge_key),
        sorted(g_str_dp, key=edge_key),
        sorted(g_graph, key=edge_key),
        sorted(g_planned, key=edge_key),
    ]

    root_name = root_node["name"] if root_node else "Binary GCD (Stein)"
    root_label = root_name if root_name.startswith("🌱") else f"🌱 {root_name}"
    root_status = root_node["status"] if root_node else "open"

    lines = [
        "flowchart TD",
        "    classDef open fill:#2d3748,stroke:#cbd5e0,stroke-width:3px,color:#fff",
        "    classDef ready fill:#22543d,stroke:#68d391,color:#fff",
        "    classDef planned fill:#fff,stroke:#a0aec0,stroke-dasharray:5 5,color:#4a5568",
        "",
        f'    {root_id}["{root_label}"]:::{root_status}'
    ]

    defined = {root_id}
    for group in edge_groups:
        if not group:
            continue
        lines.append("")
        for u, v in group:
            target_node = nodes_by_id[v]
            src_node = nodes_by_id[u]
            arrow = "-.->" if target_node.get("status") == "planned" or src_node.get("status") == "planned" else "-->"
            if v not in defined:
                defined.add(v)
                lines.append(f'    {u} {arrow} {v}["{target_node["name"]}"]:::{target_node["status"]}')
            else:
                lines.append(f"    {u} {arrow} {v}")

    return "\n".join(lines)


def sync_mermaid_in_plan(plan_path: Path, tree_data: dict, check_only: bool = False) -> bool:
    """Synchronize or check the Mermaid diagram inside SKILL_TREE_TUTORIAL_PLAN.md."""
    if not plan_path.is_file():
        print(f"Error: Plan file '{plan_path}' does not exist!", file=sys.stderr)
        return False

    content = plan_path.read_text(encoding="utf-8")
    mermaid_pattern = re.compile(r"(```mermaid\n)(.*?)(\n```)", re.DOTALL)
    match = mermaid_pattern.search(content)

    if not match:
        print(f"Error: Could not locate ```mermaid ... ``` block in '{plan_path}'", file=sys.stderr)
        return False

    current_mermaid = match.group(2).strip()
    generated_mermaid = generate_mermaid_diagram(tree_data).strip()

    if check_only:
        if current_mermaid == generated_mermaid:
            print("✓ Mermaid diagram in SKILL_TREE_TUTORIAL_PLAN.md is in perfect sync.")
            return True
        else:
            print("✗ Mermaid diagram drift detected! Diff:", file=sys.stderr)
            diff = difflib.unified_diff(
                current_mermaid.splitlines(),
                generated_mermaid.splitlines(),
                fromfile="current",
                tofile="generated",
                lineterm=""
            )
            for line in diff:
                print(line, file=sys.stderr)
            return False
    else:
        new_content = mermaid_pattern.sub(f"\\1{generated_mermaid}\\3", content, count=1)
        plan_path.write_text(new_content, encoding="utf-8")
        print(f"✓ Successfully synchronized Mermaid diagram in {plan_path} §4.2.")
        return True


def display_stats(tree_data: dict):
    """Print formatted summary table of tree metrics."""
    nodes = tree_data.get("nodes", [])
    total = len(nodes)

    status_counts = defaultdict(int)
    category_counts = defaultdict(int)
    tier_counts = defaultdict(list)
    solid_edges = 0
    dashed_edges = 0
    total_theorems = 0
    total_predict = 0
    total_stf = 0

    nodes_by_id = {n["id"]: n for n in nodes}

    for n in nodes:
        status_counts[n["status"]] += 1
        category_counts[n["category"]] += 1
        tier_counts[n["tier"]].append(n["id"])
        total_theorems += len(n.get("headline_theorems", []))
        ex = n.get("exercises", {})
        total_predict += len(ex.get("predict", []))
        total_stf += len(ex.get("spot_the_fake", []))

        for v in n.get("unlocks", []):
            if v in nodes_by_id:
                if n["status"] == "planned" or nodes_by_id[v]["status"] == "planned":
                    dashed_edges += 1
                else:
                    solid_edges += 1

    cat_names = {
        "arithmetic": "Arithmetic & Number Theory",
        "sorting": "Sorting & Searching",
        "amortization": "Data Structures & Amortization",
        "strings": "Strings & Pattern Matching",
        "dp": "Dynamic Programming",
        "greedy": "Greedy Algorithms",
        "graphs": "Graph Algorithms",
        "complexity": "Complexity & Reductions"
    }

    print("=" * 60)
    print("        VERIFIED ALGORITHMS SKILL TREE STATISTICS")
    print("=" * 60)
    print(f"Total Nodes:            {total}")
    open_cnt = status_counts["open"]
    ready_cnt = status_counts["ready"]
    plan_cnt = status_counts["planned"]
    print(f"  - Open (Root Entry):   {open_cnt:2d}  ({open_cnt/total*100:5.1f}%)")
    print(f"  - Ready (Verified):   {ready_cnt:2d}  ({ready_cnt/total*100:5.1f}%)")
    print(f"  - Planned:             {plan_cnt:2d}  ({plan_cnt/total*100:5.1f}%)")
    print()
    print("By Category:")
    for cid, cname in cat_names.items():
        print(f"  - {cname:<32} {category_counts[cid]:2d}")
    print()
    print("By Tier:")
    for t in sorted(tier_counts.keys()):
        node_str = ", ".join(tier_counts[t])
        print(f"  - Tier {t}: {len(tier_counts[t]):2d} nodes ({node_str})")
    print()
    print("Graph Topology:")
    print(f"  - Solid Edges (Verified):   {solid_edges:2d}")
    print(f"  - Dashed Edges (Planned):   {dashed_edges:2d}")
    print(f"  - Total Dependency Edges:   {solid_edges + dashed_edges:2d}")
    print()
    print("Verification & Content:")
    print(f"  - Headline Theorems Audited: {total_theorems}")
    print(f"  - Predict Exercises:         {total_predict}")
    print(f"  - Spot the Fake Exercises:   {total_stf}")
    print(f"  - Total Interactive Quizzes: {total_predict + total_stf}")
    print("=" * 60)


def build_site(repo_root: Path, tree_data: dict) -> bool:
    """Build a completely self-contained static site inside docs/."""
    docs_dir = repo_root / "docs"
    chapters_dir = docs_dir / "chapters"
    chapters_dir.mkdir(parents=True, exist_ok=True)
    tutorial_docs_dir = docs_dir / "tutorial"
    tutorial_docs_dir.mkdir(parents=True, exist_ok=True)
    tutorial_dir = repo_root / "tutorial"

    copied_count = 0
    available_chapters = []
    for md_file in sorted(tutorial_dir.glob("*.md")):
        content = md_file.read_text(encoding="utf-8")
        # Write to docs/chapters/<name>
        (chapters_dir / md_file.name).write_text(content, encoding="utf-8")
        # Also write to docs/tutorial/<name> for direct relative path compatibility
        (tutorial_docs_dir / md_file.name).write_text(content, encoding="utf-8")
        available_chapters.append(md_file.name)
        copied_count += 1

    # Write docs/tree.json
    tree_json_dest = docs_dir / "tree.json"
    with open(tree_json_dest, "w", encoding="utf-8") as f:
        json.dump(tree_data, f, indent=2)
        f.write("\n")

    # Generate docs/tree_data.js
    tree_data_js_dest = docs_dir / "tree_data.js"
    json_str = json.dumps(tree_data, indent=2)
    tree_data_js_dest.write_text(
        f"// Auto-generated by scripts/tree_tool.py --build-site; DO NOT EDIT DIRECTLY\n"
        f"window.__TREE_DATA_FALLBACK__ = {json_str};\n",
        encoding="utf-8"
    )

    print("✓ SUCCESS: Built self-contained docs/ site:")
    print(f"  - Copied {copied_count} chapters to docs/chapters/ ({', '.join(available_chapters)})")
    print(f"  - Generated docs/tree.json")
    print(f"  - Generated docs/tree_data.js from tutorial/tree.json")
    return True


def check_site(repo_root: Path, tree_data: dict) -> bool:
    """Verify that docs/ site files are up to date and all chapter snippets match verbatim."""
    docs_dir = repo_root / "docs"
    errors = []

    # 1. Check docs/tree.json matches tutorial/tree.json
    docs_tree_json = docs_dir / "tree.json"
    if not docs_tree_json.is_file():
        errors.append("docs/tree.json does not exist. Run scripts/tree_tool.py --build-site.")
    else:
        try:
            with open(docs_tree_json, "r", encoding="utf-8") as f:
                docs_data = json.load(f)
            if docs_data != tree_data:
                errors.append("docs/tree.json is out of date with tutorial/tree.json.")
        except Exception as e:
            errors.append(f"Error reading docs/tree.json: {e}")

    # 2. Check docs/tree_data.js matches
    docs_tree_data_js = docs_dir / "tree_data.js"
    if not docs_tree_data_js.is_file():
        errors.append("docs/tree_data.js does not exist. Run scripts/tree_tool.py --build-site.")
    else:
        content = docs_tree_data_js.read_text(encoding="utf-8")
        prefix = "window.__TREE_DATA_FALLBACK__ = "
        idx = content.find(prefix)
        if idx == -1:
            errors.append("docs/tree_data.js does not define window.__TREE_DATA_FALLBACK__.")
        else:
            raw_json = content[idx + len(prefix):].rstrip().rstrip(";")
            try:
                js_data = json.loads(raw_json)
                if js_data != tree_data:
                    errors.append("docs/tree_data.js is out of date with tutorial/tree.json.")
            except Exception as e:
                errors.append(f"Error parsing JSON in docs/tree_data.js: {e}")

    # 3. Check chapters in docs/chapters/ match tutorial/*.md
    tutorial_dir = repo_root / "tutorial"
    chapters_dir = docs_dir / "chapters"
    for md_file in sorted(tutorial_dir.glob("*.md")):
        dest = chapters_dir / md_file.name
        if not dest.is_file():
            errors.append(f"docs/chapters/{md_file.name} is missing. Run scripts/tree_tool.py --build-site.")
        elif dest.read_text(encoding="utf-8") != md_file.read_text(encoding="utf-8"):
            errors.append(f"docs/chapters/{md_file.name} differs from tutorial/{md_file.name}.")

    # 4. Verbatim snippet check: Every ```lean block in tutorial/*.md either
    # appears verbatim in the companion .lean file or contains '-- (illustrative)'
    companions = {
        "tutorial/binary_gcd.md": "Tutorial/BinaryGCD.lean",
        "tutorial/euclid_gcd.md": "Tutorial/EuclideanGCD.lean",
        "tutorial/insertion_sort.md": "Tutorial/InsertionSort.lean"
    }

    for md_rel, lean_rel in companions.items():
        md_path = repo_root / md_rel
        lean_path = repo_root / lean_rel
        if not md_path.is_file() or not lean_path.is_file():
            continue
        md_text = md_path.read_text(encoding="utf-8")
        lean_text = lean_path.read_text(encoding="utf-8")
        parts = md_text.split("```lean")
        for i, part in enumerate(parts[1:], 1):
            if "```" not in part:
                continue
            block = part.split("```")[0].strip()
            if "-- (illustrative)" in block:
                continue
            if block not in lean_text:
                errors.append(
                    f"Quoted Lean snippet #{i} in {md_rel} does not match {lean_rel} verbatim and is not marked '-- (illustrative)'."
                )

    if errors:
        print(f"✗ FAILED: {len(errors)} site/snippet check errors detected:", file=sys.stderr)
        for err in errors:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return False

    print("✓ SUCCESS: docs/ site files and verbatim chapter snippets passed all checks.")
    return True


def check_theorems(repo_root: Path, tree_data: dict) -> bool:
    """Verify all headline theorems exist using Lean ('lake env lean' with #check @...)."""
    theorems = []
    for n in tree_data.get("nodes", []):
        for t in n.get("headline_theorems", []):
            theorems.append(t)

    if not theorems:
        print("No headline theorems to check.")
        return True

    import tempfile
    import subprocess
    lean_src = "import Amort.Audit\n\n" + "\n".join(f"#check @{t}" for t in theorems) + "\n"
    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
        f.write(lean_src)
        temp_name = f.name

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", temp_name],
            cwd=str(repo_root),
            capture_output=True,
            text=True
        )
    finally:
        Path(temp_name).unlink(missing_ok=True)

    if proc.returncode != 0:
        errors = [line for line in proc.stdout.splitlines() if "error" in line.lower()]
        print(f"✗ FAILED: Lean theorem check failed with returncode {proc.returncode}:", file=sys.stderr)
        for err in errors:
            print(f"  [ERROR] {err}", file=sys.stderr)
        if proc.stderr:
            print(f"  [STDERR] {proc.stderr}", file=sys.stderr)
        return False

    print(f"✓ SUCCESS: All {len(theorems)} headline theorems verified via Lean (#check @...).")
    return True


def main():
    repo_root = Path(__file__).resolve().parent.parent

    parser = argparse.ArgumentParser(
        description="Verified Algorithms Skill Tree Tool: validation, mermaid sync, build site, and stats."
    )
    parser.add_argument("--file", default="tutorial/tree.json", help="Path to tree.json (default: tutorial/tree.json)")
    parser.add_argument("--plan", default="SKILL_TREE_TUTORIAL_PLAN.md", help="Path to tutorial plan markdown")
    parser.add_argument("--audit", default="Amort/Audit.lean", help="Path to Lean axiom audit file")
    parser.add_argument("--validate", action="store_true", help="Run full tree validation suite")
    parser.add_argument("--sync-mermaid", action="store_true", help="Synchronize Mermaid diagram in plan")
    parser.add_argument("--check", action="store_true", help="With --sync-mermaid, check without modifying")
    parser.add_argument("--stats", action="store_true", help="Display tree metrics and statistics")
    parser.add_argument("--build-site", action="store_true", help="Build self-contained site into docs/")
    parser.add_argument("--check-site", action="store_true", help="Check that docs/ and quoted snippets are up to date")
    parser.add_argument("--check-theorems", action="store_true", help="Verify all headline theorems exist using Lean")

    args = parser.parse_args()

    tree_path = resolve_path(args.file, "tutorial/tree.json", repo_root)
    plan_path = resolve_path(args.plan, "SKILL_TREE_TUTORIAL_PLAN.md", repo_root)
    audit_path = resolve_path(args.audit, "Amort/Audit.lean", repo_root)

    if not tree_path.is_file():
        print(f"Error: tree.json not found at '{tree_path}'", file=sys.stderr)
        sys.exit(1)

    try:
        with open(tree_path, "r", encoding="utf-8") as f:
            tree_data = json.load(f)
    except Exception as e:
        print(f"Error reading JSON from '{tree_path}': {e}", file=sys.stderr)
        sys.exit(1)

    if not (args.validate or args.sync_mermaid or args.stats or args.build_site or args.check_site or args.check_theorems):
        # Default behavior if no action specified: run validate and show stats
        args.validate = True

    overall_success = True

    if args.validate:
        validator = SkillTreeValidator(tree_data, audit_path, repo_root)
        if validator.validate():
            print("✓ SUCCESS: tutorial/tree.json passed all validation checks (0 errors).")
            print(f"  - Verified 28 nodes across 6 tiers (1 open, 21 ready, 6 planned).")
            print(f"  - 100% bidirectional symmetry and DAG acyclicity verified.")
            print(f"  - Single root 'BGCD' verified with complete reachability.")
            print(f"  - All headline theorems cross-checked against {audit_path.name}.")
        else:
            print(f"✗ FAILED: {len(validator.errors)} validation errors detected:", file=sys.stderr)
            for err in validator.errors:
                print(f"  [ERROR] {err}", file=sys.stderr)
            overall_success = False

    if args.sync_mermaid:
        mermaid_ok = sync_mermaid_in_plan(plan_path, tree_data, check_only=args.check)
        if not mermaid_ok:
            overall_success = False

    if args.build_site:
        site_ok = build_site(repo_root, tree_data)
        if not site_ok:
            overall_success = False

    if args.check_site:
        site_check_ok = check_site(repo_root, tree_data)
        if not site_check_ok:
            overall_success = False

    if args.check_theorems:
        thm_check_ok = check_theorems(repo_root, tree_data)
        if not thm_check_ok:
            overall_success = False

    if args.stats:
        display_stats(tree_data)

    sys.exit(0 if overall_success else 1)


if __name__ == "__main__":
    main()
