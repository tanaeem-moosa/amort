#!/usr/bin/env python3
"""
tests/test_tree_tool.py: Comprehensive test suite for scripts/tree_tool.py and Skill Tree DAG specifications.

Covers:
- Tier 1: Feature Coverage (CLI validation, schema, topological sort, acyclicity, bidirectional symmetry,
          Audit.lean cross-check, Mermaid sync check, --stats)
- Tier 2: Boundary & Corner Cases (Cycle injection A->B->A, missing prerequisite ID, asymmetric prerequisite/unlock,
          unverified theorem on ready node, empty exercises on ready node, duplicate node IDs, multiple roots,
          planned node with theorems)
- Tier 3: Cross-Feature Combinations (Mermaid sync preserves markdown content outside code fences, drift detection)
"""

import unittest
import sys
import os
import json
import re
import tempfile
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
TREE_TOOL_PATH = REPO_ROOT / "scripts" / "tree_tool.py"
TREE_JSON_PATH = REPO_ROOT / "tutorial" / "tree.json"
AUDIT_LEAN_PATH = REPO_ROOT / "Amort" / "Audit.lean"
PLAN_MD_PATH = REPO_ROOT / "SKILL_TREE_TUTORIAL_PLAN.md"


def get_base_tree_data():
    """Loads valid tree.json or canonical fallback."""
    if TREE_JSON_PATH.exists():
        with open(TREE_JSON_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    raise FileNotFoundError(f"Missing {TREE_JSON_PATH}")


# ==============================================================================
# In-Memory Specification Validator (Reference Oracle)
# ==============================================================================
class SkillTreeValidator:
    """Independent oracle validator for testing DAG properties and Lean audit cleanliness."""
    def __init__(self, data, audit_path=AUDIT_LEAN_PATH):
        self.data = data
        self.nodes = data.get("nodes", [])
        self.nodes_map = {n["id"]: n for n in self.nodes}
        self.audit_path = audit_path

    def validate_schema(self):
        errors = []
        required_fields = [
            "id", "name", "tier", "category", "status",
            "prerequisites", "unlocks", "algorithm_skill", "lean_skill",
            "reference_module", "headline_theorems", "chapter_path", "exercises"
        ]
        if len(self.nodes) != 28:
            errors.append(f"Expected 28 nodes, got {len(self.nodes)}")

        ids_seen = set()
        open_nodes = []
        for n in self.nodes:
            nid = n.get("id")
            if not nid:
                errors.append("Node missing ID")
                continue
            if nid in ids_seen:
                errors.append(f"Duplicate node ID '{nid}'")
            ids_seen.add(nid)

            for f in required_fields:
                if f not in n:
                    errors.append(f"Node '{nid}' missing required field '{f}'")

            status = n.get("status")
            if status not in ("open", "ready", "planned"):
                errors.append(f"Node '{nid}' has invalid status '{status}'")
            if status == "open":
                open_nodes.append(nid)

            tier = n.get("tier")
            if not isinstance(tier, int) or tier < 1 or tier > 6:
                errors.append(f"Node '{nid}' has invalid tier '{tier}'")

            # Exercises check
            ex = n.get("exercises", {})
            if status in ("open", "ready"):
                if not ex.get("predict"):
                    errors.append(f"Node '{nid}' has empty predict exercises")
                if not ex.get("spot_the_fake"):
                    errors.append(f"Node '{nid}' has empty spot_the_fake exercises")
            elif status == "planned":
                if n.get("headline_theorems"):
                    errors.append(f"Planned node '{nid}' must not declare headline theorems")

        if len(open_nodes) != 1 or open_nodes[0] != "BGCD":
            errors.append(f"Expected exactly 1 open root node 'BGCD', found: {open_nodes}")

        return errors

    def validate_bidirectional_symmetry(self):
        errors = []
        for u_id, u_node in self.nodes_map.items():
            for p_id in u_node.get("prerequisites", []):
                if p_id not in self.nodes_map:
                    errors.append(f"Node '{u_id}' has non-existent prerequisite '{p_id}'")
                elif u_id not in self.nodes_map[p_id].get("unlocks", []):
                    errors.append(f"Asymmetry: '{u_id}' lists '{p_id}' as prerequisite, but '{p_id}' does not unlock '{u_id}'")

            for w_id in u_node.get("unlocks", []):
                if w_id not in self.nodes_map:
                    errors.append(f"Node '{u_id}' has non-existent unlock '{w_id}'")
                elif u_id not in self.nodes_map[w_id].get("prerequisites", []):
                    errors.append(f"Asymmetry: '{u_id}' unlocks '{w_id}', but '{w_id}' does not list '{u_id}' as prerequisite")
        return errors

    def validate_acyclicity_and_toposort(self):
        in_degree = {n["id"]: 0 for n in self.nodes}
        adj = {n["id"]: [] for n in self.nodes}

        for n in self.nodes:
            u = n["id"]
            for v in n.get("unlocks", []):
                if v in in_degree:
                    in_degree[v] += 1
                    adj[u].append(v)

        queue = [nid for nid, deg in in_degree.items() if deg == 0]
        visited = []

        while queue:
            curr = queue.pop(0)
            visited.append(curr)
            for neighbor in adj[curr]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        if len(visited) != len(self.nodes):
            remaining = [nid for nid, deg in in_degree.items() if deg > 0]
            return False, f"Cycle detected involving nodes: {remaining}", visited
        return True, "Acyclic DAG verified", visited

    def validate_audit_theorems(self):
        if not self.audit_path.exists():
            return [f"Audit file not found: {self.audit_path}"]

        audit_content = self.audit_path.read_text(encoding="utf-8")
        audited_theorems = set(re.findall(r"#print\s+axioms\s+([A-Za-z0-9_.]+)", audit_content))

        errors = []
        for n in self.nodes:
            if n.get("status") in ("open", "ready"):
                for thm in n.get("headline_theorems", []):
                    if thm not in audited_theorems:
                        errors.append(f"Theorem '{thm}' claimed by '{n['id']}' not found in {self.audit_path.name}")
        return errors


# ==============================================================================
# Tier 1: Feature Coverage Tests
# ==============================================================================
class TestTreeToolFeatureCoverage(unittest.TestCase):
    """Tier 1: Comprehensive feature coverage of DAG validation and CLI."""

    def setUp(self):
        self.tree_data = get_base_tree_data()
        self.validator = SkillTreeValidator(self.tree_data)

    def test_01_valid_tree_schema(self):
        """Verifies that the canonical tree has 0 schema errors across all 28 nodes."""
        errors = self.validator.validate_schema()
        self.assertEqual(errors, [], f"Schema errors encountered: {errors}")

    def test_02_bidirectional_symmetry(self):
        """Verifies 100% bidirectional symmetry between prerequisites and unlocks."""
        errors = self.validator.validate_bidirectional_symmetry()
        self.assertEqual(errors, [], f"Asymmetric prerequisite links found: {errors}")

    def test_03_dag_acyclicity_and_reachability(self):
        """Verifies that the skill tree is an acyclic DAG and topological order processes all 28 nodes."""
        is_acyclic, msg, topo_order = self.validator.validate_acyclicity_and_toposort()
        self.assertTrue(is_acyclic, msg)
        self.assertEqual(len(topo_order), 28)
        self.assertEqual(topo_order[0], "BGCD", "Topological order must begin with opening node BGCD")

    def test_04_lean_audit_cross_check(self):
        """Verifies that all headline theorems for open/ready nodes are audited in Amort/Audit.lean."""
        errors = self.validator.validate_audit_theorems()
        self.assertEqual(errors, [], f"Unverified theorems declared: {errors}")

    def test_05_mermaid_syntax_structure(self):
        """Verifies that SKILL_TREE_TUTORIAL_PLAN.md contains a valid Mermaid diagram with 28 nodes."""
        self.assertTrue(PLAN_MD_PATH.exists(), f"Missing {PLAN_MD_PATH}")
        content = PLAN_MD_PATH.read_text(encoding="utf-8")
        mermaid_match = re.search(r"```mermaid\s*\n(.*?)\n```", content, re.DOTALL)
        self.assertIsNotNone(mermaid_match, "No Mermaid block found in SKILL_TREE_TUTORIAL_PLAN.md")
        mermaid_code = mermaid_match.group(1)

        # Check classes
        self.assertIn("classDef open", mermaid_code)
        self.assertIn("classDef ready", mermaid_code)
        self.assertIn("classDef planned", mermaid_code)

        # Check root and major nodes
        self.assertIn("BGCD", mermaid_code)
        self.assertIn("MERGE", mermaid_code)
        self.assertIn("LIS", mermaid_code)
        self.assertIn("KRUS", mermaid_code)

    def test_06_cli_validate_if_present(self):
        """CLI Test: runs python3 scripts/tree_tool.py --validate and expects exit code 0."""
        if not TREE_TOOL_PATH.exists():
            self.skipTest("scripts/tree_tool.py not yet implemented by M1")

        result = subprocess.run(
            [sys.executable, str(TREE_TOOL_PATH), "--validate"],
            capture_output=True,
            text=True
        )
        self.assertEqual(result.returncode, 0, f"tree_tool.py --validate failed:\n{result.stderr}\n{result.stdout}")

    def test_07_cli_stats_if_present(self):
        """CLI Test: runs python3 scripts/tree_tool.py --stats and verifies metrics."""
        if not TREE_TOOL_PATH.exists():
            self.skipTest("scripts/tree_tool.py not yet implemented by M1")

        result = subprocess.run(
            [sys.executable, str(TREE_TOOL_PATH), "--stats"],
            capture_output=True,
            text=True
        )
        self.assertEqual(result.returncode, 0)
        output = result.stdout
        self.assertIn("28", output, "Stats output should report 28 total nodes")


# ==============================================================================
# Tier 2: Boundary Value Analysis & Corner Cases
# ==============================================================================
class TestTreeToolBoundaryAndCornerCases(unittest.TestCase):
    """Tier 2: Injects deliberate graph and metadata faults to verify rejection."""

    def setUp(self):
        self.base_data = get_base_tree_data()

    def run_cli_with_temp_json(self, mutated_data, extra_args=None):
        """Helper to invoke CLI with mutated JSON fixture."""
        if not TREE_TOOL_PATH.exists():
            return None

        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
            json.dump(mutated_data, tf, indent=2)
            temp_path = tf.name

        try:
            cmd = [sys.executable, str(TREE_TOOL_PATH), "--file", temp_path, "--validate"]
            if extra_args:
                cmd.extend(extra_args)
            res = subprocess.run(cmd, capture_output=True, text=True)
            return res
        finally:
            if os.path.exists(temp_path):
                os.remove(temp_path)

    def test_01_cycle_injection_detection_direct(self):
        """Fault Injection: Injects direct cycle BGCD -> INS -> BGCD."""
        mutated = json.loads(json.dumps(self.base_data))
        # Find INS and add BGCD to its unlocks
        for n in mutated["nodes"]:
            if n["id"] == "INS":
                n["unlocks"].append("BGCD")
            if n["id"] == "BGCD":
                n["prerequisites"].append("INS")

        validator = SkillTreeValidator(mutated)
        is_acyclic, err, _ = validator.validate_acyclicity_and_toposort()
        self.assertFalse(is_acyclic, "Validator must detect direct cycle")

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit with non-zero on cycle")

    def test_02_cycle_injection_detection_long(self):
        """Fault Injection: Injects long back-edge from Tier 6 LIS to Tier 1 BGCD."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "LIS":
                n["unlocks"].append("BGCD")
            if n["id"] == "BGCD":
                n["prerequisites"].append("LIS")

        validator = SkillTreeValidator(mutated)
        is_acyclic, err, _ = validator.validate_acyclicity_and_toposort()
        self.assertFalse(is_acyclic, "Validator must detect long sink-to-root cycle")

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit with non-zero on cycle")

    def test_03_missing_prerequisite_id_rejection(self):
        """Fault Injection: Node references non-existent prerequisite ID."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "MERGE":
                n["prerequisites"].append("NONEXISTENT_NODE_XYZ")

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_bidirectional_symmetry()
        self.assertTrue(any("non-existent prerequisite" in e for e in errors))

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit non-zero for dangling prerequisite")

    def test_04_asymmetric_prerequisite_unlock_rejection(self):
        """Fault Injection: A unlocks B, but B does not list A in prerequisites."""
        mutated = json.loads(json.dumps(self.base_data))
        # Remove BGCD from EUC.prerequisites while BGCD still unlocks EUC
        for n in mutated["nodes"]:
            if n["id"] == "EUC":
                n["prerequisites"].remove("BGCD")

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_bidirectional_symmetry()
        self.assertTrue(any("Asymmetry" in e for e in errors))

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit non-zero for asymmetric link")

    def test_05_unverified_theorem_claimed_for_ready_node(self):
        """Fault Injection: Ready node claims theorem not in Amort/Audit.lean."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "INS":
                n["headline_theorems"].append("Nat.completely_fake_unverified_theorem")

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_audit_theorems()
        self.assertTrue(any("Nat.completely_fake_unverified_theorem" in e for e in errors))

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit non-zero for unverified theorem")

    def test_06_empty_exercises_on_ready_node(self):
        """Fault Injection: Ready node has empty predict exercises."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "EUC":
                n["exercises"]["predict"] = []

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_schema()
        self.assertTrue(any("empty predict exercises" in e for e in errors))

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit non-zero for empty exercises")

    def test_07_duplicate_node_ids_rejection(self):
        """Fault Injection: Injects duplicate node with id 'BGCD'."""
        mutated = json.loads(json.dumps(self.base_data))
        dup_node = dict(mutated["nodes"][0])
        dup_node["name"] = "Duplicate BGCD"
        mutated["nodes"].append(dup_node)

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_schema()
        self.assertTrue(any("Duplicate node ID" in e for e in errors))

        res = self.run_cli_with_temp_json(mutated)
        if res is not None:
            self.assertNotEqual(res.returncode, 0, "CLI must exit non-zero for duplicate node IDs")

    def test_08_multiple_roots_rejection(self):
        """Fault Injection: Second node defined with empty prerequisites."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "MODEXP":
                n["prerequisites"] = []
                n["status"] = "open"

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_schema()
        self.assertTrue(any("Expected exactly 1 open root node" in e for e in errors))

    def test_09_planned_node_with_theorems_rejection(self):
        """Fault Injection: Planned node claims headline theorems."""
        mutated = json.loads(json.dumps(self.base_data))
        for n in mutated["nodes"]:
            if n["id"] == "HEAP":
                n["headline_theorems"] = ["Nat.gcd_dvd_left"]

        validator = SkillTreeValidator(mutated)
        errors = validator.validate_schema()
        self.assertTrue(any("must not declare headline theorems" in e for e in errors))


# ==============================================================================
# Tier 3: Cross-Feature Combinations
# ==============================================================================
class TestTreeToolCrossFeatureCombinations(unittest.TestCase):
    """Tier 3: Markdown synchronization fidelity and drift detection."""

    def test_01_mermaid_sync_preserves_markdown_prose(self):
        """Verifies that --sync-mermaid preserves text before and after the Mermaid code block."""
        if not TREE_TOOL_PATH.exists():
            self.skipTest("scripts/tree_tool.py not yet implemented by M1")

        sample_markdown = (
            "# Title of Document\n\n"
            "Preceding curriculum prose that must remain untouched.\n\n"
            "## 4.2 The tree\n\n"
            "```mermaid\n"
            "flowchart TD\n"
            "    OLD --> DIAGRAM\n"
            "```\n\n"
            "## 4.3 Node catalogue\n\n"
            "Following prose table that must remain untouched.\n"
        )

        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
            tf.write(sample_markdown)
            temp_md_path = tf.name

        try:
            # Run --sync-mermaid targeting this temp file
            res = subprocess.run(
                [sys.executable, str(TREE_TOOL_PATH), "--plan", temp_md_path, "--sync-mermaid"],
                capture_output=True,
                text=True
            )
            self.assertEqual(res.returncode, 0, f"--sync-mermaid failed: {res.stderr}\n{res.stdout}")

            updated_content = Path(temp_md_path).read_text(encoding="utf-8")
            self.assertTrue(updated_content.startswith("# Title of Document\n\nPreceding curriculum prose that must remain untouched."))
            self.assertIn("## 4.3 Node catalogue\n\nFollowing prose table that must remain untouched.", updated_content)
            self.assertIn("BGCD", updated_content)
            self.assertNotIn("OLD --> DIAGRAM", updated_content)
        finally:
            if os.path.exists(temp_md_path):
                os.remove(temp_md_path)

    def test_02_mermaid_sync_drift_check(self):
        """Verifies that --sync-mermaid --check detects drift when markdown is stale."""
        if not TREE_TOOL_PATH.exists():
            self.skipTest("scripts/tree_tool.py not yet implemented by M1")

        stale_markdown = (
            "## 4.2 The tree\n\n"
            "```mermaid\n"
            "flowchart TD\n"
            "    STALE_NODE --> ANOTHER_STALE_NODE\n"
            "```\n"
        )

        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
            tf.write(stale_markdown)
            temp_md_path = tf.name

        try:
            res = subprocess.run(
                [sys.executable, str(TREE_TOOL_PATH), "--plan", temp_md_path, "--sync-mermaid", "--check"],
                capture_output=True,
                text=True
            )
            self.assertNotEqual(res.returncode, 0, "--check must exit non-zero when Mermaid diagram has drifted")
        finally:
            if os.path.exists(temp_md_path):
                os.remove(temp_md_path)

    def test_03_mermaid_dynamic_edge_generation(self):
        """Verifies that generate_mermaid_diagram extracts edges dynamically from tree_data nodes."""
        sys.path.insert(0, str(REPO_ROOT))
        from scripts.tree_tool import generate_mermaid_diagram

        base_data = get_base_tree_data()
        diagram = generate_mermaid_diagram(base_data)
        self.assertIn("BGCD --> EUC", diagram)
        self.assertIn("DYN -.-> HEAP", diagram)

        # Mutate by adding a new dynamic node and unlock edge
        mutated = json.loads(json.dumps(base_data))
        new_node = {
            "id": "NEW_NODE",
            "name": "New Dynamic Node",
            "tier": 2,
            "category": "sorting",
            "status": "ready",
            "prerequisites": ["BGCD"],
            "unlocks": [],
            "algorithm_skill": "Dynamic testing",
            "lean_skill": "Testing",
            "reference_module": "Amort.Sorting",
            "headline_theorems": [],
            "chapter_path": "tutorial/new_node.md",
            "exercises": {"predict": [], "spot_the_fake": []}
        }
        mutated["nodes"].append(new_node)
        # Add unlock from BGCD to NEW_NODE
        for n in mutated["nodes"]:
            if n["id"] == "BGCD":
                n["unlocks"].append("NEW_NODE")

        mutated_diagram = generate_mermaid_diagram(mutated)
        self.assertIn("NEW_NODE", mutated_diagram, "Dynamically added node must appear in diagram")
        self.assertIn("BGCD --> NEW_NODE", mutated_diagram, "Dynamic unlock edge must be generated")

        # Mutate to planned status and verify dashed line
        new_node["status"] = "planned"
        planned_diagram = generate_mermaid_diagram(mutated)
        self.assertIn("BGCD -.-> NEW_NODE", planned_diagram, "Planned node target must render dashed arrow -.->")


if __name__ == "__main__":
    unittest.main()
