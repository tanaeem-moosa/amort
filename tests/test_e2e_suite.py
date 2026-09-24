#!/usr/bin/env python3
"""
tests/test_e2e_suite.py: Comprehensive End-to-End Test Suite for the Verified Algorithms Skill Tree.

Covers Tiers 1 through 4:
- Tier 1: Feature Coverage (Static HTTP serving, DOM structure, tree.json schema, 28-node count, category taxonomy)
- Tier 2: Boundary Value Analysis & Corner Cases (Local file:// fallback docs/tree_data.js, malformed savefile rejection,
          empty quiz answers, incorrect quiz answers, zoom clamping boundaries)
- Tier 3: Cross-Feature Combinations (Savefile export/import round-trip, multi-hop fan-in unlock convergence for MERGE and KMP,
          deep unlock chain to Tier 6 LIS, mixed answers persistence)
- Tier 4: Real-World Learner Workload Scenarios (Full session: fresh visit -> BGCD active -> quiz solving -> BGCD mastered ->
          Tier 2 unlocked -> savefile export -> reset -> restore; branched sorting curriculum pathway)
"""

import unittest
import sys
import os
import json
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = REPO_ROOT / "docs"
TREE_JSON = REPO_ROOT / "tutorial" / "tree.json"
INDEX_HTML = DOCS_DIR / "index.html"
FALLBACK_JS = DOCS_DIR / "tree_data.js"

# Import engine simulator and helpers from scripts/test_webapp.py
sys.path.insert(0, str(REPO_ROOT))
from scripts.test_webapp import (
    SkillTreeSimulator,
    WebAppDOMValidator,
    EphemeralServer,
    clamp_zoom,
    CANONICAL_NODE_IDS,
    CANONICAL_TIERS,
    CANONICAL_PREREQS,
    CANONICAL_UNLOCKS,
    PLANNED_NODES
)


# ==============================================================================
# Tier 1: Feature Coverage
# ==============================================================================
class TestTier1WebappStaticServingAndDOM(unittest.TestCase):
    """Tier 1: Feature Coverage for HTTP serving, DOM structure, and DAG data."""

    def test_01_http_serving(self):
        """Verifies HTTP serving of web application assets via Python's standard http.server."""
        with EphemeralServer(REPO_ROOT) as srv:
            base_url = f"http://127.0.0.1:{srv.port}"
            # Test tree.json if exists
            if TREE_JSON.exists():
                url = f"{base_url}/tutorial/tree.json"
                req = urllib.request.Request(url)
                with urllib.request.urlopen(req, timeout=5) as resp:
                    self.assertEqual(resp.status, 200)
                    content = resp.read().decode("utf-8")
                    data = json.loads(content)
                    self.assertEqual(len(data.get("nodes", [])), 28)

            # Test index.html if exists
            if INDEX_HTML.exists():
                url = f"{base_url}/docs/index.html"
                req = urllib.request.Request(url)
                with urllib.request.urlopen(req, timeout=5) as resp:
                    self.assertEqual(resp.status, 200)
                    html = resp.read().decode("utf-8")
                    self.assertIn("Verified Algorithms Skill Tree", html)

    def test_02_dom_elements_structure(self):
        """Verifies DOM elements exist in docs/index.html when present."""
        if not INDEX_HTML.exists():
            self.skipTest("docs/index.html not yet created by M4")

        html_text = INDEX_HTML.read_text(encoding="utf-8")
        parser = WebAppDOMValidator()
        parser.feed(html_text)

        self.assertTrue(parser.found_canvas, "Canvas container (#canvas-container or #canvas-world) missing in index.html")
        self.assertTrue(parser.found_svg, "SVG layer (#tree-svg) missing in index.html")
        self.assertTrue(parser.found_nodes_layer, "Nodes container (#nodes-layer) missing in index.html")
        self.assertTrue(parser.found_drawer, "Inspector drawer (<dialog>) missing in index.html")
        self.assertTrue(parser.found_quiz_container, "#quiz-container missing in index.html")

        # Tabs
        self.assertIn("specs", parser.found_tabs, "Tab [data-tab='specs'] missing in inspector drawer")
        self.assertIn("quiz", parser.found_tabs, "Tab [data-tab='quiz'] missing in inspector drawer")
        self.assertIn("chapter", parser.found_tabs, "Tab [data-tab='chapter'] missing in inspector drawer")

        # Savefile controls
        for ctrl in ("btn-export-save", "file-import-save", "btn-reset-save"):
            self.assertIn(ctrl, parser.all_ids, f"Control #{ctrl} missing in index.html")

    def test_03_tree_json_loading(self):
        """Verifies tutorial/tree.json contains 28 nodes, top-level metadata, and 8 categories."""
        if not TREE_JSON.exists():
            self.skipTest("tutorial/tree.json not yet created by M1")

        with open(TREE_JSON, "r", encoding="utf-8") as f:
            data = json.load(f)

        self.assertIn("schema_version", data)
        self.assertIn("categories", data)
        self.assertIn("nodes", data)
        self.assertEqual(len(data["nodes"]), 28)
        self.assertEqual(len(data["categories"]), 8)

    def test_04_node_cardinality_and_tiers(self):
        """Verifies canonical 28 nodes across 6 tiers."""
        sim = SkillTreeSimulator()
        self.assertEqual(len(sim.nodes), 28)
        tier_counts = {}
        for n in sim.nodes:
            t = n["tier"]
            tier_counts[t] = tier_counts.get(t, 0) + 1

        self.assertEqual(tier_counts.get(1), 1, "Tier 1 must contain exactly 1 node (BGCD)")
        self.assertEqual(tier_counts.get(2), 5, "Tier 2 must contain exactly 5 nodes")
        self.assertEqual(tier_counts.get(3), 5, "Tier 3 must contain exactly 5 nodes")
        self.assertEqual(tier_counts.get(4), 7, "Tier 4 must contain exactly 7 nodes")
        self.assertEqual(tier_counts.get(5), 8, "Tier 5 must contain exactly 8 nodes")
        self.assertEqual(tier_counts.get(6), 2, "Tier 6 must contain exactly 2 nodes (LIS, KRUS)")

    def test_05_category_taxonomy(self):
        """Verifies the 8 canonical categories in tree.json."""
        if not TREE_JSON.exists():
            self.skipTest("tutorial/tree.json not yet created by M1")

        with open(TREE_JSON, "r", encoding="utf-8") as f:
            data = json.load(f)

        expected_categories = {
            "arithmetic", "sorting", "amortization", "strings",
            "dp", "greedy", "graphs", "complexity"
        }
        found_categories = {c["id"] for c in data["categories"]}
        self.assertEqual(found_categories, expected_categories)
        for cat in data["categories"]:
            self.assertTrue(cat.get("name"), f"Category {cat['id']} missing display name")
            self.assertTrue(cat.get("color"), f"Category {cat['id']} missing color")


# ==============================================================================
# Tier 2: Boundary Value Analysis & Corner Cases
# ==============================================================================
class TestTier2WebappBoundariesAndCornerCases(unittest.TestCase):
    """Tier 2: Boundary value testing for savefile, quizzes, zoom, and offline fallbacks."""

    def test_01_tree_data_offline_fallback(self):
        """Verifies docs/tree_data.js contains valid offline fallback snapshot when present."""
        if not FALLBACK_JS.exists():
            self.skipTest("docs/tree_data.js not yet created by M4")

        content = FALLBACK_JS.read_text(encoding="utf-8")
        self.assertTrue("__TREE_DATA_FALLBACK__" in content or "treeData" in content)
        # Verify JSON content inside JS variable
        import re
        match = re.search(r"=\s*(\{.*\})\s*;?", content, re.DOTALL)
        self.assertIsNotNone(match, "Failed to parse JSON payload in docs/tree_data.js")
        parsed = json.loads(match.group(1))
        self.assertEqual(len(parsed.get("nodes", [])), 28)

    def test_02_malformed_savefile_rejections(self):
        """Boundary: Rejects corrupt JSON strings, missing fields, invalid types, and tampered nodes."""
        sim = SkillTreeSimulator()

        # 1. Non-dict payload
        with self.assertRaises(ValueError):
            sim.import_savefile("malformed string")

        # 2. Missing schema_version
        with self.assertRaises(ValueError):
            sim.import_savefile({"mastered_nodes": []})

        # 3. Wrong schema version
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "2.0.0", "mastered_nodes": []})

        # 4. Non-list mastered_nodes
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": 123})

        # 5. Non-existent node ID
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["NONEXISTENT_999"]})

        # 6. Tampered: claiming planned node as mastered
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["HEAP"]})

        # 7. Tampered: missing prerequisite topological closure
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["LIS"], "answers": {}})

        # 8. Malformed: array answers field
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": [1, 2, 3]})

        # 9. Malformed: primitive answers field
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": "invalid"})

        # 10. Malformed: primitive entry inside answers
        with self.assertRaises(ValueError):
            sim.import_savefile({"schema_version": "1.0.0", "mastered_nodes": ["BGCD"], "answers": {"BGCD": "corrupt"}})

    def test_03_empty_and_whitespace_quiz_answers(self):
        """Boundary: Empty or whitespace quiz submissions must be rejected."""
        sim = SkillTreeSimulator()
        ok, msg = sim.submit_quiz_answer("BGCD", "predict", "p1", "", "6")
        self.assertFalse(ok)
        self.assertIn("cannot be empty", msg)

        ok, msg = sim.submit_quiz_answer("BGCD", "predict", "p1", "   ", "6")
        self.assertFalse(ok)
        self.assertIn("cannot be empty", msg)

        ok, msg = sim.submit_quiz_answer("BGCD", "predict", "p1", None, "6")
        self.assertFalse(ok)
        self.assertIn("cannot be empty", msg)

    def test_04_incorrect_quiz_answers_do_not_unlock(self):
        """Boundary: Incorrect quiz answers must not grant mastery."""
        sim = SkillTreeSimulator()
        ok, msg = sim.submit_quiz_answer("BGCD", "predict", "p1", "42", "6")
        self.assertFalse(ok)
        self.assertIn("Incorrect", msg)

        states = sim.compute_node_states()
        self.assertEqual(states["BGCD"], "active")
        self.assertEqual(states["EUC"], "locked")

    def test_05_zoom_scaling_boundaries(self):
        """Boundary: Viewport zoom scale must clamp within [0.25, 3.0]."""
        self.assertEqual(clamp_zoom(0.05), 0.25)
        self.assertEqual(clamp_zoom(0.25), 0.25)
        self.assertEqual(clamp_zoom(1.0), 1.0)
        self.assertEqual(clamp_zoom(3.0), 3.0)
        self.assertEqual(clamp_zoom(5.5), 3.0)
        self.assertEqual(clamp_zoom(-1.0), 1.0, "Negative scale should reset to 1.0")
        self.assertEqual(clamp_zoom("invalid"), 1.0, "Invalid scale should reset to 1.0")

    def test_06_locked_nodes_cannot_be_marked_mastered_directly(self):
        """Boundary: Locked nodes cannot be marked mastered directly before prerequisites are satisfied."""
        sim = SkillTreeSimulator()
        # Fresh visit: only BGCD is active, EUC and LIS are locked
        with self.assertRaises(ValueError):
            sim.mark_mastered("EUC")

        with self.assertRaises(ValueError):
            sim.mark_mastered("LIS")

        with self.assertRaises(ValueError):
            sim.mark_mastered("MERGE")

    def test_07_locked_node_quiz_tab_renders_locked_state(self):
        """Boundary: Locked nodes render locked notification banner and prohibit active quiz forms."""
        import subprocess
        node_script = """
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
        res = subprocess.run(["node", "-e", node_script], cwd=str(REPO_ROOT), capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, f"Node script execution failed: {res.stderr}")
        data = json.loads(res.stdout)
        self.assertTrue(data["isLockedBanner"], "Locked node quiz tab must display locked banner")
        self.assertFalse(data["hasActiveForm"], "Locked node quiz tab must not render active input forms")


# ==============================================================================
# Tier 3: Cross-Feature Combinations
# ==============================================================================
class TestTier3CrossFeatureCombinations(unittest.TestCase):
    """Tier 3: Multi-hop unlock propagation, multi-parent fan-in, and savefile round-trip."""

    def test_01_savefile_roundtrip_mastered_state(self):
        """Pairwise: Export savefile -> reset -> import restores exact mastered set and answers."""
        sim = SkillTreeSimulator()
        sim.mark_mastered("BGCD")
        sim.mark_mastered("INS")
        sim.mark_mastered("BS")
        sim.mark_mastered("MERGE")
        sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "6", "6")
        sim.submit_quiz_answer("BGCD", "spot_the_fake", "bgcd_fake_1", "b", "b")

        orig_mastered = set(sim.mastered_nodes)
        orig_answers = json.loads(json.dumps(sim.answers))
        orig_states = sim.compute_node_states()

        # Export
        save = sim.export_savefile()
        self.assertEqual(save["schema_version"], "1.0.0")

        # Reset
        sim.reset_progress()
        reset_states = sim.compute_node_states()
        self.assertEqual(len(sim.mastered_nodes), 0)
        self.assertEqual(reset_states["MERGE"], "locked")

        # Import
        restored_states = sim.import_savefile(save)
        self.assertEqual(set(sim.mastered_nodes), orig_mastered)
        self.assertEqual(sim.answers, orig_answers)
        self.assertEqual(restored_states, orig_states)
        self.assertEqual(restored_states["MERGE"], "mastered")
        self.assertEqual(restored_states["LB"], "active")

    def test_02_multi_hop_unlock_fan_in_merge(self):
        """Cross-feature: MERGE requires both INS and BS (fan-in convergence)."""
        sim = SkillTreeSimulator()
        sim.mark_mastered("BGCD")
        states = sim.compute_node_states()
        self.assertEqual(states["INS"], "active")
        self.assertEqual(states["BS"], "active")
        self.assertEqual(states["MERGE"], "locked")

        # Master only INS
        states = sim.mark_mastered("INS")
        self.assertEqual(states["MERGE"], "locked", "MERGE must remain locked when only INS is mastered")

        # Master BS
        states = sim.mark_mastered("BS")
        self.assertEqual(states["MERGE"], "active", "MERGE must unlock when both INS and BS are mastered")

    def test_03_multi_hop_unlock_fan_in_kmp(self):
        """Cross-feature: KMP requires both NAIVE and TSQ (fan-in convergence)."""
        sim = SkillTreeSimulator()
        sim.mark_mastered("BGCD")
        sim.mark_mastered("INS")
        sim.mark_mastered("DYN")
        states = sim.compute_node_states()

        self.assertEqual(states["NAIVE"], "active")
        self.assertEqual(states["TSQ"], "active")

        # Master only TSQ
        states = sim.mark_mastered("TSQ")
        states = sim.compute_node_states()
        self.assertEqual(states["KMP"], "locked", "KMP must remain locked when only TSQ is mastered")

        # Master NAIVE
        states = sim.mark_mastered("NAIVE")
        self.assertEqual(states["KMP"], "active", "KMP must unlock when both NAIVE and TSQ are mastered")

    def test_04_deep_chain_unlock_to_tier6(self):
        """Cross-feature: Deep propagation: BGCD -> INS -> NAIVE -> LCS -> KNAP -> LIS (Tier 6)."""
        sim = SkillTreeSimulator()
        sim.mark_mastered("BGCD")
        sim.mark_mastered("INS")
        sim.mark_mastered("NAIVE")
        states = sim.compute_node_states()
        self.assertEqual(states["LCS"], "active")
        self.assertEqual(states["KNAP"], "locked")
        self.assertEqual(states["LIS"], "locked")

        sim.mark_mastered("LCS")
        states = sim.compute_node_states()
        self.assertEqual(states["KNAP"], "active")
        self.assertEqual(states["LIS"], "locked")

        sim.mark_mastered("KNAP")
        states = sim.compute_node_states()
        self.assertEqual(states["LIS"], "active", "LIS (Tier 6 sink) must unlock when KNAP is mastered")

    def test_05_planned_nodes_never_unlock(self):
        """Cross-feature: Planned nodes (HEAP, DIJ, DSU, KRUS, Z, AC) always remain in 'planned' state."""
        sim = SkillTreeSimulator()
        # Master all prerequisite ancestors of HEAP
        sim.mark_mastered("BGCD")
        sim.mark_mastered("DYN")
        states = sim.compute_node_states()
        self.assertEqual(states["HEAP"], "planned", "Planned node HEAP must remain in 'planned' state")

        with self.assertRaises(ValueError):
            sim.mark_mastered("HEAP")


# ==============================================================================
# Tier 4: Real-World Learner Workload Scenarios
# ==============================================================================
class TestTier4RealWorldLearnerWorkload(unittest.TestCase):
    """Tier 4: Authentic learner workflows from fresh load to multi-topic mastery and backup."""

    def test_01_complete_learner_journey(self):
        """Simulates full learner journey: fresh visit -> solve BGCD -> unlock Tier 2 -> export -> reset -> restore."""
        sim = SkillTreeSimulator()

        # 1. Fresh Visit
        states = sim.compute_node_states()
        self.assertEqual(states["BGCD"], "active")
        self.assertEqual(sum(1 for s in states.values() if s == "mastered"), 0)
        self.assertEqual(sum(1 for s in states.values() if s == "locked"), 21)
        self.assertEqual(sum(1 for s in states.values() if s == "planned"), 6)

        # 2. Solves BGCD Quizzes
        pred_ok, _ = sim.submit_quiz_answer("BGCD", "predict", "bgcd_pred_1", "6", "6")
        self.assertTrue(pred_ok)
        fake_ok, _ = sim.submit_quiz_answer("BGCD", "spot_the_fake", "bgcd_fake_1", "b", "b")
        self.assertTrue(fake_ok)

        # 3. Marks BGCD Mastered
        states = sim.mark_mastered("BGCD")
        self.assertEqual(states["BGCD"], "mastered")
        self.assertEqual(len(sim.mastered_nodes), 1)

        # 4. Verify Downstream Unlocks
        for t2 in ["EUC", "INS", "BS", "DYN", "MODEXP"]:
            self.assertEqual(states[t2], "active", f"{t2} must be active after BGCD mastery")

        # 5. Export Savefile
        savefile = sim.export_savefile()
        self.assertEqual(savefile["schema_version"], "1.0.0")
        self.assertIn("BGCD", savefile["mastered_nodes"])

        # 6. Reset Session
        sim.reset_progress()
        post_reset = sim.compute_node_states()
        self.assertEqual(post_reset["BGCD"], "active")
        self.assertEqual(post_reset["EUC"], "locked")
        self.assertEqual(len(sim.mastered_nodes), 0)

        # 7. Import Savefile and Restore Session
        restored = sim.import_savefile(savefile)
        self.assertEqual(restored["BGCD"], "mastered")
        self.assertEqual(restored["EUC"], "active")
        self.assertEqual(restored["INS"], "active")
        self.assertEqual(len(sim.mastered_nodes), 1)

    def test_02_branched_sorting_curriculum_workflow(self):
        """Simulates learner following the Sorting & Searching curriculum path."""
        sim = SkillTreeSimulator()
        sim.mark_mastered("BGCD")

        # Learner tackles Insertion Sort
        sim.submit_quiz_answer("INS", "predict", "ins_pred_1", "10", "10")
        sim.submit_quiz_answer("INS", "spot_the_fake", "ins_fake_1", "b", "b")
        sim.mark_mastered("INS")

        # Learner tackles Binary Search
        sim.submit_quiz_answer("BS", "predict", "bs_pred_1", "3", "3")
        sim.submit_quiz_answer("BS", "spot_the_fake", "bs_fake_1", "a", "a")
        sim.mark_mastered("BS")

        # Merge Sort unlocks
        states = sim.compute_node_states()
        self.assertEqual(states["MERGE"], "active")

        # Learner masters Merge Sort
        sim.submit_quiz_answer("MERGE", "predict", "merge_pred_1", "8", "8")
        sim.mark_mastered("MERGE")

        # Tier 4 sorting nodes unlock
        states = sim.compute_node_states()
        self.assertEqual(states["LB"], "active")
        self.assertEqual(states["QS"], "active")
        self.assertEqual(states["INTV"], "active")

        # Learner exports their savefile
        savefile = sim.export_savefile()
        self.assertEqual(set(savefile["mastered_nodes"]), {"BGCD", "INS", "BS", "MERGE"})
        self.assertEqual(len(savefile["answers"]), 3)

        # Verify full recovery across fresh simulator
        new_sim = SkillTreeSimulator()
        restored = new_sim.import_savefile(savefile)
        self.assertEqual(restored["MERGE"], "mastered")
        self.assertEqual(restored["LB"], "active")
        self.assertEqual(restored["QS"], "active")
        self.assertEqual(restored["INTV"], "active")


if __name__ == "__main__":
    unittest.main()
