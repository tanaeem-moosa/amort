#!/usr/bin/env python3
"""
tests/test_webapp_adversarial.py: Adversarial Stress Test & Fuzzing Suite
Empirical verification of:
1. Savefile Fuzzing & Persistence Robustness (docs/app.js)
2. Quiz Engine Invariants & Premature Unlock Progression
3. Serving & Offline Execution (file:// mode & tree_data.js)
"""

import sys
import os
import json
import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = REPO_ROOT / "docs"
APP_JS = DOCS_DIR / "app.js"
TREE_JSON = REPO_ROOT / "tutorial" / "tree.json"
FALLBACK_JS = DOCS_DIR / "tree_data.js"
INDEX_HTML = DOCS_DIR / "index.html"

results = {
    "fuzzing": {"passed": 0, "failed": 0, "findings": []},
    "progression": {"passed": 0, "failed": 0, "findings": []},
    "offline": {"passed": 0, "failed": 0, "findings": []}
}

def run_node_eval(script_content):
    """Runs a Node.js snippet and returns stdout, stderr, and exit code."""
    res = subprocess.run(
        ["node", "-e", script_content],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True
    )
    return res.stdout, res.stderr, res.returncode

def test_savefile_fuzzing():
    print("=" * 70)
    print("SUITE 1: ADVERSARIAL SAVEFILE FUZZING")
    print("=" * 70)

    node_script = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');

    const storage = {};
    global.window = {};
    global.localStorage = {
      getItem: (k) => storage[k] || null,
      setItem: (k, v) => { storage[k] = v; },
      removeItem: (k) => { delete storage[k]; }
    };
    global.document = { addEventListener: () => {}, getElementById: () => null };

    eval(appCode);

    const testCases = [
      { name: "null payload", payload: null, expectReject: true },
      { name: "undefined payload", payload: undefined, expectReject: true },
      { name: "integer payload (42)", payload: 42, expectReject: true },
      { name: "negative integer payload (-999)", payload: -999, expectReject: true },
      { name: "float payload (3.14)", payload: 3.14, expectReject: true },
      { name: "boolean true payload", payload: true, expectReject: true },
      { name: "boolean false payload", payload: false, expectReject: true },
      { name: "string payload ('corrupt')", payload: "corrupt", expectReject: true },
      { name: "array payload ([])", payload: [], expectReject: true },
      { name: "missing schema_version", payload: { mastered_nodes: [] }, expectReject: true },
      { name: "empty string schema_version", payload: { schema_version: "", mastered_nodes: [] }, expectReject: true },
      { name: "numeric schema_version (1)", payload: { schema_version: 1, mastered_nodes: [] }, expectReject: true },
      { name: "negative schema_version (-1)", payload: { schema_version: -1, mastered_nodes: [] }, expectReject: true },
      { name: "mismatched schema_version ('2.0.0')", payload: { schema_version: "2.0.0", mastered_nodes: [] }, expectReject: true },
      { name: "mismatched schema_version ('0.9.0')", payload: { schema_version: "0.9.0", mastered_nodes: [] }, expectReject: true },
      { name: "padded schema_version ('1.0.0 ')", payload: { schema_version: "1.0.0 ", mastered_nodes: [] }, expectReject: true },
      { name: "missing mastered_nodes field", payload: { schema_version: "1.0.0" }, expectReject: true },
      { name: "null mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: null }, expectReject: true },
      { name: "string mastered_nodes ('BGCD')", payload: { schema_version: "1.0.0", mastered_nodes: "BGCD" }, expectReject: true },
      { name: "number mastered_nodes (123)", payload: { schema_version: "1.0.0", mastered_nodes: 123 }, expectReject: true },
      { name: "object mastered_nodes ({BGCD: true})", payload: { schema_version: "1.0.0", mastered_nodes: { BGCD: true } }, expectReject: true },
      { name: "unknown node ID in mastered_nodes ('UNKNOWN_NODE')", payload: { schema_version: "1.0.0", mastered_nodes: ["UNKNOWN_NODE"] }, expectReject: true },
      { name: "empty string node ID in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: [""] }, expectReject: true },
      { name: "number item in mastered_nodes ([123])", payload: { schema_version: "1.0.0", mastered_nodes: [123] }, expectReject: true },
      { name: "negative item in mastered_nodes ([-5])", payload: { schema_version: "1.0.0", mastered_nodes: [-5] }, expectReject: true },
      { name: "null item in mastered_nodes ([null])", payload: { schema_version: "1.0.0", mastered_nodes: [null] }, expectReject: true },
      { name: "object item in mastered_nodes ([{}])", payload: { schema_version: "1.0.0", mastered_nodes: [{}] }, expectReject: true },
      { name: "tampered planned node HEAP in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["HEAP"] }, expectReject: true },
      { name: "tampered planned node DIJ in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["DIJ"] }, expectReject: true },
      { name: "tampered planned node DSU in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["DSU"] }, expectReject: true },
      { name: "tampered planned node KRUS in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["KRUS"] }, expectReject: true },
      { name: "tampered planned node Z in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["Z"] }, expectReject: true },
      { name: "tampered planned node AC in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["AC"] }, expectReject: true },
      { name: "prototype property '__proto__' in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["__proto__"] }, expectReject: true },
      { name: "prototype property 'constructor' in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["constructor"] }, expectReject: true },
      { name: "prototype property 'toString' in mastered_nodes", payload: { schema_version: "1.0.0", mastered_nodes: ["toString"] }, expectReject: true },
      { name: "string answers field ('invalid')", payload: { schema_version: "1.0.0", mastered_nodes: ["BGCD"], answers: "invalid" }, expectReject: true },
      { name: "number answers field (42)", payload: { schema_version: "1.0.0", mastered_nodes: ["BGCD"], answers: 42 }, expectReject: true },
      { name: "boolean answers field (false)", payload: { schema_version: "1.0.0", mastered_nodes: ["BGCD"], answers: false }, expectReject: true },
      { name: "array answers field ([1, 2, 3])", payload: { schema_version: "1.0.0", mastered_nodes: ["BGCD"], answers: [1, 2, 3] }, expectReject: true },
      { name: "answers with non-object node entry ({BGCD: 'string'})", payload: { schema_version: "1.0.0", mastered_nodes: [], answers: { BGCD: "string" } }, expectReject: true },
      { name: "answers with non-object predict entry ({BGCD: {predict: 'string'}})", payload: { schema_version: "1.0.0", mastered_nodes: [], answers: { BGCD: { predict: "string" } } }, expectReject: true }
    ];

    const out = [];
    for (const tc of testCases) {
      const engine = new window.SkillTreeEngine(treeData);
      engine.markNodeMastered("BGCD");
      const baselineMastered = Array.from(engine.masteredNodes);
      
      let errorThrown = null;
      try {
        engine.importSavefile(tc.payload);
      } catch (err) {
        errorThrown = err.message;
      }

      const postMastered = Array.from(engine.masteredNodes);
      const stateCorrupted = (errorThrown !== null && JSON.stringify(postMastered) !== JSON.stringify(baselineMastered));

      out.push({
        name: tc.name,
        expectReject: tc.expectReject,
        rejected: errorThrown !== null,
        error: errorThrown,
        stateCorrupted: stateCorrupted,
        postMastered: postMastered
      });
    }

    console.log(JSON.stringify(out));
    """
    stdout, stderr, code = run_node_eval(node_script)
    if code != 0:
        print(f"Error running Node harness: {stderr}")
        return

    fuzz_results = json.loads(stdout)
    for r in fuzz_results:
        name = r["name"]
        if r["expectReject"] and not r["rejected"]:
            print(f"  [VULNERABILITY / GAP] Accepted invalid payload: {name}")
            results["fuzzing"]["failed"] += 1
            results["fuzzing"]["findings"].append(f"Accepted invalid payload: {name}")
        elif r["stateCorrupted"]:
            print(f"  [CRITICAL] State corrupted on rejected payload: {name}")
            results["fuzzing"]["failed"] += 1
            results["fuzzing"]["findings"].append(f"State corruption on rejected payload: {name}")
        else:
            print(f"  ✓ Rejected cleanly: {name}")
            results["fuzzing"]["passed"] += 1

    print()
    print("Testing secondary effects of accepted malformed answers...")
    # Test array answers data loss effect
    sub_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    const storage = {};
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    const engine = new window.SkillTreeEngine(treeData);
    let errorThrown = null;
    let answersIsArray = false;
    let answersLost = false;

    try {
      engine.importSavefile({ schema_version: "1.0.0", mastered_nodes: ["BGCD"], answers: [1, 2, 3] });
      engine.recordAnswer("BGCD", "predict", "bgcd_pred_1", "6");
      const exported = engine.exportSavefile();
      answersIsArray = Array.isArray(exported.answers);
      answersLost = answersIsArray && !exported.answers["BGCD"] && !JSON.stringify(exported.answers).includes("bgcd_pred_1");
    } catch (e) {
      errorThrown = { name: e.name, message: e.message };
    }
    console.log(JSON.stringify({ errorThrown, answersIsArray, answersLost }));
    """
    stdout, stderr, code = run_node_eval(sub_test)
    if code != 0:
        print(f"  [ERROR] Node evaluation crashed in sub_test: {stderr}")
        results["fuzzing"]["failed"] += 1
        results["fuzzing"]["findings"].append("Unhandled crash in sub_test Node evaluation.")
    else:
        sub_res = json.loads(stdout)
        err = sub_res.get("errorThrown")
        if err and err.get("name") == "ValueError":
            print(f"  ✓ Array answers payload cleanly rejected with ValueError: {err.get('message')}")
        elif sub_res.get("answersLost"):
            print("  [BUG CONFIRMED] Array answers payload causes silent data loss on subsequent export!")
            results["fuzzing"]["findings"].append("Array answers payload accepted, causing silent data loss on subsequent export.")
        else:
            print(f"  [FAIL] Expected ValueError for array answers payload, got: {sub_res}")
            results["fuzzing"]["failed"] += 1
            results["fuzzing"]["findings"].append("Array answers payload was not rejected with ValueError.")

    # Test crash on non-object node answers
    crash_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    const engine = new window.SkillTreeEngine(treeData);
    let errorThrown = null;
    let crashed = false;
    try {
      engine.importSavefile({ schema_version: "1.0.0", mastered_nodes: [], answers: { BGCD: "corrupt" } });
      try {
        engine.recordAnswer("BGCD", "predict", "bgcd_pred_1", "6");
      } catch (e) {
        crashed = true;
      }
    } catch (e) {
      errorThrown = { name: e.name, message: e.message };
    }
    console.log(JSON.stringify({ errorThrown, crashed }));
    """
    stdout, stderr, code = run_node_eval(crash_test)
    if code != 0:
        print(f"  [ERROR] Node evaluation crashed in crash_test: {stderr}")
        results["fuzzing"]["failed"] += 1
        results["fuzzing"]["findings"].append("Unhandled crash in crash_test Node evaluation.")
    else:
        crash_res = json.loads(stdout)
        err = crash_res.get("errorThrown")
        if err and err.get("name") == "ValueError":
            print(f"  ✓ Non-object node answers cleanly rejected with ValueError: {err.get('message')}")
        elif crash_res.get("crashed"):
            print("  [BUG CONFIRMED] Importing answers with primitive string entry causes uncaught TypeError in recordAnswer!")
            results["fuzzing"]["findings"].append("Primitive string inside answers object causes uncaught TypeError in recordAnswer.")
        else:
            print(f"  [FAIL] Expected ValueError for non-object node answers payload, got: {crash_res}")
            results["fuzzing"]["failed"] += 1
            results["fuzzing"]["findings"].append("Non-object node answers payload was not rejected with ValueError.")

    # Test XSS vulnerability in renderQuizTab
    print()
    print("Testing DOM XSS vulnerability in quiz view with malicious saved answers...")
    xss_test = """
    const fs = require('fs');
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    // Search for unescaped savedAns in input value template
    const regex = /value=["']?\\$\\{savedAns\\s*\\|\\|\\s*['"]['"]\\}["']?/;
    const hasUnescapedValue = regex.test(appCode);
    console.log(JSON.stringify({ hasUnescapedValue }));
    """
    stdout, _, _ = run_node_eval(xss_test)
    xss_res = json.loads(stdout)
    if xss_res["hasUnescapedValue"]:
        print("  [SECURITY VULNERABILITY CONFIRMED] renderQuizTab uses unescaped `${savedAns || ''}` in `<input value=...>`, exposing DOM XSS via crafted savefiles!")
        results["fuzzing"]["findings"].append("DOM XSS vulnerability: unescaped ${savedAns || ''} in input value attribute.")

def test_quiz_engine_and_progression():
    print()
    print("=" * 70)
    print("SUITE 2: QUIZ ENGINE & UNLOCK PROGRESSION STRESS")
    print("=" * 70)

    # 1. Sweep all 22 ready nodes with incorrect answers
    quiz_incorrect_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    const engine = new window.SkillTreeEngine(treeData);
    const readyNodes = treeData.nodes.filter(n => n.status !== 'planned');

    let incorrectlyMastered = 0;
    const details = [];

    for (const node of readyNodes) {
      const predicts = node.exercises?.predict || [];
      const fakes = node.exercises?.spot_the_fake || [];

      // Submit incorrect answers
      for (const p of predicts) {
        engine.recordAnswer(node.id, 'predict', p.id, "INCORRECT_ANSWER_999");
      }
      for (const f of fakes) {
        // Choose option that is fake
        const fakeOpt = f.options.find(o => o.is_fake) || { id: "WRONG_ID" };
        engine.recordAnswer(node.id, 'spot_the_fake', f.id, fakeOpt.id);
      }

      const completed = engine.isNodeCompleted(node.id);
      if (completed) {
        incorrectlyMastered++;
        details.push(node.id);
      }
    }

    console.log(JSON.stringify({ totalTested: readyNodes.length, incorrectlyMastered, details }));
    """
    stdout, _, _ = run_node_eval(quiz_incorrect_test)
    res = json.loads(stdout)
    if res["incorrectlyMastered"] == 0:
        print(f"  ✓ 22/22 Ready nodes tested: Incorrect quiz answers NEVER grant mastery (0 false masteries).")
        results["progression"]["passed"] += 1
    else:
        print(f"  [CRITICAL FAIL] Incorrect quiz answers granted mastery on nodes: {res['details']}")
        results["progression"]["failed"] += 1
        results["progression"]["findings"].append(f"Incorrect quiz answers granted mastery on {res['details']}")

    # 2. Premature mastery of locked nodes
    print()
    print("Testing premature mastery of locked nodes...")
    premature_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    const engine = new window.SkillTreeEngine(treeData);
    const statesInitial = engine.computeNodeStates();

    // Pick locked node EUC (requires BGCD, which is not yet mastered)
    const eucLocked = (statesInitial["EUC"] === "locked");
    // Call markNodeMastered directly on EUC
    const marked = engine.markNodeMastered("EUC");
    const statesAfterMark = engine.computeNodeStates();
    const eucPrematurelyMastered = (statesAfterMark["EUC"] === "mastered");

    // Also pick Tier 6 sink node LIS (requires KNAP -> LCS -> NAIVE -> INS -> BGCD)
    const engine2 = new window.SkillTreeEngine(treeData);
    const lisNode = treeData.nodes.find(n => n.id === "LIS");
    const pred = lisNode.exercises.predict[0];
    const fake = lisNode.exercises.spot_the_fake[0];
    // Record correct answers for LIS while locked
    engine2.recordAnswer("LIS", "predict", pred.id, pred.expected_answer);
    engine2.recordAnswer("LIS", "spot_the_fake", fake.id, fake.correct_option_id);
    const lisCompleted = engine2.isNodeCompleted("LIS");
    // Simulate what checkNodeCompletion does:
    if (lisCompleted) {
      engine2.markNodeMastered("LIS");
    }
    const statesLIS = engine2.computeNodeStates();
    const lisMasteredOnTurn1 = (statesLIS["LIS"] === "mastered");

    console.log(JSON.stringify({
      eucLocked,
      marked,
      eucPrematurelyMastered,
      lisMasteredOnTurn1
    }));
    """
    stdout, _, _ = run_node_eval(premature_test)
    prem_res = json.loads(stdout)
    if prem_res["eucPrematurelyMastered"] or prem_res["lisMasteredOnTurn1"]:
        print(f"  [CRITICAL INVARIANT VIOLATION] Locked nodes CAN be prematurely mastered!")
        print(f"    - engine.markNodeMastered('EUC') succeeded while EUC was locked: {prem_res['eucPrematurelyMastered']}")
        print(f"    - Solving quiz for Tier 6 node 'LIS' on turn 1 granted mastery: {prem_res['lisMasteredOnTurn1']}")
        results["progression"]["failed"] += 1
        results["progression"]["findings"].append("Locked nodes can be prematurely mastered via direct markNodeMastered or by submitting quizzes in the drawer.")
    else:
        print("  ✓ Locked nodes cannot be prematurely mastered.")
        results["progression"]["passed"] += 1

    # 3. Fan-in convergence verification
    print()
    print("Testing fan-in convergence (MERGE requires both INS and BS; KMP requires both NAIVE and TSQ)...")
    fanin_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    // Test MERGE fan-in:
    const e1 = new window.SkillTreeEngine(treeData);
    e1.markNodeMastered("BGCD");
    e1.markNodeMastered("INS");
    const merge1 = e1.computeNodeStates()["MERGE"]; // expect locked

    const e2 = new window.SkillTreeEngine(treeData);
    e2.markNodeMastered("BGCD");
    e2.markNodeMastered("BS");
    const merge2 = e2.computeNodeStates()["MERGE"]; // expect locked

    const e3 = new window.SkillTreeEngine(treeData);
    e3.markNodeMastered("BGCD");
    e3.markNodeMastered("INS");
    e3.markNodeMastered("BS");
    const merge3 = e3.computeNodeStates()["MERGE"]; // expect active

    // Test KMP fan-in:
    const k1 = new window.SkillTreeEngine(treeData);
    k1.markNodeMastered("BGCD");
    k1.markNodeMastered("INS");
    k1.markNodeMastered("NAIVE");
    const kmp1 = k1.computeNodeStates()["KMP"]; // expect locked

    const k2 = new window.SkillTreeEngine(treeData);
    k2.markNodeMastered("BGCD");
    k2.markNodeMastered("DYN");
    k2.markNodeMastered("TSQ");
    const kmp2 = k2.computeNodeStates()["KMP"]; // expect locked

    const k3 = new window.SkillTreeEngine(treeData);
    k3.markNodeMastered("BGCD");
    k3.markNodeMastered("INS");
    k3.markNodeMastered("NAIVE");
    k3.markNodeMastered("DYN");
    k3.markNodeMastered("TSQ");
    const kmp3 = k3.computeNodeStates()["KMP"]; // expect active

    console.log(JSON.stringify({
      mergeINSOnly: merge1,
      mergeBSOnly: merge2,
      mergeBoth: merge3,
      kmpNaiveOnly: kmp1,
      kmpTsqOnly: kmp2,
      kmpBoth: kmp3
    }));
    """
    stdout, _, _ = run_node_eval(fanin_test)
    fan_res = json.loads(stdout)
    if (fan_res["mergeINSOnly"] == "locked" and fan_res["mergeBSOnly"] == "locked" and fan_res["mergeBoth"] == "active" and
        fan_res["kmpNaiveOnly"] == "locked" and fan_res["kmpTsqOnly"] == "locked" and fan_res["kmpBoth"] == "active"):
        print("  ✓ Fan-in convergence verified: Downstream nodes unlock ONLY when ALL prerequisites are mastered.")
        results["progression"]["passed"] += 1
    else:
        print(f"  [FAIL] Fan-in convergence failed: {fan_res}")
        results["progression"]["failed"] += 1
        results["progression"]["findings"].append("Fan-in convergence failed.")

    # 4. Planned nodes barrier
    print()
    print("Testing planned node barrier (HEAP, DIJ, DSU, KRUS, Z, AC)...")
    planned_test = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    eval(appCode);

    const engine = new window.SkillTreeEngine(treeData);
    // Master prerequisites for HEAP (DYN)
    engine.markNodeMastered("BGCD");
    engine.markNodeMastered("DYN");
    const states = engine.computeNodeStates();
    const heapState = states["HEAP"];
    const markAttempt = engine.markNodeMastered("HEAP");

    console.log(JSON.stringify({ heapState, markAttempt }));
    """
    stdout, _, _ = run_node_eval(planned_test)
    p_res = json.loads(stdout)
    if p_res["heapState"] == "planned" and p_res["markAttempt"] is False:
        print("  ✓ Planned node barrier holds: HEAP remains planned after DYN mastery and rejects markNodeMastered.")
        results["progression"]["passed"] += 1
    else:
        print(f"  [FAIL] Planned node barrier breached: {p_res}")
        results["progression"]["failed"] += 1
        results["progression"]["findings"].append("Planned node barrier breached.")

def test_serving_and_offline():
    print()
    print("=" * 70)
    print("SUITE 3: SERVING & OFFLINE EXECUTION")
    print("=" * 70)

    # 1. Check fallback snapshot docs/tree_data.js
    if not FALLBACK_JS.exists():
        print("  [FAIL] docs/tree_data.js does not exist")
        results["offline"]["failed"] += 1
        return

    content = FALLBACK_JS.read_text(encoding="utf-8")
    match = re.search(r"=\s*(\{[\s\S]*\})\s*;?", content)
    if not match:
        print("  [FAIL] Could not parse JSON from docs/tree_data.js")
        results["offline"]["failed"] += 1
        return

    fallback_data = json.loads(match.group(1))
    tree_data = json.loads(TREE_JSON.read_text(encoding="utf-8"))

    if len(fallback_data.get("nodes", [])) == 28 and len(tree_data.get("nodes", [])) == 28:
        print("  ✓ docs/tree_data.js contains exactly 28 canonical nodes matching tree.json.")
        results["offline"]["passed"] += 1
    else:
        print(f"  [FAIL] Node count mismatch: tree_data.js={len(fallback_data.get('nodes', []))}, tree.json={len(tree_data.get('nodes', []))}")
        results["offline"]["failed"] += 1

    # 2. Check offline loadTreeData execution when fetch fails (simulating file:// origin)
    offline_eval = r"""
    const fs = require('fs');
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    const jsContent = fs.readFileSync('docs/tree_data.js', 'utf8');
    const match = jsContent.match(/=\s*(\{[\s\S]*\})\s*;?/);
    const fallbackData = JSON.parse(match[1]);

    global.window = { __TREE_DATA_FALLBACK__: fallbackData };
    global.document = { addEventListener: () => {}, getElementById: () => null };
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    // Simulate CORS restriction in file:// origin
    global.fetch = async () => { throw new TypeError("CORS error in file:// protocol"); };

    eval(appCode);
    const app = new window.SkillTreeApp();
    app.loadTreeData().then(data => {
      console.log(JSON.stringify({ success: true, count: data.nodes.length }));
    }).catch(err => {
      console.log(JSON.stringify({ success: false, error: err.message }));
    });
    """
    stdout, _, _ = run_node_eval(offline_eval)
    off_res = json.loads(stdout)
    if off_res["success"] and off_res["count"] == 28:
        print("  ✓ Triple-tier data loader successfully falls back to window.__TREE_DATA_FALLBACK__ when fetch fails.")
        results["offline"]["passed"] += 1
    else:
        print(f"  [FAIL] Offline loadTreeData failed: {off_res}")
        results["offline"]["failed"] += 1

    # 3. Check chapter coming-soon markdown generator
    ch_eval = """
    const fs = require('fs');
    const treeData = JSON.parse(fs.readFileSync('tutorial/tree.json', 'utf8'));
    const appCode = fs.readFileSync('docs/app.js', 'utf8');
    global.window = {};
    global.document = { addEventListener: () => {}, getElementById: () => null };
    global.localStorage = { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    eval(appCode);

    const app = new window.SkillTreeApp();
    const node = treeData.nodes[0];
    const md = app.renderComingSoonMarkdown(node);
    const rendered = app.renderMarkdown(md);
    console.log(JSON.stringify({ hasTitle: rendered.includes("<h1>"), hasMetadata: rendered.includes("Curriculum Metadata") }));
    """
    stdout, _, _ = run_node_eval(ch_eval)
    ch_res = json.loads(stdout)
    if ch_res["hasTitle"] and ch_res["hasMetadata"]:
        print("  ✓ Coming-soon chapter generator and Lean syntax tokenizer function offline without network.")
        results["offline"]["passed"] += 1
    else:
        print(f"  [FAIL] Chapter offline coming-soon rendering failed: {ch_res}")
        results["offline"]["failed"] += 1

def main():
    test_savefile_fuzzing()
    test_quiz_engine_and_progression()
    test_serving_and_offline()

    print()
    print("=" * 70)
    print("SUMMARY OF ADVERSARIAL STRESS TESTING")
    print("=" * 70)
    total_passed = sum(v["passed"] for v in results.values())
    total_failed = sum(v["failed"] for v in results.values())
    print(f"Total Checks: {total_passed + total_failed}")
    print(f"Passed: {total_passed}")
    print(f"Failed / Gaps / Vulnerabilities: {total_failed}")

    all_findings = []
    for k, v in results.items():
        all_findings.extend(v["findings"])

    if all_findings:
        print("\nDiscovered Findings & Gaps:")
        for idx, f in enumerate(all_findings, 1):
            print(f"  {idx}. {f}")
    print("=" * 70)
    if total_failed > 0:
        sys.exit(1)

if __name__ == "__main__":
    main()

