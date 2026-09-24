# Test Infrastructure Architecture: Verified Algorithms Skill Tree

## 1. Overview & Objectives

The **Verified Algorithms Skill Tree** is a multi-tier interactive educational web application backed by formal Lean 4 proofs, an automated validation CLI, and structured Markdown curriculum modules.

This document defines the comprehensive opaque-box and end-to-end (E2E) testing infrastructure across **Tiers 1 to 4**:
- **Tier 1: Feature Coverage (Category-Partition Testing)**: Validating all core features, CLI options, HTTP serving, DOM structure, and graph rendering.
- **Tier 2: Boundary Value Analysis (BVA) & Corner Cases**: Stress-testing invalid inputs, graph cycles, missing nodes, asymmetric links, unverified theorem claims, malformed savefiles, and empty inputs.
- **Tier 3: Cross-Feature Combinations & Pairwise Integration**: Testing interactions between subsystems (e.g., Markdown fence preservation during Mermaid generation, multi-parent dependency convergence, savefile round-trip state preservation).
- **Tier 4: Real-World Learner Workload Scenarios**: Simulating authentic learner sessions from fresh visit through quiz completion, dynamic unlock cascade, savefile backup, reset, and restoration.

---

## 2. Directory & Component Layout

```
/workspace/amort/
├── TEST_INFRA.md                 # Test architecture and methodology documentation (this file)
├── TEST_READY.md                 # Test suite readiness report and coverage checklist
├── scripts/
│   ├── test_webapp.py            # Standalone headless web app test runner (Python standard library)
│   └── tree_tool.py             # CLI validation & Mermaid synchronization tool (under test)
├── tests/
│   ├── test_tree_tool.py         # Unit & CLI integration tests for tree_tool.py (Tiers 1-3)
│   └── test_e2e_suite.py         # End-to-end integration test suite (Tiers 1-4)
├── docs/
│   ├── index.html                # Web application shell (under test)
│   ├── style.css                 # Tech tree stylesheet and glowing SVG filters (under test)
│   ├── app.js                    # Web application state and DAG render engine (under test)
│   └── tree_data.js              # Offline fallback snapshot of tree.json (under test)
├── tutorial/
│   └── tree.json                 # Single source of truth 28-node DAG (under test)
└── Amort/
    └── Audit.lean                # Authoritative axiom audit oracle for Lean theorems
```

---

## 3. Testing Methodology Across Tiers 1 to 4

### 3.1 Tier 1: Feature Coverage (Category-Partition Testing)

Each primary feature is partitioned into distinct input categories, ensuring at least 5 distinct test assertions per primary feature:

#### 1. Tree Tool CLI (`scripts/tree_tool.py`):
- **Valid Tree Invariant**: Executing `--validate` on a conforming `tutorial/tree.json` exits with code `0`.
- **Top-Level & Node Schema Conformance**: Validates all 13 required fields per node (`id`, `name`, `tier`, `category`, `status`, `prerequisites`, `unlocks`, `algorithm_skill`, `lean_skill`, `reference_module`, `headline_theorems`, `chapter_path`, `exercises`).
- **Topological Sorting**: Verifies that every node's declared `tier` matches its longest path distance from the root (`BGCD`) plus 1, and that all prerequisites precede unlocks in the topological sequence.
- **DAG Acyclicity**: Verifies that Kahn's algorithm processes all $|V| = 28$ nodes with zero unresolved in-degrees.
- **Bidirectional Prerequisite Symmetry**: For every edge $(u, v)$, asserts $v \in u.\text{unlocks} \iff u \in v.\text{prerequisites}$.
- **Lean Axiom Audit Cross-Check**: For every node where `status ∈ ["open", "ready"]`, parses `Amort/Audit.lean` and verifies that all declared `headline_theorems` appear in `#print axioms <thm>` statements without non-standard axioms.
- **Mermaid Diagram Sync**: Verifies that `--sync-mermaid --check` confirms synchronization with `SKILL_TREE_TUTORIAL_PLAN.md` §4.2, and that `--sync-mermaid` regenerates the diagram in-place without altering non-Mermaid content.
- **Tree Metrics Statistics**: Verifies that `--stats` accurately reports total nodes (28), status counts (1 open, 21 ready, 6 planned), tier counts (1 to 6), and category distributions.

#### 2. Static Web Application (`docs/index.html` & `scripts/test_webapp.py`):
- **HTTP Serving**: Verifies clean HTTP 200 responses with correct MIME types for `docs/index.html`, `docs/style.css`, `docs/app.js`, `docs/tree_data.js`, and `tutorial/tree.json` served via Python's standard `http.server`.
- **Core DOM Structure**: Using an HTML5 DOM parser, asserts the existence of:
  - Canvas viewport container (`#canvas-container` or `#canvas-world`).
  - Tech tree SVG wire layer (`#tree-svg` and `#wires-layer`).
  - Node card rendering container (`#nodes-layer`).
  - Accessible slide-out inspector dialog (`#inspector-drawer`).
  - Inspector navigation tabs (`[data-tab="specs"]`, `[data-tab="quiz"]`, `[data-tab="chapter"]`).
  - Quiz card container (`#quiz-container`).
  - Savefile controls (`#btn-export-save`, `#file-import-save`, `#btn-reset-save`).
  - Canvas zoom/pan controls (`#btn-zoom-in`, `#btn-zoom-out`, `#btn-zoom-fit`).
- **Tree Loading & Node Cardinality**: Verifies that exactly 28 node elements are rendered across 6 topological tiers.

---

### 3.2 Tier 2: Boundary Value Analysis (BVA) & Corner Cases

Boundary testing injects synthetic faults and invalid inputs to confirm robust rejection and clean error reporting:

#### 1. Tree Tool Fault Injections:
- **Direct Cycle Injection (A → B → A)**: Injects a cycle between `BGCD` and `INS` (`INS.unlocks = ["BGCD"]`). Asserts non-zero exit code and diagnostic output detailing the cycle path.
- **Long Cycle Injection (Sink → Root)**: Injects an edge from Tier 6 sink `LIS` back to Tier 1 root `BGCD`. Asserts detection of multi-node circular dependency.
- **Missing Prerequisite Node ID**: Adds a dangling prerequisite `"NONEXISTENT_NODE"` to `MERGE.prerequisites`. Asserts non-zero exit code identifying the missing node.
- **Asymmetric Prerequisite / Unlock Edge**: Removes `BGCD` from `EUC.prerequisites` while `BGCD.unlocks` retains `"EUC"`. Asserts error reporting bidirectional asymmetry.
- **Unverified Theorem Claimed for Ready Node**: Injects `Nat.fake_unverified_theorem` into `BGCD.headline_theorems`. Asserts validation fails with `UNVERIFIED_THEOREM` diagnostic.
- **Empty Exercises on Ready Node**: Sets `exercises.predict = []` on `INS`. Asserts rejection because ready/open nodes require at least one exercise per type.
- **Duplicate Node IDs**: Injects a duplicate node object with `id: "BGCD"`. Asserts duplicate key rejection.
- **Multiple Root Nodes**: Sets `MODEXP.prerequisites = []`. Asserts rejection because the pedagogical DAG requires a single unique entry point (`BGCD`).
- **Planned Node Claiming Theorems**: Sets `headline_theorems: ["Nat.gcd_dvd_left"]` on planned node `HEAP`. Asserts rejection because planned nodes must have empty headline theorems.

#### 2. Web Application Corner Cases:
- **Local `file://` Snapshot Handling**: When `fetch()` is unavailable, verifies that `docs/tree_data.js` (`window.__TREE_DATA_FALLBACK__`) provides the full 28-node dataset.
- **Malformed Savefile Rejection**:
  - Unparseable JSON syntax (truncated string).
  - Missing `schema_version`.
  - Non-array `mastered_nodes` (e.g. integer or dictionary).
  - Unknown/corrupted node IDs in savefile (e.g. `["INVALID_XYZ"]`).
  - Malformed answer records.
  - Asserts that all malformed savefiles are rejected with user-visible errors and do not overwrite existing progress.
- **Empty Quiz Answer Handling**:
  - Submitting empty or whitespace-only answers for "Predict".
  - Submitting without selecting an option in "Spot the Fake".
  - Asserts that input verification prevents progression and shows clear validation feedback.
- **Zoom Limit Clamping**:
  - Verifies minimum zoom scale boundary (clamped at `0.25x`).
  - Verifies maximum zoom scale boundary (clamped at `3.0x`).
  - Verifies that repeated zoom-in or zoom-out does not cause numeric overflow, zero division, or canvas inversion.

---

### 3.3 Tier 3: Cross-Feature Combinations & Pairwise Integration

Testing cross-component coupling and state synchronization:

1. **Mermaid Markdown In-Place Synchronization**:
   - Tests that `tree_tool.py --sync-mermaid` replaces the Mermaid diagram between ````mermaid` and ```` in `SKILL_TREE_TUTORIAL_PLAN.md` while preserving all surrounding Markdown prose, headings, and tables verbatim.
   - Tests that `--sync-mermaid --check` detects diagram drift if the Markdown block is altered manually.
2. **Multi-Hop Dependency Unlock Convergence (Fan-In)**:
   - Node `MERGE` requires both `INS` and `BS`.
   - Test verifies that mastering only `INS` leaves `MERGE` locked.
   - Test verifies that mastering only `BS` leaves `MERGE` locked.
   - Test verifies that mastering both `INS` and `BS` unlocks `MERGE`.
   - Node `KMP` requires both `NAIVE` and `TSQ`.
   - Test verifies that mastering only `NAIVE` leaves `KMP` locked.
   - Test verifies that mastering both `NAIVE` and `TSQ` unlocks `KMP`.
3. **Savefile Download → Reset → Load Round-Trip**:
   - Generates progress state with multiple completed nodes (`BGCD`, `INS`, `BS`, `MERGE`).
   - Serializes to savefile JSON conforming to the `amort_save.json` contract.
   - Executes "Reset Progress" (confirming nodes return to locked/active defaults).
   - Imports the exported savefile and verifies that 100% of mastered nodes and quiz answers are restored.

---

### 3.4 Tier 4: Real-World Learner Workload Scenarios

Comprehensive behavioral simulation of a complete learner journey:

```
[Fresh Learner Visit]
        │
        ▼
HUD: 0/22 Mastered ──► Only BGCD is Active, all other 27 nodes Locked/Planned
        │
        ▼
Selects BGCD ──► Inspector Drawer Opens (Specs & Homework Tabs)
        │
        ▼
Solves "Predict" (eval_bgcd_48_18 = "6")
Solves "Spot the Fake" (stf_bgcd_complexity = "b")
        │
        ▼
[BGCD Mastered] ──► HUD: 1/22 Mastered
        │
        ▼
[Dynamic Unlock Cascade] ──► Tier 2 Nodes Unlock: EUC, INS, BS, DYN, MODEXP
        │
        ▼
Exports Savefile (amort_save.json)
        │
        ▼
Triggers "Reset Progress" ──► HUD resets to 0/22, Tier 2 re-locks
        │
        ▼
Imports amort_save.json ──► HUD restores 1/22, Tier 2 re-unlocks
```

---

## 4. Authoritative Oracles & Ground Truth Derivation

To guarantee genuine testing integrity and eliminate facade tests, all expected test outputs are derived from explicit authoritative sources:

| Feature / Invariant | Authoritative Source | Derived Expectation |
|---|---|---|
| Headline Theorems & Axioms | `/workspace/amort/Amort/Audit.lean` | 74 headline theorems audited via `#print axioms`. Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) allowed; zero `sorryAx`. |
| Skill Tree Topology | `/workspace/amort/SKILL_TREE_TUTORIAL_PLAN.md` §4.2 | 28 nodes across 6 tiers (1 open, 21 ready, 6 planned). Root is strictly `BGCD`. |
| Node Categorization & Skills | `/workspace/amort/SKILL_TREE_TUTORIAL_PLAN.md` §4.3 | 8 categories: `arithmetic`, `sorting`, `amortization`, `strings`, `dp`, `greedy`, `graphs`, `complexity`. |
| Opening Node Exercises | `SKILL_TREE_TUTORIAL_PLAN.md` §5 & `Amort/GCD/BinaryGCD.lean` | Predict `#eval binaryGcd 48 18` = `"6"`, `#eval binaryGcd 0 7` = `"7"`. Spot the fake option `"b"`. |
| Savefile Data Contract | `PROJECT.md` § Interface Contracts (Contract 4) | Top-level keys: `schema_version` (1.0.0), `saved_at`, `mastered_nodes`, `answers`. |

---

## 5. Test Execution Guide

### 5.1 Standalone Web Application Test Runner
```bash
python3 scripts/test_webapp.py
```
*Options*:
- `--strict`: Enforces that all milestone assets (`docs/index.html`, `tutorial/tree.json`) must exist on disk.
- `--verbose`: Prints detailed step-by-step logs for each verification phase.

### 5.2 Python Unittest Suite (Full E2E Discovery)
```bash
python3 -m unittest discover tests
```

### 5.3 Individual Test Modules
```bash
# Tree Tool CLI and DAG validation checks
python3 -m unittest tests/test_tree_tool.py

# End-to-end integration, savefile, and learner simulation checks
python3 -m unittest tests/test_e2e_suite.py
```

### 5.4 Tooling Mechanical Gate Passes
```bash
# Skill tree structural & Lean audit validation
python3 scripts/tree_tool.py --validate

# Lean 4 library compilation & axiom audit
lake build Amort && lake build
```

---

## 6. Progressive Testability Standard

During project milestones:
1. **Self-Contained Fixtures**: Tests include canonical data models and fixtures so that test algorithms can be verified immediately.
2. **Graceful Milestone Gating**: Tests targeting implementation files created by subsequent milestones (`scripts/tree_tool.py` in M1, `docs/index.html` in M4) gracefully detect asset presence:
   - When assets are present, full E2E execution occurs.
   - When assets are pending, informative skip markers denote pending milestone dependencies, ensuring CI test discovery succeeds without false failures.
3. **No Facades**: All assertions test real properties (status codes, DOM tags, acyclicity, set inclusions, round-trip equality). No dummy passing assertions or trivial tautologies.
