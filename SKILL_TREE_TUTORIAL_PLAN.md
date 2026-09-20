# Verified Algorithms Skill Tree: Tutorial & Curriculum Plan

> **Philosophy**: *"Multiplication in a World of Calculators"*  
> In an era where AI can generate an implementation of any classic algorithm in seconds, raw code generation has become a commodity. The enduring human value and intellectual joy lie in understanding **why** algorithms work, **why** they terminate, and **why** their invariants guarantee correctness and optimal complexity. Formalizing algorithms in Lean 4 provides the ultimate high-resolution lens: the type checker accepts no handwaving, no skipped edge cases, and no informal arithmetic.

---

## 1. Executive Summary & Vision

This project powers an interactive, modular algorithm tutorial built entirely on the formal verification foundations in [`Amort`](file:///workspace/amort/Amort). 

Instead of a monolithic textbook, the curriculum is organized as an **Open-World Skill Tree (DAG)** where:
1. **Every algorithm is an individual node**.
2. **Learners choose their own path** based on their background and interests (e.g. Systems/Amortization, Graph Theory, Dynamic Programming, or Number Theory).
3. **Every node is governed by the 4 Core Verification Disciplines**:
   - **Step 1: Define** (Pre/post-conditions, problem specification)
   - **Step 2: Formalize** (Executable modeling, well-founded termination measures)
   - **Step 3: Prove** (Loop invariants, inductive proofs, partial/total correctness)
   - **Step 4: Analyze** (Step counting, recurrence relations, potential functions, Mathlib `IsBigO`)

The guide serves a **dual purpose**:
- **For Readers**: An approachable, code-first bridge to learn Lean 4 through concrete algorithms, free of abstract algebraic prerequisites.
- **For the Author**: A rigorous personal roadmap to master Lean 4 theorem proving and deeply understand advanced algorithms.

---

## 2. The 4 Verification Disciplines (The "Rigor Ladder")

At every node in the skill tree, learners progress through the same four distinct levels:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ 1. SPECIFICATION (Define)                                                  │
│    Formulate input types, valid predicates, and formal problem contracts.   │
│    e.g. "What does it mean for list L' to be a sorted permutation of L?"    │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 2. EXECUTABLE MODELING & HALTING (Formalize)                               │
│    Write clean, functional Lean 4 code. Define well-founded recursion       │
│    measures with `termination_by` to prove the algorithm terminates.        │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 3. SOUNDNESS & INVARIANTS (Prove)                                           │
│    Prove partial and total correctness. Establish inductive invariants for  │
│    loops/recursions. Prove equivalence against mathematical specs.          │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ 4. STEP COUNTING & ASYMPTOTICS (Analyze)                                    │
│    Instrument the algorithm with step counters. Formulate recurrences or    │
│    amortized potential functions Φ. Bridge bounds to Mathlib `IsBigO`.      │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. The Full Granular Skill Tree (Node-by-Node DAG)

Below is the complete dependency graph. Every box represents a standalone, verifiable algorithm node.

```mermaid
flowchart TD
    classDef starter fill:#2d3748,stroke:#cbd5e0,stroke-width:2px,color:#fff
    classDef num fill:#1a365d,stroke:#63b3ed,stroke-width:1px,color:#fff
    classDef sort fill:#22543d,stroke:#68d391,stroke-width:1px,color:#fff
    classDef ds fill:#744210,stroke:#f6ad55,stroke-width:1px,color:#fff
    classDef str fill:#553c9a,stroke:#b794f4,stroke-width:1px,color:#fff
    classDef dp fill:#702459,stroke:#f687b3,stroke-width:1px,color:#fff
    classDef graph fill:#1c4532,stroke:#48bb78,stroke-width:1px,color:#fff
    classDef adv fill:#742a2a,stroke:#feb2b2,stroke-width:1px,color:#fff

    %% Starter Gateways
    G1["🌱 Linear Scan & Array Sum"]:::starter
    G2["🌱 Euclidean GCD"]:::num
    G3["🌱 Insertion Sort"]:::sort

    %% Number Theory & Arithmetic Track
    G2 --> N1["Binary GCD (Stein)"]:::num
    G2 --> N2["Extended Euclidean & Bezout"]:::num
    N1 --> N3["Fast Modular Exponentiation"]:::num
    N3 --> N4["Strassen Matrix Mult"]:::adv
    N3 --> N5["FFT (Fast Fourier Transform)"]:::adv

    %% Sorting & Searching Track
    G1 --> S0["Binary Search"]:::sort
    G3 --> S1["Merge Sort"]:::sort
    S1 --> S2["Master Theorem Recurrences"]:::sort
    S1 --> S3["Sorting Lower Bound Ω(n log n)"]:::sort
    S0 --> S4["Quickselect & Partition"]:::sort

    %% Data Structures Track
    G1 --> DS1["Dynamic Array (Amortized Push)"]:::ds
    G1 --> DS2["Two-Stack Queue"]:::ds
    DS1 --> DS3["Binary Heap / Priority Queue"]:::ds
    DS3 --> DS4["Heapsort"]:::sort
    DS3 --> DS5["Online Running Median"]:::ds
    DS1 --> DS6["Disjoint Set Union (Union-Find)"]:::ds
    DS3 --> DS7["Balanced BST (AVL / RB)"]:::ds

    %% String Algorithms Track
    G1 --> ST1["Naive String Matching"]:::str
    ST1 --> ST2["Prefix Trie Dictionary"]:::str
    ST1 --> ST3["Rabin-Karp Rolling Hash"]:::str
    ST1 --> ST4["Knuth-Morris-Pratt (KMP)"]:::str
    ST4 --> ST5["Gusfield's Z-Algorithm"]:::str
    ST2 --> ST6["Aho-Corasick Automaton"]:::str
    ST4 --> ST6
    ST4 --> ST7["Suffix Array & Kasai LCP"]:::str

    %% Dynamic Programming Track
    G1 --> DP0["Telescoping & Fibonacci DP"]:::dp
    DP0 --> DP1["0/1 Knapsack"]:::dp
    DP0 --> DP2["Longest Common Subsequence"]:::dp
    DP2 --> DP3["Edit Distance (Levenshtein)"]:::dp
    S0 --> DP4["Longest Increasing Subsequence"]:::dp
    DP0 --> DP5["Matrix Chain Multiplication"]:::dp

    %% Graph Algorithms Track
    G1 --> GR1["BFS (Shortest Path)"]:::graph
    G1 --> GR2["DFS & Cycle Detection"]:::graph
    GR2 --> GR3["Topological Sort (DAGs)"]:::graph
    GR3 --> GR4["DAG Shortest Path (DP)"]:::graph
    DS3 --> GR5["Dijkstra's Algorithm"]:::graph
    GR1 --> GR5
    DS6 --> GR6["Kruskal's MST"]:::graph
    DS3 --> GR7["Prim's MST"]:::graph
    GR5 --> GR8["Bellman-Ford"]:::graph
    GR8 --> GR9["Floyd-Warshall All-Pairs"]:::graph
    GR5 --> GR10["Max-Flow (Edmonds-Karp)"]:::adv

    %% Advanced / Complexity / Approximation
    GR3 --> C1["2-SAT (SCC Linear Time)"]:::adv
    GR6 --> C2["Metric TSP 2-Approximation"]:::adv
    DP1 --> C3["Greedy Set Cover"]:::adv
    C1 --> C4["Karp Reductions (SAT → Clique)"]:::adv
```

---

## 4. Curated Player Paths (Learning Archetypes)

Learners do not need to follow a linear syllabus. They can pick an archetype:

| Archetype | Node Sequence | Core Concept Learned |
| :--- | :--- | :--- |
| **The Systems Architect** | `Dynamic Array` → `Two-Stack Queue` → `KMP` → `Z-Algorithm` → `Aho-Corasick` | Potential functions $\Phi$, amortized $O(1)$, stateful buffers. |
| **The Interview / Contest Ace** | `Binary Search` → `Merge Sort` → `0/1 Knapsack` → `Dijkstra` → `Kruskal` | Deep rigor behind standard CS interview questions. |
| **The Number Theorist** | `Euclidean GCD` → `Binary GCD` → `Fast ModPow` → `Strassen` → `FFT` | Bit-size metrics, 2-adic decomposition, ring homomorphisms. |
| **The Graph Explorer** | `BFS` → `DFS` → `Topological Sort` → `Dijkstra` → `Kruskal` → `Max Flow` | Inductive paths, cut properties, matroid exchange arguments. |
| **The Complexity Theorist** | `Sorting Lower Bound` → `2-SAT` → `Metric TSP` → `Karp Reductions` | Information-theoretic lower bounds, approximation ratios, NP-hardness. |

---

## 5. Node Specification Template ("Quest Card")

Every node in the curriculum follows this standardized 4-part structure.

### Example Node Card: `Knuth-Morris-Pratt (KMP)`

```markdown
# 📍 Node: Knuth-Morris-Pratt (KMP)
- **Track**: String Algorithms & Amortization
- **Prerequisites**: `Naive String Matching`
- **Unlocks**: `Z-Algorithm`, `Aho-Corasick`, `Suffix Array & Kasai LCP`
- **Code Reference**: `Amort/String/KMP.lean`, `Amort/String/KMP.md`

#### 1. Define the Problem
- **Specification**: Given text $T$ and pattern $P$ over alphabet $\alpha$, find all indices $i$ such that $T[i \dots i+|P|-1] = P$.
- **The Bottleneck**: Naive search backtracks the text index $i$, leading to worst-case $O(|T| \cdot |P|)$ runtime.
- **The Insight**: Advance the text pointer monotonically; use the longest proper prefix-suffix table $\pi$ to shift the pattern pointer $j$.

#### 2. Formalize It
- **Specification Predicate**:
  ```lean
  def IsSubstring (P T : List α) (i : Nat) : Prop :=
    P.isPrefixOf (T.drop i) = true
  ```
- **Preprocessing Function**:
  `computePi (P : List α) : Array Nat`
- **Main Search Loop & Termination**:
  `kmpSearchWithSteps (T P : List α) ...`
  `termination_by (T.length - i) * (P.length + 1) + (P.length - j)`

#### 3. Prove Correctness
- **Prefix Match Invariant**: At step $(i, j)$, $T[i-j \dots i-1] = P[0 \dots j-1]$.
- **Fallback Soundness**: If $P[j] \ne T[i]$, shifting $j \gets \pi[j-1]$ drops only non-viable alignments.
- **Soundness Theorem**: Every returned index $k$ satisfies `IsSubstring P T k`.
- **Completeness Theorem**: If `IsSubstring P T k`, then $k$ is in the result list.

#### 4. Analyze Time Complexity
- **The Apparent Paradox**: The inner fallback `while j > 0` can loop multiple times per text character.
- **Potential Function**: $\Phi(j) = j$.
  - Character match increments $\Phi$ by $1$.
  - Fallback strictly decrements $\Phi$.
  - Since $\Phi \ge 0$, total fallbacks cannot exceed total increments $\le |T|$.
- **Step Bound Theorem**:
  `kmpSteps T P ≤ 2 * (T.length + P.length)`
- **Mathlib Asymptotic Bridge**:
  `isBigO_kmpSteps_linear : IsBigO Filter.atTop (fun (T, P) => kmpSteps T P) (fun (T, P) => T.length + P.length)`
```

---

## 6. Implementation Architecture & Format

### Recommended Delivery Medium
1. **Interactive mdBook Site**:
   - Hosted web guide with an interactive SVG / Mermaid skill tree diagram.
   - Clicking any node opens the 4-part quest card with code walkthroughs.
2. **Literate Lean 4 Worksheets**:
   - Each node corresponds to a self-contained Lean file in `Amort/` with exercise checkpoints.
   - Exercises provide skeleton code with `#check` and targeted `sorry` blanks for learners to fill in.
3. **Automated Verification Pipeline**:
   - Continuous Integration via GitHub Actions running `lake build` to guarantee all proofs remain valid across Lean toolchain updates.

---

## 7. Phased Execution Roadmap

### Phase 1: The Gateway Triad & Showcase Nodes (Immediate Focus)
- Formalize the interactive tutorials for the 3 entry gateways:
  1. `Euclidean GCD` + `Binary GCD` (`Amort/GCD/`)
  2. `Insertion Sort` + `Merge Sort` + `Sorting Lower Bound` (`Amort/Sorting/`)
  3. `Dynamic Array` + `KMP` (`Amort/DataStructure/` & `Amort/String/`)
- Draft the overarching Preface: *"Multiplication in a World of Calculators"*.

### Phase 2: Core Branch Progression
- Fill in the DP branch: `0/1 Knapsack`, `LCS`, `Matrix Chain`.
- Fill in the Graph branch: `BFS`, `Topological Sort`, `Dijkstra`, `Kruskal`.
- Connect recurrence bridges: `Amort.Recurrence.MasterTheorem` to `MergeSort` and `BinarySearch`.

### Phase 3: Interactive Skill Tree Web App
- Build a lightweight web interface (or mdBook integration) rendering the clickable skill tree.
- Add progress tracking (local storage checklist for completed nodes).

### Phase 4: Capstone Hardness & Advanced Horizons
- `Strassen` & `FFT` algebraic bounds.
- `2-SAT` and `Karp Reductions`.
- Approximation bounds (`Metric TSP`, `Set Cover`).
