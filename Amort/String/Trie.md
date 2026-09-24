# Prefix Trie (Prefix Tree Dictionary)

> **Status: stub — not verified** (Phase 3 canon stub; prefix trie structure is modeled,
> but end-to-end dictionary lookup correctness is a specification stub).


## 1. Overview

The prefix trie is an ordered search tree data structure used to store an associative collection of strings (dictionary). Nodes correspond to prefixes of strings in the dictionary, where:
- The **root** represents the empty prefix $\varepsilon$ (with depth 0).
- Directed edges from node $u$ to node $v$ are labeled by alphabet characters $c \in \Sigma$, satisfying $\text{depth}(v) = \text{depth}(u) + 1$.
- Each node maintains a boolean termination marker $\text{isTerminal}(u)$ indicating whether the prefix represented by $u$ is a complete word in the dictionary.

This module formalizes both:
1. An **abstract automaton model** (`Amort.String.Trie`) for state-based string algorithms (such as the Aho-Corasick multi-pattern matching automaton).
2. A **concrete inductive data structure** (`Amort.String.PrefixTrie`) providing executable functional dictionary operations.

## 2. Mathematical Architecture

### Abstract Trie Automaton

```lean
structure Trie (α : Type) where
  numNodes : ℕ
  root : ℕ
  step : ℕ → α → Option ℕ
  isTerminal : ℕ → Bool
  depth : ℕ → ℕ
  depth_root : depth root = 0
  depth_step : ∀ u c v, step u c = some v → depth v = depth u + 1
```

- **Prefix-Tree Walk**:
  $$\text{walk}(u, \varepsilon) = u$$
  $$\text{walk}(u, c \cdot cs) = \begin{cases} \text{walk}(v, cs) & \text{if } \text{step}(u, c) = \text{some } v \\ \text{none} & \text{otherwise} \end{cases}$$

- **Depth Invariant**:
  $$\text{walk}(u, w) = \text{some } v \implies \text{depth}(v) = \text{depth}(u) + |w|$$
  In particular, from the root node:
  $$\text{walk}(\text{root}, w) = \text{some } v \implies \text{depth}(v) = |w|$$

### Prefix-Tree Retrieval Soundness

The membership query $\text{contains}(w)$ checks whether walking from the root node along $w$ terminates at a node marked as terminal:
$$\text{contains}(w) = \text{true} \iff \exists v \in V, \; \text{walk}(\text{root}, w) = \text{some } v \land \text{isTerminal}(v) = \text{true}$$
This theorem is formally proven as `Amort.String.Trie.contains_soundness`.

## 3. Operational Complexity Bounds

1. **Single-Word Lookup**:
   Each character of word $w$ is examined at most once via edge lookup $\text{step}(u, c)$.
   $$\text{lookupSteps}(w) \le |w|$$
   Formally proven in `lookupSteps_le` and `lookupSteps_from_root_le`.

2. **Single-Word Insertion**:
   Inserting a word $w$ adds or visits at most $|w|$ transitions:
   $$\text{insertWork}(w) = |w| \le |w|$$
   Formally defined in `insertWork` and `insertWork_le`.

3. **Dictionary Construction**:
   Constructing a trie dictionary from a collection of pattern words $\{P_1, P_2, \dots, P_k\}$ requires sequentially inserting each word, yielding total character operations:
   $$\text{buildWork}(\{P_1, \dots, P_k\}) = \sum_{i=1}^k |P_i| = O\left(\sum_{i=1}^k |P_i|\right)$$
   Formally proven in `buildWork_eq_sum` and connected to Mathlib's `IsBigO` in `AdvancedAsymptotics.lean`.

## 4. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
