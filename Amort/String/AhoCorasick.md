# Aho-Corasick Multi-Pattern Matching Automaton

> **Status: stub — not verified** (Phase 3 canon stub; potential function bound is proven,
> but failure link construction and match emission are specification stubs).


## 1. Overview

The Aho-Corasick automaton (Aho & Corasick, 1975) is the classical algorithm for searching a text $T$ of length $n$ simultaneously for occurrences of any pattern from a dictionary of keywords $\mathcal{P} = \{P_1, P_2, \dots, P_k\}$.

It extends the prefix trie of the patterns with:
1. **Failure links (suffix links)** $\text{fail}(u)$: for each node $u$, $\text{fail}(u)$ points to the node corresponding to the longest proper suffix of the string path to $u$ that is present in the trie.
2. **Output links**: associations pointing to all pattern words that end at the current node (either directly or through failure links).

## 2. Mathematical Architecture

### Automaton Structure & Invariants

```lean
structure AhoCorasick (α : Type) where
  trie : Trie α
  fail : ℕ → ℕ
  fail_root : fail trie.root = trie.root
  fail_depth_lt : ∀ u, 0 < trie.depth u → trie.depth (fail u) < trie.depth u
  outputList : ℕ → List (List α)
```

The fundamental structural property is **depth contraction**:
$$\forall u \in V, \; \text{depth}(u) > 0 \implies \text{depth}(\text{fail}(u)) < \text{depth}(u)$$
Because the failure link points to a *proper* suffix of the string represented by $u$, the length of that suffix is strictly smaller than the depth of $u$.

### State Transition with Failure-Link Fallback

Given current state $u$ and input character $c$:
- If $\text{step}(u, c) = \text{some } v$, advance to $v$ in 1 transition.
- Otherwise, if $\text{depth}(u) > 0$, backtrack along $\text{fail}(u)$ and retry character $c$.
- If $\text{depth}(u) = 0$ and no edge exists, remain at root in 1 transition.

This transition logic is formalized in `Amort.String.AhoCorasick.acStep`.

## 3. Potential Function Analysis & Linear Scanning Bound

To prove that scanning text $T$ takes at most $2|T|$ state transitions, we employ an amortized potential function:
$$\Phi(u) = \text{depth}(u)$$

### Single-Step Amortized Analysis

For any transition `(u', steps) = acStep(u, c)`:
$$\text{steps} + \Phi(u') \le \Phi(u) + 2$$
Formally proven in theorem `acStep_bound`:
- If an edge exists: $\text{steps} = 1$ and $\Phi(u') = \Phi(u) + 1$, so $\text{steps} + \Phi(u') = \Phi(u) + 2$.
- If failure link is traversed: $\Phi(\text{fail}(u)) \le \Phi(u) - 1$. By induction on tree depth, each fallback step is paid for by the reduction in potential.
- If at root with mismatch: $\text{steps} = 1$ and $\Phi(u') = 0$, so $\text{steps} + \Phi(u') = 1 \le 0 + 2$.

### Telescoping Sum Over Text $T$

Summing over all $|T|$ characters of text $T$ from starting node $u$:
$$\text{Total Steps} + \Phi(u_{\text{end}}) \le \Phi(u) + 2|T|$$
Starting from the root node where $\Phi(\text{root}) = 0$:
$$\text{Total Steps} \le 2|T|$$
Formally proven in theorems `acScan_bound`, `acScan_le_two_mul`, and `scan_steps_le`.

## 4. Overall Multi-Pattern Search Complexity

The entire Aho-Corasick algorithm consists of three sequential phases:
1. **Trie Construction & Preprocessing**:
   Building the trie dictionary from patterns $\mathcal{P}$ takes $O(\sum_{i=1}^k |P_i|)$ steps.
   Computing failure links via Breadth-First Search (BFS) processes nodes in order of non-decreasing depth, also running in $O(\sum_{i=1}^k |P_i|)$ steps.
2. **Text Scanning**:
   Processing text $T$ character by character executes in $\le 2|T|$ state transitions ($O(|T|)$).
3. **Match Reporting**:
   Emitting each reported pattern match takes $O(1)$ operations, totaling $O(z)$ operations for $z$ reported occurrences.

Hence, the total operational work is bounded by:
$$\text{Total Work} \le \sum_{i=1}^k |P_i| + 2|T| + z = O\left(\sum_{i=1}^k |P_i| + |T| + z\right)$$
Formally defined in `acTotalSearchWork` and `acTotalSearchWork_bound`.

## 5. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
