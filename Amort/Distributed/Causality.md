# Causality & Logical Clocks (`Amort.Distributed.Causality`)

## 1. Mathematical Foundations

In distributed systems, physical time cannot provide a reliable total ordering across distinct
processes due to clock skew, drift, and relativistic latency. Lamport (1978) introduced logical
time based on the causal ordering of events.

### 1.1 Events and Direct Precedence
A distributed system consists of $N$ processes (`Fin N`). An event $e$ is characterized by:
- `node : Fin N`: The process where the event occurred.
- `seq : ℕ`: The local event sequence number on that process.

Direct causal precedence (`DirectPrecedes`) arises from two physical mechanisms:
1. **Local Program Order**: If $e_1, e_2$ occur on the same process ($e_1.\text{node} =
   e_2.\text{node}$) and $e_1.\text{seq} < e_2.\text{seq}$, then $e_1$ directly precedes $e_2$.
2. **Message Passing**: If $e_1$ is the sending of a message and $e_2$ is its receipt,
   then $e_1$ directly precedes $e_2$.

### 1.2 Happens-Before Relation (`→`)
Lamport's happens-before relation (`HappensBefore`) is the transitive closure of direct precedence:
$$\to \;=\; (\text{DirectPrecedes})^+$$
In Lean 4, this is formalized using `Relation.TransGen (DirectPrecedes msgs)`.

**Strict Partial Order Properties**:
- **Transitivity**: `happensBefore_trans`: $e_1 \to e_2 \land e_2 \to e_3 \implies e_1 \to e_3$.
- **Irreflexivity**: In any causally valid execution (`CausalExecution N`), causality is
  acyclic: $\neg (e \to e)$ (`happensBefore_irrefl`).
- **Asymmetry**: $e_1 \to e_2 \implies \neg (e_2 \to e_1)$ (`happensBefore_asymm`).

---

## 2. Lamport Scalar Logical Clocks

A Lamport scalar clock assigns a natural number $C(e) \in \mathbb{N}$ to each event $e$,
satisfying two rules:
1. **Local Tick**: For successive local events on process $p$, $C(e_1) < C(e_2)$.
2. **Message Receive**: For message $(e_1, e_2)$, $C(e_1) < C(e_2)$.

### 2.1 Clock Consistency Theorem
```lean
theorem lamport_clock_consistency {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (lc : LamportClock N msgs) {e1 e2 : DistributedEvent N}
    (h : HappensBefore msgs e1 e2) : lc.clock e1 < lc.clock e2
```
**Proof**: By induction on `Relation.TransGen`:
- Base step: Direct precedence guarantees $C(e_1) < C(e_2)$ by clock construction.
- Transitive step: $C(e_1) < C(e_2) < C(e_3) \implies C(e_1) < C(e_3)$ by `Nat.lt_trans`.

### 2.2 Limitation of Scalar Clocks
The converse of the clock condition does NOT hold:
$$C(e_1) < C(e_2) \;\not\implies\; e_1 \to e_2$$
Scalar timestamps cannot distinguish between causal precedence and concurrency.

---

## 3. Vector Clocks & Causal Isomorphism

Vector Clocks (Mattern 1989, Fidge 1988) overcome the limitation of scalar clocks by assigning
a vector $V(e) \in (\text{Fin } N \to \mathbb{N})$ to each event.

### 3.1 Vector Order
- **Weak Order**: $V_1 \le V_2 \iff \forall i : \text{Fin } N, V_1(i) \le V_2(i)$ (`VCLe`).
- **Strict Order**: $V_1 < V_2 \iff V_1 \le V_2 \land V_1 \ne V_2$ (`VCLt`).
- **Equivalence**: $V_1 < V_2 \iff V_1 \le V_2 \land \exists i, V_1(i) < V_2(i)$
  (`vclt_iff_le_and_exists_lt`).

### 3.2 Fundamental Causal Isomorphism Theorems

#### Causal Domination Theorem
```lean
theorem vc_le_iff_hb_or_eq {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    VCLe (vcs.vc e1) (vcs.vc e2) ↔ HappensBeforeOrEq msgs e1 e2
```

#### Strict Causal Isomorphism Theorem
```lean
theorem vc_lt_iff_happensBefore {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    VCLt (vcs.vc e1) (vcs.vc e2) ↔ HappensBefore msgs e1 e2
```
**Proof**:
- ($\implies$): If $V(e_1) < V(e_2)$, then $V(e_1) \le V(e_2)$, which implies $e_1 \le e_2$.
  Since $V(e_1) \ne V(e_2)$, $e_1 \ne e_2$. Hence $e_1 \to e_2$.
- ($\impliedby$): If $e_1 \to e_2$, then $V(e_1) \le V(e_2)$ by causal monotonicity. If
  $V(e_1) = V(e_2)$, then evaluating at $e_2.\text{node}$ gives $e_2 \le e_1$, creating a
  causal cycle that contradicts acyclicity.
  Thus $V(e_1) \ne V(e_2)$, establishing $V(e_1) < V(e_2)$.

#### Concurrency Characterization
```lean
theorem concurrent_iff_incomparable {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    Concurrent msgs e1 e2 ↔ ¬ VCLe (vcs.vc e1) (vcs.vc e2) ∧ ¬ VCLe (vcs.vc e2) (vcs.vc e1)
```
Two distinct events are concurrent if and only if their vector clock timestamps are incomparable.
