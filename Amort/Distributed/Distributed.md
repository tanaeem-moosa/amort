# Distributed Systems Canon (`Amort.Distributed`)

> **Status: stub — not verified** (Phase 4 canon stubs; Paxos, Raft, PBFT, Vector Clocks, and
> Chandy-Lamport protocols are specification stubs awaiting full verification).


This directory formalizes the foundational theorems of distributed computing in Lean 4.
The canon spans logical time, impossibility bounds, crash-tolerant consensus, Byzantine fault
tolerance, and consistent global snapshots.

---

## 1. Modules Overview

### `Amort.Distributed.Causality`
- **Focus**: Logical time, happens-before strict partial order, and causal vector clocks.
- **Key Theorems**:
  - Lamport's happens-before relation (`→`) is irreflexive, transitive, and asymmetric.
  - Lamport scalar clock consistency: $e_1 \to e_2 \implies C(e_1) < C(e_2)$.
  - Vector Clock Causal Isomorphism: $V(e_1) < V(e_2) \iff e_1 \to e_2$.
  - Concurrency characterization: events are concurrent iff vector clocks are incomparable.
- **Chapter Documentation**: [`Causality.md`](Causality.md).

### `Amort.Distributed.Impossibility`
- **Focus**: Gilbert-Lynch CAP Theorem and Two Generals' Problem.
- **Key Theorems**:
  - Gilbert-Lynch CAP Impossibility: Under an asynchronous network partition, no protocol
    can simultaneously achieve Linearizability and Availability.
  - Two Generals' Problem: Over an unreliable lossy channel, no finite message protocol
    can guarantee common knowledge or coordinated attack (proven by induction on delivered
    messages).
- **Chapter Documentation**: [`Impossibility.md`](Impossibility.md).

### `Amort.Distributed.Consensus`
- **Focus**: Quorum intersection, Single-Decree Paxos, Multi-Paxos, and Raft invariants.
- **Key Theorems**:
  - Majority Quorum Intersection: For any system with $N > 0$, any two majority quorums
    $Q_1, Q_2 \subseteq \text{Fin } N$ intersect non-trivially ($Q_1 \cap Q_2 \ne \emptyset$).
  - Core Paxos Proposal Invariant: If value $v$ is chosen at ballot $b$, then for any ballot
    $b' > b$, any proposal issued at $b'$ must have value $v$.
  - Paxos Learner Agreement: No two learners decide different values ($v_1 = v_2$).
  - Multi-Paxos Slot Safety: At most one command is committed per log slot.
  - Replicated State Machine (RSM) Safety: Applying identical committed logs yields identical
    states.
  - Raft Leader Election Safety: At most one leader elected per term via quorum intersection.
  - Raft Log Matching Invariant: Agreement on term at index implies identical prefixes.
- **Chapter Documentation**: [`Consensus.md`](Consensus.md).

### `Amort.Distributed.BFT`
- **Focus**: Byzantine Fault Tolerance, PBFT quorum math, and the $3f + 1$ threshold.
- **Key Theorems**:
  - PBFT Quorum Intersection: In $N = 3f + 1$, any two quorums of size $2f + 1$ intersect in at
    least $f + 1$ nodes.
  - PBFT Honest Node Intersection: At least one node in the intersection is non-faulty (honest).
  - Lamport-Shostak-Pease Lower Bound: Consensus in an unauthenticated system is impossible
    when $N \le 3f$ (formal 3-node, 1-traitor counterexample).
  - Oral Messages $OM(m)$ Validity: With loyal commander, loyal votes form a strict majority.
  - Oral Messages $OM(m)$ Agreement: Lieutenants with identical message vectors decide identically.
- **Chapter Documentation**: [`BFT.md`](BFT.md).

### `Amort.Distributed.Snapshot`
- **Focus**: Consistent cuts and the Chandy-Lamport distributed snapshot algorithm.
- **Key Theorems**:
  - Chandy-Lamport Consistent Cut Theorem: The recorded local process states form a consistent
    cut ($r \le T_q \implies s \le T_p$).
  - No Inconsistent Messages: In any consistent cut, no message is received before the snapshot
    if it was sent after the snapshot.
  - Channel State Recording Soundness: Every message in a recorded channel state was sent before
    the sender's snapshot and received after the receiver's snapshot.
- **Chapter Documentation**: [`Snapshot.md`](Snapshot.md).

---

## 2. Theoretical Architecture

```
                       +----------------------------------+
                       |    Causality & Logical Clocks    |
                       |       (Lamport 1978, Fidge,      |
                       |          Mattern 1989)           |
                       +-----------------+----------------+
                                         |
                       +-----------------+----------------+
                       |                                  |
                       v                                  v
        +------------------------------+   +------------------------------+
        |     Consistent Snapshots     |   |    Impossibility Theorems    |
        |   (Chandy & Lamport 1985)    |   | (Gilbert-Lynch, Two Generals)|
        +------------------------------+   +------------------------------+
                                                          |
                                                          v
                                           +------------------------------+
                                           |   Crash-Tolerant Consensus   |
                                           |    (Paxos Synod, Multi-      |
                                           |      Paxos, Raft Safety)     |
                                           +--------------+---------------+
                                                          |
                                                          v
                                           +------------------------------+
                                           |   Byzantine Fault Tolerance  |
                                           |   (LSP 3f+1, OM(m), PBFT)    |
                                           +------------------------------+
```

---

## 3. Verification & Integrity

All modules in `Amort.Distributed` compile cleanly with `lake build Amort`. Every theorem is
fully checked using Lean 4 foundational axioms (`propext`, `Classical.choice`, `Quot.sound`)
with zero `sorry` or `sorryAx`. All lines adhere to the $\le 100$ characters limit.
