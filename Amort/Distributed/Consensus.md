# Crash-Tolerant Consensus: Paxos & Raft (`Amort.Distributed.Consensus`)

## 1. Majority Quorum Intersection Foundation

Consensus protocols rely on overlapping majorities to preserve knowledge across leader elections
and failures.

### 1.1 Majority Quorum Definition
In a system of $N$ processes (`Fin N`), a subset $Q \subseteq \text{Fin } N$ is a majority quorum
if:
$$|Q| > \lfloor N / 2 \rfloor$$

### 1.2 Quorum Intersection Theorem
```lean
theorem majority_quorum_intersection {N : ℕ} (_hN : N > 0)
    {Q1 Q2 : Finset (Fin N)}
    (hQ1 : IsMajorityQuorum N Q1) (hQ2 : IsMajorityQuorum N Q2) :
    (Q1 ∩ Q2).Nonempty
```
**Proof**: By inclusion-exclusion on finite sets:
$$|Q_1 \cup Q_2| + |Q_1 \cap Q_2| = |Q_1| + |Q_2|$$
Since $Q_1 \cup Q_2 \subseteq \text{Fin } N$, $|Q_1 \cup Q_2| \le N$.
Since $|Q_1| \ge \lfloor N/2 \rfloor + 1$ and $|Q_2| \ge \lfloor N/2 \rfloor + 1$:
$$|Q_1| + |Q_2| \ge 2 \lfloor N / 2 \rfloor + 2 > N$$
If $Q_1 \cap Q_2 = \emptyset$, then $|Q_1 \cup Q_2| = |Q_1| + |Q_2| > N$, contradiction.
Hence $Q_1 \cap Q_2 \ne \emptyset$.

---

## 2. Single-Decree Paxos (Synod Protocol)

Lamport's Paxos algorithm (1998, 2001) achieves consensus in an asynchronous network subject to
crash-recovery failures.

### 2.1 Ballot Numbers
Ballot identifiers are totally ordered pairs:
$$\text{Ballot} = \mathbb{N} \times \text{Fin } N$$
Ordering is lexicographic: round number takes precedence, ties broken by unique proposer ID
(`BallotLt`, `ballotLt_trichotomy`).

### 2.2 Two-Phase State Machine
1. **Phase 1a (Prepare)**: Proposer sends `Prepare(b)` to acceptors.
2. **Phase 1b (Promise)**: Acceptor promises not to accept ballots $< b$ and returns highest-ballot
   accepted proposal `(maxBal, maxVal)`.
3. **Phase 2a (Propose)**: Once promised by a majority quorum, proposer selects value $v$
   corresponding to the highest ballot reported in the promises (or any value if none reported),
   and sends `Propose(b, v)`.
4. **Phase 2b (Accept)**: Acceptor accepts $(b, v)$ unless it already promised a higher ballot.

### 2.3 Chosen Values & Invariants
A value $v$ is **chosen** at ballot $b$ if accepted by a majority quorum $Q_a$:
$$\text{IsChosenAt}(state, b, v) \iff$$
$$\quad \exists Q_a, \text{IsMajorityQuorum}(Q_a) \land Q_a \subseteq state.\text{accepted}(b, v)$$

**Core Paxos Proposal Invariant**:
If $v$ is chosen at ballot $b$, then for any ballot $b' > b$, any proposal issued at $b'$ must have
value $v$:
```lean
def SatisfiesPaxosProposalInvariant {N : ℕ} {α : Type} (state : PaxosState N α) : Prop :=
  ∀ b b' : Ballot N, ∀ v v' : α,
    IsChosenAt state b v →
    BallotLt b b' →
    state.proposal b' = some v' →
    v' = v
```

### 2.4 Learner Agreement Theorem
```lean
theorem paxos_learner_agreement {N : ℕ} {α : Type}
    (state : PaxosState N α)
    (h_inv : SatisfiesPaxosProposalInvariant state)
    (b1 b2 : Ballot N) (v1 v2 : α)
    (h1 : LearnerDecides state b1 v1)
    (h2 : LearnerDecides state b2 v2) :
    v1 = v2
```
**Proof**: By trichotomy on $b_1, b_2$:
- If $b_1 < b_2$: Value $v_1$ is chosen at $b_1$. By the proposal invariant, any proposal at $b_2$
  must have value $v_1$. Since $v_2$ was chosen at $b_2$, $v_2 = v_1$.
- If $b_1 = b_2$: Proposers issue at most one proposal per ballot, so $v_1 = v_2$.
- If $b_2 < b_1$: Symmetrically, $v_1 = v_2$.

---

## 3. Multi-Paxos Replicated Log

In Multi-Paxos, the replicated log is indexed by slot numbers $\mathbb{N}$. Each slot runs an
independent instance of Single-Decree Paxos (`MultiPaxosState`).

### 3.1 Slot Safety
```lean
theorem multi_paxos_slot_safety {N : ℕ} {Cmd : Type}
    (mps : MultiPaxosState N Cmd) (s : Slot) (cmd1 cmd2 : Cmd)
    (h1 : IsCommittedAt mps s cmd1) (h2 : IsCommittedAt mps s cmd2) :
    cmd1 = cmd2
```
At most one command can ever be committed in any log slot.

### 3.2 Replicated State Machine (RSM) Safety
```lean
theorem rsm_safety {State Cmd : Type} (step : State → Cmd → State) (init : State)
    (cmds1 cmds2 : List Cmd) (h_eq : cmds1 = cmds2) :
    applyLog step init cmds1 = applyLog step init cmds2
```
Deterministic execution of committed log entries ensures that all replicas traverse through
identical state transitions.

---

## 4. Raft Safety Invariants

Raft (Ongaro & Ousterhout, USENIX ATC 2014) decomposes consensus into leader election, log
replication, and safety invariants.

### 4.1 Leader Election Safety
```lean
theorem raft_leader_election_safety {N : ℕ} (hN : N > 0)
    (res : RaftElectionState N) (t : Term) (c1 c2 : Fin N)
    (h1 : IsElectedLeader res t c1) (h2 : IsElectedLeader res t c2) :
    c1 = c2
```
**Proof**: To win election in term $t$, a candidate must gather votes from a majority quorum.
Each server votes at most once per term. By majority quorum intersection, the voting quorums for
$c_1$ and $c_2$ intersect at some voter $v$. Since $v$ cast only one vote in term $t$, $c_1 = c_2$.

### 4.2 Log Matching Invariant
```lean
def SatisfiesLogMatchingInvariant {Cmd : Type} (log1 log2 : List (RaftLogEntry Cmd)) : Prop :=
  ∀ e1 e2 : RaftLogEntry Cmd,
    e1 ∈ log1 → e2 ∈ log2 →
    e1.index = e2.index → e1.term = e2.term →
    e1.command = e2.command ∧
    ∀ k < e1.index,
      log1.find? (fun e => e.index = k) = log2.find? (fun e => e.index = k)
```
If two entries in different logs have the same index and term, then they store the same command,
and their logs are identical up to that index.
