# Impossibility Theorems: CAP & Two Generals (`Amort.Distributed.Impossibility`)

## 1. Gilbert-Lynch CAP Theorem

Brewer's CAP Conjecture (2000) asserts that a distributed data store can simultaneously achieve
at most two of three properties: Consistency, Availability, and Partition Tolerance.
Gilbert & Lynch (ACM SIGACT News, 2002) provided the first formal mathematical proof of this
impossibility in an asynchronous network model.

### 1.1 Formal Model
- **Network Partition**: The nodes are partitioned into two non-empty disjoint subsets $G_1$ and
  $G_2$ (`inG1`, `inG2`). During a partition, any message transmitted between $G_1$ and $G_2$ is
  dropped by the network.
- **Client Operations**:
  - `Write(v)`: Client writes value $v \in \mathbb{N}$ to a node in $G_1$.
  - `Read`: Client queries a node in $G_2$.
- **Availability (A)**: Every read or write request submitted to a non-failing node must
  eventually receive a response.
- **Linearizability (Consistency C)**: There exists a global sequential execution extending the
  real-time ordering such that each read returns the value of the most recent write.

### 1.2 Indistinguishability & Proof of Impossibility
Consider two executions:
1. **Execution $\alpha$**: A client writes value $v \ne 0$ to node $n_1 \in G_1$. The write
   completes. Then a client reads from node $n_2 \in G_2$. Because of the network partition,
   no messages pass between $n_1$ and $n_2$.
2. **Execution $\beta$**: No write is ever performed. A client reads from node $n_2 \in G_2$.
   No messages are delivered across the partition.

**Key Lemma: Local Indistinguishability**:
Because all cross-partition messages are dropped, the local history observed by $n_2$ up to the
read response time is identical in $\alpha$ and $\beta$:
$$\text{view}(n_2, \alpha) = \text{view}(n_2, \beta) = \text{none}$$
Any deterministic or locally causal protocol must produce the same response in both executions:
$$\text{response}(n_2, \alpha) = \text{response}(n_2, \beta)$$

**Impossibility Contradiction**:
- By Linearizability on execution $\beta$ (no writes occurred), the read must return the initial
  value $0$: $\text{response}(n_2, \beta) = 0$.
- Hence $\text{response}(n_2, \alpha) = 0$.
- But in execution $\alpha$, the write of $v \ne 0$ completed before the read began.
  Linearizability requires $\text{response}(n_2, \alpha) = v$.
- Thus $v = 0$, directly contradicting $v \ne 0$!

```lean
theorem gilbert_lynch_impossibility (proto : Protocol) (v : Value) (hv : v ≠ initialValue) :
    ¬ SatisfiesLinearizability proto
```

---

## 2. Two Generals' Problem

The Two Generals' Problem (Gray 1978) is the foundational impossibility theorem for communication
over unreliable channels.

### 2.1 Problem Formulation
Two generals, $A$ and $B$, must coordinate an attack at dawn. They can communicate only by sending
messengers across enemy territory, where messengers may be captured (messages dropped).

**Requirements**:
1. **Agreement**: In every execution, both generals make the same decision:
   $$(dec\ k).1 = (dec\ k).2 \quad (\forall k \in \mathbb{N})$$
2. **Zero-Message Validity**: If zero messages are delivered, General $B$ has received no
   communication from General $A$, and cannot attack: $(dec\ 0).2 = \text{Retreat}$.
3. **Lossy Indistinguishability**: The sender of message $k$ cannot distinguish whether message
   $k$ was delivered to the recipient or lost in transit:
   - If $k$ is odd (sent by $A$): $(dec\ k).1 = (dec\ (k-1)).1$.
   - If $k$ is even (sent by $B$): $(dec\ k).2 = (dec\ (k-1)).2$.

### 2.2 Proof of Impossibility by Backward Induction
```lean
theorem step_reduction (dec : DecisionSequence)
    (h_agree : Agreement dec) (h_lossy : LossyIndistinguishable dec)
    (k : ℕ) (hk : k > 0)
    (h_attack : dec k = (Action.Attack, Action.Attack)) :
    dec (k - 1) = (Action.Attack, Action.Attack)
```
**Step Reduction**:
- If $k$ is odd: General $A$'s decision at step $k-1$ equals its decision at step $k$, which is
  $\text{Attack}$. By Agreement at step $k-1$, General $B$'s decision must also be $\text{Attack}$.
- If $k$ is even: General $B$'s decision at step $k-1$ equals its decision at step $k$, which is
  $\text{Attack}$. By Agreement at step $k-1$, General $A$'s decision must also be $\text{Attack}$.
- In both cases, $dec(k-1) = (\text{Attack}, \text{Attack})$.

**Backward Induction**:
```lean
theorem attack_zero_of_attack_k (dec : DecisionSequence)
    (h_agree : Agreement dec) (h_lossy : LossyIndistinguishable dec) :
    ∀ k : ℕ, dec k = (Action.Attack, Action.Attack) →
      dec 0 = (Action.Attack, Action.Attack)
```
By induction down to $k = 0$, coordinated attack at step $k$ forces coordinated attack at step $0$:
$$dec(0) = (\text{Attack}, \text{Attack})$$
This implies $(dec\ 0).2 = \text{Attack}$, directly contradicting Zero-Message Validity
($(dec\ 0).2 = \text{Retreat}$).

```lean
theorem two_generals_impossibility (dec : DecisionSequence)
    (h_agree : Agreement dec)
    (h_lossy : LossyIndistinguishable dec)
    (h_valid : ZeroMessageValidity dec)
    (k : ℕ) :
    dec k ≠ (Action.Attack, Action.Attack)
```
No protocol with finite message delivery over an unreliable channel can guarantee agreement.
