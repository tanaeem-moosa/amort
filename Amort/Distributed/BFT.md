# Byzantine Fault Tolerance (3f + 1) (`Amort.Distributed.BFT`)

> **Status: stub — not verified** (Phase 4 canon stub; PBFT quorum intersection is proven,
> but OM(m) inductive protocol execution is a specification stub).


## 1. Byzantine Generals Model

In an unauthenticated distributed system subject to Byzantine faults, up to $f$ out of $N$
nodes may behave arbitrarily or maliciously (sending contradictory messages to different peers,
dropping messages, or fabricating reports).

Consensus requires:
1. **Agreement**: All loyal nodes decide the identical command.
2. **Validity**: If the commanding general is loyal, all loyal lieutenants decide the command
   issued by the commander.

---

## 2. Lamport-Shostak-Pease Lower Bound ($N \le 3f$)

Lamport, Shostak, and Pease (ACM TOPLAS 1982) proved that Byzantine consensus without digital
signatures is impossible unless $N \ge 3f + 1$.

### 2.1 The Canonical 3-Node, 1-Traitor Counterexample ($N = 3, f = 1$)
Consider three nodes: Commander $C$, Lieutenant 1 ($L_1$), Lieutenant 2 ($L_2$).
- **World 1**: Commander is traitorous. $C$ sends $\text{Attack}$ to $L_1$ and $\text{Retreat}$
  to $L_2$. $L_2$ truthfully reports to $L_1$: "Commander ordered Retreat".
  $L_1$'s observation:
  $(\text{from\_commander} = \text{Attack}, \text{from\_peer} = \text{Retreat})$.
  $L_2$'s observation:
  $(\text{from\_commander} = \text{Retreat}, \text{from\_peer} = \text{Attack})$.
  Agreement requires: $\text{decideL1} = \text{decideL2}$.
- **World 2**: Commander is loyal and orders $\text{Attack}$. $L_2$ is traitorous and lies to
  $L_1$, claiming the commander ordered $\text{Retreat}$.
  $L_1$'s observation:
  $(\text{from\_commander} = \text{Attack}, \text{from\_peer} = \text{Retreat})$.
  Validity requires: $\text{decideL1} = \text{Attack}$.
- **World 3**: Commander is loyal and orders $\text{Retreat}$. $L_1$ is traitorous and lies
  to $L_2$, claiming the commander ordered $\text{Attack}$.
  $L_2$'s observation:
  $(\text{from\_commander} = \text{Retreat}, \text{from\_peer} = \text{Attack})$.
  Validity requires: $\text{decideL2} = \text{Retreat}$.

### 2.2 Proof of Impossibility
Because $L_1$'s observation in World 1 and World 2 is identical:
$$\text{decideL1}(\text{Attack}, \text{Retreat}) = \text{Attack}$$
Because $L_2$'s observation in World 1 and World 3 is identical:
$$\text{decideL2}(\text{Retreat}, \text{Attack}) = \text{Retreat}$$
In World 1, both lieutenants are loyal, so Agreement requires:
$$\text{decideL1}(\text{Attack}, \text{Retreat}) = \text{decideL2}(\text{Retreat}, \text{Attack})$$
which implies $\text{Attack} = \text{Retreat}$, a contradiction!

```lean
theorem lsp_three_node_impossibility (proto : Protocol3) :
    ¬ (
      (proto.decideL1 { from_commander := Command.Attack, from_peer := Command.Retreat } =
        Command.Attack) ∧
      (proto.decideL2 { from_commander := Command.Retreat, from_peer := Command.Attack } =
        Command.Retreat) ∧
      (proto.decideL1 { from_commander := Command.Attack, from_peer := Command.Retreat } =
        proto.decideL2 { from_commander := Command.Retreat, from_peer := Command.Attack })
    )
```

---

## 3. Oral Messages Algorithm OM(m) for $N \ge 3f + 1$

When $N \ge 3m + 1$, consensus with up to $m$ traitors is achievable via the recursive Oral
Messages algorithm $OM(m)$.

### 3.1 Algorithm Structure
- **Base Case $OM(0)$**: Commander sends command directly to all lieutenants; lieutenants adopt it.
- **Recursive Step $OM(m)$**:
  1. Commander sends command $v$ to all $N - 1$ lieutenants.
  2. Each lieutenant $i$ acts as commander in $OM(m - 1)$, sending its received command $v_i$ to
     all other $N - 2$ lieutenants.
  3. Each lieutenant $i$ gathers a vector of commands $(v_{1i}, \dots, v_{(N-1)i})$ and applies
     `majorityVote`.

### 3.2 Correctness Theorems
```lean
theorem om_validity (m : ℕ) (N : ℕ) (hm : m > 0)
    (loyal_votes : ℕ) (traitor_votes : ℕ)
    (h_loyal : loyal_votes ≥ 2 * m)
    (h_traitor : traitor_votes ≤ m)
    (total_eq : loyal_votes + traitor_votes = N - 1) :
    loyal_votes > (N - 1) / 2
```
When the commander is loyal, loyal lieutenants cast at least $2m$ identical votes out of
$N - 1 \le 3m + \dots$. Since $2m > (N - 1) / 2$, the commander's command constitutes a strict
majority, ensuring Validity.

```lean
theorem om_agreement_of_identical_votes (votes1 votes2 : List Command)
    (h_eq : votes1 = votes2) :
    majorityVote votes1 = majorityVote votes2
```
When recursive calls ensure identical received vote lists, all loyal lieutenants decide identically.

---

## 4. PBFT Quorum Math

Practical Byzantine Fault Tolerance (Castro & Liskov, OSDI 1999) establishes quorum sizes for
authenticated Byzantine systems with $N = 3f + 1$.

### 4.1 PBFT Quorum Sizes
- Total nodes: $N = 3f + 1$.
- Quorum size: $|Q| \ge 2f + 1$.
- Maximum faulty nodes: $|F| \le f$.

### 4.2 Quorum Intersection Bounds
```lean
theorem pbft_quorum_intersection (f : ℕ)
    (Q1 Q2 : Finset (Fin (PBFTSystemSize f)))
    (hQ1 : IsPBFTQuorum f Q1) (hQ2 : IsPBFTQuorum f Q2) :
    (Q1 ∩ Q2).card ≥ f + 1
```
**Proof**:
$$|Q_1 \cap Q_2| = |Q_1| + |Q_2| - |Q_1 \cup Q_2| \ge (2f + 1) + (2f + 1) - (3f + 1) = f + 1$$

### 4.3 Honest Node in Intersection
```lean
theorem pbft_honest_in_intersection (f : ℕ)
    (Q1 Q2 : Finset (Fin (PBFTSystemSize f)))
    (F : Finset (Fin (PBFTSystemSize f)))
    (hQ1 : IsPBFTQuorum f Q1) (hQ2 : IsPBFTQuorum f Q2)
    (hF : F.card ≤ f) :
    ((Q1 ∩ Q2) \ F).Nonempty
```
**Proof**:
$$|(Q_1 \cap Q_2) \setminus F| \ge |Q_1 \cap Q_2| - |F| \ge (f + 1) - f = 1 > 0$$
Any two PBFT quorums share at least one non-faulty, honest server.
