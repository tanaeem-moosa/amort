# Consistent Global Snapshots (`Amort.Distributed.Snapshot`)

## 1. System Model & Consistent Cuts

In a distributed system without a shared global memory or synchronized physical clocks, capturing
a meaningful global state requires recording a **Consistent Cut** (Chandy & Lamport, ACM TOCS 1985).

### 1.1 Processes and Channels
- A system consists of $N$ processes (`Fin N`) connected by directed communication channels
  `Channel N` (`src`, `dst`).
- Channels are assumed to be reliable and strictly FIFO (First-In, First-Out).
- A message $m$ is characterized by `send_time` on $m.\text{src}$ and `recv_time` on $m.\text{dst}$.

### 1.2 Definition of a Consistent Cut
A global cut `Cut N := Fin N → ℕ` assigns a local snapshot time $T_p$ to each process $p$.
A cut is **consistent** if no message travels backward across the cut boundary:
```lean
def IsConsistentCut {N : ℕ} (cut : Cut N) (msgs : Set (Message N)) : Prop :=
  ∀ m ∈ msgs, m.recv_time ≤ cut m.dst → m.send_time ≤ cut m.src
```
Equivalently: If an effect (message receipt) is included in the snapshot, its cause (message send)
must also be included in the snapshot.

---

## 2. Chandy-Lamport Distributed Snapshot Algorithm

The algorithm uses a special control message called a `Marker` to delineate messages sent before
and after the snapshot.

### 2.1 Marker Passing Rules
1. **Initiator Rule**: An initiator process $P_0$ records its own local state and immediately sends
   a `Marker` along all outgoing channels.
2. **Marker Receiving Rule**: When process $q$ receives a `Marker` on channel $c = (p, q)$:
   - **Case A**: If $q$ has not yet recorded its local state:
     - $q$ immediately records its local state (setting $T_q$).
     - $q$ records channel $c$ state as empty ($\emptyset$).
     - $q$ sends a `Marker` along all of its outgoing channels.
   - **Case B**: If $q$ has already recorded its local state:
     - $q$ records channel $c$ state as the sequence of all messages received on $c$ after $q$'s
       local snapshot and prior to receiving the `Marker` on $c$.

### 2.2 Formal Invariant Conditions
Under FIFO channel behavior:
1. `fifo_after`: Messages sent after $T_p$ arrive at $q$ after the Marker on channel $(p, q)$.
2. `snapshot_before_marker`: A process records its snapshot at or before receiving any Marker.

---

## 3. Main Theorems

### 3.1 Consistent Cut Theorem
```lean
theorem chandy_lamport_consistent_cut {N : ℕ} (exec : ChandyLamportExecution N) :
    IsConsistentCut exec.snapshot_time exec.msgs
```
**Proof**:
Suppose message $m$ was received before or at the receiver's snapshot point:
$$m.\text{recv\_time} \le \text{snapshot\_time}(m.\text{dst})$$
Assume for contradiction that $m$ was sent after the sender's snapshot point:
$$m.\text{send\_time} > \text{snapshot\_time}(m.\text{src})$$
By the FIFO rule (`fifo_after`), $m$ must arrive after the Marker on channel
$(m.\text{src}, m.\text{dst})$:
$$m.\text{recv\_time} > \text{marker\_recv\_time}(m.\text{src}, m.\text{dst})$$
By the Snapshot Trigger rule (`snapshot_before_marker`), the receiver recorded its state at or
before the Marker arrived:
$$\text{marker\_recv\_time}(m.\text{src}, m.\text{dst}) \ge \text{snapshot\_time}(m.\text{dst})$$
Combining these yields:
$$m.\text{recv\_time} > \text{snapshot\_time}(m.\text{dst})$$
which directly contradicts $m.\text{recv\_time} \le \text{snapshot\_time}(m.\text{dst})$!
Therefore, $m.\text{send\_time} \le \text{snapshot\_time}(m.\text{src})$.
The recorded state forms a consistent cut.

### 3.2 Impossibility of Inconsistent Messages
```lean
theorem consistent_cut_no_inconsistent {N : ℕ} {cut : Cut N} {msgs : Set (Message N)}
    (h_cons : IsConsistentCut cut msgs) (m : Message N) (hm : m ∈ msgs) :
    classifyMessage cut m ≠ MessageCutClassification.Inconsistent
```
In any consistent cut, no message is sent after the cut and received before the cut.

### 3.3 Channel State Soundness
```lean
theorem channel_state_soundness {N : ℕ} (exec : ChandyLamportExecution N)
    (m : Message N) (h_in_chan : InChannelState exec m) :
    m.send_time ≤ exec.snapshot_time m.src
```
Every message recorded in a channel's state was sent before or at the sender's snapshot point.
No message recorded in channel state was sent after the snapshot was taken.
