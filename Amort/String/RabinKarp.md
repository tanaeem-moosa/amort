# Rabin-Karp Rolling Hash String Matching

## 1. Overview

The Rabin-Karp algorithm (Karp & Rabin, 1987) is an algebraic randomized string matching technique based on fingerprinting. Given a pattern $P$ of length $m$ and text $T$ of length $n$:
- It computes a polynomial rolling hash $H(P)$ of the pattern and compares it with the rolling hash of each length-$m$ sliding window of $T$.
- When the window slides from $T[i \dots i+m-1]$ to $T[i+1 \dots i+m]$, the new hash value is computed in $O(1)$ arithmetic operations using the previous hash value.
- Full character comparisons are only executed when the window hash matches the pattern hash (eliminating comparisons on mismatching windows).

## 2. Mathematical Architecture

### Polynomial Rolling Hash

For an integer sequence $w = [w_0, w_1, \dots, w_{m-1}]$ and base $B \ge 1$:
$$H(w) = \sum_{j=0}^{m-1} w[j] \cdot B^{m - 1 - j}$$

The recursive evaluation rule (Horner's method) is:
$$H(\varepsilon) = 0$$
$$H(c \cdot cs) = c \cdot B^{|cs|} + H(cs)$$

Appending a character $c$ to word $cs$ satisfies:
$$H(cs ++ [c]) = H(cs) \cdot B + c$$
Formally proven in theorem `polyHash_append_singleton`.

### Sliding Window Hash Update Identity

Let the current window be $w = c_{\text{old}} \cdot cs$ of length $m$, and the next window be $w' = cs ++ [c_{\text{new}}]$.
Substituting the Horner relation:
$$H(w') = H(cs ++ [c_{\text{new}}]) = H(cs) \cdot B + c_{\text{new}}$$
Since $H(w) = c_{\text{old}} \cdot B^{m-1} + H(cs)$, we have $H(cs) = H(w) - c_{\text{old}} \cdot B^{m-1}$.
Therefore:
$$H(w') = (H(w) - c_{\text{old}} \cdot B^{m-1}) \cdot B + c_{\text{new}} = H(w) \cdot B - c_{\text{old}} \cdot B^m + c_{\text{new}}$$

Under modular arithmetic with modulus $p$:
$$H(S[i+1 \dots i+m]) \equiv \big( H(S[i \dots i+m-1]) \cdot B - S[i] \cdot B^m + S[i+m] \big) \pmod p$$
Formally proven in theorems `polyHash_sliding_window` and `polyHash_sliding_window_mod`.

### Hash Congruence Soundness

- Integer Soundness: $w_1 = w_2 \implies H(w_1) = H(w_2)$ (`polyHash_congruence_soundness`).
- Modular Soundness: $w_1 = w_2 \implies H(w_1) \equiv H(w_2) \pmod p$ (`polyHash_mod_congruence`).

Because the mapping $w \mapsto H(w)$ is a well-defined mathematical function, identical substrings always produce identical hash values (zero false negatives).

## 3. Operational Complexity Bounds

1. **Preprocessing**:
   Evaluating the initial hash $H(P)$ and initial text window $H(T[0 \dots m-1])$ takes $2m$ arithmetic operations.
2. **Window Sliding**:
   For each of the $n - m$ shifts, updating the hash takes $O(1)$ operations ($1$ multiplication, $1$ subtraction, $1$ addition).
3. **Collision Verification**:
   If there are $k$ positions where hash values match, full string verification takes $k \cdot m$ character comparisons.

Total operational work:
$$\text{Work} = 2m + n + k \cdot m$$
In the average case (under a random prime modulus $p$ chosen uniformly, or when no false positives occur, $k \approx \text{matches}$), $k$ is small, yielding an average-case operational step bound:
$$\text{Average Work} \le 2(n + m) = O(|T| + |P|)$$
Formally defined in `rabinKarpWork` and `rabinKarpAverageWork`, with bound `rabinKarpWork_no_collisions`.

## 4. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
