# Huffman Coding & Optimal Prefix Codes

> **Status: stub — not verified** (Phase 3 canon stub; sibling exchange arithmetic is proven,
> but prefix tree construction algorithm is a specification stub).


## Mathematical Specification
Alphabet symbols $x \in \alpha$ possess positive frequencies $w(x) > 0$.
Prefix codes correspond to binary trees `HuffmanTree α`:
- Leaf: symbol $x$ with weight $w$.
- Internal node: joins two subtrees with weight $w(l) + w(r)$.

## External Path Length Equivalence
The weighted external path length is defined as:
$$\text{WPL}(T) = \sum_{x \in \text{leaves}(T)} w(x) \cdot \text{depth}(x)$$
We prove by induction that this is identically equal to the sum of the weights of all internal nodes:
$$\text{costAtDepth } 0\ T = \text{WPL}(T)$$
via the depth-shift recurrence:
$$\text{costAtDepth } d\ T = d \cdot \text{totalWeight}(T) + \text{WPL}(T)$$

## Greedy Choice Property
For leaves $a, x$ with weights $w_a \le w_x$ and depths $d_a \le d_x$:
$$w_a \cdot d_x + w_x \cdot d_a \le w_a \cdot d_a + w_x \cdot d_x$$
Hence, swapping minimal-frequency symbols to maximal-depth sibling positions never increases
the tree cost. This guarantees that an optimal prefix tree exists having the two lowest-frequency
symbols as siblings at maximum depth.

## Operational Complexity
Using a binary min-heap:
- Linear build-heap on $n$ symbols: $2n$ operations.
- $n - 1$ merge steps, each using 2 `extractMin` and 1 `insert` ($\le 5 \cdot \text{Nat.size } n$).
- Total work: $W(n) \le 7n \cdot \text{Nat.size } n = O(n \log n)$.
