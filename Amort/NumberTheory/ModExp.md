# Fast Modular Exponentiation: Repeated Squaring

## Algorithm State and Invariant
The loop state $(acc, base, exp)$ satisfies:
$$acc \cdot base^{exp} \equiv a^b \pmod m$$
- When $exp$ is even ($exp = 2k$): $base \leftarrow base^2 \pmod m$, $exp \leftarrow k$.
  $$acc \cdot (base^2)^k = acc \cdot base^{2k} = acc \cdot base^{exp}$$
- When $exp$ is odd ($exp = 2k + 1$): $acc \leftarrow acc \cdot base \pmod m$, $base \leftarrow base^2 \pmod m$, $exp \leftarrow k$.
  $$(acc \cdot base) \cdot (base^2)^k = acc \cdot base^{2k + 1} = acc \cdot base^{exp}$$
When $exp = 0$, $acc \cdot base^0 = acc \equiv a^b \pmod m$.

## Complexity
- Number of iterations is $\text{Nat.size } b$.
- Multiplications per iteration $\le 2$.
- Total multiplications $\le 2 \cdot \text{Nat.size } b = O(\log b)$.
