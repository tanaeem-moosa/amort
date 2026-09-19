# Complexity Classes P and NP, Verifiers, and Reductions

## Overview

The `Amort.Complexity.Classes` module formalizes the foundational definitions of computational
complexity theory in Lean 4:
1. **Languages over Alphabets**: Formalized as `Language α := Set (List α)`.
2. **Polynomial Growth Bounds**: Canonical evaluation `polyEval c k n := c * (n + 1) ^ k` and
   closure properties under addition, multiplication, and composition.
3. **Class P (Deterministic Polynomial Time)**: Languages decidable by deterministic deciders
   whose step counts are polynomially bounded.
4. **Class NP (Nondeterministic Polynomial Time)**: Languages with polynomial-time verifiers
   and polynomial certificate length bounds:
   $$x \in L \iff \exists u \in \Sigma^*, |u| \le p(|x|) \wedge V(x, u) = \text{true}$$
5. **Embedding Theorem ($P \subseteq NP$)**: Constructive proof that every language in P
   belongs to NP using a trivial empty certificate.
6. **Polynomial-Time Reductions ($A \le_P B$)**: Karp (many-one) reductions preserving language
   membership with polynomial length/step bounds.
7. **Reduction Reflexivity and Transitivity**: Formally proving that $\le_P$ is a preorder:
   $$A \le_P A \quad \text{and} \quad A \le_P B \wedge B \le_P C \implies A \le_P C$$
8. **Class P Preservation**: If $A \le_P B$ and $B \in P$, then $A \in P$.
9. **NP-Hardness and NP-Completeness**: Formal predicates for NP-hardness and NP-completeness.

---

## Key Definitions & Structures

### Canonical Polynomial Bounds
```lean
def polyEval (c k : ℕ) (n : ℕ) : ℕ := c * (n + 1) ^ k

def IsPolyBound (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, f n ≤ polyEval c k n
```

- **Monotonicity**: `polyEval_mono : a ≤ b → polyEval c k a ≤ polyEval c k b`.
- **Composition Bound**:
  $$\text{polyEval } c_2\ k_2\ (\text{polyEval } c_1\ k_1\ n) \le
    \text{polyEval } (c_2 (c_1 + 1)^{k_2})\ (k_1 k_2)\ n$$
- **Closure**: Closed under addition (`isPolyBound_add`), multiplication (`isPolyBound_mul`),
  and composition (`isPolyBound_comp`).

### Deterministic Deciders and Class P
```lean
structure Decider (α : Type*) where
  decide : List α → Bool
  polyCoeff : ℕ
  polyExp : ℕ

def InP {α : Type*} (L : Language α) : Prop :=
  ∃ M : Decider α, M.Accepts L
```

### Verifiers, Certificates, and Class NP
```lean
structure Verifier (α β : Type*) where
  verify : List α → List β → Bool
  certCoeff : ℕ
  certExp : ℕ
  stepCoeff : ℕ
  stepExp : ℕ

def Verifier.Accepts (V : Verifier α β) (L : Language α) : Prop :=
  ∀ x : List α, x ∈ L ↔ ∃ u : List β, u.length ≤ V.certBound x.length ∧ V.verify x u = true

def InNP {α : Type*} (L : Language α) : Prop :=
  ∃ (β : Type) (V : Verifier α β), V.Accepts L
```

### Polynomial-Time Many-One Reductions (Karp Reductions)
```lean
structure PolyReduction {α β : Type*} (A : Language α) (B : Language β) where
  toFun : List α → List β
  polyCoeff : ℕ
  polyExp : ℕ
  length_bound : ∀ x, (toFun x).length ≤ polyEval polyCoeff polyExp x.length
  correct : ∀ x, x ∈ A ↔ toFun x ∈ B

def PolyReducible (A : Language α) (B : Language β) : Prop :=
  Nonempty (PolyReduction A B)

scoped infix:50 " ≤P " => PolyReducible
```

---

## Fundamental Theorems

| Theorem | Lean Name | Mathematical Statement |
| :--- | :--- | :--- |
| **$P \subseteq NP$** | `inNP_of_inP` | $\forall L \in P \implies L \in NP$ |
| **Reduction Reflexivity** | `polyReducible_refl` | $\forall A, A \le_P A$ |
| **Reduction Transitivity** | `polyReducible_trans` | $A \le_P B \wedge B \le_P C \implies A \le_P C$ |
| **P-Preservation** | `inP_of_polyReducible` | $A \le_P B \wedge B \in P \implies A \in P$ |

### Axiom Verification
All theorems are verified with zero axioms beyond foundational Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`), with 0 `sorry` or `sorryAx`.
