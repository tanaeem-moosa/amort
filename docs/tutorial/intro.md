# Start here

*Read this before the first node, Binary GCD.*

## What this tutorial is for

AI assistants can now write code and proofs faster than we can read them. You can ask one to prove its claims in Lean, and Lean will check every proof. But a proof only shows that *some* statement is true. When an AI agent wrote the proofs in this repository, the mistakes that slipped through were never wrong proofs. They were statements that promised less than their names did: a "correct" theorem about the wrong function, or a cost bound that was true by definition.

So this tutorial teaches one skill: reading a Lean statement and deciding whether it's the right one. You own the statement, the AI writes the proof, and Lean referees.

## How these chapters work

Each chapter takes one algorithm through the same five steps. First we say what the problem is. Then we write down, in Lean, what a correct answer means. Then we look at the algorithm. Last come the two theorems: one says the algorithm is correct, and one says how many steps it takes.

You don't have to write the proofs. It's more important to understand the setup: the definitions and the theorem statements. A proof that an AI wrote and Lean checked validates itself, so you never need to read one to trust it, though it can be fun to understand them. What Lean can't tell you is whether a theorem says what you think it says. A proof that compiles only means *some* statement is true. Reading the statement and deciding whether it's the right one is your job, and it's what these chapters practise.

Every chapter ends with the same kinds of exercise:

- **Predict:** say what a piece of Lean code returns, then run it.
- **State it yourself:** turn an English claim into a Lean statement, then compare it with the repository's.
- **Spot the fake:** pick out which of several real, compiling theorems actually proves a claim.
- **Prove it with AI** (optional): hand a statement to an AI assistant, let Lean check the proof, and make sure the statement didn't change along the way.

## What you need

You should be comfortable in one programming language. Any language will do; the chapters show each algorithm in Python next to the Lean.

You don't need to know any Lean yet. The chapters explain the notation as it appears, and each one ends with a table of what it introduced. Some reading beforehand makes the first chapter easier:

| Reading | Why | Time |
| :--- | :--- | :--- |
| **[*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/), chapter 1** (recommended) | Lean as a programming language: `def`, pattern matching, structures and `#eval`. This is enough to read every algorithm in the tree. | 2–3 hours |
| [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) (optional) | Runs in the browser. It gives you a feel for what a proof is, which helps when you judge statements, but you won't need to write proofs. | 3–6 hours |
| [*Theorem Proving in Lean 4*](https://lean-lang.org/theorem_proving_in_lean4/) (reference) | The full story of how Lean's logic works, for when you want to know more. | — |
| [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) (reference) | Look up any Mathlib name a chapter uses, such as `Nat.gcd` or `List.Perm`, and see its exact statement. | — |

## Running the examples

You can read every chapter without installing anything. To run the examples and try the exercises, you need Lean on your own machine, because the chapters depend on Mathlib:

1. Install Lean with the instructions at [lean-lang.org](https://lean-lang.org/install/). This sets up `elan`, which manages Lean versions, and the Lean extension for VS Code.
2. Clone this repository and, in its folder, run `lake exe cache get` to download a prebuilt Mathlib. Building Mathlib yourself takes hours.
3. Run `lake build`. This checks every proof in the repository and every example in the chapters.

Each chapter has a companion file in `Tutorial/`, such as `Tutorial/BinaryGCD.lean`. Open it in VS Code to see Lean's output next to the code. The algorithms and their full proofs live in `Amort/`.

When you're ready, start with [Binary GCD](binary_gcd.md).
