// Bundled fallback snapshot of tutorial/tree.json for offline/file:// execution
window.__TREE_DATA_FALLBACK__ = {
  "schema_version": "1.0.0",
  "version": "1.0.0",
  "title": "Verified Algorithms Skill Tree",
  "description": "A verified algorithms curriculum and interactive skill tree formalised in Lean 4.",
  "categories": [
    {
      "id": "arithmetic",
      "name": "Arithmetic & Number Theory",
      "color": "#3b82f6"
    },
    {
      "id": "sorting",
      "name": "Sorting & Searching",
      "color": "#10b981"
    },
    {
      "id": "amortization",
      "name": "Data Structures & Amortization",
      "color": "#8b5cf6"
    },
    {
      "id": "strings",
      "name": "Strings & Pattern Matching",
      "color": "#f59e0b"
    },
    {
      "id": "dp",
      "name": "Dynamic Programming",
      "color": "#ec4899"
    },
    {
      "id": "greedy",
      "name": "Greedy Algorithms",
      "color": "#14b8a6"
    },
    {
      "id": "graphs",
      "name": "Graph Algorithms",
      "color": "#6366f1"
    },
    {
      "id": "complexity",
      "name": "Complexity & Reductions",
      "color": "#ef4444"
    }
  ],
  "nodes": [
    {
      "id": "BGCD",
      "name": "🌱 Binary GCD (Stein)",
      "tier": 1,
      "category": "arithmetic",
      "status": "open",
      "prerequisites": [],
      "unlocks": ["EUC", "INS", "BS", "DYN", "MODEXP"],
      "algorithm_skill": "Bit tricks (parity, halving); one spec, a non-obvious algorithm",
      "lean_skill": "def, if/else, #eval, theorem as a claim, termination_by, = Nat.gcd a b, WithSteps counting pattern, Nat.size as bit length",
      "reference_module": "Amort.GCD.BinaryGCD",
      "headline_theorems": [
        "Nat.binaryGcd_eq_gcd",
        "Nat.binaryGcdWithSteps_fst",
        "Nat.binaryGcdWithSteps_snd_le_size_add_size",
        "Nat.binaryGcdWithSteps_snd_le_two_mul_size_add",
        "Nat.isBigO_binaryGcdSteps_atTop"
      ],
      "chapter_path": "tutorial/binary_gcd.md",
      "exercises": {
        "predict": [
          {
            "id": "bgcd_pred_1",
            "prompt": "What does `#eval binaryGcd 48 18` evaluate to in Lean 4?",
            "input_type": "number",
            "expected_answer": "6",
            "explanation": "48 and 18 share common factor 2. Halving: 2 * binaryGcd 24 9 = 2 * binaryGcd 12 9 = 2 * binaryGcd 6 9 = 2 * binaryGcd 3 9 = 2 * binaryGcd 3 3 = 2 * 3 = 6."
          },
          {
            "id": "bgcd_pred_2",
            "prompt": "What does `#eval binaryGcd 0 7` evaluate to according to the base case of Stein's algorithm?",
            "input_type": "number",
            "expected_answer": "7",
            "explanation": "If a = 0, the algorithm immediately returns b (here 7), matching Mathlib's Nat.gcd convention."
          }
        ],
        "spot_the_fake": [
          {
            "id": "bgcd_fake_1",
            "prompt": "Which of the following theorem formulations genuinely establishes the logarithmic bit complexity of Binary GCD without circular definitions?",
            "options": [
              {
                "id": "a",
                "text": "def gcdCost (a b : ℕ) := Nat.size a + Nat.size b\ntheorem gcdCost_le (a b : ℕ) : gcdCost a b ≤ Nat.size a + Nat.size b",
                "is_fake": true,
                "explanation": "Fake: Defines cost as its own answer. This theorem is a tautology about gcdCost, decoupled from the execution of binaryGcd."
              },
              {
                "id": "b",
                "text": "theorem binaryGcdWithSteps_fst (a b : ℕ) : (binaryGcdWithSteps a b).1 = binaryGcd a b\ntheorem binaryGcdSteps_le_size_add_size (a b : ℕ) : binaryGcdSteps a b ≤ Nat.size a + Nat.size b",
                "is_fake": false,
                "explanation": "Genuine: The first theorem couples the instrumented counter to the authentic executable algorithm, and the second bounds actual recursion steps by the bit lengths of the inputs."
              },
              {
                "id": "c",
                "text": "theorem binaryGcdSteps_le_add (a b : ℕ) : binaryGcdSteps a b ≤ a + b",
                "is_fake": true,
                "explanation": "Weak/Misleading: While true and coupled, bounding by a + b is linear in numeric values, which is exponential in input bit lengths."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "A genuine complexity proof must tie an instrumented counter to the executable algorithm (.1 = algo x) and bound the count by input bit lengths rather than circular definitions."
          }
        ]
      }
    },
    {
      "id": "EUC",
      "name": "Euclid's GCD",
      "tier": 2,
      "category": "arithmetic",
      "status": "ready",
      "prerequisites": ["BGCD"],
      "unlocks": ["EXT"],
      "algorithm_skill": "Remainders; comparing two algorithms against one spec",
      "lean_skill": "Two implementations proved equal to the same spec; min in a bound",
      "reference_module": "Amort.GCD.EuclideanGCD",
      "headline_theorems": [
        "Nat.euclidGcd_eq_gcd",
        "Nat.euclidGcdWithSteps_fst",
        "Nat.euclidGcdWithSteps_snd",
        "Nat.euclidGcdWithSteps_snd_le_two_mul_size_min",
        "Nat.euclidGcdWithSteps_snd_le_two_mul_size_add",
        "Nat.isBigO_euclidGcdWithSteps_snd_atTop"
      ],
      "chapter_path": "tutorial/euclid_gcd.md",
      "exercises": {
        "predict": [
          {
            "id": "euc_pred_1",
            "prompt": "What does `#eval euclidGcd 105 252` evaluate to?",
            "input_type": "number",
            "expected_answer": "21",
            "explanation": "252 % 105 = 42; 105 % 42 = 21; 42 % 21 = 0. The remainder becomes 0, so the GCD is 21."
          }
        ],
        "spot_the_fake": [
          {
            "id": "euc_fake_1",
            "prompt": "Which theorem statement guarantees that Euclidean GCD satisfies the exact mathematical specification of greatest common divisor?",
            "options": [
              {
                "id": "a",
                "text": "theorem euclidGcd_self (a b : ℕ) : euclidGcd a b = euclidGcd a b",
                "is_fake": true,
                "explanation": "Fake: A reflexive identity proves nothing about correctness; any buggy function satisfies f x = f x."
              },
              {
                "id": "b",
                "text": "theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b",
                "is_fake": false,
                "explanation": "Genuine: Proves exact equality to Mathlib's canonical Nat.gcd specification for all natural inputs."
              },
              {
                "id": "c",
                "text": "theorem euclidGcd_divides (a b : ℕ) : euclidGcd a b ∣ a",
                "is_fake": true,
                "explanation": "Incomplete: Proves only that the result divides a, not that it divides b or that it is the greatest such divisor (e.g. returning 1 satisfies this)."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Correctness requires establishing that the algorithm output coincides with the independent specification Nat.gcd, rather than partial divisibility or tautologies."
          }
        ]
      }
    },
    {
      "id": "MODEXP",
      "name": "Fast Modular Exponentiation",
      "tier": 2,
      "category": "arithmetic",
      "status": "ready",
      "prerequisites": ["BGCD"],
      "unlocks": [],
      "algorithm_skill": "Halving the exponent",
      "lean_skill": "Modular arithmetic (% m, Nat.ModEq), hypotheses like 1 < m",
      "reference_module": "Amort.NumberTheory.ModExp",
      "headline_theorems": [
        "Amort.NumberTheory.modExp_correct",
        "Amort.NumberTheory.modExpWithCount_fst",
        "Amort.NumberTheory.modExpWithCount_snd_le",
        "Amort.NumberTheory.isBigO_modExpWithCount_snd_size"
      ],
      "chapter_path": "tutorial/mod_exp.md",
      "exercises": {
        "predict": [
          {
            "id": "modexp_pred_1",
            "prompt": "What does `#eval modExp 3 13 100` evaluate to?",
            "input_type": "number",
            "expected_answer": "23",
            "explanation": "3^13 mod 100: 3^1=3, 3^2=9, 3^4=81, 3^8=6561 ≡ 61. 3^13 = 3^8 * 3^4 * 3^1 ≡ 61 * 81 * 3 ≡ 41 * 3 = 123 ≡ 23 (mod 100)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "modexp_fake_1",
            "prompt": "Which theorem statement correctly formulates the correctness of modular exponentiation with necessary modulus hypotheses?",
            "options": [
              {
                "id": "a",
                "text": "theorem modExp_correct (b e m : ℕ) (h : 1 < m) : modExp b e m = (b ^ e) % m",
                "is_fake": false,
                "explanation": "Genuine: Correctly requires 1 < m to rule out modulus 0 and modulus 1 edge cases, establishing exact equality to (b ^ e) % m."
              },
              {
                "id": "b",
                "text": "theorem modExp_correct_unbounded (b e m : ℕ) : modExp b e m = (b ^ e) % m",
                "is_fake": true,
                "explanation": "Fake: Without 1 < m, if m = 0 then (b ^ e) % 0 = b ^ e in Lean while modular reduction fails, or m = 1 gives non-conforming edge behavior."
              },
              {
                "id": "c",
                "text": "theorem modExp_sound (b e m : ℕ) : modExp b e m ≤ m",
                "is_fake": true,
                "explanation": "Weak: Only bounds the value magnitude, proving nothing about whether the computed exponentiation is correct."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "Modular arithmetic correctness requires explicit non-trivial modulus hypotheses (1 < m) to prevent division/modulo by zero or trivial equivalence."
          }
        ]
      }
    },
    {
      "id": "INS",
      "name": "Insertion Sort",
      "tier": 2,
      "category": "sorting",
      "status": "ready",
      "prerequisites": ["BGCD"],
      "unlocks": ["MERGE", "NAIVE"],
      "algorithm_skill": "The sorting spec: sorted and a permutation",
      "lean_skill": "List, List.Perm (~), List.Pairwise; why sorted alone is a fake spec",
      "reference_module": "Amort.Sorting.InsertionSort",
      "headline_theorems": [
        "List.insertionSortWithCount_fst",
        "List.insertionSortWithCount_perm",
        "List.insertionSortWithCount_fst_sorted",
        "List.insertionSortWithCount_snd_le_triangular",
        "List.insertionSortWithCount_snd_le_sq",
        "List.isBigO_insertionSortWithCount_snd_atTop"
      ],
      "chapter_path": "tutorial/insertion_sort.md",
      "exercises": {
        "predict": [
          {
            "id": "ins_pred_1",
            "prompt": "Given input list `[4, 2, 7, 1]`, what does `#eval (insertionSortWithCount [4, 2, 7, 1]).1` evaluate to?",
            "input_type": "text",
            "expected_answer": "[1, 2, 4, 7]",
            "explanation": "Insertion sort sorts elements in ascending order, returning the sorted permutation [1, 2, 4, 7]."
          }
        ],
        "spot_the_fake": [
          {
            "id": "ins_fake_1",
            "prompt": "Which specification genuinely proves that a sorting function sorts the input list rather than producing a trivial output?",
            "options": [
              {
                "id": "a",
                "text": "theorem sort_correct (xs : List ℕ) : (sort xs).Pairwise (· ≤ ·)",
                "is_fake": true,
                "explanation": "Fake: A function returning [] or [0, 0, 0] satisfies Pairwise (· ≤ ·), completely losing the input elements."
              },
              {
                "id": "b",
                "text": "theorem sort_correct (xs : List ℕ) : (sort xs).length = xs.length ∧ (sort xs).Pairwise (· ≤ ·)",
                "is_fake": true,
                "explanation": "Fake: A function returning [0, 0, 0, 0] for any 4-element list satisfies length equality and sortedness, but destroys input values."
              },
              {
                "id": "c",
                "text": "theorem sort_correct (xs : List ℕ) : (sort xs).Perm xs ∧ (sort xs).Pairwise (· ≤ ·)",
                "is_fake": false,
                "explanation": "Genuine: Both conditions are required: Perm xs guarantees conservation of elements and multiplicities, and Pairwise (· ≤ ·) guarantees ordering."
              }
            ],
            "correct_option_id": "c",
            "summary_explanation": "A genuine sorting spec must demand BOTH sortedness (Pairwise (· ≤ ·)) and element conservation via multiset permutation (Perm xs)."
          }
        ]
      }
    },
    {
      "id": "BS",
      "name": "Binary Search",
      "tier": 2,
      "category": "sorting",
      "status": "ready",
      "prerequisites": ["BGCD"],
      "unlocks": ["MERGE"],
      "algorithm_skill": "Invariants on sorted input; returning an index",
      "lean_skill": "Option, xs[i]?, preconditions as hypotheses (xs.Pairwise (· ≤ ·) →), ↔ statements",
      "reference_module": "Amort.Recurrence.BinarySearch",
      "headline_theorems": [
        "Amort.Recurrence.binarySearch_some_get",
        "Amort.Recurrence.binarySearch_isSome_iff",
        "Amort.Recurrence.binarySearchWithCount_fst",
        "Amort.Recurrence.binarySearchWithCount_snd_le_steps",
        "Amort.Recurrence.binarySearchWithCount_snd_le_size",
        "Amort.Recurrence.binarySearchArray_isSome_iff",
        "Amort.Recurrence.binarySearchArrayWithCount_fst",
        "Amort.Recurrence.binarySearchArrayWithCount_snd_le_size",
        "Amort.Recurrence.binarySearchSteps_isBigO_size"
      ],
      "chapter_path": "tutorial/binary_search.md",
      "exercises": {
        "predict": [
          {
            "id": "bs_pred_1",
            "prompt": "Searching for element 7 in sorted array `#[1, 3, 5, 7, 9, 11]`, what 0-based index does `binarySearch` return?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "7 is located at index 3 in #[1, 3, 5, 7, 9, 11] (0-indexed: 0->1, 1->3, 2->5, 3->7)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "bs_fake_1",
            "prompt": "Which theorem statement genuinely specifies binary search without introducing invalid assumptions?",
            "options": [
              {
                "id": "a",
                "text": "theorem binarySearch_spec (xs : List ℕ) (target : ℕ) (h : xs.Pairwise (· ≤ ·)) : (binarySearch xs target).isSome ↔ target ∈ xs",
                "is_fake": false,
                "explanation": "Genuine: Requires the essential sorted precondition xs.Pairwise (· ≤ ·) and provides a two-way (↔) equivalence between finding an index and element membership."
              },
              {
                "id": "b",
                "text": "theorem binarySearch_unsorted (xs : List ℕ) (target : ℕ) : (binarySearch xs target).isSome ↔ target ∈ xs",
                "is_fake": true,
                "explanation": "Fake: Binary search fails on unsorted lists; claiming equivalence without the sorted precondition is mathematically false."
              },
              {
                "id": "c",
                "text": "theorem binarySearch_sound (xs : List ℕ) (target : ℕ) : (binarySearch xs target).isSome → True",
                "is_fake": true,
                "explanation": "Tautological: P → True provides zero guarantees about search results."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "Binary search correctness critically relies on the input being sorted (xs.Pairwise (· ≤ ·)); omitting this precondition is unsound."
          }
        ]
      }
    },
    {
      "id": "DYN",
      "name": "Dynamic Array (amortized)",
      "tier": 2,
      "category": "amortization",
      "status": "ready",
      "prerequisites": ["BGCD"],
      "unlocks": ["TSQ", "HEAP"],
      "algorithm_skill": "Amortized analysis with a potential function",
      "lean_skill": "structure, integer potentials, total cost of k operations ≤ 3k",
      "reference_module": "Amort.DataStructure.DynamicArray",
      "headline_theorems": [
        "Amort.DataStructure.pushSeqCost_telescope_initOne",
        "Amort.DataStructure.pushSeqCost_initOne_le"
      ],
      "chapter_path": "tutorial/dynamic_array.md",
      "exercises": {
        "predict": [
          {
            "id": "dyn_pred_1",
            "prompt": "Under the potential function Φ = 2 * size - capacity (with initial capacity 1, initial size 0), what is the amortized cost bound per push operation?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "Each push has amortized cost 3: 1 for the actual write, and 2 saved into the potential to pay for the future doubling reallocation."
          }
        ],
        "spot_the_fake": [
          {
            "id": "dyn_fake_1",
            "prompt": "Which formulation correctly establishes an amortized time bound over a sequence of operations?",
            "options": [
              {
                "id": "a",
                "text": "theorem push_worst_case_constant (arr : DynamicArray) (x : ℕ) : actualCost (push arr x) ≤ 3",
                "is_fake": true,
                "explanation": "Fake: A single push triggering reallocation takes O(n) actual time to copy elements, so worst-case single operation cost is not bounded by 3."
              },
              {
                "id": "b",
                "text": "theorem pushSeqCost_initOne_le (k : ℕ) : totalActualCost (pushSequence k) ≤ 3 * k",
                "is_fake": false,
                "explanation": "Genuine: Amortization bounds the aggregate actual cost over all k operations by 3k, accounting for occasional expensive reallocation bursts."
              },
              {
                "id": "c",
                "text": "def amortizedBound (k : ℕ) := 3 * k\ntheorem amortized_bound_le (k : ℕ) : amortizedBound k ≤ 3 * k",
                "is_fake": true,
                "explanation": "Fake: Tautological definition of bound without coupling to the sequence of array operations."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Amortized complexity does not mean every individual operation is cheap; it proves that the sum of actual costs over any sequence of k operations is bounded linearly (total ≤ 3k)."
          }
        ]
      }
    },
    {
      "id": "EXT",
      "name": "Extended Euclid & Bézout",
      "tier": 3,
      "category": "arithmetic",
      "status": "ready",
      "prerequisites": ["EUC"],
      "unlocks": [],
      "algorithm_skill": "Certificates (Bézout coefficients)",
      "lean_skill": "ℤ vs ℕ, casts, results as tuples",
      "reference_module": "Amort.NumberTheory.ExtendedGCD",
      "headline_theorems": [
        "Amort.NumberTheory.extGCD_bezout",
        "Amort.NumberTheory.extGCD_gcd"
      ],
      "chapter_path": "tutorial/extended_gcd.md",
      "exercises": {
        "predict": [
          {
            "id": "ext_pred_1",
            "prompt": "For integers a = 35 and b = 15, Nat.gcd 35 15 = 5. What value of x satisfies 35 * x + 15 * y = 5 when y = -2?",
            "input_type": "number",
            "expected_answer": "1",
            "explanation": "35*(1) + 15*(-2) = 35 - 30 = 5 = Nat.gcd 35 15."
          }
        ],
        "spot_the_fake": [
          {
            "id": "ext_fake_1",
            "prompt": "Which type signature correctly captures Bézout's identity for Extended GCD?",
            "options": [
              {
                "id": "a",
                "text": "theorem extGCD_bezout (a b : ℕ) : ∃ x y : ℕ, (a : ℤ) * x + (b : ℤ) * y = Nat.gcd a b",
                "is_fake": true,
                "explanation": "Fake: Natural coefficients cannot solve a*x + b*y = gcd(a, b) when a, b > gcd(a, b) since both terms would be strictly positive."
              },
              {
                "id": "b",
                "text": "theorem extGCD_bezout (a b : ℕ) : let (g, x, y) := extGCD a b; (a : ℤ) * x + (b : ℤ) * y = g ∧ g = Nat.gcd a b",
                "is_fake": false,
                "explanation": "Genuine: Coefficients x and y must be signed integers (ℤ), and the certificate explicitly verifies that the linear combination equals the gcd."
              },
              {
                "id": "c",
                "text": "theorem extGCD_spec (a b : ℕ) : (extGCD a b).1 ∣ a ∧ (extGCD a b).1 ∣ b",
                "is_fake": true,
                "explanation": "Incomplete: Common divisor property does not prove Bézout certificate identity."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Bézout coefficients must be signed integers (ℤ) because one coefficient is necessarily non-positive when both inputs are positive."
          }
        ]
      }
    },
    {
      "id": "MERGE",
      "name": "Merge Sort",
      "tier": 3,
      "category": "sorting",
      "status": "ready",
      "prerequisites": ["INS", "BS"],
      "unlocks": ["LB", "QS", "INTV"],
      "algorithm_skill": "Divide and conquer; the T(n) = 2T(n/2) + n recurrence",
      "lean_skill": "Recurrences as statements; n * Nat.size n as n log n",
      "reference_module": "Amort.Sorting.MergeSort",
      "headline_theorems": [
        "List.mergeSortWithCount_fst",
        "List.mergeSortWithCount_perm",
        "List.mergeSortWithCount_fst_sorted",
        "List.mergeSortWithCount_snd_le_mul_size",
        "List.isBigO_mergeSortWithCount_snd_atTop"
      ],
      "chapter_path": "tutorial/merge_sort.md",
      "exercises": {
        "predict": [
          {
            "id": "merge_pred_1",
            "prompt": "What is the maximum number of comparisons needed to merge two sorted lists of lengths 4 and 4 in the worst case?",
            "input_type": "number",
            "expected_answer": "7",
            "explanation": "Merging two sorted lists of length m and n takes at most m + n - 1 comparisons. For 4 and 4: 4 + 4 - 1 = 7."
          }
        ],
        "spot_the_fake": [
          {
            "id": "merge_fake_1",
            "prompt": "Which recurrence bound correctly captures the asymptotic complexity of Merge Sort in Lean?",
            "options": [
              {
                "id": "a",
                "text": "theorem mergeSort_snd_le_linear (xs : List α) : (mergeSortWithCount xs).2 ≤ xs.length",
                "is_fake": true,
                "explanation": "Fake: Comparison sorting cannot run in O(n) worst case; merge sort performs n log n comparisons."
              },
              {
                "id": "b",
                "text": "theorem mergeSortWithCount_snd_le_mul_size (xs : List α) : (mergeSortWithCount xs).2 ≤ xs.length * Nat.size xs.length",
                "is_fake": false,
                "explanation": "Genuine: Correctly bounds comparison count by n * Nat.size n, where Nat.size n represents ⌈log₂(n+1)⌉ (bit length)."
              },
              {
                "id": "c",
                "text": "def sortTime (n : ℕ) := n * Nat.size n\ntheorem sortTime_bound (n : ℕ) : sortTime n ≤ n * Nat.size n",
                "is_fake": true,
                "explanation": "Fake: Decoupled tautology about a helper function rather than the execution of mergeSortWithCount."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "In Lean, n log n comparison bounds are formalized via n * Nat.size n directly coupled to the second component of the instrumented algorithm tuple."
          }
        ]
      }
    },
    {
      "id": "TSQ",
      "name": "Two-Stack Queue",
      "tier": 3,
      "category": "amortization",
      "status": "ready",
      "prerequisites": ["DYN"],
      "unlocks": ["KMP", "BFS"],
      "algorithm_skill": "Amortized cost over operation sequences",
      "lean_skill": "Specifying behaviour via an abstract model (toList)",
      "reference_module": "Amort.DataStructure.TwoStackQueue",
      "headline_theorems": [
        "Amort.DataStructure.TwoStackQueue.pop_fst",
        "Amort.DataStructure.TwoStackQueue.pop_snd_toList",
        "Amort.DataStructure.TwoStackQueue.pop_spec",
        "Amort.DataStructure.totalActualCost_le_three_mul"
      ],
      "chapter_path": "tutorial/two_stack_queue.md",
      "exercises": {
        "predict": [
          {
            "id": "tsq_pred_1",
            "prompt": "After enqueuing elements 10, 20, 30 into an empty TwoStackQueue and calling pop, what element is dequeued?",
            "input_type": "number",
            "expected_answer": "10",
            "explanation": "A queue maintains First-In-First-Out (FIFO) semantics, so the first enqueued element (10) is the first dequeued."
          }
        ],
        "spot_the_fake": [
          {
            "id": "tsq_fake_1",
            "prompt": "Which specification correctly defines FIFO correctness for a Two-Stack Queue?",
            "options": [
              {
                "id": "a",
                "text": "theorem pop_spec (q : TwoStackQueue α) : (q.pop).1.isSome ↔ q.toList ≠ []",
                "is_fake": true,
                "explanation": "Incomplete: Only checks if an element can be popped, not which element is returned or what state remains."
              },
              {
                "id": "b",
                "text": "theorem pop_spec (q : TwoStackQueue α) : match q.pop with | (none, q') => q.toList = [] ∧ q'.toList = [] | (some x, q') => q.toList = x :: q'.toList",
                "is_fake": false,
                "explanation": "Genuine: Ties the queue state to an abstract List model (q.toList), asserting that popping removes precisely the head element in FIFO order."
              },
              {
                "id": "c",
                "text": "theorem pop_size_decrease (q : TwoStackQueue α) : (q.pop).2.size = q.size - 1",
                "is_fake": true,
                "explanation": "Incomplete: Size reduction does not guarantee FIFO ordering (a stack also decreases in size)."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Data structure correctness is best proved against an abstract model: mapping queue states to List α via toList and showing pop extracts the head element."
          }
        ]
      }
    },
    {
      "id": "NAIVE",
      "name": "Naive String Matching",
      "tier": 3,
      "category": "strings",
      "status": "ready",
      "prerequisites": ["INS"],
      "unlocks": ["KMP", "LCS"],
      "algorithm_skill": "Specifying a search problem",
      "lean_skill": "Specs as Prop (IsSubstringAt); sound and complete as one ↔",
      "reference_module": "Amort.String.NaiveMatch",
      "headline_theorems": [
        "Amort.String.mem_naiveMatch_iff",
        "Amort.String.naiveMatchCount_le_mul"
      ],
      "chapter_path": "tutorial/naive_string_matching.md",
      "exercises": {
        "predict": [
          {
            "id": "naive_pred_1",
            "prompt": "How many matches does naive string search find for pattern 'ab' in text 'abacaba'?",
            "input_type": "number",
            "expected_answer": "2",
            "explanation": "'ab' occurs at index 0 ('ab'acaba) and index 4 (abac'ab'a)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "naive_fake_1",
            "prompt": "Which theorem statement specifies exact correctness (soundness and completeness) for string pattern matching?",
            "options": [
              {
                "id": "a",
                "text": "theorem match_sound (pat text : List Char) (i : ℕ) : i ∈ naiveMatch pat text → IsSubstringAt pat text i",
                "is_fake": true,
                "explanation": "Incomplete: Soundness alone allows an algorithm that always returns [] (finding nothing) without ever being wrong."
              },
              {
                "id": "b",
                "text": "theorem mem_naiveMatch_iff (pat text : List Char) (i : ℕ) : i ∈ naiveMatch pat text ↔ IsSubstringAt pat text i",
                "is_fake": false,
                "explanation": "Genuine: An if-and-only-if (↔) specification guarantees both soundness (no false positives) and completeness (no missed matches)."
              },
              {
                "id": "c",
                "text": "theorem match_count_bound (pat text : List Char) : (naiveMatch pat text).length ≤ text.length",
                "is_fake": true,
                "explanation": "Weak: Only bounds the number of matches without ensuring that matches correspond to actual occurrences."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "A search algorithm specification must be bidirectional (↔) so that it guarantees finding all true matches and nothing else."
          }
        ]
      }
    },
    {
      "id": "HEAP",
      "name": "Binary Heap / Heapsort",
      "tier": 3,
      "category": "amortization",
      "status": "planned",
      "prerequisites": ["DYN"],
      "unlocks": ["DIJ"],
      "algorithm_skill": "Priority queue invariant, sift-down, heapsort",
      "lean_skill": "Tree invariants on flat arrays, inductive heap property",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/binary_heap.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    },
    {
      "id": "LB",
      "name": "Sorting Lower Bound Ω(n log n)",
      "tier": 4,
      "category": "sorting",
      "status": "ready",
      "prerequisites": ["MERGE"],
      "unlocks": ["RED"],
      "algorithm_skill": "Proving no algorithm can do better",
      "lean_skill": "Inductive trees, Equiv.Perm, factorial; first IsBigO/IsTheta",
      "reference_module": "Amort.Sorting.DecisionTree",
      "headline_theorems": [
        "Amort.Sorting.DecisionTree.leafCount_le_two_pow_depth",
        "Amort.Sorting.factorial_le_leafCount",
        "Amort.Sorting.isTheta_factorial_n_log_n"
      ],
      "chapter_path": "tutorial/sorting_lower_bound.md",
      "exercises": {
        "predict": [
          {
            "id": "lb_pred_1",
            "prompt": "For 3 distinct items, there are 3! = 6 permutations. What is the minimum depth of a binary decision tree that can distinguish all 6 permutations?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "A tree of depth d has at most 2^d leaves. 2^2 = 4 < 6, so depth 2 cannot distinguish 6 outcomes. 2^3 = 8 ≥ 6, so depth at least 3 is required."
          }
        ],
        "spot_the_fake": [
          {
            "id": "lb_fake_1",
            "prompt": "Which mathematical chain establishes the comparison-based sorting lower bound Ω(n log n)?",
            "options": [
              {
                "id": "a",
                "text": "theorem sorting_lower_bound : leafCount ≤ 2^depth ∧ factorial n ≤ leafCount → n * Nat.size n ≤ depth",
                "is_fake": false,
                "explanation": "Genuine: Connects the binary decision tree leaf bound (leafCount ≤ 2^depth) to input permutations (n! ≤ leafCount), deducing depth ≥ log₂(n!) = Ω(n log n)."
              },
              {
                "id": "b",
                "text": "theorem linear_sorting_exists : ∃ (algo : List ℕ → List ℕ), (algo xs).Perm xs ∧ (algo xs).Pairwise (· ≤ ·) ∧ cost ≤ xs.length",
                "is_fake": true,
                "explanation": "Fake: Violates the information-theoretic lower bound for comparison sorting."
              },
              {
                "id": "c",
                "text": "theorem lower_bound_tautology (n : ℕ) : n * Nat.size n = n * Nat.size n",
                "is_fake": true,
                "explanation": "Fake: Meaningless tautology."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "Lower bounds are established by proving that every comparison decision tree for n items must have at least n! leaves, forcing depth ≥ ⌈log₂(n!)⌉ = Ω(n log n)."
          }
        ]
      }
    },
    {
      "id": "QS",
      "name": "Quicksort (worst case)",
      "tier": 4,
      "category": "sorting",
      "status": "ready",
      "prerequisites": ["MERGE"],
      "unlocks": [],
      "algorithm_skill": "Worst case, and showing a bound is tight",
      "lean_skill": "Worst-case attainment theorems (= n(n−1)/2 on a specific input)",
      "reference_module": "Amort.Sorting.Quicksort",
      "headline_theorems": [
        "Amort.Sorting.quicksort_perm",
        "Amort.Sorting.quicksort_sorted",
        "Amort.Sorting.quicksortWithCount_fst",
        "Amort.Sorting.quicksortWithCount_snd_le_mul",
        "Amort.Sorting.quicksortWithCount_replicate_eq_mul",
        "Amort.Sorting.isBigO_quicksortWithCount_snd_sq"
      ],
      "chapter_path": "tutorial/quicksort.md",
      "exercises": {
        "predict": [
          {
            "id": "qs_pred_1",
            "prompt": "When Quicksort with first-element pivot is run on an already sorted 4-element list [1, 2, 3, 4], how many element comparisons are performed?",
            "input_type": "number",
            "expected_answer": "6",
            "explanation": "Unbalanced partitions yield comparisons (4-1) + (3-1) + (2-1) = 3 + 2 + 1 = 6 = n*(n-1)/2."
          }
        ],
        "spot_the_fake": [
          {
            "id": "qs_fake_1",
            "prompt": "Which theorem proves that the O(n²) worst-case bound for Quicksort is mathematically tight?",
            "options": [
              {
                "id": "a",
                "text": "theorem quicksort_worst_case_upper (xs : List ℕ) : (quicksortWithCount xs).2 ≤ xs.length * xs.length",
                "is_fake": true,
                "explanation": "Incomplete: Upper bound proves cost is at most n², but does not prove n² is ever attained (tightness)."
              },
              {
                "id": "b",
                "text": "theorem quicksortWithCount_replicate_eq_mul (n : ℕ) (x : ℕ) : (quicksortWithCount (List.replicate n x)).2 = n * (n - 1) / 2",
                "is_fake": false,
                "explanation": "Genuine: Attainment theorem proving that on an identical/sorted list of length n, the comparison count equals exactly n(n-1)/2, establishing tightness."
              },
              {
                "id": "c",
                "text": "theorem quicksort_always_n_log_n (xs : List ℕ) : (quicksortWithCount xs).2 ≤ xs.length * Nat.size xs.length",
                "is_fake": true,
                "explanation": "Fake: Deterministic Quicksort is not O(n log n) in the worst case."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "A worst-case bound is tight only when accompanied by an attainment theorem demonstrating a concrete input family achieving the quadratic bound."
          }
        ]
      }
    },
    {
      "id": "INTV",
      "name": "Interval Scheduling (greedy)",
      "tier": 4,
      "category": "greedy",
      "status": "ready",
      "prerequisites": ["MERGE"],
      "unlocks": [],
      "algorithm_skill": "Greedy choice",
      "lean_skill": "Optimality statements: for every alternative solution S, S.length ≤ …",
      "reference_module": "Amort.Greedy.IntervalScheduling",
      "headline_theorems": [
        "Amort.Greedy.greedyIntervalSchedule_optimal",
        "Amort.Greedy.intervalSchedule_valid",
        "Amort.Greedy.intervalSchedule_optimal",
        "Amort.Greedy.intervalScheduleWithCount_fst",
        "Amort.Greedy.intervalScheduleWithCount_snd_le_mul",
        "Amort.Greedy.isBigO_intervalScheduleWithCount_snd_mul_size"
      ],
      "chapter_path": "tutorial/interval_scheduling.md",
      "exercises": {
        "predict": [
          {
            "id": "intv_pred_1",
            "prompt": "Given non-overlapping choices among intervals [1, 3], [2, 5], [3, 6], [5, 7], what is the maximum number of mutually compatible intervals?",
            "input_type": "number",
            "expected_answer": "2",
            "explanation": "Selecting [1, 3] and [5, 7] yields 2 compatible intervals, which is maximal for this set."
          }
        ],
        "spot_the_fake": [
          {
            "id": "intv_fake_1",
            "prompt": "Which theorem statement establishes that greedy interval scheduling produces a globally optimal solution?",
            "options": [
              {
                "id": "a",
                "text": "theorem greedy_valid (intervals : List Interval) : isValidSchedule (greedySchedule intervals)",
                "is_fake": true,
                "explanation": "Incomplete: Proves only that the greedy schedule is valid (no overlaps), not that it selects the maximum number of intervals."
              },
              {
                "id": "b",
                "text": "theorem greedyIntervalSchedule_optimal (intervals : List Interval) (other : List Interval) (h : isValidSchedule other) (h_sub : other ⊆ intervals) : other.length ≤ (greedySchedule intervals).length",
                "is_fake": false,
                "explanation": "Genuine: Universal optimality: for ANY valid schedule subset 'other', its length is at most the greedy schedule length."
              },
              {
                "id": "c",
                "text": "theorem greedy_heuristics (intervals : List Interval) : (greedySchedule intervals).length ≥ 1",
                "is_fake": true,
                "explanation": "Weak: Only guarantees at least one interval (and fails on empty input)."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Optimality theorems must be universally quantified over all possible valid alternative solutions S, proving |S| ≤ |S_greedy|."
          }
        ]
      }
    },
    {
      "id": "KMP",
      "name": "Knuth–Morris–Pratt",
      "tier": 4,
      "category": "strings",
      "status": "ready",
      "prerequisites": ["NAIVE", "TSQ"],
      "unlocks": ["Z", "AC"],
      "algorithm_skill": "The failure function; never re-reading the text",
      "lean_skill": "One function carrying both a correctness theorem and a linear-cost theorem",
      "reference_module": "Amort.String.KMP",
      "headline_theorems": [
        "Amort.String.computePiWithCount_fst",
        "Amort.String.computePi_getD",
        "Amort.String.computePiWithCount_snd_le",
        "Amort.String.mem_kmpMatch_iff",
        "Amort.String.kmpWithCount_fst",
        "Amort.String.kmpWithCount_snd_le",
        "Amort.String.kmpScan_bound",
        "Amort.String.kmpScan_le_two_mul",
        "Amort.String.isBigO_kmpWithCount_snd_list"
      ],
      "chapter_path": "tutorial/kmp.md",
      "exercises": {
        "predict": [
          {
            "id": "kmp_pred_1",
            "prompt": "For the pattern 'ABACABA', what is the length of the longest proper prefix that is also a suffix (i.e. the final entry of the pi table)?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "'ABA' is both a prefix and a suffix of 'ABACABA' (length 3)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "kmp_fake_1",
            "prompt": "Which formulation represents the genuine verified KMP theorem from proof_review.md rather than the auditing review fake?",
            "options": [
              {
                "id": "a",
                "text": "def kmpMatch (pat text : List Char) := naiveMatch pat text\ntheorem kmp_correct : kmpMatch pat text = naiveMatch pat text",
                "is_fake": true,
                "explanation": "The infamous review fake: Defines kmpMatch as an alias for naiveMatch! This compiles with 0 errors but proves nothing about KMP."
              },
              {
                "id": "b",
                "text": "theorem mem_kmpMatch_iff (pat text : List Char) (i : ℕ) : i ∈ kmpMatch pat text ↔ IsSubstringAt pat text i\ntheorem kmpScan_le_two_mul (pat text : List Char) : (kmpWithCount pat text).2 ≤ 2 * text.length",
                "is_fake": false,
                "explanation": "Genuine: Defines the authentic KMP state machine, proves equivalence to the substring spec, and bounds comparisons by 2 * text.length."
              },
              {
                "id": "c",
                "text": "theorem kmp_linear_steps : 4 * text.length ≤ 4 * text.length",
                "is_fake": true,
                "explanation": "The infamous review fake: A reflexive inequality on text length proving nothing about the algorithm."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Beware of definitions that secretly alias a simpler algorithm or bounds that reduce to trivialities (4n ≤ 4n); verified algorithms must prove authentic logic."
          }
        ]
      }
    },
    {
      "id": "LCS",
      "name": "Longest Common Subsequence",
      "tier": 4,
      "category": "dp",
      "status": "ready",
      "prerequisites": ["NAIVE"],
      "unlocks": ["ED", "KNAP"],
      "algorithm_skill": "Optimal substructure; memo tables",
      "lean_skill": "Optimisation specs: achievable and nothing better; table = recursion",
      "reference_module": "Amort.String.LCS",
      "headline_theorems": [
        "Amort.String.lcs_is_optimal",
        "Amort.String.lcsTable_eval",
        "Amort.String.lcsWithCount_fst",
        "Amort.String.lcsWithCount_snd_le",
        "Amort.String.isBigO_lcsWithCount_snd_list"
      ],
      "chapter_path": "tutorial/lcs.md",
      "exercises": {
        "predict": [
          {
            "id": "lcs_pred_1",
            "prompt": "What is the length of the Longest Common Subsequence of strings 'ABCBDAB' and 'BDCABA'?",
            "input_type": "number",
            "expected_answer": "4",
            "explanation": "Common subsequences of length 4 include 'BCBA', 'BDAB', 'BCAB'."
          }
        ],
        "spot_the_fake": [
          {
            "id": "lcs_fake_1",
            "prompt": "Which specification characterizes an optimal solution in dynamic programming for LCS?",
            "options": [
              {
                "id": "a",
                "text": "theorem lcs_achievable (xs ys : List α) : IsSubsequence (lcs xs ys) xs ∧ IsSubsequence (lcs xs ys) ys",
                "is_fake": true,
                "explanation": "Incomplete: Proves output is a common subsequence, but [] satisfies this without being longest."
              },
              {
                "id": "b",
                "text": "theorem lcs_is_optimal (xs ys : List α) : IsSubsequence (lcs xs ys) xs ∧ IsSubsequence (lcs xs ys) ys ∧ (∀ zs, IsSubsequence zs xs → IsSubsequence zs ys → zs.length ≤ (lcs xs ys).length)",
                "is_fake": false,
                "explanation": "Genuine: Establishes both feasibility (is common subsequence) and optimality (no other common subsequence is longer)."
              },
              {
                "id": "c",
                "text": "theorem lcs_table_symmetric (xs ys : List α) : lcsTable xs ys = lcsTable ys xs",
                "is_fake": true,
                "explanation": "Irrelevant: Symmetry of DP table does not prove optimality."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "DP optimization specifications require two parts: feasibility (solution satisfies constraints) and optimality (no valid candidate achieves a better objective value)."
          }
        ]
      }
    },
    {
      "id": "BFS",
      "name": "Breadth-First Search",
      "tier": 4,
      "category": "graphs",
      "status": "ready",
      "prerequisites": ["TSQ"],
      "unlocks": ["BF", "TWOSAT", "DSU"],
      "algorithm_skill": "Shortest paths in unweighted graphs",
      "lean_skill": "Graphs as adjacency functions, reachability; algorithm = spec (bfsWithCount … = bfsDist …)",
      "reference_module": "Amort.Graph.Traversal",
      "headline_theorems": [
        "Amort.Graph.handshaking_lemma",
        "Amort.Graph.bfsDist_eq_top_iff",
        "Amort.Graph.bfsDist_eq_coe_iff",
        "Amort.Graph.bfsDist_source",
        "Amort.Graph.bfsWork_le",
        "Amort.Graph.bfsLoop_fuel_invariant",
        "Amort.Graph.bfsWithCount_source",
        "Amort.Graph.bfsWithCount_walk",
        "Amort.Graph.bfsWithCount_fst_eq",
        "Amort.Graph.bfsWithCount_snd_le"
      ],
      "chapter_path": "tutorial/bfs.md",
      "exercises": {
        "predict": [
          {
            "id": "bfs_pred_1",
            "prompt": "In a 4-cycle graph (vertices 0, 1, 2, 3 with edges 0-1, 1-2, 2-3, 3-0), what is the BFS distance from vertex 0 to vertex 2?",
            "input_type": "number",
            "expected_answer": "2",
            "explanation": "Path 0 -> 1 -> 2 has length 2; path 0 -> 3 -> 2 has length 2."
          }
        ],
        "spot_the_fake": [
          {
            "id": "bfs_fake_1",
            "prompt": "Which specification prevents the 'all-zero distance' fake detected in the repository audit?",
            "options": [
              {
                "id": "a",
                "text": "def dist (u v : V) := 0\ntheorem dist_triangle (u v w : V) : dist u w ≤ dist u v + dist v w",
                "is_fake": true,
                "explanation": "The infamous review fake: The constant 0 function satisfies the triangle inequality (0 ≤ 0 + 0) but gives no shortest-path information!"
              },
              {
                "id": "b",
                "text": "theorem bfsWithCount_fst_eq (G : Graph) (src tgt : V) : (bfsWithCount G src tgt).1 = bfsDist G src tgt",
                "is_fake": false,
                "explanation": "Genuine: Directly equates the executable algorithm output to the graph-theoretic shortest walk infimum (bfsDist)."
              },
              {
                "id": "c",
                "text": "theorem bfs_visits_subset (G : Graph) (src : V) : (bfs G src).length ≤ G.vertexCount",
                "is_fake": true,
                "explanation": "Weak: Only bounds visited vertex count."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "A shortest-path spec must link the algorithm to the true graph distance metric (bfsDist) rather than loose inequalities that degenerate solutions satisfy."
          }
        ]
      }
    },
    {
      "id": "DIJ",
      "name": "Dijkstra",
      "tier": 4,
      "category": "graphs",
      "status": "planned",
      "prerequisites": ["HEAP"],
      "unlocks": [],
      "algorithm_skill": "Priority-first exploration, non-negative edge relaxation",
      "lean_skill": "Loop invariants with visited sets, priority queue interface contracts",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/dijkstra.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    },
    {
      "id": "ED",
      "name": "Edit Distance",
      "tier": 5,
      "category": "strings",
      "status": "ready",
      "prerequisites": ["LCS"],
      "unlocks": [],
      "algorithm_skill": "Alignments as explicit objects",
      "lean_skill": "Inductive predicates (IsAlignment)",
      "reference_module": "Amort.String.EditDistance",
      "headline_theorems": [
        "Amort.String.editDist_is_minimal_alignment",
        "Amort.String.editDistTable_eval",
        "Amort.String.editDistWithCount_fst",
        "Amort.String.editDistWithCount_snd_le",
        "Amort.String.isBigO_editDistWithCount_snd_list"
      ],
      "chapter_path": "tutorial/edit_distance.md",
      "exercises": {
        "predict": [
          {
            "id": "ed_pred_1",
            "prompt": "What is the edit distance (Levenshtein distance) between 'SNOWY' and 'SUNNY'?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "SNOWY -> SUNOWY (insert U) -> SUNNY (replace O with N) -> SUNNY (delete W): 3 edits."
          }
        ],
        "spot_the_fake": [
          {
            "id": "ed_fake_1",
            "prompt": "Which theorem statement accurately specifies minimum edit distance?",
            "options": [
              {
                "id": "a",
                "text": "theorem editDist_is_minimal_alignment (s t : List Char) : ∃ a : Alignment s t, a.cost = editDist s t ∧ ∀ a' : Alignment s t, a.cost ≤ a'.cost",
                "is_fake": false,
                "explanation": "Genuine: Formalizes alignments as an inductive predicate and proves editDist attains the minimum cost over all valid alignments."
              },
              {
                "id": "b",
                "text": "theorem editDist_hamming (s t : List Char) (h : s.length = t.length) : editDist s t = (List.zip s t).filter (fun (x, y) => x ≠ y).length",
                "is_fake": true,
                "explanation": "Fake: Conflates general edit distance (allowing insertions/deletions) with Hamming distance (substitutions only)."
              },
              {
                "id": "c",
                "text": "theorem editDist_le_length (s t : List Char) : editDist s t ≤ s.length + t.length",
                "is_fake": true,
                "explanation": "Weak: Upper bound only; does not establish minimality."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "Edit distance correctness requires proving that the DP value is achieved by a concrete alignment and that no valid alignment has lower cost."
          }
        ]
      }
    },
    {
      "id": "KNAP",
      "name": "0/1 Knapsack",
      "tier": 5,
      "category": "dp",
      "status": "ready",
      "prerequisites": ["LCS"],
      "unlocks": ["LIS"],
      "algorithm_skill": "Subset choice via DP",
      "lean_skill": "Finset, sums over subsets",
      "reference_module": "Amort.DP.Knapsack",
      "headline_theorems": [
        "Amort.DP.knapsack_is_optimal",
        "Amort.DP.knapsackRow_eval",
        "Amort.DP.knapsackWithCount_fst",
        "Amort.DP.knapsackWithCount_snd",
        "Amort.DP.knapsackWithCount_snd_le"
      ],
      "chapter_path": "tutorial/knapsack.md",
      "exercises": {
        "predict": [
          {
            "id": "knap_pred_1",
            "prompt": "Given knapsack capacity W = 7 and items (weight 3, val 4), (weight 4, val 5), (weight 2, val 3), what is the optimal 0/1 knapsack value?",
            "input_type": "number",
            "expected_answer": "9",
            "explanation": "Select items 2 (wt 4, val 5) and 1 (wt 3, val 4) -> total wt 7, total val 9."
          }
        ],
        "spot_the_fake": [
          {
            "id": "knap_fake_1",
            "prompt": "Which specification defines optimal 0/1 Knapsack over a finite set of items?",
            "options": [
              {
                "id": "a",
                "text": "theorem knapsack_greedy_optimal (items : List Item) (W : ℕ) : knapsack items W = greedyDensity items W",
                "is_fake": true,
                "explanation": "Fake: Greedy by value/weight density does not solve 0/1 knapsack optimally."
              },
              {
                "id": "b",
                "text": "theorem knapsack_is_optimal (items : List Item) (W : ℕ) : (knapsack items W).weight ≤ W ∧ ∀ S ⊆ items, S.weight ≤ W → S.value ≤ (knapsack items W).value",
                "is_fake": false,
                "explanation": "Genuine: Feasible weight within capacity W, and value at least as high as any candidate subset S satisfying the capacity constraint."
              },
              {
                "id": "c",
                "text": "theorem knapsack_positive (items : List Item) (W : ℕ) : knapsack items W ≥ 0",
                "is_fake": true,
                "explanation": "Trivial: Non-negativity holds for any natural number."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "0/1 Knapsack optimality must quantify over all valid subsets (S ⊆ items with S.weight ≤ W), proving none achieves higher value."
          }
        ]
      }
    },
    {
      "id": "BF",
      "name": "Bellman–Ford",
      "tier": 5,
      "category": "graphs",
      "status": "ready",
      "prerequisites": ["BFS"],
      "unlocks": [],
      "algorithm_skill": "Negative weights; detecting negative cycles",
      "lean_skill": "WithTop ℤ (∞ as ⊤); defining negative cycles independently of algorithm",
      "reference_module": "Amort.Graph.BellmanFord",
      "headline_theorems": [
        "Amort.Graph.bellmanFordWithCount_fst",
        "Amort.Graph.bellmanFordWithCount_snd",
        "Amort.Graph.bellmanFordWithCount_snd_le",
        "Amort.Graph.bellmanFord_le_path_weight",
        "Amort.Graph.bellmanFord_achieved",
        "Amort.Graph.bellmanFord_optimal",
        "Amort.Graph.hasNegCycleCheck_iff",
        "Amort.Graph.noNegCycle_not_hasReachableNegCycle",
        "Amort.Graph.hasReachableNegCycle_not_noNegCycle",
        "Amort.Graph.isBigO_bellmanFord_totalRelaxations_atTop"
      ],
      "chapter_path": "tutorial/bellman_ford.md",
      "exercises": {
        "predict": [
          {
            "id": "bf_pred_1",
            "prompt": "In a directed graph with 6 vertices, how many edge-relaxation rounds does Bellman-Ford run before checking for negative cycles?",
            "input_type": "number",
            "expected_answer": "5",
            "explanation": "Shortest simple paths contain at most |V| - 1 edges; for |V| = 6, 6 - 1 = 5 rounds are performed."
          }
        ],
        "spot_the_fake": [
          {
            "id": "bf_fake_1",
            "prompt": "Which theorem statement formulates negative cycle detection without circular self-definition?",
            "options": [
              {
                "id": "a",
                "text": "def hasNegCycle (G : Graph) := bellmanFordCheck G\ntheorem hasNegCycle_iff : hasNegCycle G ↔ bellmanFordCheck G",
                "is_fake": true,
                "explanation": "The infamous review fake: Defines 'negative cycle' as the algorithm's check itself! A bug in the check would simply redefine what a negative cycle is."
              },
              {
                "id": "b",
                "text": "theorem hasNegCycleCheck_iff (G : Graph) (src : V) : hasReachableNegCycle G src ↔ (bellmanFord G src).hasNegCycle = true",
                "is_fake": false,
                "explanation": "Genuine: Defines reachable negative cycles independently as a directed cycle of vertices whose edge weight sum is negative, and proves equivalence to the algorithm's check."
              },
              {
                "id": "c",
                "text": "theorem bellmanFord_steps (G : Graph) : stepCount ≤ G.vertexCount * G.edgeCount",
                "is_fake": true,
                "explanation": "Weak: Only bounds operational steps without addressing negative cycle detection correctness."
              }
            ],
            "correct_option_id": "b",
            "summary_explanation": "Never accept a specification where a mathematical property is defined as the algorithm that searches for it; properties must be defined independently."
          }
        ]
      }
    },
    {
      "id": "TWOSAT",
      "name": "2-SAT characterization",
      "tier": 5,
      "category": "complexity",
      "status": "ready",
      "prerequisites": ["BFS"],
      "unlocks": [],
      "algorithm_skill": "Implication graphs",
      "lean_skill": "Characterisation theorems (satisfiable ↔ graph property)",
      "reference_module": "Amort.Complexity.TwoSAT",
      "headline_theorems": [
        "Amort.Complexity.twoSAT_soundness_and_completeness"
      ],
      "chapter_path": "tutorial/two_sat.md",
      "exercises": {
        "predict": [
          {
            "id": "twosat_pred_1",
            "prompt": "In a 2-SAT implication graph, variable x and its negation ¬x belong to the same Strongly Connected Component (SCC). Is the 2-SAT formula satisfiable or unsatisfiable?",
            "input_type": "choice",
            "expected_answer": "unsatisfiable",
            "explanation": "If x ~> ¬x and ¬x ~> x, x implies its negation and vice versa, creating a contradiction (unsatisfiable)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "twosat_fake_1",
            "prompt": "Which characterization theorem correctly establishes the Aspvall, Plass & Tarjan criterion for 2-SAT?",
            "options": [
              {
                "id": "a",
                "text": "theorem twoSAT_soundness_and_completeness (φ : CNF2) : Satisfiable φ ↔ ∀ v, ¬(v ~> ¬v ∧ ¬v ~> v)",
                "is_fake": false,
                "explanation": "Genuine: A 2-SAT formula is satisfiable if and only if no variable lies in the same strongly connected component as its negation."
              },
              {
                "id": "b",
                "text": "theorem twoSAT_soundness_only (φ : CNF2) : Satisfiable φ → (∀ c ∈ φ, c.length = 2)",
                "is_fake": true,
                "explanation": "Irrelevant: Restates the syntactic definition of 2-CNF clauses."
              },
              {
                "id": "c",
                "text": "theorem twoSAT_linear_solve (φ : CNF3) : Satisfiable φ ↔ (solve2SAT φ = true)",
                "is_fake": true,
                "explanation": "Fake: Claims 3-SAT (NP-complete) can be solved by 2-SAT."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "2-SAT is characterized by graph connectivity: unsatisfiability occurs iff there is a mutual implication between a variable and its negation."
          }
        ]
      }
    },
    {
      "id": "RED",
      "name": "3-SAT → Independent Set",
      "tier": 5,
      "category": "complexity",
      "status": "ready",
      "prerequisites": ["LB"],
      "unlocks": [],
      "algorithm_skill": "Reductions between problems",
      "lean_skill": "A constructed object plus an ↔ connecting two problems",
      "reference_module": "Amort.Complexity.KarpReductions",
      "headline_theorems": [
        "Amort.Complexity.sat3_to_independentSet_correct"
      ],
      "chapter_path": "tutorial/karp_reductions.md",
      "exercises": {
        "predict": [
          {
            "id": "red_pred_1",
            "prompt": "In Karp's reduction from 3-SAT to Independent Set, a formula with 4 clauses produces a graph. To satisfy the formula, what size independent set must exist (k = number of clauses)?",
            "input_type": "number",
            "expected_answer": "4",
            "explanation": "One vertex is selected per clause gadget (no two from the same clause or contradictory literals), so k equals the number of clauses (4)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "red_fake_1",
            "prompt": "Which theorem statement genuinely proves a polynomial-time reduction from problem A to problem B?",
            "options": [
              {
                "id": "a",
                "text": "theorem reduction_correct (φ : 3SATInstance) : Satisfiable φ ↔ HasIndependentSet (reduceToGraph φ) φ.clauseCount",
                "is_fake": false,
                "explanation": "Genuine: Proves exact bidirectional equivalence between formula satisfiability and existence of an independent set of size k in the constructed gadget graph."
              },
              {
                "id": "b",
                "text": "theorem reduction_one_way (φ : 3SATInstance) : Satisfiable φ → HasIndependentSet (reduceToGraph φ) φ.clauseCount",
                "is_fake": true,
                "explanation": "Incomplete: One direction alone allows a reduction that always produces a graph with an independent set, failing on unsatisfiable formulas."
              },
              {
                "id": "c",
                "text": "theorem reduction_size_poly (φ : 3SATInstance) : (reduceToGraph φ).vertexCount ≤ 3 * φ.clauseCount",
                "is_fake": true,
                "explanation": "Incomplete: Size bound proves polynomial size gadget, but establishes zero connection to satisfiability."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "A reduction must prove bidirectional equivalence (A is YES ↔ B is YES); a one-way implication fails to preserve hardness."
          }
        ]
      }
    },
    {
      "id": "DSU",
      "name": "Union–Find",
      "tier": 5,
      "category": "amortization",
      "status": "planned",
      "prerequisites": ["BFS"],
      "unlocks": ["KRUS"],
      "algorithm_skill": "Disjoint set trees, path compression, union-by-rank",
      "lean_skill": "Equivalence relation invariants, partition modeling",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/union_find.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    },
    {
      "id": "Z",
      "name": "Z-Algorithm",
      "tier": 5,
      "category": "strings",
      "status": "planned",
      "prerequisites": ["KMP"],
      "unlocks": [],
      "algorithm_skill": "Z-box window maintenance, prefix matching in linear time",
      "lean_skill": "Window invariants, amortized right-boundary advancement",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/z_algorithm.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    },
    {
      "id": "AC",
      "name": "Aho–Corasick",
      "tier": 5,
      "category": "strings",
      "status": "planned",
      "prerequisites": ["KMP"],
      "unlocks": [],
      "algorithm_skill": "Multi-pattern automaton, dictionary matching with failure links",
      "lean_skill": "Trie traversal, state machine simulation proofs",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/aho_corasick.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    },
    {
      "id": "LIS",
      "name": "Longest Increasing Subsequence",
      "tier": 6,
      "category": "dp",
      "status": "ready",
      "prerequisites": ["KNAP"],
      "unlocks": [],
      "algorithm_skill": "DP over prefixes",
      "lean_skill": "Subsequences (List.Sublist)",
      "reference_module": "Amort.DP.LIS",
      "headline_theorems": [
        "Amort.DP.lis_is_optimal"
      ],
      "chapter_path": "tutorial/lis.md",
      "exercises": {
        "predict": [
          {
            "id": "lis_pred_1",
            "prompt": "For the list [3, 10, 2, 1, 20], what is the length of the Longest Increasing Subsequence?",
            "input_type": "number",
            "expected_answer": "3",
            "explanation": "The longest strictly increasing subsequence is [3, 10, 20] (length 3)."
          }
        ],
        "spot_the_fake": [
          {
            "id": "lis_fake_1",
            "prompt": "Which specification correctly defines the Longest Increasing Subsequence problem?",
            "options": [
              {
                "id": "a",
                "text": "theorem lis_is_optimal (xs : List ℕ) : (lis xs).Sublist xs ∧ (lis xs).Pairwise (· < ·) ∧ ∀ ys, ys.Sublist xs → ys.Pairwise (· < ·) → ys.length ≤ (lis xs).length",
                "is_fake": false,
                "explanation": "Genuine: Output is a valid sublist of xs, strictly increasing (Pairwise (· < ·)), and has length at least as large as any other strictly increasing sublist."
              },
              {
                "id": "b",
                "text": "theorem lis_contiguous (xs : List ℕ) : (lis xs).IsInfix xs ∧ (lis xs).Pairwise (· < ·)",
                "is_fake": true,
                "explanation": "Fake: Requires contiguous subarray (IsInfix) rather than general subsequence (Sublist)."
              },
              {
                "id": "c",
                "text": "theorem lis_sorted (xs : List ℕ) : (lis xs).Pairwise (· ≤ ·)",
                "is_fake": true,
                "explanation": "Fake: Non-decreasing is not strictly increasing, and permits trivial [] outputs."
              }
            ],
            "correct_option_id": "a",
            "summary_explanation": "LIS requires subsequence (Sublist, not Infix), strict inequality (Pairwise (· < ·)), and universal optimality over all competing sublists."
          }
        ]
      }
    },
    {
      "id": "KRUS",
      "name": "Kruskal MST",
      "tier": 6,
      "category": "graphs",
      "status": "planned",
      "prerequisites": ["DSU"],
      "unlocks": [],
      "algorithm_skill": "Minimum spanning tree, cut property, greedy cycle prevention",
      "lean_skill": "Matroid optimality, acyclicity predicates",
      "reference_module": null,
      "headline_theorems": [],
      "chapter_path": "tutorial/kruskal.md",
      "exercises": {
        "predict": [],
        "spot_the_fake": []
      }
    }
  ]
};
