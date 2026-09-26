# Skill Tree Review — commit `78818cc` (web app, `tree.json`, pilot chapters)

**Reviewed:** 2026-09-25 against `main` at `5e91375`.
**Audience:** the agent fixing these items. The author will check the results.

> **Fixer:** work through §2 in order. Each item has a **Done when** check. Do not report an item
> as done without running its check and pasting the output into your handoff.

---

## 1. What was verified and is fine

- `lake build` succeeds (2147 jobs, including the new `Tutorial` library).
- `tutorial/tree.json` matches `SKILL_TREE_TUTORIAL_PLAN.md`: 28 nodes, root `BGCD`, 1 open,
  21 ready and 6 planned. All **107 headline theorems** it cites exist in Lean. This was checked by
  running `#check` on every name, not by text-matching `Audit.lean`. No planned node cites a theorem.
- `scripts/tree_tool.py --validate` and `--sync-mermaid --check` pass. `tests/test_tree_tool.py`
  (19), `tests/test_e2e_suite.py` (19) and `scripts/test_webapp_adversarial.py` (49) pass.
- All 23 **Predict** answers in `tree.json` are correct. The executable ones were confirmed with
  `#eval`; the rest were checked by hand.
- `tutorial/binary_gcd.md` follows the plan's five steps faithfully and is accurate, apart from
  the items below. Its "Spot the fake" examples are compiled in `Tutorial/BinaryGCD.lean`.

---

## 2. Required fixes

### 2.1 Chapters never load in the app (seen by the author) — highest priority
**Observed:** opening Binary GCD → *Tutorial Chapter* shows the **generated filler** ("In this
curriculum step, we explore the authentic algorithm without facades…") instead of the real
268-line `tutorial/binary_gcd.md`.
**Cause:** the app is served from `docs/`, and `loadChapter` fetches
`tutorial/binary_gcd.md` / `../tutorial/binary_gcd.md`. Both lie outside the site root when
`docs/` is the root (a local server started in `docs/`, `file://`, or GitHub Pages). The
fetch fails silently, and `generateFallbackChapterMarkdown` takes over.
**Fix:** make `docs/` self-contained. Add a build step (`scripts/tree_tool.py --build-site`) that
copies or bundles `tutorial/*.md` and `tree.json` into `docs/`, e.g. `docs/chapters/<id>.md`
plus a generated `docs/tree_data.js`. The app then loads only from paths inside `docs/`.
**Done when:** `cd docs && python3 -m http.server` → Binary GCD, Euclid and Insertion Sort each
show their real chapter (first heading equals the `.md` file's first heading), and a test asserts it.

### 2.2 Remove the filler chapter
A generated chapter that praises the node's rigour ("without facades or circular shortcuts") is
exactly the kind of unearned claim this tutorial teaches readers to distrust.
**Fix:** delete `generateFallbackChapterMarkdown`. For nodes with no chapter, show
*"Chapter coming soon"*, followed by the node's skills, prerequisites and headline theorems,
clearly labelled as data from `tree.json`. If a chapter exists but fails to load, show an
**error** rather than falling back.
**Done when:** `grep -n "facades\|generateFallbackChapterMarkdown" docs/app.js` prints nothing.

### 2.3 Chapter reading layout (seen by the author)
**Observed:** the chapter opens in a side panel covering about half the screen, with the tree
blurred behind it. Long-form reading is cramped, and the blurred node cards are illegible.
**Fix:**
- The chapter gets a **full-width reading view** (its own route, e.g. `#/node/BGCD/chapter`,
  with a max text width of about 75 characters, centred) and a "← Back to tree" link. The
  browser back button must work.
- The side panel stays as a quick *preview*: name, skills, prerequisites, unlocks, and an
  "Open chapter" button.
- Order the tabs by what a learner does: **Chapter** first, then **Exercises**. Rename
  "Homework Verifier" to "Exercises": it checks quiz answers, not homework, and "verifier"
  suggests Lean is involved.
**Done when:** a screenshot at 1440 px and one at 390 px (phone) are attached to the handoff,
showing the full-width chapter with no horizontal scrolling.

### 2.4 Cost model wording in the GCD chapters
`tutorial/binary_gcd.md` says each step is "an O(1) bit test, shift, or subtraction". That is
false for big numbers: subtracting or halving an n-bit number costs O(n) bit operations.
**Fix:** state exactly what is counted: *"We count **recursive calls**. Each call does one parity
test plus a halving and/or one subtraction, so the count is at most the number of input bits.
Measured in bit operations, each call costs O(n), giving O(n²) in total."* Apply the same
treatment to `tutorial/euclid_gcd.md`, where each call does one `%`. Do **not** describe the
counter as "the number of subtractions": halving-only calls do no subtraction.
**Done when:** `grep -n "O(1)" tutorial/*.md` returns only sentences that name the operation being
counted.

### 2.5 Wrong `#eval` output
`Tutorial/BinaryGCD.lean:53` says `#eval Nat.binaryGcdWithSteps 105 252  -- (21, 9)`, but
Lean prints `(21, 5)`.
**Fix:** correct it, and prevent recurrences. Replace hand-written `-- result` comments with
`#guard` (e.g. `#guard Nat.binaryGcdWithSteps 105 252 = (21, 5)`), which fails the build when wrong.
**Done when:** no `#eval … -- <value>` comments remain in `Tutorial/` or `tutorial/`; all
claimed outputs are `#guard`s, or `#eval`s whose output is quoted from an actual run.

### 2.6 Licence: switch to Apache 2.0
**Decision (author):** the project uses **Apache License 2.0**.
- Replace `LICENSE` with the **official, unmodified** text from
  <https://www.apache.org/licenses/LICENSE-2.0.txt>. Do not retype it or paraphrase it.
- Move the "not affiliated with the author's employer" disclaimer **out of** `LICENSE` and into
  `README.md`, which already has it. Extra text in `LICENSE` stops GitHub from detecting the licence.
- The 103 Lean headers already say "Released under Apache 2.0 license as described in the file
  LICENSE", so leave them. Make the copyright line consistent: headers say
  "Copyright (c) 2026 Amort Authors" while `LICENSE` said "tanaeem-moosa". Either add an `AUTHORS`
  file listing tanaeem-moosa, or use the same name everywhere.
- Update any README text that says MIT.
**Done when:** `git grep -il "MIT License"` prints nothing, GitHub shows "Apache-2.0" on the repo
page, and `head -3 LICENSE` shows the official Apache header.

### 2.7 One source of truth, generated copies
- `docs/tree_data.js` is a hand-made copy of `tree.json`. It is identical today, but nothing
  regenerates it. Generate it in the §2.1 build step.
- Chapters quote Lean that differs from the Lean files: `binary_gcd.md` shows
  `gcdCost … := by rfl`, while `Tutorial/BinaryGCD.lean` has `fakeCost … := le_refl _`. The plan (§6.2)
  requires chapters to quote statements verbatim. Either generate the Lean snippets in chapters
  from the `.lean` files, or add a check that every ```` ```lean ```` block in a chapter either
  appears verbatim in the companion file or is marked `-- (illustrative)`.
**Done when:** `tree_tool.py --check-site` fails if `docs/tree_data.js` or any quoted snippet is
out of date, and passes now.

### 2.8 CI
`.github/workflows/lean_action_ci.yml` only runs `lake build`. Add:
- `tree_tool.py --validate`, `--sync-mermaid --check` and `--check-site`;
- the Python tests (standardise on `python3 -m unittest`, since `pytest` is not installed here);
- a **Lean-based** theorem-existence check: generate `#check @<name>` for every headline theorem
  in `tree.json` and run it with `lake env lean` (replacing the text-match against `Audit.lean`);
- a GitHub Pages deploy workflow that publishes `docs/` after the build step.
**Done when:** a push to a branch runs all of these, and breaking any one of them fails CI.

---

## 3. Improvements (after §2)

1. **Hide answers until the reader commits.** In the markdown chapters, wrap "Spot the fake"
   verdicts and "State it yourself" solutions in `<details><summary>Show answer</summary>`.
   Currently the answer sits right under the question.
2. **Make "State it yourself" real.** Today it shows finished statements with proofs. Per plan §2.1,
   give the English claim first ("binary GCD is commutative"), ask the reader to write the Lean
   statement, then reveal the reference, with an `example : Yours ↔ Reference` check where possible.
3. **Unlock progression.** Mark a node complete when its exercises are answered correctly, and show
   newly unlocked nodes. Keep progress in `localStorage` only, with no accounts.
4. **Repo tidying.**
   - `.agents/` is git-ignored, but 11 agent log files were committed earlier. Run
     `git rm -r --cached .agents` (nothing sensitive was found, but they are noise in a public repo).
   - Move `TEST_INFRA.md` and `TEST_READY.md` out of the repo root (e.g. `docs-dev/` or
     `tests/README.md`), and put all tests in `tests/` (`scripts/test_webapp*.py` too).
5. **Next chapters.** After §2 lands, write the remaining pilot chapters from the plan's roadmap:
   Binary Search, Dynamic Array and Modular Exponentiation, in the same format as `binary_gcd.md`.
