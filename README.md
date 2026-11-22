# Lean 4 Learning Portfolio

My notes and worked exercises from learning Lean 4 and Mathlib, from
functional programming basics up to proofs about rings, groups, sets and functions.

## Contents

| Directory | Source | What it covers |
|---|---|---|
| `Basic/chapter1/` | [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), ch. 1 | Evaluation, types, structures, datatypes and pattern matching, polymorphism |
| `Foundations/` | [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) | Simple type theory, types as objects |
| `MIL/` | [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | Calculating with `rw`, ring and group identities proved from the axioms, using lemmas for inequalities |
| `Lean_for_the_Curious_Mathematician/` | [LftCM](https://github.com/lftcm2023/lftcm2023) | Logic, sets, functions (injective / surjective / bijective) |
| `Imp/` | Mathematics in Lean | Reference sheet of the most important Mathlib lemmas, grouped by structure |
| `Lean.md`, `Leanqna.md` | Original | Notes on Lean from first principles, and 50 Lean 4 questions with answers |

## Selected proofs

- `MIL/Basics/ProvingIdentities.lean`: `mul_zero`, `zero_mul`, `mul_inv_cancel`, `mul_one` and
  `mul_inv_rev` for an arbitrary ring or group, derived from the axioms alone
  (no `simp` or `ring`), with each rewrite step explained.
- `Imp/Logic.lean`: `my_lemma`, if `|x| < ε` and `|y| < ε` with `ε ≤ 1` then `|x * y| < ε`,
  proved with a `calc` chain and `gcongr`.
- `Lean_for_the_Curious_Mathematician/Basics.lean`: infinitely many primes (`Euclid_Thm`).

## Status

The whole project builds against Mathlib with no errors. Some exercises are still
open and marked with `sorry`. Lean reports each one as a warning:

| File | Open exercises |
|---|---|
| `Lean_for_the_Curious_Mathematician/Sets.lean` | 15 |
| `Lean_for_the_Curious_Mathematician/Functions.lean` | 8 |
| `MIL/Basics/TheoremandLemma.lean` | 5 |
| `Lean_for_the_Curious_Mathematician/Basics.lean` | 3 |
| `MIL/Introduction/Overview.lean` | 1 (Fermat's Last Theorem, left as `sorry` on purpose) |

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`.

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```
