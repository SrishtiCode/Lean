# Lean 4 Learning Portfolio

My worked solutions to Lean 4 / Mathlib exercises, plus a tactic reference.
All solutions are my own work on exercises from the sources credited below.
Everything compiles with no `sorry`.

![CI](https://github.com/SrishtiCode/Lean/actions/workflows/lean_action_ci.yml/badge.svg)

## Contents

| Directory | Source | What it covers |
|---|---|---|
| `MIL_Solutions/` | [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | Logic, sets, functions, algebra, analysis |
| `LftCM2023_Solutions/` | [LftCM 2023, Sets & Functions](https://github.com/lftcm2023/lftcm2023) | Injective/surjective functions, images and preimages |
| `Cheatsheet/` | Original | Tactics and key lemmas, with a worked example for each |
| `Foundations/` | Original notes | Type theory, types as objects |

## Selected proofs
- `LftCM2023_Solutions/...`: <e.g. "composition of injective functions is injective">
- `MIL_Solutions/...`: <e.g. "sqrt 2 is irrational">

## Skills demonstrated
Tactic proofs (`rw`, `simp`, `rcases`, `obtain`, `constructor`, `induction`,
`omega`, `linarith`, `aesop`), set and function reasoning, working with Mathlib.

## Build
    lake exe cache get && lake build
