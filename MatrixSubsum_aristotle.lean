/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HSMul (Matrix (Fin n) (Fin n) ℤ) (Fin n → ℤ) ?m.2159

Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSMul (Matrix (Fin n) (Fin n) ℤ) (Fin n → ℤ) ?m.9040

Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
structure DerivedSets {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v : (Fin n) → ℤ) (p q : Finset ℕ) where
  p': Finset ℕ
  q': Finset ℕ
  nontrivial: p' ≠ {}
  h_prime: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)
  supp_disj: Disjoint p' q'
  p'_derived: p' ⊆ p
  q'_derived: q' ⊆ q

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

function expected at
  DerivedSets
term has type
  ?m.1868-/
lemma poly_cancel {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v: (Fin n) → ℤ) (p q : Finset ℕ) (hpq: p = q) : Nonempty (DerivedSets A v p q) := by
  sorry