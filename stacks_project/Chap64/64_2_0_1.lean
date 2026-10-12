/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

/-!
# 64.2.0.1 (03SK): the preliminary trace formula

Source: `trace-equation-trace-formula-initial`,
`source/stacks-official-a04446e57ec1/tex/trace.tex`, lines 36–60.

For a finite type scheme X of dimension 1 over a finite field k, a prime ℓ,
and a constructible flat Z/ℓⁿZ-sheaf F, the source first displays

  ∑ x ∈ X(k), Tr(Frob | F_x̄) = ∑ i = 0,…,2, (-1)^i Tr(π_X* | H_c^i(X_k̄,F)).

The equality is intended to take values in Z/ℓⁿZ. This is a preliminary
description of the formula to be developed, explicitly qualified immediately
after the display: “this formulation is slightly wrong as stated.” The more
precise display `trace-equation-trace-formula-second` is likewise introduced as
“albeit a false one”; its explanation says that the trace on the right does not
make sense for the sheaves under consideration (trace.tex, lines 294–311).

The obstruction is not that every instance of the displayed equality is false.
Even a flat finite-coefficient sheaf can have nonflat individual cohomology
modules, on which the intended module trace is unavailable. Lines 466–483 give
the Z/ℓ²Z coinvariant example and explain the remedy: traces on the total perfect
derived cohomology complex. The later rigorous trace formula is a separate
statement, with its own objects and hypotheses.

This module preserves the preliminary display and its explicit source warning
as explanatory content; it asserts no equation or negation of the equation.
Source-coverage classification is separate from mathematical success.

Classification aliases for the same source entry:
`03SK::statement_repair::1`, `03SK::statement_repair::2`.
These identify repair episodes, not additional mathematical claims.
-/
