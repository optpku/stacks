/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.Symmetric.FiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Elementary Symmetric Polynomials

The canonical map and finite-free owner live in ReasLib.  This file records the textbook
`Fin n`/`ℤ` specialization without importing the proof-only successor and AdjoinRoot plumbing.

@stack 00SR
-/

universe u

/- Example 10.136.8, tag `00SR`: the elementary-symmetric extension of the integer polynomial ring
in `n` coefficient variables to the polynomial ring in `n` root variables is finite free. -/
@[stacks 00SR]
#check MvPolynomial.ElementarySymmetric.finiteFreeFin ℤ

#check @MvPolynomial.ElementarySymmetric.algHomFin
#check @MvPolynomial.ElementarySymmetric.algHom_apply_X
#check @MvPolynomial.ElementarySymmetric.finiteFree
