/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import StacksCheckRecall

/-!
# Minimal-polynomial coefficients in a fraction field

@stack 00H7

Lemma 10.38.6 is the coefficientwise consequence of the canonical
minimal-polynomial identity over fraction fields recalled below.
-/

@[expose] public section

@[stacks 00H7]
#check @minpoly.isIntegrallyClosed_eq_field_fractions
