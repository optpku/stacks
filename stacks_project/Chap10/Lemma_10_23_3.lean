/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.23.3

@stack 00EP
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.23.3 (1): if a finite list of elements of `S` generates the unit ideal and each
principal localization `S_g` is of finite type over `R`, then `S` is of finite type over `R`.
This is exactly the canonical locality theorem
`Algebra.FiniteType.of_span_eq_top_target`. -/
@[stacks 00EP "(1), finite type"]
#check @Algebra.FiniteType.of_span_eq_top_target

/- Lemma 10.23.3 (2): if a finite list of elements of `S` generates the unit ideal and each
principal localization `S_g` is of finite presentation over `R`, then `S` is of finite
presentation over `R`. This is exactly the canonical locality theorem
`Algebra.FinitePresentation.of_span_eq_top_target`. -/
@[stacks 00EP "(2), finite presentation"]
#check @Algebra.FinitePresentation.of_span_eq_top_target
