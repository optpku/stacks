/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.11 (Tag 00Q8): the one-generator case of algebraic Zariski's Main Theorem.

@stack 00Q8
-/

@[stacks 00Q8 "finite type from a polynomial quotient"]
#check @Algebra.FiniteType.of_surjective

@[stacks 00Q8 "finite-type Zariski main owner"]
#check @Algebra.ZariskisMainProperty.of_finiteType
