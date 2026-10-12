/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Acyclicity from Quotient Resolution Classes

This textbook entry recalls the bounded-above and unbounded left-acyclicity criteria from the
shared ReasLib resolution-class API.
-/

/- Lemma 13.15.7: if every object is a quotient of a member of `P`, `P` is closed under
subobjects, and applying `F` preserves the indicated short exact sequences, then every member of
`P` is left acyclic for the unbounded derived functor of `F`. -/
@[stacks 05T9]
#check @CategoryTheory.Functor.LeftAcyclic.of_mem
