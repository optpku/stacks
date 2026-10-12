/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 13.12.1 (`0152`): the derived localization DeltaFunctor is owned by the neutral
`DerivedCategory.DeltaFunctor` leaf.  The chapter entry is a labeled recall surface. -/
@[stacks 0152] #check
  @CategoryTheory.DerivedCategory.Delta.functor
@[stacks 0152] #check
  @CategoryTheory.DerivedCategory.Delta.functor_toFunctor
@[stacks 0152] #check
  @CategoryTheory.DerivedCategory.Delta.functor_δ
