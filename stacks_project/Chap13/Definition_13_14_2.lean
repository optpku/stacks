/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.14.2 (05S9)

The Stacks notion of being defined at an object retains essential constancy of the
localization-indexed diagram.  The chapter therefore recalls the strong owners
`Functor.RightDerived.DefinedAt` and `Functor.LeftDerived.DefinedAt`; Mathlib's weaker pointwise
Kan-extension predicates are available only through the explicit one-way bridge.
-/

open CategoryTheory

/- Definition 13.14.2 (1): right-derived source-definedness at an object. -/
@[stacks 05S9 "(1)"] #check @CategoryTheory.Functor.RightDerived.DefinedAt

/- Definition 13.14.2 (2): left-derived source-definedness at an object. -/
@[stacks 05S9 "(2)"] #check @CategoryTheory.Functor.LeftDerived.DefinedAt

/- The pointwise-existence companions intentionally remain bridges, not the source definition. -/
#check @CategoryTheory.Functor.RightDerived.DefinedAt.hasPointwise
#check @CategoryTheory.Functor.LeftDerived.DefinedAt.hasPointwise
