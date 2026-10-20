module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.14.9 (05S9)

“Everywhere defined” is the quantified strong source notion, not merely pointwise existence at
every object.  The weak Mathlib predicate is retained as a derived companion through the canonical
bridge instance.
-/

open CategoryTheory

/- Right-derived source-definedness at every source object. -/
@[stacks 05S9 "right everywhere-defined source notion"]
#check @CategoryTheory.Functor.RightDerived.EverywhereDefined

/- Left-derived source-definedness at every source object. -/
@[stacks 05S9 "left everywhere-defined source notion"]
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined

/- Explicit weak companions for clients which only need pointwise Kan-extension existence. -/
#check @CategoryTheory.Functor.RightDerived.EverywhereDefined.hasPointwise
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined.hasPointwise
