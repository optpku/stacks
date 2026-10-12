/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u)

/-
Remark 4.2.2 is a metamathematical size convention: ordinarily the objects of a category form a
set, while a stated whitelist—sets, algebraic structures, spaces, schemes, (pre)sheaves, and
functor categories—is allowed to have a proper class of objects.

Lean represents every object collection by some `Type u`; using a larger `u` replaces the
set/proper-class distinction. In particular, mathlib's `SmallCategory C` means that the object and
morphism universes of `C` coincide, while `LargeCategory C` means that the object universe is one
level above the morphism universe. Neither abbreviation expresses the Stacks whitelist. The
predicates `Small.{w} C` and `EssentiallySmall.{w} C` are closer size APIs, but they are relative
to an explicitly chosen universe `w`, which this remark does not supply.

Consequently there is no source-faithful proposition or class to introduce here. The canonical
Lean replacement is simply the universe-polymorphic category structure below; the listed examples
retain their ordinary library owners and need no item-specific wrappers or `LargeCategory`
assertions.
-/
@[stacks 0015 "set/class convention represented by universe-polymorphic categories"]
#check (Category.{v} C : Type max u (v + 1))

end CategoryTheory
