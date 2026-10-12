/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ConnectedComponents
public import ReasLib.CategoryTheory.Zigzag.Groupoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected components of a groupoid

The neutral zigzag criterion for a groupoid identifies the kernel of the connected-component
quotient with isomorphism of objects.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ConnectedComponents.mk

variable {J : Type u} [Category.{v} J] [IsGroupoid J]

/-- In a groupoid, two objects have the same connected-component class exactly when they are
isomorphic. -/
@[stacks 04SC "connected components of a groupoid"]
theorem eq_iff_isomorphic {X Y : J} :
    ConnectedComponents.mk X = ConnectedComponents.mk Y ↔
      IsIsomorphic X Y := sorry

end CategoryTheory.ConnectedComponents.mk
