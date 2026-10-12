/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.IsConnected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zigzags in groupoids

In a groupoid, zigzag-connectedness and isomorphism are the same relation. This neutral fact is
independent of any quotient construction built from connected components.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Zigzag

variable {J : Type u} [Category.{v} J] [IsGroupoid J]

/-- In a groupoid, two objects are joined by a zigzag exactly when they are isomorphic. -/
@[stacks 04SC "zigzags in a groupoid"]
theorem iff_isomorphic {X Y : J} :
    CategoryTheory.Zigzag X Y ↔ IsIsomorphic X Y := sorry

end CategoryTheory.Zigzag
