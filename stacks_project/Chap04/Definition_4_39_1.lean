/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Groupoid.Thin
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [IsGroupoid C]

/- Definition 4.39.1 recalls that a setoid is a groupoid. -/
#check IsGroupoid

/- Definition 4.39.1 recalls that a setoid has at most one morphism between any two objects. -/
#check Quiver.IsThin

/- Definition 4.39.1: for a groupoid, thinness is equivalent to every object having only its
identity automorphism. -/
@[stacks 02XZ "groupoids with only identity automorphisms"]
#check (CategoryTheory.isThin_iff_subsingleton_aut (C := C) :
  Quiver.IsThin C ↔ ∀ X : C, Subsingleton (Aut X))

end CategoryTheory
