/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Definition 4.38.2: a category fibred in sets is a discrete fibration, expressed intrinsically
by existence and uniqueness of lifts with prescribed codomain. -/
@[stacks 0043]
#check (Functor.IsDiscreteFibration p : Prop)

end CategoryTheory
