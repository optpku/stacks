/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.Equalizer
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D]
variable {A B C : D} {f : A ⟶ B} {g₁ g₂ : B ⟶ C} {h : f ≫ g₁ = f ≫ g₂}

/- 35.4.1.1: the diagram `A ⟶ B ⇉ C` is an equalizer when the fork determined by
`f` and its equalizing equation `h` is limiting. -/
@[stacks 08WG] #check (CategoryTheory.Limits.IsEqualizer f g₁ g₂ h : Prop)

end CategoryTheory.Limits
