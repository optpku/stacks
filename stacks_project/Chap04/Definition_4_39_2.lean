module

public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Definition 4.39.2: a category fibred in setoids is fibred in groupoids with thin standard
fibres, equivalently its projection is fibred in groupoids and faithful. -/
@[stacks 04SA]
#check (Functor.IsFibered.InSetoids p : Prop)

end CategoryTheory
