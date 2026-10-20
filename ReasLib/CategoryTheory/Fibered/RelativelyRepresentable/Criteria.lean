module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Faithful
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.FiberPair
public import ReasLib.CategoryTheory.Fibered.Representable.Setoids

/-!
# Recognition criteria for relative representability

Relative representability forces representability of the fiberwise-iso-class presheaves of slice
base changes. Together with the faithfulness leaf and the converse fiber-pair criterion, this
gives both fiberwise and total-functor recognition statements.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids

namespace relativelyRepresentable

/-- A relatively representable morphism satisfies the source-facing fiber-pair presheaf
condition. -/
theorem onFiberPairs
    {F : X ⟶ Y} (hF : relativelyRepresentable F) :
    Hom.fiberPairClasses.representable F := sorry

/-- A relatively representable morphism has representable iso-class presheaf after every
canonical slice base change. -/
@[stacks 02Y7 "fiber-class consequence on slice base changes"]
theorem onSlices
    {F : X ⟶ Y} (hF : relativelyRepresentable F) :
    Hom.sliceFiberClasses.representable F := sorry

/-- Relative representability is equivalent to fiberwise faithfulness together with the
source-facing fiber-pair presheaf condition. -/
@[stacks 02Y8 "forward implication"]
theorem iffFiberwise
    (F : X ⟶ Y) :
    relativelyRepresentable F ↔
      (∀ U : C, (fiberFunctor F U).Faithful) ∧
        Hom.fiberPairClasses.representable F := sorry

/-- Relative representability is equivalent to faithfulness of the total based functor together
with representability of the iso-class presheaf after every canonical slice base change. -/
@[stacks 02Y8 "forward implication"]
theorem iffTotal
    (F : X ⟶ Y) :
    relativelyRepresentable F ↔
      (toBasedFunctor F).Faithful ∧
        Hom.sliceFiberClasses.representable F := sorry

end relativelyRepresentable

end FiberedCategoryOver.Groupoids

end CategoryTheory
