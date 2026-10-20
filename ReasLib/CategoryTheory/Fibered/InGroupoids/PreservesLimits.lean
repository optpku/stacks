module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Limit preservation between categories fibred in groupoids

Based functors between categories fibred in groupoids preserve pullbacks.
Faithful based functors between such categories also preserve equalizers.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory.BasedFunctor

open Limits
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- A based functor between categories fibred in groupoids preserves pullbacks. -/
instance preservesPullbacksInGroupoids (F : X ⥤ᵇ Y)
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p] :
    PreservesLimitsOfShape WalkingCospan F.toFunctor := sorry

/-- A faithful based functor between categories fibred in groupoids preserves equalizers. -/
instance preservesEqualizersInGroupoids (F : X ⥤ᵇ Y)
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.Faithful F.toFunctor] :
    PreservesLimitsOfShape WalkingParallelPair F.toFunctor := sorry

end CategoryTheory.BasedFunctor
