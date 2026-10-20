module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence of inverse-image Hom categories

This leaf records the equivalence instance for the inverse-image/direct-image Hom functor.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace StackOver.InverseImage

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- The bundled specialization of the generic inverse-image/direct-image Hom equivalence. -/
@[stacks 04WK]
instance homFunctor.isEquivalence
    [u.IsContinuous J K]
    {S : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (T : StackOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} K) :
    (homFunctor I T).IsEquivalence := sorry

end StackOver.InverseImage

end CategoryTheory
