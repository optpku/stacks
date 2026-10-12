/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction

/-!
# Equivalence of bundled pushforward-pullback Hom categories

The cartesian Hom comparison is an equivalence; this file transports that fact to the canonical
Hom categories of bundled fibered categories.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Lemma 8.12.8 (tag 04WI): the fixed-universe pushforward-pullback Hom functor associated
to an explicit projection choice is an equivalence. -/
@[stacks 04WI "fixed-universe pushforward-pullback Hom equivalence"]
instance homFunctor.isEquivalence
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (hX : ProjectionChoice u X)
    (Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D) :
    (homFunctor u hX Y).IsEquivalence := sorry

end FiberedCategoryOver.Pushforward

end CategoryTheory
