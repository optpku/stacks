module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse-image Hom functor

This leaf owns the forward Hom functor associated to a chosen inverse-image stack. Computation and
equivalence APIs are kept in focused sibling leaves.
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

/-- Lemma 8.12.10 (tag 04WK): the canonical functor from morphisms out of a chosen inverse-image
stack `I` to morphisms from `S` into the pullback of `T` along `u`. -/
@[stacks 04WK]
noncomputable def homFunctor
    [u.IsContinuous J K]
    {S : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (T : StackOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} K) :
    (I.target ⟶ T) ⥤
      (S ⟶ StackOver.pullback (J := J) (K := K) u T) :=
  StackOver.Hom.precomp T I.comparisonHom ⋙
    FiberedCategoryOver.Pushforward.homFunctor u I.sourceChoice
      T.toFiberedCategoryOver ⋙
      (StackOver.Hom.ambientEquivalence S (StackOver.pullback u T)).functor

end StackOver.InverseImage

end CategoryTheory
