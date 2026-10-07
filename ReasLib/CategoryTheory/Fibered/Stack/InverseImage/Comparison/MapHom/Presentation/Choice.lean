module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Choice
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.OfHomQuasiInverse.Coherence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Presentation
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Presentation.InversionChoice

/-!
# Choice naturality of inverse-image morphism presentation independence

The comparison between the direct and Hom-quasi-inverse presentations is compatible with changing
either quasi-inverse input or the pushforward inversion proof.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.mapHom

variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

set_option maxHeartbeats 800000 in
/-- Presentation independence is natural in the chosen quasi-inverse of the canonical Hom
functor. -/
@[stacks 04WS "presentation Hom-choice comparison"]
theorem homQuasiInverseIso.homChoice
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom q_hom' : Functor.QuasiInverse (homFunctor I I'.target)) :
    homQuasiInverseIso I I' h q_stack q_hom ≪≫
        mapHom.ofHomQuasiInverse.choiceIso I I' q_hom q_hom' =
      homQuasiInverseIso I I' h q_stack q_hom' := sorry

/-- The forward Hom-choice square for presentation independence commutes objectwise. -/
@[stacks 04WS "presentation Hom-choice forward component"]
theorem homQuasiInverseIso.hom.homChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom q_hom' : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homQuasiInverseIso I I' h q_stack q_hom).hom.app F ≫
        (mapHom.ofHomQuasiInverse.choiceIso I I' q_hom q_hom').hom.app F =
      (homQuasiInverseIso I I' h q_stack q_hom').hom.app F := sorry

/-- The inverse Hom-choice square for presentation independence commutes objectwise. -/
@[stacks 04WS "presentation Hom-choice inverse component"]
theorem homQuasiInverseIso.inv.homChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom q_hom' : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.choiceIso I I' q_hom q_hom').inv.app F ≫
        (homQuasiInverseIso I I' h q_stack q_hom).inv.app F =
      (homQuasiInverseIso I I' h q_stack q_hom').inv.app F := sorry

set_option maxHeartbeats 800000 in
/-- Presentation independence is natural in the stackification quasi-inverse used by the direct
construction. -/
@[stacks 04WS "presentation stack-choice comparison"]
theorem homQuasiInverseIso.stackChoice
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack q_stack' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target)) :
    mapHom.choiceIso I I' h q_stack q_stack' ≪≫
        homQuasiInverseIso I I' h q_stack' q_hom =
      homQuasiInverseIso I I' h q_stack q_hom := sorry

/-- The forward stackification-choice square for presentation independence commutes
objectwise. -/
@[stacks 04WS "presentation stack-choice forward component"]
theorem homQuasiInverseIso.hom.stackChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack q_stack' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (mapHom.choiceIso I I' h q_stack q_stack').hom.app F ≫
        (homQuasiInverseIso I I' h q_stack' q_hom).hom.app F =
      (homQuasiInverseIso I I' h q_stack q_hom).hom.app F := sorry

/-- The inverse stackification-choice square for presentation independence commutes
objectwise. -/
@[stacks 04WS "presentation stack-choice inverse component"]
theorem homQuasiInverseIso.inv.stackChoice_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack q_stack' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homQuasiInverseIso I I' h q_stack' q_hom).inv.app F ≫
        (mapHom.choiceIso I I' h q_stack q_stack').inv.app F =
      (homQuasiInverseIso I I' h q_stack q_hom).inv.app F := sorry

end StackOver.InverseImage.mapHom

end CategoryTheory
