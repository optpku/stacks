/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Finite-limit criteria for type-valued functors

This module packages the concrete terminal-fiber and pullback-comparison tests
which imply finite-limit preservation for a functor into `Type`.  The tests are
kept separate from sites so that they can also be used for ordinary
type-valued functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

namespace PullbackComparison

/-- A `Type`-valued functor has bijective pullback comparisons. -/
def bijective [HasPullbacks C] (F : C ⥤ Type w) : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    Function.Bijective (pullbackComparison F f g)

/-- Bijective pullback comparisons make a `Type`-valued functor preserve pullbacks. -/
theorem preserves [HasPullbacks C] (F : C ⥤ Type w)
    (hF : bijective F) :
    PreservesLimitsOfShape WalkingCospan F := sorry

end PullbackComparison

namespace FiniteLimits

/-- A singleton terminal fiber and bijective pullback comparisons imply preservation of finite
limits by a `Type`-valued functor. -/
theorem of_terminal_and_pullbacks [HasTerminal C] [HasPullbacks C]
    (F : C ⥤ Type w) (h_terminal : Unique (F.obj (⊤_ C)))
    (h_pullback : PullbackComparison.bijective F) :
    PreservesFiniteLimits F := sorry

end FiniteLimits

namespace Elements

/-- The category of elements of a `Type`-valued functor is cofiltered when its terminal fiber is
a singleton and its pullback comparisons are bijective. -/
theorem isCofiltered_of_terminal_and_pullbacks [HasTerminal C] [HasPullbacks C]
    (F : C ⥤ Type w) (h_terminal : Unique (F.obj (⊤_ C)))
    (h_pullback : PullbackComparison.bijective F) :
    IsCofiltered F.Elements := sorry

end Elements

end CategoryTheory.FunctorToTypes
