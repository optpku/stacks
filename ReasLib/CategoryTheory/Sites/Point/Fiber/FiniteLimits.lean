module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Functor.PresheafFiber
public import ReasLib.CategoryTheory.Functor.TypeValued.FiniteLimits

/-!
# Finite-limit tests for fibers of site points

This module turns the concrete finite-limit test for a `Type`-valued functor
into the left-exactness statement needed by the associated sheaf fiber.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point.Fiber.Stalk

variable {C : Type u} [Category.{v} C]

/-- The sheaf fiber of a `Type`-valued functor preserves finite limits when its terminal fiber is
a singleton and its pullback comparisons are bijective. -/
theorem preservesFiniteLimits
    (J : GrothendieckTopology C) [HasTerminal C] [HasPullbacks C]
    (F : C ⥤ Type (max u v)) [InitiallySmall.{max u v} F.Elements]
    (h_terminal : Unique (F.obj (⊤_ C)))
    (h_pullback : FunctorToTypes.PullbackComparison.bijective F) :
    PreservesFiniteLimits (sheafToPresheaf J (Type (max u v)) ⋙ F.presheafFiber) := sorry

end CategoryTheory.GrothendieckTopology.Point.Fiber.Stalk
