/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

open CategoryTheory CategoryTheory.Limits

@[expose] public section

universe w v u uA vA

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (Φ : J.Point.{w})
variable {A : Type uA} [Category.{vA} A]

/-- The fiber functor of a site point is exact on presheaves under AB5 hypotheses. -/
theorem presheafFiber_exact
    [LocallySmall.{w} C] [HasFiniteLimits A] [HasColimitsOfSize.{w, w} A]
    [HasProducts.{w} A]
    [HasFilteredColimitsOfSize.{max w vA, max w vA} A]
    [AB5OfSize.{max w vA, max w vA} A] :
    exactFunctor (Cᵒᵖ ⥤ A) A (Φ.presheafFiber (A := A)) := sorry

/-- The fiber functor of a site point is exact on sheaves under AB5 hypotheses. -/
theorem sheafFiber_exact
    [LocallySmall.{w} C] [HasFiniteLimits A] [HasColimitsOfSize.{w, w} A]
    [HasProducts.{w} A]
    [HasFilteredColimitsOfSize.{max w vA, max w vA} A]
    [AB5OfSize.{max w vA, max w vA} A] :
    exactFunctor (Sheaf J A) A (Φ.sheafFiber (A := A)) := sorry

end CategoryTheory.GrothendieckTopology.Point
