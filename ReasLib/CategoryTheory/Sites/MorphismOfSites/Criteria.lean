/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Finite-limit criteria for morphisms of sites

This module records the terminal-object and pullback criteria for representable
flatness and morphisms of sites.  The statements are independent of a chosen
presentation in the Stacks Project.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/-- An explicitly chosen terminal object whose image is terminal gives terminal-object
preservation. -/
theorem preservesTerminal_of_isTerminal
    (u : C ⥤ D) (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X)) :
    PreservesLimit (Functor.empty.{0} C) u := sorry

end Functor

namespace RepresentablyFlat

/-- A functor preserving a terminal object and pullbacks is representably flat. -/
theorem of_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    RepresentablyFlat u := sorry

/-- An explicit terminal object whose image is terminal, together with pullback preservation,
makes a functor representably flat. -/
theorem of_terminal_and_pullbacks
    (u : C ⥤ D) (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    RepresentablyFlat u := sorry

end RepresentablyFlat

namespace IsMorphismOfSites

/-- A continuous functor preserving a terminal object and pullbacks
defines a morphism of sites. -/
@[stacks 00X6]
theorem of_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := sorry

/-- A continuous functor carrying an explicit terminal object to a terminal object and preserving
pullbacks defines a morphism of sites. -/
theorem of_terminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K] (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := sorry

/-- A continuous functor with filtered opposite structured-arrow categories is a morphism of
sites. -/
theorem of_filteredStructuredArrow
    (u : C ⥤ D) [u.IsContinuous J K]
    (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) :
    IsMorphismOfSites J K u := sorry

end IsMorphismOfSites

end CategoryTheory
