/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Coherent

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/-- Over a coherent commutative ring, a filtered-colimit-preserving extension to module
categories of a left exact functor between finitely presented module categories preserves
finite limits. -/
theorem filteredColimitExtension_preservesFiniteLimits_of_coherent_toModuleCat
    {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [PreservesFiniteLimits (F ⋙ (isFinitePresentation.{v, max u v} B).ι)]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    PreservesFiniteLimits F' := sorry

end ModuleCat
