/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Regularity of algebraic spaces descends along locally finitely presented,
flat, surjective morphisms. -/
instance isRegular_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsRegular S : ObjectProperty (AlgebraicSpace S))
      ((@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- The target of a locally finitely presented, flat, surjective morphism of
algebraic spaces with regular source is regular. -/
theorem IsRegular.of_locallyOfFinitePresentation_flat_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Surjective f] [IsRegular X] :
    IsRegular Y :=
  ObjectProperty.of_hom_of_source (P := @IsRegular S)
    (Q := (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end AlgebraicGeometry.AlgebraicSpace
