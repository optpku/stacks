/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Local Noetherianity is inherited from the source of a locally finitely presented,
flat, surjective morphism of algebraic spaces. -/
instance isLocallyNoetherian_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsLocallyNoetherian S : ObjectProperty (AlgebraicSpace S))
      ((@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is locally of finite presentation, flat, and surjective, and
`X` is locally Noetherian, then `Y` is locally Noetherian. -/
theorem IsLocallyNoetherian.of_locallyOfFinitePresentation_flat_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Surjective f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Y :=
  CategoryTheory.ObjectProperty.of_hom_of_source
    (Q := (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end AlgebraicGeometry.AlgebraicSpace
