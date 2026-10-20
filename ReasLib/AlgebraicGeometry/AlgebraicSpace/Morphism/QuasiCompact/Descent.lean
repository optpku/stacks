/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Descent of quasi-compact morphisms of algebraic spaces

Quasi-compactness of morphisms of algebraic spaces descends along universally
open surjections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compactness of morphisms of algebraic spaces over a scheme descends
along universally open surjections. -/
instance quasiCompact_descendsAlong_universallyOpen_inf_surjective {S : Scheme.{u}} :
    MorphismProperty.DescendsAlong
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S))
      ((@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

namespace QuasiCompact

/-- Quasi-compactness of morphisms of algebraic spaces descends along a
universally open surjection, expressed by an `IsPullback` square. -/
theorem of_universallyOpen_surjective {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [UniversallyOpen g] [Surjective g] [QuasiCompact f']
    (h : IsPullback f' g' g f) : QuasiCompact f :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)))
    (Q := ((@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S))))
    h ⟨inferInstance, inferInstance⟩ inferInstance

/-- If `g` is universally open and surjective and the base-change projection
`pullback.snd f g` is quasi-compact, then `f` is quasi-compact. -/
theorem of_pullback_snd_of_universallyOpen_surjective {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [UniversallyOpen g] [Surjective g] [HasPullback f g]
    [QuasiCompact (pullback.snd f g)] : QuasiCompact f :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (f := f) (g := g)
    (P := (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)))
    (Q := ((@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S))))
    ⟨inferInstance, inferInstance⟩ inferInstance

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
