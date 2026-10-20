/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact.Descent
import StacksCheckRecall

/-!
# Descent of quasi-compact morphisms of algebraic spaces

Quasi-compactness of morphisms of algebraic spaces descends along universally
open surjections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

/- Lemma 67.8.7: Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme
`S`, and let `g : Y' ⟶ Y` be universally open and surjective. If a base change of
`f` along `g` is quasi-compact, then `f` is quasi-compact. -/
@[stacks 04ZJ] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_descendsAlong_universallyOpen_inf_surjective :
    ∀ {S : Scheme.{u}}, CategoryTheory.MorphismProperty.DescendsAlong
      (@AlgebraicGeometry.AlgebraicSpace.QuasiCompact S :
        CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
      ((@AlgebraicGeometry.AlgebraicSpace.UniversallyOpen S :
        CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)) ⊓
        (@AlgebraicGeometry.AlgebraicSpace.Surjective S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))))

#check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.of_universallyOpen_surjective :
  ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [AlgebraicSpace.UniversallyOpen g] [AlgebraicSpace.Surjective g]
    [AlgebraicSpace.QuasiCompact f'],
    IsPullback f' g' g f → AlgebraicSpace.QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.of_pullback_snd_of_universallyOpen_surjective :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicSpace.UniversallyOpen g] [AlgebraicSpace.Surjective g]
    [HasPullback f g] [AlgebraicSpace.QuasiCompact (pullback.snd f g)],
    AlgebraicSpace.QuasiCompact f)
