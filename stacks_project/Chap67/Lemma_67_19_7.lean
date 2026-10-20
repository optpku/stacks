/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Composition
import StacksCheckRecall

/-!
# Composition of universally injective morphisms of algebraic spaces

The composition of a pair of universally injective morphisms of algebraic spaces
is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.19.7: The composition of universally injective morphisms of algebraic
spaces is universally injective. -/
@[stacks 03MY] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyInjective_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.UniversallyInjective S :
        MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.universallyInjective_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f]
    [AlgebraicGeometry.AlgebraicSpace.UniversallyInjective g],
    AlgebraicGeometry.AlgebraicSpace.UniversallyInjective (f ≫ g))
