/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
import StacksCheckRecall

/-!
# Composition of surjective morphisms of algebraic spaces

The composition of a pair of surjective morphisms of algebraic spaces is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.5.4: The composition of surjective morphisms is surjective. -/
@[stacks 03MG] #check (AlgebraicGeometry.AlgebraicSpace.surjective_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.Surjective f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective g],
    AlgebraicGeometry.AlgebraicSpace.Surjective (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.surjective_isStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@AlgebraicGeometry.AlgebraicSpace.Surjective S : MorphismProperty (AlgebraicSpace S)))
