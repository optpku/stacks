/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Perfect.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.47.3: A composition of perfect morphisms is perfect. -/
@[stacks 06C1]
#check (AlgebraicGeometry.AlgebraicSpace.Perfect.comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Perfect f] [Perfect g], Perfect (f ≫ g))

/- Composition stability of the same perfect-morphism property. -/
#check (AlgebraicGeometry.AlgebraicSpace.Perfect.instIsStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@Perfect S : MorphismProperty (AlgebraicSpace S)))
