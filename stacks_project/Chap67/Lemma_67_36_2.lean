/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.Stability
import StacksCheckRecall

/-!
# Composition of syntomic morphisms of algebraic spaces

The composition of a pair of syntomic morphisms of algebraic spaces is
syntomic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.36.2: The composition of syntomic morphisms is syntomic. -/
@[stacks 03Z8] #check
  (AlgebraicGeometry.AlgebraicSpace.syntomic_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.syntomic_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Syntomic f] [Syntomic g],
    Syntomic (f ≫ g))
