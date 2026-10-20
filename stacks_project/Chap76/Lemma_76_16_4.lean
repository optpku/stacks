/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
import StacksCheckRecall

/-!
# Composition of formally étale morphisms of algebraic spaces

A composition of formally étale morphisms of algebraic spaces is formally
étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.16.4: A composition of formally étale morphisms of algebraic
spaces is formally étale. -/
@[stacks 0612] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.FormallyEtale f]
      [AlgebraicGeometry.AlgebraicSpace.FormallyEtale g],
      AlgebraicGeometry.AlgebraicSpace.FormallyEtale (f ≫ g))

/- Formally étale morphisms of algebraic spaces are stable under composition. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.instIsStableUnderComposition :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.FormallyEtale S :
          MorphismProperty (AlgebraicSpace S)))
