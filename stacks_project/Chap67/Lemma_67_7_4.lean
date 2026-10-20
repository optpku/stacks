/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive.Composition
import StacksCheckRecall

/-!
# Composition of submersive morphisms of algebraic spaces

The composition of a pair of submersive morphisms of algebraic spaces is
submersive, and the composition of a pair of universally submersive morphisms
of algebraic spaces is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.7.4 (1): The composition of submersive morphisms of algebraic spaces
is submersive. -/
@[stacks 0CFS] #check
  (AlgebraicGeometry.AlgebraicSpace.submersive_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.Submersive S :
        MorphismProperty (AlgebraicSpace S)))

/- Lemma 67.7.4 (2): The composition of universally submersive morphisms of
algebraic spaces is universally submersive. -/
@[stacks 0CFS] #check
  (AlgebraicGeometry.AlgebraicSpace.universallySubmersive_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive S :
        MorphismProperty (AlgebraicSpace S)))
