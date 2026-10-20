/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.BaseChange

/-!
# Base change of surjective morphisms of algebraic spaces

The base change of a surjective morphism of algebraic spaces by any morphism of
algebraic spaces is again a surjective morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.5.5: The base change of a surjective morphism of algebraic spaces is
surjective. -/
@[stacks 03MH] #check (AlgebraicGeometry.AlgebraicSpace.surjective_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Surjective S :
      MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
